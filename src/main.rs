
// Privacy-Preserving Transaction Categorization
// using TFHE Library with Parallelization  

// 
use rayon::prelude::*;
use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fs::{self, File},
    io::{BufWriter, Write},
    time::{Duration, Instant},
};
use bloomfilter::Bloom;
use csv::{ReaderBuilder, WriterBuilder};
use regex::Regex;
use serde::{Deserialize, Serialize};
use tfhe::{
    integer::{BooleanBlock, ClientKey, RadixCiphertext, ServerKey},
    shortint::parameters::PARAM_MESSAGE_2_CARRY_2_KS_PBS,
};

// Text preprocessing //
fn clean(raw: &str) -> String {
    let re = Regex::new(r"[a-z0-9]+").unwrap();
    re.find_iter(&raw.to_lowercase())
        .map(|m| m.as_str())
        .collect::<Vec<_>>()
        .join(" ")
}

fn words<'a>(s: &'a str) -> impl Iterator<Item = &'a str> + 'a {
    s.split_whitespace()
}

// CSV / JSON Structs //
#[allow(non_snake_case)]
#[derive(Deserialize)]
struct BankRow {
    ID: u32,
    #[serde(rename = "Transaction Description")]
    Transaction_Description: String,
}

#[derive(Deserialize)]
struct JsonRule {
    category: String,
    patterns: Vec<String>,
}

#[derive(Serialize)]
struct OutputRow {
    ID: u32,
    #[serde(rename = "Transaction Description")]
    desc: String,
    Category: String,
}

#[derive(Serialize)]
struct DebugRow {
    ID: u32,
    #[serde(rename = "Transaction Description")]
    desc: String,
    Status: String,
    CandidateCategories: String,
    CandidatePatternIDs: String,
    NumCandidateCategories: usize,
    NumIndexLookups: usize,
    NumFinalCandidates: usize,
}

// FHE WRAPPER //
#[derive(Clone)]
struct Fhe {
    client: ClientKey,
    server: ServerKey,
}

impl Fhe {
    // Generate the TFHE key pair using the 128‑bit‑security parameters
    fn new() -> Self {
        let client = ClientKey::new(PARAM_MESSAGE_2_CARRY_2_KS_PBS);
        let server = ServerKey::new_radix_server_key(&client);
        Self { client, server }
    }
    fn enc_byte(&self, b: u8) -> RadixCiphertext {
        self.client.encrypt_radix(b as u64, 4)
    }
    fn enc_str(&self, s: &str) -> Vec<RadixCiphertext> {
        s.bytes().map(|b| self.enc_byte(b)).collect()
    }
    fn eq(&self, a: &RadixCiphertext, b: &RadixCiphertext) -> BooleanBlock {
        let (mut x, mut y) = (a.clone(), b.clone());
        self.server.smart_eq(&mut x, &mut y)
    }
    fn and(&self, x: &BooleanBlock, y: &BooleanBlock) -> BooleanBlock {
        self.server.boolean_bitand(x, y)
    }
    fn or(&self, x: &BooleanBlock, y: &BooleanBlock) -> BooleanBlock {
        self.server.boolean_bitor(x, y)
    }
    fn enc_true(&self) -> BooleanBlock {
        self.client.encrypt_bool(true)
    }
    fn enc_false(&self) -> BooleanBlock {
        self.client.encrypt_bool(false)
    }
    fn dec_bool(&self, b: &BooleanBlock) -> bool {
        self.client.decrypt_bool(b)
    }
}

// Encrypted Pattern //
#[derive(Debug, Clone)]
struct PatPart {
    literal: Option<u8>,
    repeat: usize,
}

#[derive(Debug, Clone)]
struct EncPattern {
    parts: Vec<PatPart>,
    enc_bytes: Vec<Option<RadixCiphertext>>,
    expected_len: usize,
    first_lit_offset: usize,
    first_lit_enc: RadixCiphertext,
}

impl EncPattern {
    fn compile(fhe: &Fhe, pat: &str) -> Result<Self, &'static str> {
        let mut parts = Vec::new();
        let mut enc_bytes = Vec::new();
        let bytes = pat.as_bytes();
        let (mut i, mut char_pos) = (0, 0);
        let (mut first_off, mut first_enc) = (usize::MAX, None);
        while i < bytes.len() {
            match bytes[i] as char {
                '.' if i + 1 < bytes.len() && bytes[i + 1] as char == '{' => {
                    let mut j = i + 2;
                    while j < bytes.len() && bytes[j] as char != '}' {
                        j += 1;
                    }
                    if j < bytes.len() {
                        if let Ok(n) = pat[i + 2..j].parse::<usize>() {
                            parts.push(PatPart { literal: None, repeat: n });
                            enc_bytes.extend(std::iter::repeat(None).take(n));
                            char_pos += n;
                            i = j + 1;
                        } else {
                            parts.push(PatPart { literal: Some(b'.'), repeat: 1 });
                            enc_bytes.push(Some(fhe.enc_byte(b'.')));
                            char_pos += 1;
                            i += 1;
                        }
                    } else {
                        parts.push(PatPart { literal: Some(b'.'), repeat: 1 });
                        enc_bytes.push(Some(fhe.enc_byte(b'.')));
                        char_pos += 1;
                        i += 1;
                    }
                }
                '.' => {
                    parts.push(PatPart { literal: None, repeat: 1 });
                    enc_bytes.push(None);
                    char_pos += 1;
                    i += 1;
                }
                c => {
                    parts.push(PatPart { literal: Some(c as u8), repeat: 1 });
                    let ct = fhe.enc_byte(c as u8);
                    enc_bytes.push(Some(ct.clone()));
                    if first_enc.is_none() {
                        first_off = char_pos;
                        first_enc = Some(ct);
                    }
                    char_pos += 1;
                    i += 1;
                }
            }
        }
        first_enc.ok_or("pattern needs literal").map(|fe| Self {
            parts,
            enc_bytes,
            expected_len: char_pos,
            first_lit_offset: first_off,
            first_lit_enc: fe,
        })
    }
    fn sentinel_scan(&self, fhe: &Fhe, enc_tx: &[RadixCiphertext]) -> Vec<BooleanBlock> {
        if enc_tx.len() < self.expected_len {
            return Vec::new();
        }
        let n = enc_tx.len() - self.expected_len + 1;
        (0..n).map(|s| fhe.eq(&self.first_lit_enc, &enc_tx[s + self.first_lit_offset])).collect()
    }
    fn full_match_survivors(
        &self,
        fhe: &Fhe,
        enc_tx: &[RadixCiphertext],
        wins: &[usize],
    ) -> BooleanBlock {
        let mut acc = fhe.enc_false();
        for &w in wins {
            let mut ok = fhe.enc_true();
            for (i, eo) in self.enc_bytes.iter().enumerate() {
                if let Some(b) = eo {
                    let eq = fhe.eq(b, &enc_tx[w + i]);
                    ok = fhe.and(&ok, &eq);
                }
            }
            acc = fhe.or(&acc, &ok);
        }
        acc
    }
}

// Rules Parsing //
struct IndexedPattern {
    id: usize,
    category: String,
    compiled_fhe: EncPattern,
}

fn load_csv(path: &str) -> Result<Vec<BankRow>, Box<dyn Error>> {
    Ok(ReaderBuilder::new()
        .has_headers(true)
        .from_path(path)?
        .deserialize()
        .collect::<Result<_, _>>()?)
}

fn load_rules(
    path: &str,
    fhe: &Fhe,
) -> Result<(Vec<IndexedPattern>, HashMap<String, Bloom<String>>, HashMap<String, Vec<usize>>), Box<dyn Error>> {
    let txt = fs::read_to_string(path)?;
    let raw: Vec<JsonRule> = serde_json::from_str(&txt)?;
    let stop: HashSet<&str> = [
        "a", "an", "and", "as", "at", "be", "by", "for", "from", "in", "is", "it", "of", "on",
        "that", "the", "to", "with", "acct", "payment", "purchase", "online", "transfer", "debit",
    ]
    .iter()
    .cloned()
    .collect();
    let mut pats = Vec::new();
    let mut cat_tokens = HashMap::<String, HashSet<String>>::new();
    let mut inv = HashMap::<String, Vec<usize>>::new();
    let mut pid = 0;
    let mut dbg = BufWriter::new(File::create("rules_debug.txt")?);
    writeln!(dbg, "--- Rule Parsing Log ---")?;
    for jr in raw {
        writeln!(dbg, "\n[CATEGORY] {}", jr.category)?;
        for p in jr.patterns {
            let cl = clean(&p);
            if cl.is_empty() {
                continue;
            }
            match EncPattern::compile(fhe, &cl) {
                Ok(ep) => {
                    pats.push(IndexedPattern {
                        id: pid,
                        category: jr.category.clone(),
                        compiled_fhe: ep,
                    });
                    for w in words(&cl) {
                        if !stop.contains(w) {
                            cat_tokens.entry(jr.category.clone()).or_default().insert(w.into());
                            inv.entry(w.into()).or_default().push(pid);
                        }
                    }
                    pid += 1;
                }
                Err(e) => writeln!(dbg, "ERROR compiling '{}': {}", p, e)?,
            }
        }
    }
    const MAX: usize = 100;
    const FP: f64 = 0.01;
    let mut blooms = HashMap::new();
    for (c, toks) in &cat_tokens {
        let mut bf = Bloom::new_for_fp_rate(MAX, FP);
        for t in toks {
            bf.set(t);
        }
        writeln!(dbg, "\nBuilt Bloom for '{}' with {} tokens", c, toks.len())?; // ← fixed
        blooms.insert(c.clone(), bf);
    }
    dbg.flush()?;
    Ok((pats, blooms, inv))
}

// PIPELINE //
fn process(
    fhe: &Fhe,
    rows: &[BankRow],
    all: &[IndexedPattern],
    blooms: &HashMap<String, Bloom<String>>,
    inv: &HashMap<String, Vec<usize>>,
) -> (Vec<OutputRow>, HashMap<String, Duration>) {
    let mut timings = HashMap::new();

    // Phase.1 : plaintext filtering
    let pre_filter_start = Instant::now();
    let mut maybe_ids = Vec::<u32>::new();
    let mut row_desc = HashMap::<u32, String>::new();
    let mut row_clean = HashMap::<u32, String>::new();
    let mut row_cats = HashMap::<u32, Vec<String>>::new();
    let mut row_pats = HashMap::<u32, Vec<EncPattern>>::new();
    let mut unlisted = Vec::<OutputRow>::new();
    for row in rows {
        let cleaned = clean(&row.Transaction_Description);
        let wv: Vec<String> = words(&cleaned).map(|s| s.to_string()).collect();
        let mut cand_cats: HashSet<String> = blooms // ← type annotation
            .iter()
            .filter(|(_, bf)| wv.iter().any(|w| bf.check(w)))
            .map(|(c, _)| c.clone())
            .collect();
        if cand_cats.is_empty() {
            unlisted.push(OutputRow {
                ID: row.ID,
                desc: row.Transaction_Description.clone(),
                Category: "Unlisted".into(),
            });
            continue;
        }
        let mut ids: HashSet<usize> = HashSet::new();
        for w in &wv {
            if let Some(v) = inv.get(w) {
                ids.extend(v);
            }
        }
        let mut pats = Vec::new();
        let mut cats = Vec::new();
        for &pid in &ids {
            if cand_cats.contains(all[pid].category.as_str()) {
                // ← works now
                pats.push(all[pid].compiled_fhe.clone());
                cats.push(all[pid].category.clone());
            }
        }
        if pats.is_empty() {
            unlisted.push(OutputRow {
                ID: row.ID,
                desc: row.Transaction_Description.clone(),
                Category: "Unlisted".into(),
            });
            continue;
        }
        maybe_ids.push(row.ID);
        row_desc.insert(row.ID, row.Transaction_Description.clone());
        row_clean.insert(row.ID, cleaned);
        row_cats.insert(row.ID, cats);
        row_pats.insert(row.ID, pats);
    }
    timings.insert(
        "Pre-filtering & Preprocessing".to_string(),
        pre_filter_start.elapsed(),
    );

    // Phase.2: encrypt transactions (parallel) //
    let enc_tx_start = Instant::now();
    let enc_map: HashMap<u32, Vec<RadixCiphertext>> = maybe_ids
        .iter()
        .map(|id| (*id, fhe.enc_str(&row_clean[id])))
        .collect();
    timings.insert(
        "Encrypting Transaction Data".to_string(),
        enc_tx_start.elapsed(),
    );

    let matching_start = Instant::now();

    // Phase.3a: Sentinel Scan (Server) //
    let sentinel_scan_start = Instant::now();
    let sentinel_cts: HashMap<u32, Vec<Vec<BooleanBlock>>> = maybe_ids
        .par_iter()
        .map(|id| {
            let enc_tx = &enc_map[id];
            let scans: Vec<_> = row_pats[id]
                .par_iter()
                .map(|p| p.sentinel_scan(fhe, enc_tx))
                .collect();
            (*id, scans)
        })
        .collect();
    timings.insert(
        "Pattern Matching: Sentinel Scan (Server)".to_string(),
        sentinel_scan_start.elapsed(),
    );

    // Phase.3b: Decrypt Sentinel (to identify survivors) //
    let sentinel_decrypt_start = Instant::now();
    let mut survivors = HashMap::<u32, Vec<Vec<usize>>>::new();
    for id in &maybe_ids {
        let vecs: Vec<Vec<usize>> = sentinel_cts[id]
            .iter()
            .map(|v| {
                v.iter()
                    .enumerate()
                    .filter_map(|(i, ct)| if fhe.dec_bool(ct) { Some(i) } else { None })
                    .collect()
            })
            .collect();
        survivors.insert(*id, vecs);
    }
    timings.insert(
        "Pattern Matching: Sentinel Decrypt (Client)".to_string(),
        sentinel_decrypt_start.elapsed(),
    );


    // Phase.3c: Full Homomorphic Pattern Matching (Server) //
    let full_match_start = Instant::now();
    let hit_cts: HashMap<u32, Vec<BooleanBlock>> = maybe_ids
        .par_iter()
        .map(|id| {
            let enc_tx = &enc_map[id];
            let hits: Vec<_> = row_pats[id]
                .par_iter()
                .zip(&survivors[id])
                .map(|(p, surv)| p.full_match_survivors(fhe, enc_tx, surv))
                .collect();
            (*id, hits)
        })
        .collect();
    timings.insert(
        "Pattern Matching: Full Match (Server)".to_string(),
        full_match_start.elapsed(),
    );


    // Phase.3d: Decrypt final results (Client) //
    let final_decrypt_start = Instant::now();
    let mut results = Vec::<OutputRow>::new();
    for id in maybe_ids {
        let mut cat = "Unlisted".to_string();
        for (idx, ct) in hit_cts[&id].iter().enumerate() {
            if fhe.dec_bool(ct) {
                cat = row_cats[&id][idx].clone();
                break;
            }
        }
        results.push(OutputRow {
            ID: id,
            desc: row_desc.remove(&id).unwrap(),
            Category: cat,
        });
    }
    timings.insert(
        "Pattern Matching: Final Decrypt & Categorize".to_string(),
        final_decrypt_start.elapsed(),
    );

    timings.insert(
        "Total Encrypted Pattern Matching".to_string(),
        matching_start.elapsed(),
    );

    results.extend(unlisted);
    (results, timings)
}


fn dur(d: Duration) -> String {
    format!("{:.2?}", d)
}

fn write_csv(rows: &[OutputRow]) -> Result<(), Box<dyn Error>> {
    let mut w = WriterBuilder::new().from_path("result.csv")?;
    w.serialize(("ID", "Transaction Description", "Category"))?;
    for r in rows {
        w.serialize(r)?;
    }
    w.flush()?;
    Ok(())
}

// Main //
fn main() -> Result<(), Box<dyn Error>> {
    let total_start = Instant::now();

    println!("Client: Initializing TFHE Keys...");
    let key_gen_start = Instant::now();
    let fhe = Fhe::new();
    let key_gen_duration = key_gen_start.elapsed();
    println!("  -> Setup Completed in {}", dur(key_gen_duration));

    println!("Client: Loading categorization rules in rules.json...");
    let rules_start = Instant::now();
    let (patterns, blooms, inv) = load_rules("rules.json", &fhe)?;
    let rules_duration = rules_start.elapsed();
    println!("  -> Rules compiled in {}", dur(rules_duration));

    println!("Client: Reading bankstatement.csv...");
    let load_csv_start = Instant::now();
    let rows = load_csv("bankstatement.csv")?;
    let load_csv_duration = load_csv_start.elapsed();
    println!("  -> loaded in {}", dur(load_csv_duration));

    println!("\nHomomorphic processing of {} rows of transactions from bankstatement.csv...", rows.len());
    let (res, process_timings) = process(&fhe, &rows, &patterns, &blooms, &inv);

    let write_csv_start = Instant::now();
    write_csv(&res)?;
    let write_csv_duration = write_csv_start.elapsed();

    println!("\n--- Detailed Execution Time ---");
    println!(
        "1. TFHE Key Generation:                             {}",
        dur(key_gen_duration)
    );
    println!(
        "2. Pre-filtering (Plaintext):                       {}",
        dur(process_timings["Pre-filtering & Preprocessing"])
    );
    println!("3. Data Preprocessing:                              (Included in pre-filtering time)");
    println!(
        "4. Loading & Encrypting Categorization Rules:       {}",
        dur(rules_duration)
    );
    println!("5. Loading & Encrypting Transaction Data:");
    println!(
        "   - Loading from CSV:                            {}",
        dur(load_csv_duration)
    );
    println!(
        "   - Encrypting Transactions:                     {}",
        dur(process_timings["Encrypting Transaction Data"])
    );
    println!("6. Performing Encrypted Pattern Matching:");
    println!(
        "   - Sentinel Scan (Server):                      {}",
        dur(process_timings["Pattern Matching: Sentinel Scan (Server)"])
    );
    println!(
        "   - Sentinel Decrypt (Client):                   {}",
        dur(process_timings["Pattern Matching: Sentinel Decrypt (Client)"])
    );
    println!(
        "   - Full Match (Server):                         {}",
        dur(process_timings["Pattern Matching: Full Match (Server)"])
    );
    println!(
        "   - Final Decrypt (Client):                      {}",
        dur(process_timings["Pattern Matching: Final Decrypt & Categorize"])
    );
    println!("   --------------------------------------------------");
    println!(
        "   Total for Pattern Matching:                    {}",
        dur(process_timings["Total Encrypted Pattern Matching"])
    );
    println!(
        "7. Writing Results to CSV File:                     {}",
        dur(write_csv_duration)
    );
    println!("\nDone – total time including all setup: {}", dur(total_start.elapsed()));

    Ok(())
}
