// Copyright (C) 2020-2022 Robert Bermani
// Test address: 15hsQvBYKcJzJfKWDHzLN1CzZ8K9WWJbSZ
use anyhow::{bail, Result};
use clap::Parser;
use fasthash::xx;
use num_bigint::RandBigInt;
use ripemd::Ripemd160;
use secp256k1::{PublicKey, Secp256k1, SecretKey};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fs::{File, OpenOptions};
use std::io::{prelude::*, BufReader};
use std::str::Lines;
use std::sync::{Arc, Mutex};
use std::thread;

const ADDRESS_FILE: &str = "address.txt";
const BS58_OUT_FILE: &str = "bs58outfile.bin";
const BTC_ADDR_LEN: usize = 25;
const SECRETKEY_LEN: usize = 32;
const RM160_DIGEST_LEN: usize = 20;
const SECRETKEY_BITS: u64 = 256;

/// Application for random brute force attack against Bitcoin address lists.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(short, long)]
    run_single_threaded: bool,
    #[clap(short, long, default_value_t = 100_000_000)]
    interval: u32,
}

fn gen_and_check_keys(
    priv_key: &[u8; SECRETKEY_LEN],
    addr: &Arc<HashMap<u64, [u8; RM160_DIGEST_LEN]>>,
) -> bool {
    let mut found_key = false;
    let secp = Secp256k1::new();
    let secret_key = SecretKey::from_slice(priv_key).expect("32 bytes, within curve order");
    let public_key = PublicKey::from_secret_key(&secp, &secret_key);

    let pubkey_comp = public_key.serialize();
    let pubkey_uncomp = public_key.serialize_uncompressed();

    let mut sh256_hasher = Sha256::new();
    let mut rm160_hasher = Ripemd160::new();

    sh256_hasher.update(pubkey_comp);
    let pkey_comp_sh256digest = sh256_hasher.finalize_reset();

    sh256_hasher.update(pubkey_uncomp);
    let pkey_uncomp_sh256digest = sh256_hasher.finalize();

    rm160_hasher.update(pkey_comp_sh256digest);
    let pkey_comp_rm160digest = rm160_hasher.finalize_reset();

    rm160_hasher.update(pkey_uncomp_sh256digest);
    let pkey_uncomp_rm160digest = rm160_hasher.finalize();

    let hash160c = xx::hash64(&pkey_comp_rm160digest);
    let hash160u = xx::hash64(&pkey_uncomp_rm160digest);

    if addr.contains_key(&hash160c) || addr.contains_key(&hash160u) {
        found_key = true;
    }
    found_key
}

fn read_binfile_lines(hash_map: &mut HashMap<u64, [u8; RM160_DIGEST_LEN]>) -> Result<()> {
    let mut file_vec = Vec::new();
    let file = File::open(BS58_OUT_FILE).expect("File not Found!");
    println!("Loading Base58 Address memoization list.");
    let mut reader = BufReader::new(file);
    let _bytes_rd = reader.read_to_end(&mut file_vec)?;
    for line in file_vec.chunks_exact(RM160_DIGEST_LEN) {
        let h = xx::hash64(&line[..RM160_DIGEST_LEN]);
        hash_map.insert(h, line.try_into().expect("slice with incorrect length"));
    }
    Ok(())
}

fn parse_address_filebyline(filebuf: &mut String) -> Lines<'_> {
    let file = File::open(ADDRESS_FILE).expect("File not Found!");
    let mut reader = BufReader::new(file);
    let _file_len = reader.read_to_string(filebuf).expect("Failed to read file");
    filebuf.lines()
}

fn convert_address_to_rm160bin() -> Result<()> {
    let mut outfile = OpenOptions::new()
        .read(false)
        .write(true)
        .append(false)
        .create(true)
        .open(BS58_OUT_FILE)
        .expect("File not Found!");

    let mut filebuf = String::new();
    let lines = parse_address_filebyline(&mut filebuf);

    for line in lines {
        if !line.is_empty() {
            let mut raw_addr: [u8; BTC_ADDR_LEN] = [0xFF; BTC_ADDR_LEN];
            bs58::decode(line).into(&mut raw_addr)?;

            let mut rm160_addr: [u8; 20] = [0; 20];
            rm160_addr.copy_from_slice(&raw_addr[1..21]);

            outfile.write_all(&rm160_addr)?;
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let args = Args::parse();

    if !std::path::Path::new(BS58_OUT_FILE).exists() {
        println!("Base58 address memoization list doesn't exist, creating.");
        convert_address_to_rm160bin()?;
        println!("Base58 address memoization list was generated successfully.");
    }

    let mut num_cores = 1;

    if !args.run_single_threaded {
        num_cores = num_cpus::get();
        println!("This system provides {} cores", num_cores);
    } else {
        println!("Running in single threaded mode");
    }

    let mut address_map: HashMap<u64, [u8; RM160_DIGEST_LEN]> = HashMap::new();
    read_binfile_lines(&mut address_map)?;
    println!("The address list contains {} addresses", address_map.len());

    // Test address list for known priv/pub keypair
    let test_priv_key: [u8; SECRETKEY_LEN] = [
        185, 254, 205, 82, 80, 165, 32, 181, 60, 76, 54, 34, 4, 151, 89, 25, 118, 184, 104, 68,
        159, 107, 107, 224, 227, 78, 131, 235, 69, 246, 37, 165,
    ];

    let address_list = Arc::new(address_map);

    if !gen_and_check_keys(&test_priv_key, &address_list) {
        println!("Hash Map did not pass the Known Key test.");
        bail!("Known Key test failed!");
    }
    println!("Hash Map passed the Known Key test.");

    let successfile = Arc::new(Mutex::new(
        OpenOptions::new()
            .read(false)
            .append(true)
            .create(true)
            .open("success.txt")
            .expect("File not Found!"),
    ));

    let mut addr_vector = vec![];
    for _ in 0..num_cores {
        addr_vector.push(address_list.clone());
    }

    let mut join_hnds = Vec::new();
    for (cnt, addr) in addr_vector.into_iter().enumerate() {
        let fh = Arc::clone(&successfile);
        join_hnds.push(thread::spawn(move || {
            println!("Spawning compute thread {}", cnt);
            let mut rng = rand::thread_rng();
            loop {
                println!("Generating new {} try interval on thread {}", args.interval, cnt);
                let mut rndnum = rng.gen_biguint(SECRETKEY_BITS);
                for _ in 0..args.interval {
                    let mut rndvec = rndnum.to_bytes_be();
                    if rndvec.len() != SECRETKEY_LEN {
                        rndvec.resize(SECRETKEY_LEN, 0);
                    }
                    let rndbytes = <&[u8; SECRETKEY_LEN]>::try_from(rndvec.as_slice()).unwrap();
                    if gen_and_check_keys(rndbytes, &addr) {
                        println!("Found a secret key matching an address in address list format:");
                        println!("PrivKey: {:?}", rndbytes);
                        let mut f = fh.lock().unwrap();
                        writeln!(&mut f, "Private Key: {:?}", rndbytes)
                            .expect("File Write Failed");
                        f.flush().expect("File Flush Failed");
                    }
                    rndnum += 1_u32;
                }
            }
        }));
    }

    for hnd in join_hnds {
        let _ = hnd.join();
    }

    Ok(())
}
