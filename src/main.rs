// Copyright (C) 2020-2022 Robert Bermani
// Test address: 15hsQvBYKcJzJfKWDHzLN1CzZ8K9WWJbSZ
use anyhow::{bail, Result};
use bitcoin_bech32::WitnessProgram;
use bitvec::prelude::*;
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
    #[clap(short, long, default_value_t = 2_000_000)]
    interval: u32,
}

/// This function calculates the number of combinations nCr,
/// which represents the number of possible combinations that
/// can be obtained by taking a sample of items from a larger set.
/// C(n,r) = n! / (r!(n-r)!) where ! is factorial operator.
fn count_combinations(n: u64, r: u64) -> u64 {
    if r > n {
        0
    } else {
        (1..=r).fold(1, |acc, val| acc * (n - val + 1) / val)
    }
}

/// Given an initial value of Hamming weight n, this function returns Some next value in the lexicographically ordered
/// series of all values of Hamming weight n in 8 bits.
/// It returns None on overflow or after final value in the series
/// # Example
/// For Hamming weight 2:
/// init_value: 0b0000000011
/// lexic_hamming_next(init_value) = Some(0b00000101)
/// lexic_hamming_next(0b00000101) = Some(0b00001001)
fn lexic_hamming_next(v: u8) -> Option<u8> {
    let t: u8 = v | (v - 1);
    let sub = v.trailing_zeros() + 1;
    t.checked_add(1).map(|checked_ovf| checked_ovf | (((!t & ((!(!t))+1)) - 1) >> sub))
}

fn gen_and_check_keys(
    priv_key: &[u8; SECRETKEY_LEN],
    addr: &Arc<HashMap<u64, [u8; RM160_DIGEST_LEN]>>,
) -> bool {
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
        if let Some((_key,val)) = addr.get_key_value(&hash160u) {
            if val == pkey_uncomp_rm160digest.as_slice() {
                return true;
            } else {
                println!("xxHash64 key collision detected. Key hash matched, but not value.");
            }
        }
        if let Some((_key,val)) = addr.get_key_value(&hash160c) {
            if val == pkey_comp_rm160digest.as_slice() {
                return true;
            } else {
                println!("xxHash64 key collision detected. Key hash matched, but not value.");
            }
        }
    }
    false
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

    for (cnt,line) in lines.enumerate() {
        if !line.is_empty() {
            let mut rm160_addr: [u8; 20] = [0; 20];
            if line.starts_with("bc1") {
                let wit_prog = WitnessProgram::from_address(line).unwrap();
                let dec_rm160 = wit_prog.program();
                if dec_rm160.len() != RM160_DIGEST_LEN {
                    bail!("Line: {}: Decoded Bech32 address did not match RM160 digest len. len: {} expected: {}", cnt+1, dec_rm160.len(),
                        RM160_DIGEST_LEN);
                }
                rm160_addr.copy_from_slice(dec_rm160);
            } else {
                let mut raw_addr: [u8; BTC_ADDR_LEN] = [0xFF; BTC_ADDR_LEN];
                bs58::decode(line).into(&mut raw_addr)?;
                rm160_addr.copy_from_slice(&raw_addr[1..21]);
            }

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
    for (thread, addr) in addr_vector.into_iter().enumerate() {
        let fh = Arc::clone(&successfile);
        join_hnds.push(thread::spawn(move || {
            println!("Spawning compute thread {}", thread);
            let mut rng = rand::thread_rng();
            loop {
                //println!("Generating new {} try interval on thread {}", args.interval, thread);
                let rndnum = rng.gen_biguint(SECRETKEY_BITS);
                //for _ in 0..args.interval {
                    let mut rndvec = rndnum.to_bytes_be();
                    rndvec.resize(SECRETKEY_LEN, 0);
                    let rndbytes = <&mut[u8; SECRETKEY_LEN]>::try_from(rndvec.as_mut_slice()).unwrap();
                    for x in 0..SECRETKEY_BITS {
                        let immut_byteref: &_ = rndbytes;
                        //println!("{} {:?}", x, rndbytes);
                        if gen_and_check_keys(immut_byteref, &addr) {
                            println!("Found a secret key matching an address in address list format:");
                            println!("PrivKey: {:?}", rndbytes);
                            let mut f = fh.lock().unwrap();
                            writeln!(&mut f, "Private Key: {:?}", rndbytes)
                                .expect("File Write Failed");
                            f.flush().expect("File Flush Failed");
                        }
                        let rndbits = rndbytes.view_bits_mut::<Msb0>();
                        rndbits.rotate_left(1);
                    }
                    //println!("Shifted 256 times");
                    //rndnum += 1_u32;
                //}
            }
        }));
    }

    for hnd in join_hnds {
        let _ = hnd.join();
    }

    Ok(())
}
