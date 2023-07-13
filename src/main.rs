#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]
#![allow(unused_variables)]
#![allow(unreachable_code)]

extern crate kic;
extern crate clap;
use clap::{Arg, App};
use kic::*;
use contract;
use kic::term::{Term, definition_book,};
use std::io;
use std::io::prelude::*;
use std::fs::File;
use std::collections::HashMap;

fn main() {
  let matches = App::new("My App")
    .version("1.0")
    .author("Victor Taelin <victor.taelin@gmail.com>")
    .about("Interaction Calculus CLI")
    .arg(Arg::with_name("file")
      .help("The input file to process")
      .required(true)
      .index(1))
    .get_matches();

  let file_name = matches.value_of("file").unwrap();
  let mut file = File::open(file_name).expect("Unable to open the file");
  let mut code = String::new();
  file.read_to_string(&mut code).expect("Unable to read the file");

  let string_ref: &str = &code;

  let parser: Vec<(String, contract::parser::AstTerm)> = contract::parser::parse_contract(string_ref).expect("Parser Err");

  // let modified_vec: Vec<(String, Term)> = parser.iter().map(|(srt, second_elem)| (*srt, contract::parser::AstTerm::from(*second_elem))).collect();
  let modified_vec: Vec<(String, Term)> = parser.into_iter().fold(Vec::new(), |mut acc, (first_elem, second_elem)| {
    // let second_elem = contract::parser::AstTerm::from(second_elem);
    let second_elem = contract::parser::AstTerm::into(second_elem);
    acc.push((first_elem, second_elem ));
    acc
});

  let hashmap: HashMap<String, Term> = modified_vec.iter().cloned().collect();

  let hashmap_clone = hashmap.clone();
  
  let mut definition_book= term::definition_book::DefinitionBook::new(hashmap);

  // let (term, mut definition_) = term::from_string(code.as_bytes());

  let term = hashmap_clone.get("run")
    .cloned()
    .ok_or_else(|| panic!("'def run' not found"))
    .unwrap(); 

  definition_book.print();
  definition_book.extract_closed_subterms();
  definition_book.print();

  let (norm, rules) = term::normalize_with_stats(&term, &definition_book);

  println!("{}\n", norm);
  println!("{:?} rewrites", rules);
}
