use std::fmt;

use logos::{FilterResult, Lexer, Logos};

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(error=LexingError)]
pub enum Token {
  #[regex("[_a-zA-Z][_a-zA-Z0-9]*", |lex| lex.slice().parse().ok())]
  Name(String), // TODO: Figure out a way that we don't need to clone but can pass this token to a static error type

  #[regex(r"\\|λ")]
  Lambda,

  #[token("def")]
  Def,

  #[token("let")]
  Let,

  #[token("dup")]
  Dup,

  #[token("=")]
  Equals,

  #[token(";")]
  Semicolon,

  #[token("@")]
  At,

  #[token(".")]
  Dot,

  #[token("(")]
  LParen,

  #[token(")")]
  RParen,

  #[regex("//.*", logos::skip)]
  SingleLineComment,

  #[token("/*", comment)]
  MultiLineComment,

  #[regex(r"[ \t\f\r\n]+", logos::skip)]
  Whitespace,

  Error(LexingError),
}

#[derive(Default, Debug, PartialEq, Clone)]
pub enum LexingError {
  UnclosedComment,

  #[default]
  InvalidCharacter,
}

// Lexer for nested multi-line comments
#[derive(Logos)]
pub enum MultiLineComment {
  #[token("/*")]
  Open,

  #[token("*/")]
  Close,

  #[regex("(?s).")]
  Other,
}

fn comment<'a>(lexer: &mut Lexer<'a, Token>) -> FilterResult<(), LexingError> {
  let start = lexer.remainder();
  let mut comment = MultiLineComment::lexer(start);
  let mut depth = 1; // Already matched an Open token, so count it
  loop {
    if let Some(token) = comment.next() {
      match token {
        Ok(MultiLineComment::Open) => depth += 1,
        Ok(MultiLineComment::Close) => depth -= 1,
        Ok(MultiLineComment::Other) => {}
        Err(()) => unreachable!(),
      }
    } else {
      // Unclosed comment
      return FilterResult::Error(LexingError::UnclosedComment);
    }
    if depth <= 0 {
      break;
    }
  }
  let end = comment.remainder();
  let span = (end as *const str as *const () as usize) - (start as *const str as *const () as usize);
  lexer.bump(span);
  FilterResult::Skip
}

impl fmt::Display for Token {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Name(s) => write!(f, "{}", s),
      Self::Lambda => write!(f, r"λ"),
      Self::Def => write!(f, "def"),
      Self::Dup => write!(f, "dup"),
      Self::Let => write!(f, "let"),
      Self::Equals => write!(f, "="),
      Self::Semicolon => write!(f, ";"),
      Self::At => write!(f, "@"),
      Self::Dot => write!(f, "."),
      Self::LParen => write!(f, "("),
      Self::RParen => write!(f, ")"),
      Self::SingleLineComment => write!(f, "<SingleLineComment>"),
      Self::MultiLineComment => write!(f, "<MultiLineComment>"),
      Self::Whitespace => write!(f, "<Whitespace>"),
      Self::Error(LexingError::InvalidCharacter) => write!(f, "<InvalidCharacter>"),
      Self::Error(LexingError::UnclosedComment) => write!(f, "<UnclosedComment>"),
    }
  }
}