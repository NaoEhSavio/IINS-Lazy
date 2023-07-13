use super::lexer::Token;

use chumsky::{
  extra,
  input::{Stream, ValueInput},
  prelude::{Input, Rich},
  primitive::{choice, just},
  recursive::recursive,
  select,
  span::SimpleSpan,
  IterParser, Parser,
};
use std::iter::FromIterator;
use term::Term as IcTerm;
use justerror::Error;
use logos::Logos;
use std::{
  collections::HashMap,
  fmt,
};
use std::collections::VecDeque;

pub type VarName = String;

#[Error]
#[derive(PartialEq)]
pub struct ParsingError(#[fmt(debug)] Vec<Rich<'static, Token>>);

#[derive(Debug, Clone, PartialEq)]
pub enum AstTerm {
  Application { terms: Vec<Self> },
  Lambda { vars: Vec<VarName>, body: Box<Self> },
  VarRef { name: VarName },
  // TODO: Dup syntax is disabled, for now dups are always infered.
  // Dup { fst: VarName, snd: VarName, val: Box<AstTerm>, next: Box<AstTerm> },
  Fix { name: VarName, body: Box<AstTerm> },
}

/// Conversion from parser terms into the actual IC terms we're using.
/// Always adds the needed dups so that our result is a valid term.
/// Variable names are not necessarily kept the same.
impl From<AstTerm> for IcTerm {
  fn from(value: AstTerm) -> Self {
    fn go(value: AstTerm) -> IcTerm {
      match value {
        AstTerm::Application { mut terms } => {
          let fun = terms.remove(0);
          let mut app: IcTerm = fun.into();
          for term in terms {
            app = IcTerm::App { fun: Box::new(app), arg: Box::new(term.into()) }
          }
          app
        }
        AstTerm::Lambda { vars, body } => {
          let mut term = Box::new((*body).into());
          for var in vars.into_iter().rev() {
            term = IcTerm::Lam { nam: var.into_bytes(), typ: None, bod: term }.into();
          }
          *term
        }
        AstTerm::VarRef { name } => IcTerm::Var { nam: name.into_bytes() },
        // AstTerm::Dup { fst, snd, val, next } => IcTerm::Dup {
        //   tag: todo!(),
        //   fst: fst.into_bytes(),
        //   snd: snd.into_bytes(),
        //   val: Box::new((*val).into()),
        //   nxt: Box::new((*next).into()),
        // },
        AstTerm::Fix { name, body } => IcTerm::Fix { nam: name.into_bytes(), bod: Box::new((*body).into()) },
      }
    }

    let term = go(value);
    infer_dups(term)
  }
}
// fn to_term (value: AstTerm) -> IcTerm {
//   match value {
//     AstTerm::Application { mut terms } => {
//       let fun = terms.remove(0);
//       let mut app: IcTerm = fun.into();
//       for term in terms {
//         app = IcTerm::App { fun: Box::new(app), arg: Box::new(term.into()) }
//       }
//       app
//     }
//     AstTerm::Lambda { vars, body } => {
//       let mut term = Box::new((*body).into());
//       for var in vars.into_iter().rev() {
//         term = IcTerm::Lam { nam: var.into_bytes(), typ: None, bod: term }.into();
//       }
//       *term
//     }
//     AstTerm::VarRef { name } => IcTerm::Var { nam: name.into_bytes() },
//     // AstTerm::Dup { fst, snd, val, next } => IcTerm::Dup {
//     //   tag: todo!(),
//     //   fst: fst.into_bytes(),
//     //   snd: snd.into_bytes(),
//     //   val: Box::new((*val).into()),
//     //   nxt: Box::new((*next).into()),
//     // },
//     AstTerm::Fix { name, body } => IcTerm::Fix { nam: name.into_bytes(), bod: Box::new((*body).into()) },
//   }
// }

// impl fmt::Display for AstTerm {
//   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//     match self {
//       AstTerm::Application { terms } => {
//         write!(f, "({})", terms.iter().map(Self::to_string).collect::<Vec<_>>().join(" "))
//       }
//       AstTerm::Lambda { vars, body } => write!(f, r"(λ{} . {})", vars.join(" "), body),
//       AstTerm::VarRef { name } => write!(f, "{name}"),
//       AstTerm::Fix { name, body } => write!(f, "(@{name} {body})"),
//     }
//   }
// }

/// Adds the necessary dups to an IC term so that is valid and affine.
fn infer_dups(value: IcTerm) -> IcTerm {
  fn go(value: IcTerm, scope: &mut HashMap<Vec<u8>, usize>) -> IcTerm {
    match value {
      // TODO: Theres some bug causing "\a. (\a. a)" to become
      // "λa λa_0_0 a_0_0" instead of "λa λa_0 a_0" (extra _0 when shadowing).
      // "\a. a (\a. a)" becomes "λa_0 (a_0 λa_0_0_0 a_0_0_0)" (extra _0_0 at the end)
      IcTerm::Lam { nam, typ, bod } => {
        let typ = typ.map(|x| go(*x, scope).into());
        // Add lambda var to scope, shadowing old one if present
        let old_count = scope.insert(nam.clone(), 0);
        let bod = go(*bod, scope).into();
        let num_uses = scope.remove(&nam).unwrap();
        // Unshadow old var
        if let Some(old_count) = old_count {
          scope.insert(nam.clone(), old_count);
        }
        add_dups_to_lam(nam, typ, bod, num_uses)
      }
      IcTerm::Var { nam } => {
        // Count this var use and give it a new unique name
        if let Some(num_uses) = scope.get_mut(&nam) {
          let term = IcTerm::Var { nam: make_dup_name(&nam, *num_uses) };
          *num_uses += 1;
          term
        } else {
          // Unbound var, could be a def, could be actually unbound
          IcTerm::Var { nam }
        }
      }
      IcTerm::App { fun, arg } => IcTerm::App { fun: go(*fun, scope).into(), arg: go(*arg, scope).into() },
      IcTerm::Sup { tag, fst, snd } => {
        IcTerm::Sup { tag, fst: go(*fst, scope).into(), snd: go(*snd, scope).into() }
      }
      IcTerm::Dup { tag, fst, snd, val, nxt } => {
        // There shouldn't be any dups, but if there are pretend they're two lambdas
        let val = go(*val, scope).into();
        let old_count_fst = scope.insert(fst.clone(), 0);
        let old_count_snd = scope.insert(snd.clone(), 0);
        let nxt = go(*nxt, scope).into();
        let num_uses_fst = scope.remove(&fst).unwrap();
        let num_uses_snd = scope.remove(&snd).unwrap();
        if let Some(old_count_fst) = old_count_fst {
          scope.insert(fst.clone(), old_count_fst);
        }
        if let Some(old_count_snd) = old_count_snd {
          scope.insert(snd.clone(), old_count_snd);
        }
        add_dups_to_dup(tag, (fst, snd), val, nxt, (num_uses_fst, num_uses_snd))
      }
      IcTerm::Fix { nam, bod } => IcTerm::Fix { nam, bod: go(*bod, scope).into() },
      IcTerm::Ann { val, typ } => IcTerm::Ann { val: go(*val, scope).into(), typ: go(*typ, scope).into() },
      term @ IcTerm::Set => term,
    }
  }

  fn add_dups_to_lam(nam: Vec<u8>, typ: Option<Box<IcTerm>>, bod: Box<IcTerm>, num_uses: usize) -> IcTerm {
    match num_uses {
      // TODO: It would be nice if the lambda var didn't change names here
      1 => IcTerm::Lam { nam: make_dup_name(&nam, 0), typ, bod },
      num_uses => {
        let bod = add_dups_to_body(&nam, bod, num_uses);
        IcTerm::Lam { nam, typ, bod }
      }
    }
  }

  fn add_dups_to_dup(
    tag: u32,
    (fst, snd): (Vec<u8>, Vec<u8>),
    val: Box<IcTerm>,
    nxt: Box<IcTerm>,
    (num_uses_fst, num_uses_snd): (usize, usize),
  ) -> IcTerm {
    let (fst, nxt) = match num_uses_fst {
      1 => (make_dup_name(&fst, 0), nxt),
      num_uses_fst => {
        let nxt = add_dups_to_body(&fst, nxt, num_uses_fst);
        (fst, nxt)
      }
    };
    let (snd, nxt) = match num_uses_snd {
      1 => (make_dup_name(&snd, 0), nxt),
      num_uses_snd => {
        let nxt = add_dups_to_body(&snd, nxt, num_uses_snd);
        (snd, nxt)
      }
    };
    IcTerm::Dup { tag, fst, snd, val, nxt }
  }

  fn make_dup_name(nam: &[u8], idx: usize) -> Vec<u8> {
    // TODO: Make sure this name is unique and not shadowing something else accidentally
    [nam, b"_", idx.to_string().as_bytes()].concat()
  }

  fn add_dups_to_body(nam: &[u8], mut bod: Box<IcTerm>, num_uses: usize) -> Box<IcTerm> {
    let mut refs = VecDeque::from_iter((0 .. num_uses).map(|i| make_dup_name(&nam, i)));
    let mut idx = num_uses;
    while let (Some(fst), Some(snd)) = (refs.pop_front(), refs.pop_front()) {
      let dup_name = if refs.is_empty() {
        nam.to_vec() // Topmost DUP refers to original lambda var
      } else {
        // Generate new name, using free indices (above `num_uses`)
        let name = make_dup_name(&nam, idx);
        idx += 1;
        refs.push_back(name.clone());
        name
      };
      // TODO: do something with the tag
      bod = IcTerm::Dup { tag: 0, fst, snd, val: IcTerm::Var { nam: dup_name }.into(), nxt: bod }.into();
    }
    bod
  }

  go(value, &mut HashMap::new())
}

/// Kindelia contract parser. Grammar:
/// <name> ::= <alphanumeric_name>
/// <Ref>  ::= <name>
/// <Nested> ::= "(" <Term> ")"
/// <Item> ::= <Ref> | <Nested>
/// <App> ::= <Item> <Item>+
/// <Lam>  ::= ("λ"|"\") <name>+ "." <Term>
/// <Dup>  ::= "dup" <name> <name> "=" <Term> ";" <Term>
/// <Let>  ::= "let" <name> "=" <Term> ";" <Term>
/// <Fix>  ::= "@" <name> <Term>
/// <Term> ::= <Lam> | <App> | <Item> | <Dup> | <Let> | <Fix>
/// <Def> ::= "def" <name> = <Term>
/// <Root> ::= <Def>+
/// 

/// Module for parsing contracts in interaction calculus term form
fn contract_parser<'a, I: ValueInput<'a, Token = Token, Span = SimpleSpan>>()
-> impl Parser<'a, I, Vec<(VarName, AstTerm)>, extra::Err<Rich<'a, Token>>> {
  let name = select!(Token::Name(name) => name.to_string());
  let def = just(Token::Def).ignore_then(name).then_ignore(just(Token::Equals)).then(term_parser());
  def.repeated().collect::<Vec<_>>()
}
fn term_parser<'a, I: ValueInput<'a, Token = Token, Span = SimpleSpan>>()
-> impl Parser<'a, I, AstTerm, extra::Err<Rich<'a, Token>>> {
  let name = select!(Token::Name(name) => name.to_string());

  recursive(|term| {
    let ref_ = name.map(|name| AstTerm::VarRef { name });

    let nested = term.clone().delimited_by(just(Token::LParen), just(Token::RParen));

    let item = ref_.or(nested);

    let app = item
      .clone()
      .repeated()
      .at_least(1)
      .collect::<Vec<_>>()
      // This strange "hack" avoids ambiguity between Items in an App and Items in a Term which can cause large backtracking.
      .map(|mut terms| if terms.len() == 1 { terms.remove(0) } else { AstTerm::Application { terms } });

    let lam = just(Token::Lambda)
      .ignore_then(name.repeated().at_least(1).collect::<Vec<_>>().then_ignore(just(Token::Dot)))
      .then(term.clone())
      .map(|(vars, body)| AstTerm::Lambda { vars, body: body.into() });

    // let dup = just(Token::Dup)
    //   .ignore_then(name)
    //   .then(name)
    //   .then_ignore(just(Token::Equals))
    //   .then(term.clone())
    //   .then_ignore(just(Token::Semicolon))
    //   .then(term.clone())
    //   .map(|(((fst, snd), val), next)| AstTerm::Dup { fst, snd, val: val.into(), next: next.into() });

    let let_ = just(Token::Let)
      .ignore_then(name)
      .then_ignore(just(Token::Equals))
      .then(term.clone())
      .then_ignore(just(Token::Semicolon))
      .then(term.clone())
      .map(|((name, body), next)| AstTerm::Application {
        terms: vec![AstTerm::Lambda { vars: vec![name], body: next.into() }, body.into()],
      });

    let fix = just(Token::At)
      .ignore_then(name)
      .then(term)
      .map(|(name, body)| AstTerm::Fix { name, body: body.into() });

    choice((lam, app, let_, fix))
  })
}

/// Parses some contract source code into an AST or a list of errors.
pub fn parse_contract(code: &str) -> Result<Vec<(VarName, AstTerm)>, ParsingError> {
	let token_iter = Token::lexer(code).spanned().map(|(token, span)| match token {
	  Ok(t) => (t, span.into()),
	  Err(err) => (Token::Error(err), span.into()),
	});
	let token_stream = Stream::from_iter(token_iter).spanned((code.len() .. code.len()).into());
  
	let res = contract_parser()
	  .parse(token_stream)
	  .into_result()
	  .map_err(|vec| ParsingError(vec.into_iter().map(|x| x.into_owned()).collect()));
	res
  }

  pub fn parse_term(code: &str) -> Result<AstTerm, ParsingError> {
    let token_iter = Token::lexer(code).spanned().map(|(token, span)| match token {
      Ok(t) => (t, span.into()),
      Err(err) => (Token::Error(err), span.into()),
    });
    let token_stream = Stream::from_iter(token_iter).spanned((code.len() .. code.len()).into());
  
    let res = term_parser()
      .parse(token_stream)
      .into_result()
      .map_err(|vec| ParsingError(vec.into_iter().map(|x| x.into_owned()).collect()));
    res
  }