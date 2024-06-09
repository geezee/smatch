/*
smatch -- regexes for trees; grep for s-exprs

Copyright (C) 2024  George Zakhour

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

use std::fmt::{Debug, Formatter};
use std::rc::{Rc};
use std::fs::{read_to_string, metadata, read_dir};
use std::io::{stdin};

use std::collections::HashMap;

use clap::{Parser};
use regex::{Regex};



macro_rules! one_of {
  ($c:expr) => { false };
  ($c:expr, $opt:expr $(,$opts:expr)*) => { ($c == $opt || one_of!($c $(,$opts)*)) };
}

// when .iter().map() is not enough
macro_rules! vec_map { ($var:ident in $lst:expr => $f:expr) => {{
  let mut result = vec![];
  for $var in $lst { result.push($f); }
  result
}};}

macro_rules! err  { ($($args:expr),*) => { Err(SmatchError(format!($($args),*))) };}
macro_rules! err2 { ($($args:expr),*) => {     SmatchError(format!($($args),*))  };}



enum Either<S,T> {
  Left(S),
  Right(T),
}

impl<S,T> Either<S,T> {
  fn from_result(r: Result<S,T>) -> Either<S,T> { match r {
    Ok(a) => Either::Left(a),
    Err(b) => Either::Right(b),
  }}
}


struct SmatchError(String);

impl Debug for SmatchError {
  fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
    write!(fmt, "{}", self.0)
  }
}



#[derive(PartialEq)]
enum Token {
  OpenParen(usize),
  CloseParen(usize),
  Numeral(usize, usize),
  Decimal(usize, usize),
  Str(usize, usize),
  Symbol(usize, usize),
}

#[derive(Debug, Clone, PartialEq)]
enum Literal<'a> {
  Numeral(usize),
  Decimal(f64),
  Str(&'a str),
  Symbol(&'a str),
}

#[derive(Debug, Clone, PartialEq)]
enum SExpr<'a> {
  Atom(Literal<'a>),
  List(Vec<SExpr<'a>>),
}


enum SExprParser {} impl SExprParser {
  fn next_token (contents: &str, cursor: &mut usize) -> Result<Token, SmatchError> {{{
    use Token::*;
    let bytes = contents.as_bytes();

    macro_rules! inbounds { () => {*cursor < bytes.len()};}
    macro_rules! current { () => {bytes[*cursor] as char};}
    macro_rules! consume { () => {{let c = current!(); *cursor += 1; c }}; }
    macro_rules! peek { () => {if *cursor+1 >= bytes.len() { None } else { Some(bytes[*cursor+1] as char) }}; }

    fn valid_id_char(c: char) -> bool {
      ('a'<=c && c<='z') || ('A'<=c && c<='Z') || ('0'<=c && c<='9') ||
      one_of!(c, '~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.' , '?', '/', ':')
    }

    // skip whitespace
    while inbounds!() && one_of!(bytes[*cursor] as char, ' ', '\n', '\r', '\t') { *cursor += 1; }

    if !inbounds!() { return err!("End-of-input") }

    let token_start = *cursor;

    let result = match consume!() {
      ';' => {
        while inbounds!() && !one_of!(current!(), '\n', '\r') { consume!(); }
        Self::next_token(contents, cursor)
      },
      '(' => Ok(OpenParen(*cursor-1)),
      ')' => Ok(CloseParen(*cursor-1)),
      '0'..='9' => {
        while inbounds!() && '0' <= current!() && current!() <= '9' { consume!(); }
        Ok(if inbounds!() && current!() == '.' {
          consume!();
          while inbounds!() && '0' <= current!() && current!() <= '9' { consume!(); }
          Decimal(token_start, *cursor)
        } else {
          Numeral(token_start, *cursor)
        })
      },
      '"' => loop {
        if !inbounds!() { break err!("{}: Non-terminated string", *cursor-1) }
        if current!() == '"' && peek!() == Some('"') {
          consume!();
        } else if current!() == '"' {
          consume!(); break Ok(Str(token_start+1, *cursor-1))
        }
        consume!();
    },
      '|' => loop {
        if !inbounds!() { break err!("{}: Non-terminated quoted symbol", *cursor-1) }
        if current!() == '\\' { break Err(SmatchError(format!("{cursor}: \\ not allowed in quoted symbols"))) }
        if current!() == '|' { consume!(); break Ok(Symbol(token_start+1, *cursor-1)) }
        consume!();
      }
      c if valid_id_char(c) => loop {
        if !inbounds!() || !valid_id_char(current!()) { break Ok(Symbol(token_start, *cursor)) }
        consume!();
      }
      c => err!("{}: Illegal character {c}", *cursor-1)
    };

    while inbounds!() && one_of!(bytes[*cursor] as char, ' ', '\n', '\r', '\t') { *cursor += 1; }

    result
  }}}

  fn parse<'a>(contents: &'a str) -> impl Iterator<Item=Either<(SExpr<'a>, usize, usize), SmatchError>> {{{
    use Token::*;
    use SExpr::*;

    fn aux<'a>(contents: &'a str, cursor: &mut usize) -> Result<SExpr<'a>, SmatchError> {
      let token = SExprParser::next_token(contents, cursor)?;
      match token {
        CloseParen(_) => err!("{cursor}: Too many closing parentheses"),
        Numeral(start, end) => Ok(Atom(Literal::Numeral(
          contents[start..end].parse().map_err(|_| err2!("{cursor}: Could not parse number"))?))),
        Decimal(start, end) => Ok(Atom(Literal::Decimal(
          contents[start..end].parse().map_err(|_| err2!("{cursor}: Could not parse number"))?))),
        Str(start, end) => Ok(Atom(Literal::Str(&contents[start..end]))),
        Symbol(start, end) => Ok(Atom(Literal::Symbol(&contents[start..end]))),
        OpenParen(_) => {
          let mut vec = vec![];
          loop {
            let old_cursor = *cursor;
            let token = SExprParser::next_token(contents, cursor)?;
            if let CloseParen(_) = token {
              break;
            } else {
              *cursor = old_cursor;
              vec.push(aux(contents, cursor)?);
            }
          };
          Ok(List(vec))
        }
      }
    }

    struct ParseIterator<'a> {
      contents: &'a str,
      cursor: usize
    }

    impl<'a> Iterator for ParseIterator<'a> {
      type Item=Either<(SExpr<'a>, usize, usize), SmatchError>;

      fn next(&mut self) -> Option<Self::Item> {
        let start = self.cursor;
        if self.cursor >= self.contents.len() { None }
        else {
          let result = aux(self.contents, &mut self.cursor);
          let result_with_pos = result.map(|r| (r, start, self.cursor));
          Some(Either::from_result(result_with_pos))
        }
      }
    }

    ParseIterator { contents, cursor: 0 }
  }}}

  fn print_sexpr<'a>(filename: &'a str, content: &'a str, start: usize, end: usize, opts: &Cli) {{{
    let bytes = content.as_bytes();

    let mut start = start;
    let mut in_comment = false;
    loop {
      if start >= bytes.len() { return }
      let b = bytes[start];
      if in_comment && b == b'\n' { in_comment = false; }
      if !in_comment && b == b';' { in_comment = true; }
      if !in_comment && !one_of!(b, b' ', b'\n', b'\r', b'\t') { break }
      start += 1;
    }

    let mut line = 1;
    let mut preamble = if opts.line_number {
      for i in 0..start {
        if bytes[i] == b'\n' {
          line += 1;
        }
      }
      format!("{filename}:{line}:")
    } else { String::new() };

    let mut i = start;
    while i < end {
      if bytes[i] == b'\n' {
        println!("{preamble}{}", String::from_utf8(bytes[start..i].to_vec()).unwrap());
        start = i+1;
        if opts.line_number {
          line += 1;
          preamble = std::iter::repeat(' ').take(preamble.len()).collect();
        }
      }
      i += 1;
    }

    if start < i {
      println!("{preamble}{}", String::from_utf8(bytes[start..i].to_vec()).unwrap());
    }
  }}}
}


#[derive(Debug, Clone)]
struct Env<'a> {
  bindings: HashMap<&'a str, Rc<Pattern<'a>>>,
  parent: Option<&'a Env<'a>>
}

impl<'a> Default for Env<'a> {
  fn default() -> Self {
    Env { bindings: HashMap::new(), parent: None }
  }
}

impl<'a> Env<'a> {
  fn extend(&mut self, var: &'a str, binding: &'_ Rc<Pattern<'a>>) {
    self.bindings.insert(var, binding.clone());
  }

  fn get(&self, var: &'_ str) -> Option<Rc<Pattern<'a>>> {
    self.bindings.get(var).cloned().or_else(|| self.parent.and_then(|p| p.get(var)))
  }

  fn fork(&self) -> Env<'_> {
    Env { bindings: HashMap::new(), parent: Some(self) }
  }
}



#[derive(Debug, Clone)]
enum Multiplicity {
  Zero,
  Once,
  ZeroOrMore,
  OneOrMore,
  ZeroOrOne,
  LessThan(u16),
  MoreThan(u16),
  Between(u16, u16),
}

#[derive(Debug, Clone)]
enum Pattern<'a> {
  Wildcard,
  Atom,
  Literal(&'a Literal<'a>),
  Var(&'a str),
  Re(Regex),
  Choice(Vec<Pattern<'a>>),
  And(Vec<Pattern<'a>>),
  List(Vec<Pattern<'a>>),
  Repeat(Multiplicity, Rc<Pattern<'a>>),
  Depth(Multiplicity, Rc<Pattern<'a>>),
  Let(HashMap<&'a str, Rc<Pattern<'a>>>, Rc<Pattern<'a>>)
}


impl Multiplicity {
  fn from<'a>(sexpr: &'a SExpr<'a>) -> Result<(Multiplicity, Pattern<'a>), SmatchError> {{{
    use SExpr::*;
    use Multiplicity::*;
    use Literal::*;

    match sexpr {
      List(lst) => match &lst[..] {
        [Atom(Symbol("@*")), pattern] => Ok((ZeroOrMore, Pattern::from(pattern)?)),
        [Atom(Symbol("@+")), pattern] => Ok((OneOrMore, Pattern::from(pattern)?)),
        [Atom(Symbol("@?")), pattern] => Ok((ZeroOrOne, Pattern::from(pattern)?)),
        [Atom(Symbol("@less")), Atom(Numeral(n)), pattern] => {
          let n = (*n).try_into().map_err(|_| err2!("{n} is too large for @less"))?;
          Ok((LessThan(n), Pattern::from(pattern)?))
        },
        [Atom(Symbol("@more")), Atom(Numeral(n)), pattern] => {
          let n = (*n).try_into().map_err(|_| err2!("{n} is too large for @more"))?;
          Ok((MoreThan(n), Pattern::from(pattern)?))
        },
        [Atom(Symbol("@between")), Atom(Numeral(n)), Atom(Numeral(m)), pattern] if *n < *m => {
          let n = (*n).try_into().map_err(|_| err2!("{n} is too large for @between"))?;
          let m = (*m).try_into().map_err(|_| err2!("{m} is too large for @between"))?;
          Ok((Between(n, m), Pattern::from(pattern)?))
        },
        [Atom(Symbol(cmd @ ("@*" | "@+" | "@?" | "@less" | "@more" | "@between"))), ..]
          => err!("Wrong arguments to {cmd}"),
        _ => Ok((Once, Pattern::from(sexpr)?)),
      }
      Atom(_) => Ok((Once, Pattern::from(sexpr)?)),
    }.map(|(m,p)| (m.canonical(), p))
  }}}

  // canonical guarantees that the arguments of LessThan, MoreThan, and Between are always >=1
  fn canonical(&self) -> Multiplicity {{{ use Multiplicity::*; match self {
    LessThan(0) => Zero,
    LessThan(1) => ZeroOrOne,
    MoreThan(0) => ZeroOrMore,
    MoreThan(1) => OneOrMore,
    Between(1,1) => Once,
    Between(0,n) => LessThan(*n).canonical(),
    _ => self.clone(),
  }}}}

  fn decrease(&self) -> Result<Multiplicity, ()> {{{ use Multiplicity::*;
    match self.canonical() {
      Zero => Err(()),
      Once => Ok(Zero),
      ZeroOrMore => Ok(ZeroOrMore),
      OneOrMore => Ok(ZeroOrMore),
      ZeroOrOne => Ok(Zero),
      LessThan(n) => Ok(LessThan(n-1)),
      MoreThan(n) => Ok(MoreThan(n-1)),
      Between(n, m) => Ok(Between(n-1, m-1)),
    }.map(|m| m.canonical())
  }}}

  fn allows(&self, n: usize) -> bool {{{
    use Multiplicity::*;
    match self {
      Zero => n == 0,
      Once => n == 1,
      ZeroOrMore => true, // n >= 0 is useless
      OneOrMore => n >= 1,
      ZeroOrOne => n == 0 || n == 1,
      LessThan(m) => n <= ((*m).into()),
      MoreThan(m) => n >= ((*m).into()),
      Between(m1, m2) => n >= ((*m1).into()) && n <= ((*m2).into()),
    }
  }}}

  // return [n, m) such that at least n (inclusive) must match and at most m (inclusive) must match
  fn range(&self, infty: usize) -> (usize, usize) {{{
    use Multiplicity::*;
    match self {
      Zero => (0, 0),
      Once => (1, 1),
      ZeroOrMore => (0, infty),
      OneOrMore => (1, infty),
      ZeroOrOne => (0, 1),
      LessThan(n) => (0, <u16 as Into<usize>>::into(*n)),
      MoreThan(n) => ((*n).into(), infty),
      Between(n1, n2) => ((*n1).into(), (*n2).into()),
    }
  }}}
}


impl<'a> Pattern<'a> {
  fn from(sexpr: &'a SExpr<'a>) -> Result<Pattern<'a>, SmatchError> {{{
    use SExpr::*;
    use Literal::*;
    match sexpr {
    Atom(Symbol("@_")) => Ok(Pattern::Wildcard),
    Atom(Symbol("@atom")) => Ok(Pattern::Atom),
    Atom(Symbol(name)) if name.as_bytes()[0] == b'@' => Ok(Pattern::Var(name)),
    Atom(lit) => Ok(Pattern::Literal(lit)),
    List(lst) => match &lst[..] {
      [Atom(Symbol("@re")), Atom(Str(re))] =>
        Ok(Pattern::Re(Regex::new(&str::replace(re, "\"\"", "\"")).unwrap())),
      [Atom(Symbol("@*"|"@+"|"@?"|"@less"|"@more"|"@between")), ..] => {
        let (repeat, pattern) = Multiplicity::from(sexpr)?;
        Ok(Pattern::Repeat(repeat, Rc::new(pattern)))
      },
      [Atom(Symbol("@depth")), repeat] => {
        let (repeat, pattern) = Multiplicity::from(repeat)?;
        Ok(Pattern::Depth(repeat, Rc::new(pattern)))
      },
      [Atom(Symbol("@or")), patterns @ ..] if patterns.len() > 0 =>
        Ok(Pattern::Choice(vec_map!(p in patterns => Pattern::from(p)?))),
      [Atom(Symbol("@and")), patterns @ ..] if patterns.len() > 0 =>
        Ok(Pattern::And(vec_map!(p in patterns => Pattern::from(p)?))),
      [Atom(Symbol("@let")), parts @ ..] if parts.len() > 0 => {
        let mut bindings = HashMap::new();
        for part in &parts[..parts.len()-1] { match part {
          Atom(_) => err!("the variable and its bound pattern are parenthesised")?,
          List(lst) => match &lst[..] {
            [Atom(Symbol(var)), p] => {
              bindings.insert(&var[..], Rc::new(Pattern::from(p)?));
            },
            _ => err!("Wrong binding argument to @let")?
          }
        }}
        let subpattern = Pattern::from(&parts[parts.len()-1])?;
        Ok(Pattern::Let(bindings, Rc::new(subpattern)))
      },
      [Atom(Symbol(cmd @ ("@re" | "@depth" | "@or" | "@and" | "@let"))), ..]
        => err!("Wrong arguments to {cmd}"),
      [patterns @ ..] => Ok(Pattern::List(vec_map!(x in patterns => Pattern::from(x)?))),
    }}
  }}}

  // return [n, m) such that at least n (inclusive) must match and at most m (inclusive) must match
  fn range(&self, infty: usize) -> (usize, usize) {{{
    use Pattern::*;

    match self {
      Wildcard | Atom | Literal(_) | Re(_) | List(_) | Depth(_,_) => (1, 1),
      Choice(ps) => {
        let ranges = ps.iter().map(|p| p.range(infty));
        (ranges.clone().map(|bs| bs.0).min().unwrap(), ranges.map(|bs| bs.1).max().unwrap())
      },
      And(ps) => {
        let ranges = ps.iter().map(|p| p.range(infty));
        (ranges.clone().map(|bs| bs.0).max().unwrap(), ranges.map(|bs| bs.1).min().unwrap())
      },
      Repeat(mult, p) => {
        let (min1, max1) = mult.range(infty);
        let (min2, max2) = p.range(infty);
        (min1 * min2, max1 * max2)
      },
      // let's not analyze environments here
      Let(_, _) => (0, infty),
      Var(_) => (0, infty),
    }
  }}}
}


impl<'a> Pattern<'a> {
  fn check<'b, 'c>(&self, sexpr: &'b SExpr<'a>, env: &'c Env<'a>) -> bool {{{
    use Pattern::*;

    match (self, sexpr) {
      (Literal(lit1), SExpr::Atom(lit2))
        => *lit1 == lit2,

      (Re(re), SExpr::Atom(crate::Literal::Symbol(id)))
        => re.is_match(id),

      (Wildcard, _)
        => true,

      (Pattern::Atom, SExpr::Atom(_))
        => true,

      (Var(var), term)
        => env.get(var).map(|p| p.check(term, env)).unwrap_or(false),

      (Choice(patterns), sexpr)
        => patterns.iter().any(|p| p.check(sexpr, env)),

      (And(patterns), sexpr)
        => patterns.iter().all(|p| p.check(sexpr, env)),

      (List(patterns), SExpr::List(terms))
        if patterns.len() == 0
        => terms.len() == 0,

      (List(patterns), SExpr::List(terms))
        => {
          let p = &patterns[0];
          let ps = List(patterns[1..].to_vec());
          let (min, max) = p.range(terms.len());
          for k in (min..=max.min(terms.len())).rev() { // intuition: being greedy is better
            if (k == 0 && p.check(&SExpr::List(vec![]), env)
                       && ps.check(sexpr, env)) ||
               (k == 1 && p.check(&terms[0], env)
                       && ps.check(&SExpr::List(terms[1..].to_vec()) , env)) ||
               (k >= 2 && p.check(&SExpr::List(terms[0..k].to_vec()), env)
                       && ps.check(&SExpr::List(terms[k..].to_vec()), env))
            {
              return true
            }
          }
          return false
        },

      (Repeat(mult, _), SExpr::List(empty))
        if empty.len() == 0
        => mult.allows(0),

      (Repeat(mult, pattern), SExpr::Atom(_))
        => mult.allows(1)
        && pattern.check(sexpr, env),

      (Repeat(mult, p), SExpr::List(terms))
        if terms.len() > 0
        => mult.allows(terms.len())
        && p.check(&terms[0], env)
        && mult.decrease().map_or(false, |m|
             Repeat(m, p.clone()).check(&SExpr::List(terms[1..].to_vec()), env)),

      (Depth(mult, p), SExpr::Atom(_))
        => mult.allows(0)
        && p.check(sexpr, env),

      (Depth(mult, p), SExpr::List(terms))
        => (mult.allows(0) && p.check(sexpr, env))
        || mult.decrease().map_or(false, |m| {
             let p = Depth(m, p.clone());
             terms.iter().any(|t| p.check(t, env))
           }),

      (Let(bindings, pattern), term)
        => {
          let mut env = env.fork();
          for (v, p) in bindings { env.extend(v, p); }
          pattern.check(term, &env)
        }

      // illegal cases:
      (Atom, SExpr::List(_)) |
      (Literal(_), SExpr::List(_)) |
      (List(_), SExpr::Atom(_)) |
      (Re(_), _)
        => false,

      // cases that should be unreachable:
      (Repeat(_,_), SExpr::List(_))
        => unreachable!(),
    }
  }}}
}




#[derive(Parser, Clone)]
#[command(about)]
struct Cli {
  /// The pattern to search for
  pattern: Option<String>,

  /// The file containing the pattern to search for
  #[arg(short='f')]
  pattern_file: Option<String>,

  /// The files to search in for the pattern
  files: Vec<String>,

  /// skip over syntactically incorrect files
  #[arg(short, long, default_value_t=false)]
  ignore_syntax_errors: bool,

  /// display the filename and line number for each match
  #[arg(short='n', long, default_value_t=false)]
  line_number: bool,

  /// recursively read the contents of each directory
  #[arg(short, long, default_value_t=false)]
  recursive: bool,

  /// Invert the sense of matching, to select non-matching s-expr.
  #[arg(short='v', long, default_value_t=false)]
  invert_match: bool,

  /// Only print the number of matches
  #[arg(short, long, default_value_t=false)]
  count: bool,
}


fn handle_contents(pattern: &Pattern<'_>, file: &str, contents: &str, opts: &Cli) -> Result<usize, SmatchError> {{{
  use Either::*;

  let mut num_matches_file = 0;
  for parse_result in SExprParser::parse(contents) { match parse_result {
    Left((sexpr, start, end)) => {
      if pattern.check(&sexpr, &Env::default()) != opts.invert_match {
        if !opts.count {
          SExprParser::print_sexpr(&file, contents, start, end, &opts);
        }
        num_matches_file += 1;
      }
    }
    Right(error) => {
      if opts.ignore_syntax_errors { break; }
      else { return err!("{file}: {error:?}"); }
    }
  }}

  if opts.count {
    println!("{file}:{num_matches_file}");
  }

  Ok(num_matches_file)
}}}

fn handle_args(pattern_str: String, files: &Vec<String>, opts: &Cli) -> Result<usize, SmatchError> {{{
  use Either::*;

  let mut pattern_sexpr = None;
  for (i, parse_result) in SExprParser::parse(&pattern_str).enumerate() {
    if i > 0 { return err!("Only one pattern allowed"); }
    match parse_result {
      Left((p, _, _)) => { pattern_sexpr = Some(p); }
      Right(error) => { return err!("while parsing pattern: {error:?}"); }
    }
  }

  if let None = pattern_sexpr { return err!("No pattern expression found"); }

  let pattern_sexpr = pattern_sexpr.unwrap();
  let pattern = Pattern::from(&pattern_sexpr)
                        .map_err(|error| err2!("while parsing pattern: {error:?}"))?;

  let mut file_queue = files.clone();

  let mut num_matches = 0;

  if files.len() == 0 {
    return handle_contents(&pattern, "/dev/fd/0", &{
      let mut result = String::new();
      for line in stdin().lines() {
        result.push_str(&line.expect("Cannot read from stdin"));
        result.push('\n');
      }
      result
    }, opts);
  }

  while file_queue.len() > 0 {
    let file = file_queue.swap_remove(0);
    let is_dir = metadata(&file).map_or(false, |f| f.file_type().is_dir());

    if is_dir {
      if opts.recursive {
        let mut files = read_dir(&file).unwrap()
          .map(|f| f.unwrap().path().into_os_string().into_string().unwrap()).collect();
        file_queue.append(&mut files);
        continue;
      } else { return err!("{file} is a directory"); }
    }

    num_matches += handle_contents(&pattern, &file, &match read_to_string(&file) {
      Ok(contents) => contents,
      Err(error) => { return err!("{file}: {error}"); }
    }, opts)?;
  }

  Ok(num_matches)
}}}


fn main() -> Result<(), SmatchError> {
  let cli = Cli::parse();

  let num_matches = match cli.clone() {
    Cli { pattern: None, pattern_file: None, .. }
      => err!("Missing pattern argument or pattern file"),
    Cli { pattern: Some(_), pattern_file: Some(_), .. }
      => err!("Expecting either a pattern or a pattern file, not both"),
    Cli { pattern: Some(pattern), files, .. } =>
      handle_args(pattern, &files, &cli),
    Cli { pattern_file: Some(pattern_file), files, .. } => {
      let pattern = read_to_string(&pattern_file);
      match pattern {
        Ok(pattern) => handle_args(pattern, &files, &cli),
        Err(e) => err!("pattern file: {e}"),
      }
    }
  }?;

  if num_matches == 0 {
    std::process::exit(1);
  }

  Ok(())
}
