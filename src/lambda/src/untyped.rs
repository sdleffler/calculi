use std::borrow::Cow;
use std::cell::Cell;
use std::collections::HashMap;
use std::fmt;

use nom::*;

use ::{get_deepest_custom_error, whitespace};

macro_rules! string {
    ($i:expr, $s:expr) => (fix_error!($i, String, complete!(tag_s!($s))))
}

macro_rules! req_string (
    ($i:expr, $s:expr) => (error!($i, ErrorKind::Custom(format!("Expected token `{}`!", $s)), string!($s)))
);

macro_rules! str_error {
    ($i:expr, $s:expr, $submac:ident ! ($($args:tt)*)) => ({ let res: IResult<&str, _, String> = error!($i, ErrorKind::Custom($s), $submac ! ($($args)*)); res });
    ($i:expr, $s:expr, $func:ident) => (error!($i, ErrorKind::Custom($s), $func));
}

macro_rules! cmd_errval {
    ($i:expr, $s:expr) => ({ let res: IResult<&str, Result<String, String>, String> = value!($i, Err($s)); res });
}

#[derive(Clone, Debug)]
pub enum Expr {
    Lambda(Ident, Box<Expr>),
    Apply(Box<Expr>, Box<Expr>),
    Term(Ident),
}

#[derive(Clone, Debug, Default)]
pub struct Context {
    ident_max: Cell<usize>,
    vals: HashMap<Ident, Expr>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Ident(String, usize);

use self::Expr::*;

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Lambda(ref i, ref body) => write!(f, "λ{}.{}", i, body),
            &Apply(ref lhs, ref rhs) => write!(f, "{} {}", lhs, rhs),
            &Term(ref i) => i.fmt(f),
        }
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let &Ident(ref name, _) = self;
        name.fmt(f)
    }
}

impl<T: AsRef<str>> From<T> for Expr {
    fn from(s: T) -> Expr {
        use nom::IResult::*;
        match expr(s.as_ref(), &Cell::new(0), Cow::Owned(HashMap::new())) {
            Done(i, e) => {
                if i.len() > 0 {
                    panic!("Unparsed output: {:?}", i);
                }
                e
            },
            other => panic!("Parse error! {:?}", other),
        }
    }
}

impl Expr {
    pub fn reduce(self, mut ctx: Cow<Context>) -> Expr {
        match self {
            Lambda(id, body) =>
                {
                    ctx.to_mut().vals.remove(&id);
                    Lambda(id, Box::new(body.reduce(ctx)))
                },
            Apply(lhs, rhs) =>
                if let Lambda(id, body) = lhs.clone().reduce(Cow::Borrowed(ctx.as_ref())) {
                    ctx.to_mut().vals.insert(id, *rhs);
                    body.reduce(ctx)
                } else { Apply(lhs, rhs) },
            Term(id) =>
                if let Some(val) = ctx.vals.get(&id) {
                    val.clone().reduce(Cow::Borrowed(ctx.as_ref()))
                } else { Term(id) },
        }
    }
}

impl Context {
    fn new() -> Context {
        Context { ident_max: Cell::new(0), vals: HashMap::new() }
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = String::from("Context: {\n");
        for (ref id, ref val) in self.vals.iter() {
            s.push_str(format!("    {} = {}\n", id, val).as_str())
        }
        s.push_str("}\n");
        s.fmt(f)
    }
}

fn is_ident_char(c: char) -> bool { c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' }
named!(ident<&str, String, String>, map!(take_while1_s!(is_ident_char), String::from));

fn atomic_expr<'a>(input: &'a str, unique: &Cell<usize>, mut ctx: Cow<HashMap<String, usize>>) -> IResult<&'a str, Expr, String> {
    preceded!(input,
        whitespace,
        alt_complete!(
            chain!(
                alt_complete!(string!("λ") | string!("\\")) ~
                whitespace ~
                id: chain!(
                    id: str_error!(format!("Expected a variable after start of lambda abstraction!"), ident),
                    || {
                        let cur = unique.get();
                        unique.set(cur + 1);
                        ctx.to_mut().insert(id.clone(), cur);
                        Ident(id, cur)
                    }
                ) ~
                whitespace ~
                req_string!(".") ~
                body: str_error!(format!("Expected expression after start of lambda expression roughly equivalent to `λ{}.`!", id), apply!(expr, unique, Cow::Borrowed(ctx.as_ref()))),
                || Expr::Lambda(id, Box::new(body))
            ) |
            map!(ident, |s: String| {
                Term(
                    if let Some(&u) = ctx.get(&s) {
                        Ident(s, u)
                    } else {
                        Ident(s, 0)
                    }
                )
            }) |
            delimited!(string!("("), str_error!(format!("Expected expression inside parentheses!"), apply!(expr, unique, Cow::Borrowed(ctx.as_ref()))), string!(")"))
        )
    )
}

fn expr<'a>(input: &'a str, unique: &Cell<usize>, ctx: Cow<HashMap<String, usize>>) -> IResult<&'a str, Expr, String> {
    map!(input, str_error!(format!("Expected an expression!"), many1!(apply!(atomic_expr, unique, Cow::Borrowed(ctx.as_ref())))), |exprs: Vec<Expr>| {
            let mut iter = exprs.into_iter();
            let fst = iter.next().unwrap();
            iter.fold(fst, |lhs, rhs| Expr::Apply(Box::new(lhs), Box::new(rhs)))
        })
}

fn command<'a>(input: &'a str, ctx: &mut Context) -> IResult<&'a str, Result<String, String>, String> {
    alt_complete!(input,
        chain!(
            whitespace ~
            string!("let") ~
            whitespace ~
            id: str_error!(format!("Expected identifier after `let`!"), ident) ~
            whitespace ~
            req_string!("=") ~
            e: str_error!(format!("Expected expression after `let {} = `!", id), apply!(expr, &ctx.ident_max, Cow::Owned(HashMap::new()))),
            || {
                let normal = e.reduce(Cow::Borrowed(ctx));
                let s = normal.to_string();
                ctx.vals.insert(Ident(id, 0), normal);
                Ok(s)
            }
        ) |
        map!(apply!(expr, &ctx.ident_max.clone(), Cow::Owned(HashMap::new())), |expr: Expr| Ok(expr.reduce(Cow::Borrowed(ctx)).to_string())) |
        cmd_errval!(format!("Expected `let` assignment or expression!"))
    )
}

pub fn evaluate(s: &str) -> Result<Expr, String> {
    match expr(s, &Cell::new(0), Cow::Owned(HashMap::new())) {
        IResult::Done(input, output) => if input.len() > 0 { Err(format!("Invalid input `{}`!", input)) } else { Ok(output.reduce(Cow::Owned(Context::new()))) },
        err @ _ => Err(format!("Parse error: {:?}", err)),
    }
}

pub fn evaluate_in_ctx(s: &str, ctx: &mut Context) -> Result<String, String> {
    let ires: IResult<&str, Result<String, String>, String> = command(s, ctx);

    match ires {
        IResult::Done(input, output) => if input.len() > 0 { Err(format!("Error parsing input `{}`; this is a bug - not all input was consumed by the parser, and no error returned!", input)) } else { output },
        IResult::Error(err) => {
            let err_dbg_str = format!("{:?}", err);
            Err(get_deepest_custom_error(err).unwrap_or(format!("Internal error! This is a bug! Oops! nom error: {}", err_dbg_str)))
        },
        _ => Err(format!("Unable to parse expression {}; this is a bug. IResult dump: \n{:?}", s, ires)),
    }
}
