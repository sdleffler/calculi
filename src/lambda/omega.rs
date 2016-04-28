use std::borrow::Cow;
use std::cell::Cell;
use std::collections::HashMap;
use std::fmt;

use nom::*;

use lambda::{get_deepest_custom_error, whitespace};

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Lambda { var: Ident, ty: Type, body: Box<Expr> },
    Apply { lhs: Box<Expr>, rhs: Box<Expr> },
    Term(Ident),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    TyLambda { var: Ident, body: Box<Type> },
    TyApply { lhs: Box<Type>, rhs: Box<Type> },
    Func { arg: Box<Type>, ret: Box<Type> },
    Atomic(Ident),
}

pub enum TypeError {
    Mismatch { expected: Type, got: (Expr, Type) },
    Application { subj: (Expr, Type), arg: (Expr, Type) },
    UntypedTerm(Ident),
}

#[derive(Clone, Debug)]
pub struct Context {
    ident_max: Cell<usize>,
    vals: HashMap<Ident, (Option<Expr>, Type)>,
    types: HashMap<Ident, Type>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Ident(String, usize);

use self::Expr::*;
use self::Type::*;
use self::TypeError::*;

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Lambda { ref var, ref ty, ref body } => match ty {
                &Func { .. } => write!(f, "λ{}:({}).{}", var, ty, body),
                _ => write!(f, "λ{}:{}.{}", var, ty, body),
            },
            &Apply { ref lhs, ref rhs } => write!(f, "{} {}", lhs, rhs),
            &Term(ref i) => i.fmt(f),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &TyLambda { ref var, ref body } => write!(f, "λ{}.{}", var, body),
            &TyApply { ref lhs, ref rhs } => write!(f, "{} {}", lhs, rhs),
            &Func { ref arg, ref ret } => match arg.as_ref() {
                &Func { .. } => write!(f, "({})→{}", arg, ret),
                _ => write!(f, "{}→{}", arg, ret),
            },
            &Atomic(ref id) => id.fmt(f),
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Mismatch { ref expected, got: (ref got_expr, ref got_ty) } => write!(f, "Type mismatch: expected {}, got {} : {}!", expected, got_expr, got_ty),
            &Application { subj: (ref subj_expr, ref subj_ty), arg: (ref arg_expr, ref arg_ty) } => write!(f, "Tried to call {} : {} as a function with argument {} : {}!", arg_expr, arg_ty, subj_expr, subj_ty),
            &UntypedTerm(ref ident) => write!(f, "Term {} is untyped!", ident),
        }
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = String::from("Context:\n    Types:\n");
        for (ref id, ref ty) in self.types.iter() {
            s.push_str(format!("        {} = {};", id, ty).as_str())
        }
        s.push_str("    Values:\n");
        for (ref id, &(ref opt_val, ref ty)) in self.vals.iter() {
            s.push_str(
                match opt_val {
                    &Some(ref val) => format!("        {} : {} = {};\n", id, ty, val),
                    &None => format!("        {} : {};\n", id, ty),
                }.as_str()
            )
        }
        s.fmt(f)
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let &Ident(ref name, _) = self;
        name.fmt(f)
    }
}

impl Expr {
    pub fn reduce<'a>(self, mut ctx: Cow<Context>) -> Result<(Expr, Type), TypeError> {
        match self {
            Lambda { var, ty, body } =>
                {
                    ctx.to_mut().vals.insert(var.clone(), (None, ty.clone()));
                    let (body, body_ty) = try!(body.reduce(Cow::Borrowed(ctx.as_ref())));
                    Ok((Lambda { var: var.clone(), ty: ty.clone(), body: Box::new(body) }, Type::Func { arg: Box::new(ty.clone()), ret: Box::new(body_ty) }))
                },
            Apply { lhs, rhs } =>
                {
                    // Try to reduce lhs and find its type.
                    let (lhs, lhs_ty) = try!(lhs.reduce(Cow::Borrowed(ctx.as_ref())));
                    if let Func { arg: lhs_arg, ret: lhs_ret } = lhs_ty {
                        let (rhs, rhs_ty) = try!(rhs.reduce(Cow::Borrowed(ctx.as_ref())));
                        if !lhs_arg.eq_in_ctx(&rhs_ty, Cow::Borrowed(ctx.as_ref())) {
                            Err(TypeError::Mismatch {
                                got: (rhs, rhs_ty),
                                expected: *lhs_arg,
                            })
                        } else {
                            if let Lambda { var, ty: _, body } = lhs {
                                ctx.to_mut().vals.insert(var, (Some(rhs), *lhs_arg));
                                body.reduce(ctx)
                            } else {
                                Ok((Apply { lhs: Box::new(lhs), rhs: Box::new(rhs) }, *lhs_ret))
                            }
                        }
                    } else {
                        Err(TypeError::Application {
                            subj: try!(lhs.reduce(Cow::Borrowed(ctx.as_ref()))),
                            arg: try!(rhs.reduce(ctx))
                        })
                    }
                },
            Term(ident) =>
                if let Some(&(ref opt_val, ref ty)) = ctx.vals.get(&ident) {
                    match opt_val.as_ref() {
                        Some(val) => Ok((val.clone(), ty.clone().reduce(Cow::Borrowed(ctx.as_ref())))),
                        None => Ok((Term(ident), ty.clone().reduce(Cow::Borrowed(ctx.as_ref())))),
                    }
                } else {
                    Err(TypeError::UntypedTerm(ident))
                },
        }
    }
}

impl Type {
    pub fn eq_in_ctx(&self, rhs: &Type, mut ctx: Cow<Context>) -> bool {
        match (self, rhs) {
            (&TyLambda { var: ref lvar, body: ref lbody }, &TyLambda { var: ref rvar, body: ref rbody }) =>
                {
                    ctx.to_mut().types.insert(lvar.clone(), Atomic(rvar.clone()));
                    let rbody = rbody.clone().reduce(Cow::Borrowed(ctx.as_ref()));
                    lbody.as_ref().eq_in_ctx(&rbody, ctx)
                },
            (&TyApply { lhs: ref l_lhs, rhs: ref l_rhs }, &TyApply { lhs: ref r_lhs, rhs: ref r_rhs }) => l_lhs.eq_in_ctx(r_lhs, Cow::Borrowed(ctx.as_ref())) && l_rhs.eq_in_ctx(r_rhs, Cow::Borrowed(ctx.as_ref())),
            (&Func { arg: ref larg, ret: ref lret }, &Func { arg: ref rarg, ret: ref rret }) => larg == rarg && lret == rret,
            (&Atomic(ref lident), &Atomic(ref rident)) =>
                lident == rident ||
                match (ctx.types.get(lident), ctx.types.get(rident)) {
                    (Some(lhs_val), Some(rhs_val)) => lhs_val == rhs_val,
                    _ => false,
                },
            (&Atomic(ref a), ref b) => match ctx.types.get(a)
                {
                    Some(a) => a.eq_in_ctx(b, Cow::Borrowed(ctx.as_ref())),
                    None => false,
                },
            (ref b, &Atomic(ref a)) => match ctx.types.get(a)
                { // Non-DRY due to lifetime weirdness.
                    Some(a) => a.eq_in_ctx(b, Cow::Borrowed(ctx.as_ref())),
                    None => false,
                },
            _ => false,
        }
    }

    pub fn reduce(self, mut ctx: Cow<Context>) -> Type {
        match self {
            TyLambda { var, body } => { ctx.to_mut().types.remove(&var); TyLambda { var: var, body: Box::new(body.reduce(ctx)) } },
            TyApply { lhs, rhs } =>
                {
                    let lhs = lhs.reduce(Cow::Borrowed(ctx.as_ref()));
                    let rhs = rhs.reduce(Cow::Borrowed(ctx.as_ref()));
                    if let TyLambda { var, body } = lhs {
                        ctx.to_mut().types.insert(var, rhs);
                        body.reduce(ctx)
                    } else {
                        TyApply { lhs: Box::new(lhs), rhs: Box::new(rhs) }
                    }
                },
            Func { arg, ret } => Func { arg: Box::new(arg.reduce(Cow::Borrowed(ctx.as_ref()))), ret: Box::new(ret.reduce(ctx)) },
            Atomic(ident) => { if let Some(ty) = ctx.types.get(&ident) { ty.clone() } else { Atomic(ident) } },
        }
    }
}

impl Context {
    pub fn new() -> Context {
        Context { ident_max: Cell::new(1), vals: HashMap::new(), types: HashMap::new() }
    }
}

impl Default for Context {
    fn default() -> Context {
        Context::new()
    }
}

fn is_term_ident_char(c: char) -> bool { c >= 'a' && c <= 'z' }
named!(_term_ident<&str, String>, map!(take_while1_s!(is_term_ident_char), String::from));
named!(term_ident<&str, String, String>, fix_error!(String, _term_ident));

fn is_type_begin_char(c: char) -> bool { c >= 'A' && c <= 'Z' }
fn is_type_body_char(c: char) -> bool { (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') }
named!(_type_ident<&str, String>, map!(tuple!(take_while1_s!(is_type_begin_char), take_while_s!(is_type_body_char)), |(pre, suf)| String::from(pre) + suf));
named!(type_ident<&str, String, String>, fix_error!(String, _type_ident));

fn atomic_ty<'a>(input: &'a str, unique: &Cell<usize>, mut ctx: Cow<HashMap<String, usize>>) -> IResult<&'a str, Type, String> {
    preceded!(input,
        whitespace,
        alt_complete!(
            chain!(
                alt_complete!(string!("λ") | string!("\\")) ~
                whitespace ~
                id: chain!(
                    id: str_error!(format!("Expected a type variable in type-level lambda abstraction!"), type_ident),
                    || {
                        let cur = unique.get();
                        unique.set(cur + 1);
                        ctx.to_mut().insert(id.clone(), cur);
                        Ident(id, cur)
                    }
                ) ~
                whitespace ~
                req_string!(".") ~
                body: str_error!(format!("Expected type body in type-level lambda abstraction beginning `λ{}.`!", id), apply!(ty, unique, Cow::Borrowed(ctx.as_ref()))),
                || TyLambda { var: id, body: Box::new(body) }
            ) |
            chain!(
                lhs: alt_complete!(
                    map!(type_ident, |s| {
                        let u = ctx.get(&s).map_or(0usize, |&scope| scope);
                        Atomic(Ident(s, u))
                    }) |
                    delimited!(string!("("), str_error!(format!("Expected type inside parentheses!"), apply!(ty, unique, Cow::Borrowed(ctx.as_ref()))), req_string!(")"))
                ) ~
                whitespace ~
                rhs: preceded!(alt_complete!(string!("->") | string!("→")), str_error!(format!("Expected type after `{} → `!", lhs), apply!(ty, unique, Cow::Borrowed(ctx.as_ref()))))?,
                move || match rhs {
                    Some(rhs) => Type::Func { arg: Box::new(lhs), ret: Box::new(rhs) },
                    None => lhs,
                }
            )
        )
    )
}

fn ty<'a>(input: &'a str, unique: &Cell<usize>, ctx: Cow<HashMap<String, usize>>) -> IResult<&'a str, Type, String> {
    map!(input, many1!(apply!(atomic_ty, unique, Cow::Borrowed(ctx.as_ref()))), |types: Vec<Type>| {
            let mut iter = types.into_iter();
            let fst = iter.next().unwrap();
            iter.fold(fst, |lhs, rhs| TyApply { lhs: Box::new(lhs), rhs: Box::new(rhs) })
        })
}

fn atomic_expr<'a>(input: &'a str, unique: &Cell<usize>, mut ctx: Cow<HashMap<String, usize>>) -> IResult<&'a str, Expr, String> {
    delimited!(input,
        whitespace,
        alt_complete!(
            chain!(
                alt_complete!(string!("λ") | string!("\\")) ~
                whitespace ~
                id: chain!(
                    id: str_error!(format!("Expected a variable after start of lambda abstraction!"), term_ident),
                    || {
                        let cur = unique.get();
                        unique.set(cur + 1);
                        ctx.to_mut().insert(id.clone(), cur);
                        Ident(id, cur)
                    }
                ) ~
                whitespace ~
                req_string!(":") ~
                ty: str_error!(format!("Expected type bound for lambda abstraction beginning with `λ{}:`!", id), apply!(ty, unique, Cow::Borrowed(ctx.as_ref()))) ~
                req_string!(".") ~
                body: str_error!(format!("Expected body expression for lambda abstraction beginning with `λ{}:{}.`!", id, ty), apply!(expr, unique, Cow::Borrowed(ctx.as_ref()))),
                || Expr::Lambda { var: id, ty: ty, body: Box::new(body) }
            ) |
            map!(term_ident, |s| {
                let u = ctx.get(&s).map_or(0usize, |&scope| scope);
                Term(Ident(s, u))
            }) |
            delimited!(string!("("), str_error!(format!("Expected expression inside parentheses!"), apply!(expr, unique, ctx)), string!(")"))
        ),
        whitespace
    )
}

fn expr<'a>(input: &'a str, unique: &Cell<usize>, ctx: Cow<HashMap<String, usize>>) -> IResult<&'a str, Expr, String> {
    map!(input, many1!(apply!(atomic_expr, unique, Cow::Borrowed(ctx.as_ref()))), |exprs: Vec<Expr>| {
            let mut iter = exprs.into_iter();
            let fst = iter.next().unwrap();
            iter.fold(fst, |lhs, rhs| Expr::Apply { lhs: Box::new(lhs), rhs: Box::new(rhs) })
        })
}

pub fn evaluate(s: &str) -> Result<String, String> {
    match expr(s, &Cell::new(1), Cow::Owned(HashMap::new())) {
        IResult::Done(input, output) => if input.len() > 0 { Err("Unconsumed input!".to_string()) } else { output.reduce(Cow::Owned(Context::new())).map(|(expr, ty)| format!("{} : {}", expr, ty)).map_err(|err| err.to_string()) },
        err @ _ => Err(format!("Parse error: {:?}", err)),
    }
}

fn command<'a>(s: &'a str, ctx: &mut Context) -> IResult<&'a str, Result<String, String>, String> {
    alt_complete!(s,
        preceded!(
            tuple!(whitespace, string!("let"), whitespace),
            alt_complete!(
                chain!(
                    id: term_ident ~
                    whitespace ~
                    string!("=") ~
                    expr: str_error!(format!("Expected expression after `let {} = `!", id), apply!(expr, &ctx.ident_max, Cow::Owned(HashMap::new()))),
                    || {
                        let (expr, ty) = match expr.reduce(Cow::Borrowed(ctx)) {
                            Ok((expr, ty)) => (expr, ty),
                            Err(ty_err) => { return Err(ty_err.to_string()); },
                        };
                        let s = format!("{} : {}", expr, ty);
                        ctx.vals.insert(Ident(id, 0), (Some(expr), ty));
                        Ok(s)
                    }
                ) |
                chain!(
                    id: term_ident ~
                    whitespace ~
                    string!(":") ~
                    ty: str_error!(format!("Expected type after `let {} : `!", id), apply!(ty, &ctx.ident_max, Cow::Owned(HashMap::new()))),
                    || {
                        let s = format!("{} : {}", id, ty);
                        ctx.vals.insert(Ident(id, 0), (None, ty));
                        Ok(s)
                    }
                ) |
                chain!(
                    id: type_ident ~
                    whitespace ~
                    req_string!("=") ~
                    ty: str_error!(format!("Expected type after `let {} = ` command!", id), apply!(ty, &ctx.ident_max, Cow::Owned(HashMap::new()))),
                    || {
                        let s = ty.to_string();
                        ctx.types.insert(Ident(id, 0), ty);
                        Ok(s)
                    }
                )
            )
        ) |
        chain!(
            val: apply!(expr, &mut ctx.ident_max, Cow::Owned(HashMap::new())) ~
            whitespace ~
            bound: preceded!(string!(":"), apply!(ty, &ctx.ident_max, Cow::Owned(HashMap::new())))?,
            || {
                let (expr, ty) = match val.reduce(Cow::Borrowed(ctx)) {
                    Ok((expr, ty)) => (expr, ty),
                    Err(ty_err) => { return Err(ty_err.to_string()); },
                };

                match bound {
                    Some(ref exp_ty) =>
                        {
                            // I'm annoyed by the .clone() here, but it's there to alleviate problems with nom and the way its chain!() macros expand. Too lazy to really fix now.
                            let exp_ty = exp_ty.clone().reduce(Cow::Borrowed(ctx));
                            if !ty.eq_in_ctx(&exp_ty, Cow::Borrowed(ctx)) {
                                Err(format!("{} : {} ({} != {})\nExpected type did not match!", expr, ty, exp_ty, ty))
                            } else {
                                Ok(format!("{} : {}", expr, ty))
                            }
                        },
                    _ => Ok(format!("{} : {}", expr, ty))
                }
            }
        ) |
        chain!(
            ty: apply!(ty, &mut ctx.ident_max, Cow::Owned(HashMap::new())),
            || Ok(ty.reduce(Cow::Borrowed(ctx)).to_string())
        ) |
        cmd_errval!(format!("Expected `let <id> = <expression>`, `let <type_id> : <type>`, `let <id> = <type>`, `<expression> : <type>`, `<expression>`, or `<type>`!"))
    )
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
