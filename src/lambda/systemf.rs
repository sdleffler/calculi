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

#[derive(Clone, Debug, Hash, PartialEq)]
pub enum Expr {
    Lambda { var: Ident, ty: Type, body: Box<Expr> },
    TyLambda { var: Ident, body: Box<Expr> },
    Apply { lhs: Box<Expr>, rhs: Box<Expr> },
    TyApply { lhs: Box<Expr>, rhs: Type },
    Term(Ident),
}

#[derive(Clone, Debug, Hash)]
pub enum Type {
    Forall { var: Ident, body: Box<Type> },
    Func { arg: Box<Type>, ret: Box<Type> },
    Atomic(Ident),
}

#[derive(Clone, Default)]
pub struct Context {
    ident_max: Cell<usize>,
    vals: HashMap<Ident, (Option<Expr>, Type)>,
    types: HashMap<Ident, Type>,
}

#[derive(Clone)]
pub enum TypeError {
    Mismatch { expected: Type, got: (Expr, Type) },
    Application { subj: (Expr, Type), arg: (Expr, Type) },
    TyApplication { subj: (Expr, Type), arg: Type },
    UntypedTerm(Ident),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Ident(String, usize);

use self::Expr::*;
use self::Type::*;

impl Expr {
    pub fn reduce(self, mut ctx: Cow<Context>) -> Result<(Expr, Type), TypeError> {
        match self {
            Lambda { var, ty, body } => {
                ctx.to_mut().vals.insert(var.clone(), (None, ty.clone()));
                let (body, body_ty) = try!(body.reduce(Cow::Borrowed(ctx.as_ref())));
                let ty = ty.reduce(ctx);
                Ok((Lambda { var: var, ty: ty.clone(), body: Box::new(body) }, Func { arg: Box::new(ty), ret: Box::new(body_ty) }))
            },
            TyLambda { var, body } => {
                ctx.to_mut().types.remove(&var);
                let (body, body_ty) = try!(body.reduce(ctx));
                Ok((TyLambda { var: var.clone(), body: Box::new(body) }, Forall { var: var, body: Box::new(body_ty) }))
            },
            Apply { lhs, rhs } => {
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
                    Err(TypeError::Application { subj: try!(lhs.reduce(Cow::Borrowed(ctx.as_ref()))), arg: try!(rhs.reduce(ctx)) })
                }
            },
            TyApply { lhs, rhs } => {
                let (lhs, lhs_ty) = try!(lhs.reduce(Cow::Borrowed(ctx.as_ref())));
                if let Forall { var, body } = lhs_ty {
                    let rhs = rhs.reduce(Cow::Borrowed(ctx.as_ref()));
                    if let TyLambda { var, body } = lhs {
                        ctx.to_mut().types.insert(var, rhs);
                        body.reduce(ctx)
                    } else {
                        let ret_ty = body.substitute(&var, &rhs);
                        Ok((TyApply { lhs: Box::new(lhs), rhs: rhs }, ret_ty))
                    }
                } else {
                    Err(TypeError::TyApplication { subj: (lhs, lhs_ty), arg: rhs })
                }
            },
            Term(ident) => {
                if let Some(&(ref opt_val, ref ty)) = ctx.vals.get(&ident) {
                    match opt_val.as_ref() {
                        Some(val) => Ok((val.clone(), ty.clone().reduce(Cow::Borrowed(ctx.as_ref())))),
                        None => Ok((Term(ident), ty.clone().reduce(Cow::Borrowed(ctx.as_ref())))),
                    }
                } else {
                    Err(TypeError::UntypedTerm(ident))
                }
            }
        }
    }
}

impl Type {
    pub fn eq_in_ctx(&self, rhs: &Type, mut ctx: Cow<Context>) -> bool {
        match (self, rhs) {
            (&Forall { var: ref lvar, body: ref lbody },
                &Forall { var: ref rvar, body: ref rbody }) => {
                    ctx.to_mut().types.remove(lvar);
                    lbody.as_ref().eq_in_ctx(&rbody.clone().substitute(rvar, &Atomic(lvar.clone())), ctx)
                },
            (&Func { arg: ref larg, ret: ref lret }, &Func { arg: ref rarg, ret: ref rret }) => larg == rarg && lret == rret,
            (&Atomic(ref lident), &Atomic(ref rident)) => lident == rident || match (ctx.types.get(lident), ctx.types.get(rident)) {
                (Some(lhs_val), Some(rhs_val)) => lhs_val == rhs_val,
                _ => false,
            },
            (&Atomic(ref a), ref b) => match ctx.types.get(a) {
                Some(a) => a.eq_in_ctx(b, Cow::Borrowed(ctx.as_ref())),
                None => false,
            },
            (ref b, &Atomic(ref a)) => match ctx.types.get(a) { // Non-DRY due to lifetime weirdness.
                Some(a) => a.eq_in_ctx(b, Cow::Borrowed(ctx.as_ref())),
                None => false,
            },
            _ => false,
        }
    }

    pub fn reduce(self, mut ctx: Cow<Context>) -> Type {
        match self {
            Forall { var, body } => { ctx.to_mut().types.remove(&var); Forall { var: var, body: Box::new(body.reduce(ctx)) } }
            Func { arg, ret } => Func { arg: Box::new(arg.reduce(Cow::Borrowed(ctx.as_ref()))), ret: Box::new(ret.reduce(ctx)) },
            Atomic(ident) => { if let Some(ty) = ctx.types.get(&ident) { ty.clone() } else { Atomic(ident) } },
        }
    }

    pub fn substitute(self, ident: &Ident, val: &Type) -> Type {
        match self {
            Forall { var, body } => if &var == ident { Forall { var: var, body: body } } else { Forall { var: var.clone(), body: Box::new(body.substitute(ident, val)) } },
            Func { arg, ret } => Func { arg: Box::new(arg.substitute(ident, val)), ret: Box::new(ret.substitute(ident, val)) },
            Atomic(a_ident) => if &a_ident == ident { val.clone() } else { Atomic(a_ident) }
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, rhs: &Type) -> bool {
        self.eq_in_ctx(rhs, Cow::Owned(Context::new()))
    }
}

impl Context {
    pub fn new() -> Context {
        Context { ident_max: Cell::new(0), vals: HashMap::new(), types: HashMap::new() }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Lambda { ref var, ref ty, ref body } => match ty {
                &Atomic(_) => write!(f, "λ{}:{}.{}", var, ty, body),
                _ => write!(f, "λ{}:({}).{}", var, ty, body),
            },
            &TyLambda { ref var, ref body } => write!(f, "Λ{}.{}", var, body),
            &Apply { ref lhs, ref rhs } => write!(f, "{} {}", lhs, rhs),
            &TyApply { ref lhs, ref rhs } => write!(f, "{} {}", lhs, rhs),
            &Term(ref ident) => ident.fmt(f),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Forall { ref var, ref body } => write!(f, "∀{}.{}", var, body),
            &Func { ref arg, ref ret } => match arg.as_ref() {
                &Atomic(_) => write!(f, "{}→{}", arg, ret),
                _ => write!(f, "({})→{}", arg, ret),
            },
            &Atomic(ref ident) => ident.fmt(f),
        }
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = String::from("Γ = {\n");
        for (ref id, &(ref opt_val, ref ty)) in self.vals.iter() {
            s.push_str(
                match opt_val {
                    &Some(ref val) => format!("    {} : {} = {}\n", id, ty, val),
                    &None => format!("    {} : {}\n", id, ty),
                }.as_str()
            )
        }
        s.push_str("}\n");
        s.fmt(f)
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::TypeError::*;
        match self {
            &Mismatch { ref expected, got: (ref got_expr, ref got_ty) } => write!(f, "Expected type `{}`, but got expression `{}` of type `{}` instead! (TypeError::Mismatch)", expected, got_expr, got_ty),
            &Application { subj: (ref subj_expr, ref subj_ty), arg: (ref arg_expr, ref arg_ty) } => write!(f, "Tried to apply expression `{}` of non-function type `{}` to expression `{}` of type `{}`. (TypeError::Application)", subj_expr, subj_ty, arg_expr, arg_ty),
            &TyApplication { subj: (ref subj_expr, ref subj_ty), ref arg } => write!(f, "Tried to apply type lambda `{}` of non-polymorphic type `{}` to type `{}`! (Tried to supply a type argument to a non-generic type!) (TypeError::TyApplication)", subj_expr, subj_ty, arg),
            &UntypedTerm(ref ident) => write!(f, "Ran into an untyped term, `{}`! (TypeError::UntypedTerm)", ident),
        }
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let &Ident(ref name, _) = self;
        write!(f, "{}", name)
    }
}

fn is_term_ident_char(c: char) -> bool { c >= 'a' && c <= 'z' }
named!(_term_ident<&str, String>, map!(take_while1_s!(is_term_ident_char), String::from));
named!(term_ident<&str, String, String>, fix_error!(String, _term_ident));

fn is_type_begin_char(c: char) -> bool { c >= 'A' && c <= 'Z' }
fn is_type_body_char(c: char) -> bool { (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') }
named!(_type_ident<&str, String>, map!(tuple!(take_while1_s!(is_type_begin_char), take_while_s!(is_type_body_char)), |(pre, suf)| String::from(pre) + suf));
named!(type_ident<&str, String, String>, fix_error!(String, _type_ident));

fn ty<'a>(input: &'a str, unique: &Cell<usize>, mut ctx: Cow<HashMap<String, usize>>) -> IResult<&'a str, Type, String> {
    chain!(input,
        whitespace ~
        lhs: alt_complete!(
            chain!(
                alt_complete!(string!("∀") | string!("forall")) ~
                whitespace ~
                id: chain!(
                    id: str_error!(format!("Expected type identifier after universal quantifier!"), type_ident),
                    || {
                        let cur = unique.get();
                        ctx.to_mut().insert(id.clone(), cur);
                        unique.set(cur + 1);
                        Ident(id, cur)
                    }
                ) ~
                whitespace ~
                req_string!(".") ~
                body: str_error!(format!("Expected type body for univerally quantified type!"), apply!(ty, unique, Cow::Borrowed(ctx.as_ref()))),
                || Forall { var: id, body: Box::new(body) }
            ) |
            map!(type_ident, |s| {
                let u = ctx.get(&s).map_or(0usize, |&scope| scope);
                Atomic(Ident(s, u))
            }) |
            delimited!(string!("("), str_error!(format!("Expected type inside parentheses in type context!"), apply!(ty, unique, Cow::Borrowed(ctx.as_ref()))), req_string!(")"))
        ) ~
        whitespace ~
        rhs: complete!(preceded!(alt_complete!(string!("->") | string!("→")), str_error!(format!("Expected type after function type constructor!"), apply!(ty, unique, Cow::Borrowed(ctx.as_ref())))))?,
        move || match rhs {
            Some(rhs) => Func { arg: Box::new(lhs), ret: Box::new(rhs) },
            None => lhs,
        }
    )
}

fn atomic_expr<'a>(input: &'a str, unique: &Cell<usize>, mut ctx: Cow<HashMap<String, usize>>) -> IResult<&'a str, Expr, String> {
    delimited!(input,
        whitespace,
        alt_complete!(
            chain!(
                alt_complete!(string!("λ") | string!("\\")) ~
                whitespace ~
                id: map!(str_error!(format!("Expected term identifier after beginning of λ abstraction!"), term_ident), |new_id: String| {
                    let cur = unique.get();
                    ctx.to_mut().insert(new_id.clone(), cur);
                    unique.set(cur);
                    Ident(new_id, cur)
                }) ~
                whitespace ~
                req_string!(":") ~
                ty: str_error!(format!("Expected a type bound for λ argument! System F requires all λ abstractions have explicit type bounds."), apply!(ty, unique, Cow::Borrowed(ctx.as_ref()))) ~
                req_string!(".") ~
                body: str_error!(format!("Expected an expression body for λ abstraction!"), apply!(expr, unique, Cow::Borrowed(ctx.as_ref()))),
                || Lambda { var: id, ty: ty, body: Box::new(body) }
            ) |
            chain!(
                alt_complete!(string!("Λ") | string!("given")) ~
                whitespace ~
                id: map!(str_error!(format!("Expected type identifier after beginning of Λ type abstraction!"), type_ident), |new_id: String| {
                        let cur = unique.get();
                        unique.set(cur + 1);
                        ctx.to_mut().insert(new_id.clone(), cur);
                        Ident(new_id, cur)
                    }) ~
                whitespace ~
                req_string!(".") ~
                body: str_error!(format!("Expected an expression body for Λ type abstraction!"), apply!(expr, unique, Cow::Borrowed(ctx.as_ref()))),
                || TyLambda { var: id, body: Box::new(body) }
            ) |
            map!(term_ident, |id| { let u = ctx.get(&id).map_or(0usize, |&scope| scope); Term(Ident(id, u)) }) |
            delimited!(string!("("), str_error!(format!("Expected an expression inside parentheses!"), apply!(expr, unique, Cow::Borrowed(ctx.as_ref()))), req_string!(")"))
        ),
        whitespace
    )
}

enum App {
    Expr(Expr),
    Type(Type),
}

fn expr<'a>(input: &'a str, unique: &Cell<usize>, ctx: Cow<HashMap<String, usize>>) -> IResult<&'a str, Expr, String> {
    map!(input,
        tuple!(
            str_error!(format!("Where's the beef!?"), apply!(atomic_expr, unique, Cow::Borrowed(ctx.as_ref()))),
            many0!(alt_complete!(map!(apply!(atomic_expr, unique, Cow::Borrowed(ctx.as_ref())), App::Expr) | map!(apply!(ty, unique, Cow::Borrowed(ctx.as_ref())), App::Type)))
        ),
        |(fst, apps): (Expr, Vec<App>)|
            apps.into_iter().fold(fst, |lhs, app| match app {
                App::Expr(rhs) => Apply { lhs: Box::new(lhs), rhs: Box::new(rhs) },
                App::Type(rhs) => TyApply { lhs: Box::new(lhs), rhs: rhs },
            })
    )
}

pub fn evaluate(s: &str) -> Result<String, String> {
    match expr(s, &Cell::new(0), Cow::Owned(HashMap::new())) {
        IResult::Done(input, expr) =>
            if input.len() > 0 {
                Err(String::from("Parse error: Not all input was consumed!"))
            } else {
                expr.reduce(Cow::Owned(Context::new())).map(|(expr, ty)| format!("{} : {}", expr, ty)).map_err(|ty_err| ty_err.to_string())
            },
        err @ _ => Err(format!("{:?}", err)),
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
                    Some(ref exp_ty) if !ty.eq_in_ctx(exp_ty, Cow::Borrowed(ctx)) => Err(format!("{} : {} ({} != {})\nExpected type did not match!", expr, ty, exp_ty, ty)),
                    _ => Ok(format!("{} : {}", expr, ty))
                }
            }
        ) |
        cmd_errval!(format!("Expected `let <id> = <expression>`, `let <type_id> : <type>`, `let <id> = <type>`, `<expression> : <type>`, or expression!"))
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
