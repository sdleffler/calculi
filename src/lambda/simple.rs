use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

use nom::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr<I: Clone + Eq + fmt::Display + Hash> {
    Lambda { var: I, ty: Type<I>, body: Box<Expr<I>> },
    Apply { lhs: Box<Expr<I>>, rhs: Box<Expr<I>> },
    Term(I),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<I: Clone + Eq + fmt::Display + Hash> {
    Func { arg: Box<Type<I>>, ret: Box<Type<I>> },
    Atomic(I),
}

pub enum TypeError<I: Clone + Eq + fmt::Display + Hash> {
    Mismatch { expected: Type<I>, got: Type<I> },
    Application { subj: Type<I>, arg: Type<I> },
    NotFound(I),
}

use self::Expr::*;
use self::Type::*;
use self::TypeError::*;

impl<I: Clone + Eq + fmt::Display + Hash> fmt::Display for Expr<I> {
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

impl<I: Clone + Eq + fmt::Display + Hash> fmt::Display for Type<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Func { ref arg, ref ret } => match arg.as_ref() {
                &Func { .. } => write!(f, "({})→{}", arg, ret),
                _ => write!(f, "{}→{}", arg, ret),
            },
            &Atomic(ref id) => id.fmt(f),
        }
    }
}

impl<I: Clone + Eq + fmt::Display + Hash> fmt::Display for TypeError<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Mismatch { ref expected, ref got } => write!(f, "Type mismatch: expected {}, got {}", expected, got),
            &Application { ref subj, ref arg } => write!(f, "Expected a function of type {} → ?, got {}", arg, subj),
            &NotFound(ref ident) => write!(f, "Identifier {} is undefined.", ident),
        }
    }
}

impl<I: Clone + Eq + fmt::Display + Hash> Expr<I> {
    pub fn substitute(&self, subj: &I, val: &Expr<I>) -> Expr<I> {
        match self {
            &Lambda { ref var, ref ty, ref body } => if var == subj { self.clone() } else { Expr::Lambda { var: var.clone(), ty: ty.clone(), body: Box::new(body.substitute(subj, val)) } },
            &Apply { ref lhs, ref rhs } => Apply { lhs: Box::new(lhs.substitute(subj, val)), rhs: Box::new(rhs.substitute(subj, val)) },
            &Term(ref id) => if id == subj { val.clone() } else { self.clone() },
        }
    }

    pub fn type_of<'a>(&self, mut ctx: Cow<'a, HashMap<I, Type<I>>>) -> Result<Type<I>, TypeError<I>> {
        match self {
            &Lambda { ref var, ref ty, ref body } => Ok(Type::Func { arg: Box::new(ty.clone()), ret: { ctx.to_mut().insert(var.clone(), ty.clone()); Box::new(try!(body.type_of(ctx))) } }),
            &Apply { ref lhs, ref rhs } => match (try!(lhs.type_of(ctx.clone())), try!(rhs.type_of(ctx.clone()))) {
                (Func { arg, ret }, rhs) => if &rhs == arg.as_ref() { Ok(*ret) } else { Err(TypeError::Mismatch { expected: *arg, got: rhs }) },
                (lhs, rhs) => Err(TypeError::Application { subj: lhs, arg: rhs }),
            },
            &Term(ref id) => ctx.get(id).map_or(Err(TypeError::NotFound(id.clone())), |ty| Ok(ty.clone())),
        }
    }

    pub fn reduce<'a>(&self, mut ctx: Cow<'a, HashMap<I, Type<I>>>) -> Result<(Expr<I>, Type<I>), TypeError<I>> {
        match self {
            &Lambda { ref var, ref ty, ref body } => {
                ctx.to_mut().insert(var.clone(), ty.clone());
                let (body, body_ty) = try!(body.reduce(ctx));
                Ok((Lambda { var: var.clone(), ty: ty.clone(), body: Box::new(body) }, Type::Func { arg: Box::new(ty.clone()), ret: Box::new(body_ty) }))
            },
            &Apply { ref lhs, ref rhs } =>
                match try!(lhs.reduce(ctx.clone())) {
                    (lhs, Func { .. }) => {
                        if let Lambda { var, ty: _, body } = lhs {
                            body.substitute(&var, rhs).reduce(ctx)
                        } else {
                            Ok((self.clone(), try!(self.type_of(ctx))))
                        }
                    },
                    _ => unreachable!(),
                },
            &Term(_) => Ok((self.clone(), try!(self.type_of(ctx)))),
        }
    }
}

named!(ident<&str, String>,
    chain!(
        pre: alpha ~
        suf: alphanumeric?,
        || { String::from(pre) + suf.unwrap_or("") }
    )
);

named!(ty<&str, Type<String> >,
    chain!(
        many0!(multispace) ~
        lhs: alt_complete!(
            map!(ident, Type::Atomic) |
            delimited!(tag_s!("("), ty, tag_s!(")"))
        ) ~
        many0!(multispace) ~
        rhs: preceded!(alt_complete!(tag_s!("->") | tag_s!("→")), ty)?,
        move || match rhs {
            Some(rhs) => Type::Func { arg: Box::new(lhs), ret: Box::new(rhs) },
            None => lhs,
        }
    )
);

named!(atomic_expr<&str, Expr<String> >,
    delimited!(
        many0!(multispace),
        alt_complete!(
            chain!(
                alt_complete!(tag_s!("λ") | tag_s!("\\")) ~
                many0!(multispace) ~
                id: ident ~
                many0!(multispace) ~
                tag_s!(":") ~
                ty: ty ~
                tag_s!(".") ~
                body: expr,
                || { Expr::Lambda { var: id, ty: ty, body: Box::new(body) } }
            ) |
            map!(ident, Expr::Term) |
            delimited!(tag_s!("("), expr, tag_s!(")"))
        ),
        many0!(multispace)
    )
);

named!(pub expr<&str, Expr<String> >,
    map!(many1!(atomic_expr), |exprs: Vec<Expr<String>>| {
            let mut iter = exprs.into_iter();
            let fst = iter.next().unwrap();
            iter.fold(fst, |lhs, rhs| Expr::Apply { lhs: Box::new(lhs), rhs: Box::new(rhs) })
        })
);

pub fn evaluate(s: &str) -> Result<String, String> {
    match expr(s) {
        IResult::Done(input, output) => if input.len() > 0 { Err("Unconsumed input!".to_string()) } else { output.reduce(Cow::Owned(HashMap::new())).map(|(expr, ty)| format!("{} : {}", expr, ty)).map_err(|err| err.to_string()) },
        err @ _ => Err(format!("Parse error: {:?}", err)),
    }
}
