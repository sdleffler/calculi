#[macro_use]
extern crate nom;

pub mod simple;
pub mod systemf;
pub mod untyped;

use nom::*;

fn whitespace(input: &str) -> IResult<&str, (), String> {
    let (input, _) = try_parse!(input, many0!(multispace));
    IResult::Done(input, ())
}

fn get_deepest_custom_error(err: Err<&str, String>) -> Option<String> {
    use nom::Err::*;
    match err {
        Code(ek) | Position(ek, _) => if let ErrorKind::Custom(string) = ek { Some(string) } else { None },
        Node(ek, next) | NodePosition(ek, _, next) => {
            if let ErrorKind::Custom(string) = ek {
                match get_deepest_custom_error(*next) {
                    Some(deeper) => Some(deeper),
                    None => Some(string),
                }
            } else {
                get_deepest_custom_error(*next)
            }
        },
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
