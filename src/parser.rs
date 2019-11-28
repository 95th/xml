pub type ParseResult<'a, T> = Result<(&'a str, T), &'a str>;

pub trait Parser {
    type Output;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output>;

    fn map<F, T>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Output) -> T,
    {
        Map { parser: self, f }
    }

    fn pred<F>(self, predicate: F) -> Predicate<Self, F>
    where
        Self: Sized,
        F: Fn(&Self::Output) -> bool,
    {
        Predicate {
            parser: self,
            predicate,
        }
    }

    fn and_then<P, F>(self, f: F) -> AndThen<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Output) -> P,
        P: Parser,
    {
        AndThen { parser: self, f }
    }

    fn or<P>(self, other: P) -> Or<Self, P>
    where
        Self: Sized,
        P: Parser<Output = Self::Output>,
    {
        Or {
            first: self,
            second: other,
        }
    }

    fn zip<P>(self, other: P) -> Zip<Self, P>
    where
        Self: Sized,
        P: Parser,
    {
        Zip {
            first: self,
            second: other,
        }
    }

    fn zero_or_more(self) -> ZeroOrMore<Self>
    where
        Self: Sized,
    {
        ZeroOrMore { parser: self }
    }

    fn one_or_more(self) -> OneOrMore<Self>
    where
        Self: Sized,
    {
        OneOrMore { parser: self }
    }

    fn boxed(self) -> BoxedParser<Self::Output>
    where
        Self: 'static + Sized,
    {
        BoxedParser(Box::new(self))
    }
}

pub struct Map<P, F> {
    parser: P,
    f: F,
}

impl<P, F, T> Parser for Map<P, F>
where
    P: Parser,
    F: Fn(P::Output) -> T,
{
    type Output = T;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        self.parser
            .parse(input)
            .map(|(rest, parsed)| (rest, (self.f)(parsed)))
    }
}

pub struct Predicate<P, F> {
    parser: P,
    predicate: F,
}

impl<P, F> Parser for Predicate<P, F>
where
    P: Parser,
    F: Fn(&P::Output) -> bool,
{
    type Output = P::Output;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        if let Ok((rest, parsed)) = self.parser.parse(input) {
            if (self.predicate)(&parsed) {
                return Ok((rest, parsed));
            }
        }
        Err(input)
    }
}

pub struct AndThen<P, F> {
    parser: P,
    f: F,
}

impl<P, Q, F> Parser for AndThen<P, F>
where
    P: Parser,
    F: Fn(P::Output) -> Q,
    Q: Parser,
{
    type Output = Q::Output;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        let (rest, parsed) = self.parser.parse(input)?;
        (self.f)(parsed).parse(rest)
    }
}

pub struct Zip<P, Q> {
    first: P,
    second: Q,
}

impl<P, Q> Parser for Zip<P, Q>
where
    P: Parser,
    Q: Parser,
{
    type Output = (P::Output, Q::Output);

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        let (rest, first) = self.first.parse(input)?;
        let (rest, second) = self.second.parse(rest)?;
        Ok((rest, (first, second)))
    }
}

pub struct Or<P, Q> {
    first: P,
    second: Q,
}

impl<P, Q> Parser for Or<P, Q>
where
    P: Parser,
    Q: Parser<Output = P::Output>,
{
    type Output = P::Output;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        self.first
            .parse(input)
            .or_else(|_| self.second.parse(input))
    }
}

pub struct ZeroOrMore<P> {
    parser: P,
}

impl<P: Parser> Parser for ZeroOrMore<P> {
    type Output = Vec<P::Output>;

    fn parse<'a>(&self, mut input: &'a str) -> ParseResult<'a, Self::Output> {
        let mut result = Vec::new();

        while let Ok((rest, parsed)) = self.parser.parse(input) {
            input = rest;
            result.push(parsed);
        }

        Ok((input, result))
    }
}

pub struct OneOrMore<P> {
    parser: P,
}

impl<P: Parser> Parser for OneOrMore<P> {
    type Output = Vec<P::Output>;

    fn parse<'a>(&self, mut input: &'a str) -> ParseResult<'a, Self::Output> {
        let mut result = Vec::new();

        let (rest, parsed) = self.parser.parse(input)?;
        input = rest;
        result.push(parsed);

        while let Ok((rest, parsed)) = self.parser.parse(input) {
            input = rest;
            result.push(parsed);
        }

        Ok((input, result))
    }
}

pub struct BoxedParser<T>(Box<dyn Parser<Output = T>>);

impl<T> Parser for BoxedParser<T> {
    type Output = T;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        self.0.parse(input)
    }
}
