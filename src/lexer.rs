use std::{fmt::Display, process::exit};

pub fn tokenize(file: &String) -> Tokens {
    let mut chars = file.chars();

    let mut tokens = Tokens::new();

    loop {
        let mut buffer = Vec::new();

        loop {
            if let Some(char) = chars.next() {
                if SpecialSymbol::match_char(&char) || Operator::match_char(&char) {
                    if buffer.len() > 0 {
                        tokens.push(Token::from_buffer(buffer));
                    }
                    let token = Token::from_buffer(vec![char]);
                    tokens.push(token);
                    break;
                }
                else if char.is_ascii_whitespace() {
                    if buffer.len() > 0 {
                        tokens.push(Token::from_buffer(buffer));
                    }
                    break;
                }
                buffer.push(char)

            } else {
                // Check if last token was a closing bracket
                if tokens.tokens.last().is_some_and(|token| if let Token::SpecialSymbol(SpecialSymbol::CloseBracket) = token {true} else {false}) {
                    return tokens;
                }

                eprintln!("Unexpected end of file");
                exit(1);
            }
        }
    }
}

pub struct Tokens {
    tokens: Vec<Token>
}
impl Tokens {
    pub fn new() -> Self {
        Tokens { tokens: Vec::new() }
    }
    pub fn push(&mut self, token: Token) {
        self.tokens.push(token);
    }
}
impl Display for Tokens {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut lines = Vec::new();
        let mut line = Vec::new();

        let push = |line: &mut Vec<String>, string: &str| {
            line.push(string.to_string())
        };

        let new_line = |lines: &mut Vec<Vec<String>>, line: &mut Vec<String>| {
            lines.push(line.clone());
            *line = Vec::new()
        };

        self.tokens.iter().for_each(|token| {
            match token {
                Token::Keyword(keyword) => {
                    match keyword {
                        Keyword::Function => push(&mut line, "Function"),
                        Keyword::Assignment => push(&mut line, "Assign"),
                        Keyword::Return => push(&mut line, "Return")
                    }
                },
                Token::Value(value) => {
                    match value {
                        Value::Integer(i) => push(&mut line, &i.to_string()),
                        Value::Float(f) => push(&mut line, &f.to_string()),
                        Value::Boolean(b) => push(&mut line, &b.to_string()),
                    }
                },
                Token::Identifier(id) => push(&mut line, &format!("\"{}\"", &id)),
                Token::SpecialSymbol(symbol) => match symbol {
                    SpecialSymbol::Equals => push(&mut line, "="),
                    SpecialSymbol::Terminator => {push(&mut line, ";"); new_line(&mut lines, &mut line)},
                    SpecialSymbol::OpenParen => push(&mut line, "("),
                    SpecialSymbol::CloseParen => push(&mut line, ")"),
                    SpecialSymbol::OpenBracket => {push(&mut line, "{"); new_line(&mut lines, &mut line)},
                    SpecialSymbol::CloseBracket => {push(&mut line, "}"); new_line(&mut lines, &mut line)},
                    SpecialSymbol::Comma => push(&mut line, ","),
                },
                Token::Operator(op) => match op {
                    Operator::Plus => push(&mut line, "+"),
                    Operator::Minus => push(&mut line, "-"),
                    Operator::Multiply => push(&mut line, "*"),
                    Operator::Divide => push(&mut line, "/"),
                },
            }
        });

        write!(f, "{}", lines.iter().map(|line| format!("=> {}", line.join(" "))).collect::<Vec<String>>().join("\n"))
    }
}

pub enum Token {
    Keyword(Keyword),
    Value(Value),
    Identifier(String),
    SpecialSymbol(SpecialSymbol),
    Operator(Operator)
}

impl Token {
    pub fn from_buffer(buffer: Vec<char>) -> Token {
        let string: String = buffer.into_iter().collect();

        if let Some(keyword) = Keyword::from_string(&string) {
            return Token::Keyword(keyword);
        }
        if let Some(symbol) = SpecialSymbol::from_string(&string) {
            return Token::SpecialSymbol(symbol);
        }
        if let Some(operator) = Operator::from_string(&string) {
            return Token::Operator(operator);
        }
        if let Some(value) = Value::from_string(&string) {
            return Token::Value(value);
        }

        return Token::Identifier(string);
    }
}

pub enum Keyword {
    Function,
    Assignment,
    Return
}
impl Keyword {
    pub fn from_string(string: &String) -> Option<Keyword> {
        match string.as_str() {
            "fn" => Some(Keyword::Function),
            "let" => Some(Keyword::Assignment),
            "ret" => Some(Keyword::Return),
            _ => None
        }
    }
}

pub enum Value {
    Integer(i64),
    Float(f64),
    Boolean(bool),
}
impl Value {
    pub fn from_string(string: &String) -> Option<Value> {
        if let Some(int) = string.parse::<i64>().ok() {
            return Some(Self::Integer(int));
        }
        if let Some(float) = string.parse::<f64>().ok() {
            return Some(Self::Float(float));
        }
        match string.as_str() {
            "true" => Some(Self::Boolean(true)),
            "false" => Some(Self::Boolean(false)),
            _ => None
        }
    }
}

pub enum SpecialSymbol {
    Equals,
    Terminator,
    OpenParen,
    CloseParen,
    OpenBracket,
    CloseBracket,
    Comma,
}
impl SpecialSymbol {
    pub fn from_string(string: &String) -> Option<SpecialSymbol> {
        match string.as_str() {
            "=" => Some(SpecialSymbol::Equals),
            ";" => Some(SpecialSymbol::Terminator),
            "(" => Some(SpecialSymbol::OpenParen),
            ")" => Some(SpecialSymbol::CloseParen),
            "{" => Some(SpecialSymbol::OpenBracket),
            "}" => Some(SpecialSymbol::CloseBracket),
            "," => Some(SpecialSymbol::Comma),
            _ => None
        }
    }
    pub fn match_char(char: &char) -> bool {
        Self::from_string(&char.to_string()).is_some()
    }
}

pub enum Operator {
    Plus,
    Minus,
    Multiply,
    Divide
}
impl Operator {
    pub fn from_string(string: &String) -> Option<Operator> {
        match string.as_str() {
            "+" => Some(Operator::Plus),
            "-" => Some(Operator::Minus),
            "*" => Some(Operator::Multiply),
            "/" => Some(Operator::Divide),
            _ => None
        }
    }
    pub fn match_char(char: &char) -> bool {
        Self::from_string(&char.to_string()).is_some()
    }
}