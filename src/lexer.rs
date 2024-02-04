use std::{collections::VecDeque, fmt::Display};

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
                if buffer.len() > 0 {
                    tokens.push(Token::from_buffer(buffer));
                }
                tokens.push(Token::EOF);
                return tokens;
            }
        }
    }
}

pub struct Tokens {
    tokens: VecDeque<Token>
}
impl Tokens {
    pub fn new() -> Self {
        Tokens { tokens: VecDeque::new() }
    }
    pub fn push(&mut self, token: Token) {
        self.tokens.push_back(token);
    }
    // Returns next token and consumes it, panics if no tokens remain
    pub fn next(&mut self) -> Token {
        self.tokens.pop_front().unwrap_or(Token::EOF)
    }
    // Returns next token, panics if no tokens remain
    pub fn peek(&mut self) -> &Token {
        self.tokens.front().unwrap_or(&Token::EOF)
    }
}
impl Display for Tokens {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut lines = Vec::new();
        let mut line = Vec::new();

        self.tokens.iter().for_each(|token| {
            line.push(format!("{token}"));

            match token {
                Token::SpecialSymbol(SpecialSymbol::Terminator) 
                | Token::SpecialSymbol(SpecialSymbol::OpenBracket) 
                | Token::SpecialSymbol(SpecialSymbol::CloseBracket) => {
                    lines.push(line.clone());
                    line = Vec::new();
                },
                _ => ()
            }
        });

        write!(f, "{}", lines.iter().map(|line| format!("=> {}", line.join(" "))).collect::<Vec<String>>().join("\n"))
    }
}

pub enum Token {
    EOF,
    Keyword(Keyword),
    Value(Value),
    Type(Type),
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
        if let Some(type_) = Type::from_string(&string) {
            return Token::Type(type_);
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
impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::EOF => write!(f, "EOF"),
            Token::Identifier(id) => write!(f, "\"{id}\""),
            Token::Keyword(keyword) => {
                match keyword {
                    Keyword::Function => write!(f, "Function"),
                    Keyword::Assignment => write!(f, "Assign"),
                    Keyword::Return => write!(f, "Return"),
                    Keyword::External => write!(f, "External"),
                }
            },
            Token::Type(type_) => {
                match type_ {
                    Type::Void => write!(f, "Void"),
                    Type::Integer => write!(f, "Integer"),
                    Type::Float => write!(f, "Float"),
                    Type::Boolean => write!(f, "Boolean"),
                }
            }
            Token::Value(value) => {
                match value {
                    Value::Integer(i) => write!(f, "{}", &i.to_string()),
                    Value::Float(v) => write!(f, "{}", &v.to_string()),
                    Value::Boolean(b) => write!(f, "{}", &b.to_string()),
                }
            },
            Token::SpecialSymbol(symbol) => {
                match symbol {
                    SpecialSymbol::Equals => write!(f, "="),
                    SpecialSymbol::Terminator => write!(f, ";"),
                    SpecialSymbol::OpenParen => write!(f, "("),
                    SpecialSymbol::CloseParen => write!(f, ")"),
                    SpecialSymbol::OpenBracket => write!(f, "{{"),
                    SpecialSymbol::CloseBracket => write!(f, "}}"),
                    SpecialSymbol::Comma => write!(f, ","),
                }
            },
            Token::Operator(op) => {
                match op {
                    Operator::Plus => write!(f, "+"),
                    Operator::Minus => write!(f, "-"),
                    Operator::Multiply => write!(f, "*"),
                    Operator::Divide => write!(f, "/"),
                }
            },
        }
    }
}


pub enum Keyword {
    Function,
    Assignment,
    Return,
    External
}
impl Keyword {
    pub fn from_string(string: &String) -> Option<Keyword> {
        match string.as_str() {
            "fn" => Some(Keyword::Function),
            "let" => Some(Keyword::Assignment),
            "ret" => Some(Keyword::Return),
            "extern" => Some(Keyword::External),
            _ => None
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Type {
    Void,
    Integer,
    Float,
    Boolean
}
impl Type {
    pub fn from_string(string: &String) -> Option<Type> {
        match string.as_str() {
            "void" => Some(Self::Void),
            "int" => Some(Self::Integer),
            "float" => Some(Self::Float),
            "bool" => Some(Self::Boolean),
            _ => None
        }
    }
}

#[derive(Debug)]
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
    pub fn get_type(&self) -> Type {
        match self {
            Value::Integer(_) => Type::Integer,
            Value::Float(_) => Type::Float,
            Value::Boolean(_) => Type::Boolean,
        }
    }
}

#[derive(Clone, Copy)]
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

#[derive(Clone, Copy, Debug)]
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