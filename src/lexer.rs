use std::{collections::VecDeque, fmt::Display};

pub fn tokenize(file: &String) -> Tokens {
    let mut chars = file.chars();

    let mut tokens = Tokens::new();

    let mut line = 1;
    let mut column = 0;

    let mut buffer = Vec::new();
    let mut buffer_start = (column+1, line);

    loop {
        column += 1;
        if let Some(char) = chars.next() {
            if char == '\n' {
                line += 1;
                column = 1;
            }
            if Token::expect_char(&buffer, &char) {
                buffer.push(char);
            } else {
                if buffer.len() > 0 {
                    println!("adding {buffer:?} to tokens");
                    tokens.push(Token::from_buffer(&buffer).unwrap(), buffer_start);
                }
                buffer = Vec::new();
                if Token::expect_char(&buffer, &char) {
                    buffer.push(char)
                }
                buffer_start = (column, line);
            }
        } else {
            if buffer.len() > 0 {
                tokens.push(Token::from_buffer(&buffer).unwrap(), buffer_start);
            }
            tokens.push(Token::EOF, (column, line));    
            return tokens;
        }
    }
}

#[derive(Debug)]
pub struct Tokens {
    tokens: VecDeque<Token>,
    locations: VecDeque<(usize, usize)>
}
impl Tokens {
    pub fn new() -> Self {
        Tokens { tokens: VecDeque::new(), locations: vec![(0, 0)].into() }
    }
    #[allow(dead_code)] // This function is for tests
    pub fn from_vec(tokens: Vec<Token>) -> Self {
        Tokens { tokens: tokens.into_iter().collect(), locations: VecDeque::new() }
    }
    pub fn push(&mut self, token: Token, location: (usize, usize)) {
        self.tokens.push_back(token);
        self.locations.push_back(location);
    }
    pub fn next(&mut self) -> Token {
        self.locations.pop_front();
        self.tokens.pop_front().unwrap_or(Token::EOF)
    }
    pub fn peek(&mut self) -> &Token {
        self.tokens.front().unwrap_or(&Token::EOF)
    }
    pub fn peek_nth(&self, nth: usize) -> &Token {
        self.tokens.get(nth).unwrap_or(&Token::EOF)
    }
    pub fn get_prev_location(&self) -> (usize, usize) {
        self.locations.get(0).copied().unwrap_or((0, 0))
    }
    pub fn get_curr_location(&self) -> (usize, usize) {
        self.locations.get(1).copied().unwrap_or((0, 0))
    }
    pub fn get_location_nth(&self, nth: usize) -> (usize, usize) {
        self.locations.get(nth+1).copied().unwrap_or((0, 0))
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

impl PartialEq for Tokens {
    fn eq(&self, other: &Self) -> bool {
        self.tokens == other.tokens
    }
}

#[derive(PartialEq, Debug)]
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
    pub fn from_buffer(buffer: &Vec<char>) -> Option<Token> {
        let string: String = buffer.into_iter().collect();

        if let Some(keyword) = Keyword::from_string(&string) {
            return Some(Token::Keyword(keyword));
        }
        if let Some(type_) = Type::from_string(&string) {
            return Some(Token::Type(type_));
        }
        if let Some(symbol) = SpecialSymbol::from_string(&string) {
            return Some(Token::SpecialSymbol(symbol));
        }
        if let Some(operator) = Operator::from_string(&string) {
            return Some(Token::Operator(operator));
        }
        if let Some(value) = Value::from_string(&string) {
            return Some(Token::Value(value));
        }
        if let Some(id) = id_from_string(&string) {
            return Some(Token::Identifier(id));
        }

        return None;
    }
    pub fn expect_char(buffer: &Vec<char>, char: &char) -> bool {
        if char.is_whitespace() {
            return false;
        }
        if buffer.get(0).is_some() {
            let mut buffer = buffer.clone();
            buffer.push(*char);
            Token::from_buffer(&buffer).is_some()
        } else {
            return true;
        }
    }
}
impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::EOF => write!(f, "EOF"),
            Token::Identifier(id) => write!(f, "\"{}\"", id),
            Token::Keyword(keyword) => {
                match keyword {
                    Keyword::Function => write!(f, "Function"),
                    Keyword::Declaration => write!(f, "Decleration"),
                    Keyword::Return => write!(f, "Return"),
                    Keyword::External => write!(f, "External"),
                    Keyword::If => write!(f, "If"),
                    Keyword::While => write!(f, "While"),
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
                    Value::Void => write!(f, "Void"),
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
                    Operator::LessThan => write!(f, "<"),
                    Operator::GreaterThan => write!(f, ">"),
                    Operator::LessThanOrEqual => write!(f, "<="),
                    Operator::GreaterThanOrEqual => write!(f, ">="),
                    Operator::Equal => write!(f, "=="),
                    Operator::NotEqual => write!(f, "!="),
                }
            },
        }
    }
}


#[derive(PartialEq, Debug)]
pub enum Keyword {
    Function,
    Declaration,
    Return,
    External,
    If,
    While
}
impl Keyword {
    pub fn from_string(string: &String) -> Option<Keyword> {
        match string.as_str() {
            "fn" => Some(Keyword::Function),
            "let" => Some(Keyword::Declaration),
            "ret" => Some(Keyword::Return),
            "extern" => Some(Keyword::External),
            "if" => Some(Keyword::If),
            "while" => Some(Keyword::While),
            _ => None
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
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


#[derive(Debug, PartialEq)]
pub enum Value {
    Void,
    Integer(i64),
    Float(f64),
    Boolean(bool),
}
impl Value {
    pub fn from_string(string: &String) -> Option<Value> {
        if string.chars().next().unwrap() == '+' {
            return None;
        }
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
            Value::Void => Type::Void,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
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
}



#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Operator {
    Plus,
    Minus,
    Multiply,
    Divide,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    Equal,
    NotEqual
}
impl Operator {
    pub fn from_string(string: &String) -> Option<Operator> {
        match string.as_str() {
            "+" => Some(Operator::Plus),
            "-" => Some(Operator::Minus),
            "*" => Some(Operator::Multiply),
            "/" => Some(Operator::Divide),
            "<" => Some(Operator::LessThan),
            ">" => Some(Operator::GreaterThan),
            "<=" => Some(Operator::LessThanOrEqual),
            ">=" => Some(Operator::GreaterThanOrEqual),
            "==" => Some(Operator::Equal),
            "!=" => Some(Operator::NotEqual),
            _ => None
        }
    }
    pub fn get_operation_order(&self) -> usize {
        match self {
            Operator::Multiply | Operator::Divide => 0,
            Operator::Plus | Operator::Minus => 1,
            Operator::LessThan | Operator::GreaterThan | Operator::LessThanOrEqual
            | Operator::GreaterThanOrEqual | Operator::Equal | Operator::NotEqual => 2,
        }
    }
}

pub fn id_from_string(id: &String) -> Option<String> {
    if id.is_empty() {
        return None;
    }
    // Check if the identifier is a keyword
    if Keyword::from_string(id).is_some() {
        return None;
    }

    let mut chars = id.chars().peekable();

    // Check if the identifier starts with a number
    if chars.peek().is_some_and(|char| char.is_ascii_digit()) {
        return None;
    }
    
    // Check if the contains only allowed characters
    for char in chars {
        if !(char.is_ascii_alphanumeric() || char == '_') {
           return None;
        }
    }
    return Some( id.clone() );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize() {
        let input = "fn calculate(a, b) { let sum = a + b; ret sum * 2; }".to_string();
        let expected_tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Function),
            Token::Identifier("calculate".to_string()),
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Identifier("a".to_string()),
            Token::SpecialSymbol(SpecialSymbol::Comma),
            Token::Identifier("b".to_string()),
            Token::SpecialSymbol(SpecialSymbol::CloseParen),
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::Keyword(Keyword::Declaration),
            Token::Identifier("sum".to_string()),
            Token::SpecialSymbol(SpecialSymbol::Equals),
            Token::Identifier("a".to_string()),
            Token::Operator(Operator::Plus),
            Token::Identifier("b".to_string()),
            Token::SpecialSymbol(SpecialSymbol::Terminator),
            Token::Keyword(Keyword::Return),
            Token::Identifier("sum".to_string()),
            Token::Operator(Operator::Multiply),
            Token::Value(Value::Integer(2)),
            Token::SpecialSymbol(SpecialSymbol::Terminator),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),
            Token::EOF
        ]);

        let result_tokens = tokenize(&input);
        assert_eq!(result_tokens, expected_tokens);
    }

    #[test]
    fn test_keyword_from_string() {
        assert_eq!(Keyword::from_string(&"fn".to_string()), Some(Keyword::Function));
        assert_eq!(Keyword::from_string(&"let".to_string()), Some(Keyword::Declaration));
        assert_eq!(Keyword::from_string(&"ret".to_string()), Some(Keyword::Return));
        assert_eq!(Keyword::from_string(&"extern".to_string()), Some(Keyword::External));
        assert_eq!(Keyword::from_string(&"invalid".to_string()), None);
    }
    #[test]
    fn test_type_from_string() {
        assert_eq!(Type::from_string(&"void".to_string()), Some(Type::Void));
        assert_eq!(Type::from_string(&"int".to_string()), Some(Type::Integer));
        assert_eq!(Type::from_string(&"float".to_string()), Some(Type::Float));
        assert_eq!(Type::from_string(&"bool".to_string()), Some(Type::Boolean));
        assert_eq!(Type::from_string(&"invalid".to_string()), None);
    }
    #[test]
    fn test_id_from_string() {
        assert_eq!(id_from_string(&"".to_string()), None);
        assert_eq!(id_from_string(&"1invalid".to_string()), None);
        assert_eq!(id_from_string(&"valid_id".to_string()), Some("valid_id".to_string()));
        assert_eq!(id_from_string(&"invalid@id".to_string()), None);
        assert_eq!(id_from_string(&"invalid id".to_string()), None);
        assert_eq!(id_from_string(&"extern".to_string()), None);
    }
    #[test]
    fn test_value_from_string() {
        assert_eq!(Value::from_string(&"123".to_string()), Some(Value::Integer(123)));
        assert_eq!(Value::from_string(&"123.456".to_string()), Some(Value::Float(123.456)));
        assert_eq!(Value::from_string(&"true".to_string()), Some(Value::Boolean(true)));
        assert_eq!(Value::from_string(&"false".to_string()), Some(Value::Boolean(false)));
        assert_eq!(Value::from_string(&"invalid".to_string()), None);
    }

    #[test]
    fn test_value_get_type() {
        assert_eq!(Value::Integer(123).get_type(), Type::Integer);
        assert_eq!(Value::Float(123.456).get_type(), Type::Float);
        assert_eq!(Value::Boolean(true).get_type(), Type::Boolean);
    }

    #[test]
    fn test_special_symbol_from_string() {
        assert_eq!(SpecialSymbol::from_string(&"=".to_string()), Some(SpecialSymbol::Equals));
        assert_eq!(SpecialSymbol::from_string(&";".to_string()), Some(SpecialSymbol::Terminator));
        assert_eq!(SpecialSymbol::from_string(&"(".to_string()), Some(SpecialSymbol::OpenParen));
        assert_eq!(SpecialSymbol::from_string(&")".to_string()), Some(SpecialSymbol::CloseParen));
        assert_eq!(SpecialSymbol::from_string(&"{".to_string()), Some(SpecialSymbol::OpenBracket));
        assert_eq!(SpecialSymbol::from_string(&"}".to_string()), Some(SpecialSymbol::CloseBracket));
        assert_eq!(SpecialSymbol::from_string(&",".to_string()), Some(SpecialSymbol::Comma));
        assert_eq!(SpecialSymbol::from_string(&"invalid".to_string()), None);
    }

    #[test]
    fn test_operator_from_string() {
        assert_eq!(Operator::from_string(&"+".to_string()), Some(Operator::Plus));
        assert_eq!(Operator::from_string(&"-".to_string()), Some(Operator::Minus));
        assert_eq!(Operator::from_string(&"*".to_string()), Some(Operator::Multiply));
        assert_eq!(Operator::from_string(&"/".to_string()), Some(Operator::Divide));
        assert_eq!(Operator::from_string(&"invalid".to_string()), None);
    }
}