use std::{collections::HashMap, error::Error, fmt::Display};

use crate::lexer::{self, Keyword, Operator, SpecialSymbol, Token, Tokens, Type, Value};

#[derive(Debug, Clone)]
pub struct ParseError{
    msg: String
}
impl ParseError {
    pub fn new(msg: String) -> Self {
        Self {
            msg
        }
    }
}
impl Error for ParseError{}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.msg)
    }
}

pub fn parse(mut tokens: Tokens) -> Result<SyntaxTree, ParseError> {
    let mut syntax_tree = SyntaxTree::new();
    loop {
        match tokens.peek() {
            lexer::Token::EOF => break,
            lexer::Token::Keyword(lexer::Keyword::Function) => {
                syntax_tree.push(parse_function(&mut tokens)?)
            },
            lexer::Token::Keyword(lexer::Keyword::External) => {
                syntax_tree.external(parse_extern(&mut tokens)?)
            },
            token => {
                return Err(ParseError::new(format!("Unexpected token: {token}")));
            }
        }
    }

    return Ok(syntax_tree)
}

pub fn parse_extern(tokens: &mut Tokens) -> Result<String, ParseError> {
    // Consume External token
    match tokens.next() {
        Token::Keyword(Keyword::External) => (),
        token => { // Should never run as this is checked in parse
            return Err(ParseError::new(format!("Unexpected token: {token}")));
        }
    };

    // Get external module name
    let name = match tokens.next() {
        Token::Identifier(id) => id,
        token => {
            return Err(ParseError::new(format!("Unexpected token after extern: {token}")));
        }
    };

    // Consume terminator
    match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::Terminator) => Ok(name),
        token => {
            return Err(ParseError::new(format!("Unexpected token after extern: {token}")));
        }
    }
}

pub fn parse_function(tokens: &mut Tokens) -> Result<Function, ParseError> {
    // Consume Function token
    match tokens.next() {
        Token::Keyword(Keyword::Function) => (),
        token => { // Should never run as this is checked in parse
            return Err(ParseError::new(format!("Unexpected token: {token}")));
        }
    };

    // Get function name
    let name = match tokens.next() {
        Token::Identifier(id) => id,
        token => {
            return Err(ParseError::new(format!("Unexpected token after fn: {token}")));
        }
    };

    // Get function arguments
    let parameters = match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::OpenParen) => {
            let mut params = Vec::new();
            match tokens.peek() {
                Token::SpecialSymbol(SpecialSymbol::CloseParen) => (), // No arguments
                _ => {
                    loop {
                        match tokens.next() {
                            Token::Identifier(id) => {
                                if let Token::Type(type_) = tokens.next() {
                                    params.push((id, type_));
                                } else {
                                    return Err(ParseError::new(format!("Function argument type not provided")));
                                }
                            },
                            token => {
                                return Err(ParseError::new(format!("Unexpected token in function arguments: {token}")));
                            }
                        }
        
                        match tokens.peek() {
                            Token::SpecialSymbol(SpecialSymbol::Comma) => (),
                            Token::SpecialSymbol(SpecialSymbol::CloseParen) => break,
                            token => {
                                return Err(ParseError::new(format!("Unexpected token in function arguments: {token}")));
                            }
                        }
                        tokens.next(); // Consume comma
                    }
                }
            }
            
            tokens.next(); // Consume Close parentheses
            Ok(params)
        },
        token => {
            return Err(ParseError::new(format!("Unexpected token after function name: {token}")));
        }
    }?;

    let return_type = match tokens.next() {
        Token::Type(type_) => Ok(type_),
        token => {
            Err(ParseError::new(format!("Unexpected token after function paramaters: {token}")))
        }
    }?;

    Ok(Function {
        name,
        closure: parse_closure(return_type, parameters, tokens)?,
    })
}

fn parse_closure(return_type: Type, parameters: Vec<(String, Type)>, tokens: &mut Tokens) -> Result<Closure, ParseError> {
    match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::OpenBracket) => Ok(()),
        token => {
            Err(ParseError::new(format!("Unexpected token at the start of a closure: {token}")))
        }
    }?;

    let mut variables: HashMap<String, Type> = parameters.iter().cloned().collect();
    let mut instructions = Vec::new();

    loop {
        if let Token::SpecialSymbol(SpecialSymbol::CloseBracket) = tokens.peek() {
            tokens.next();
            break;
        }
        instructions.push(parse_instruction(tokens, &mut variables)?);
    }

    return Ok(Closure {
        return_type,
        parameters,
        instructions,
    });
}

fn parse_instruction(tokens: &mut Tokens, variables: &mut HashMap<String, Type>) -> Result<Instruction, ParseError> {
    let instruction = match tokens.next() {
        Token::Keyword(Keyword::Assignment) => {
            let id = match tokens.next() {
                Token::Identifier(id) => Ok(id),
                token => {
                    return Err(ParseError::new(format!("Unexpected token after let: {token}")))
                }
            }?;

            match tokens.next() {
                Token::SpecialSymbol(SpecialSymbol::Equals) => Ok(()),
                token => {
                    Err(ParseError::new(format!("Unexpected token after assignment variable: {token}")))
                }
            }?;

            variables.insert(id.clone(), Type::Void);

            Ok(Instruction::Assignment { id, value: parse_expression(tokens, variables)? })
        },
        Token::Keyword(Keyword::Return) => {
            Ok(Instruction::Return(parse_expression(tokens, variables)?))
        },
        Token::Identifier(id) => {
            if variables.contains_key(&id) {
                match tokens.next() {
                    Token::SpecialSymbol(SpecialSymbol::Equals) => (),
                    token => return Err(ParseError::new(format!("Unexpected token after variable name: {token}")))
                }
                Ok(Instruction::Assignment { id, value: parse_expression(tokens, variables)? })
            } else {
                Ok(Instruction::FunctionCall(parse_function_call(id, tokens, variables)?))
            }
        },
        token => {
            Err(ParseError::new(format!("Unexpected token at the start of an instruction: {token}")))
        }
    }?;
    tokens.next();
    Ok(instruction)
}

fn parse_function_call(function: String, tokens: &mut Tokens, variables: &mut HashMap<String, Type>) -> Result<FunctionCall, ParseError> {
    let parameters = match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::OpenParen) => {
            let mut params = Vec::new();
            loop {
                params.push(parse_expression(tokens, variables)?);

                match tokens.next() {
                    Token::SpecialSymbol(SpecialSymbol::Comma) => Ok(()),
                    Token::SpecialSymbol(SpecialSymbol::CloseParen) => break,
                    token => {
                        Err(ParseError::new(format!("Unexpected token in function parameters: {token}")))
                    }
                }?
            }
            Ok(params)
        }
        token => {
            Err(ParseError::new(format!("Unexpected token after function name 1: {token}")))
        }
    }?;
    Ok(FunctionCall::new(function, parameters))
}

fn parse_expression(tokens: &mut Tokens, variables: &mut HashMap<String, Type>) -> Result<Expression, ParseError> {
    let mut operands = Vec::new();
    let mut operators = Vec::new();

    let mut last_element_was_operator = true;

    let in_paretheses = if let Token::SpecialSymbol(SpecialSymbol::OpenParen) = tokens.peek() {tokens.next(); true} else {false};

    loop {
        match tokens.peek() {
            Token::SpecialSymbol(SpecialSymbol::OpenParen) => {
                if !last_element_was_operator {
                    return Err(ParseError::new(format!("Expected operator")));
                }
                operands.push(parse_expression(tokens, variables)?);
                last_element_was_operator = false;
                continue;
            },
            Token::SpecialSymbol(SpecialSymbol::CloseParen) => {
                if !in_paretheses {
                    break;
                }
                Ok(())
            },
            Token::SpecialSymbol(symbol) => {
                if in_paretheses {
                    return Err(ParseError::new(format!("Unexpected symbol in expression: {}", Token::SpecialSymbol(*symbol))))
                }
                break;
            }
            _ => Ok(())
        }?;

        match tokens.next() {
            Token::Value(value) => {
                operands.push(Expression::Value(value))
            },
            Token::Identifier(id) => {
                operands.push(match tokens.peek() {
                    Token::SpecialSymbol(SpecialSymbol::OpenParen) => Expression::FunctionCall(parse_function_call(id, tokens, variables)?),
                    _ => Expression::Variable(id)
                });
                last_element_was_operator = false;
            },
            Token::SpecialSymbol(SpecialSymbol::CloseParen) => {
                break; // Checked earlier that we are in paretheses
            },
            Token::Operator(op) => {
                if last_element_was_operator {
                    return Err(ParseError::new(format!("Unexpected operator after operator")))
                }
                last_element_was_operator = true;
                operators.push(op);
            },
            token => {
                return Err(ParseError::new(format!("Unexpected token in expression: {token}")))
            },
        }
    };

    loop {
        let index = operators.iter().enumerate().find(|(_, op)| {
            match op {
                Operator::Plus => false,
                Operator::Minus => false,
                Operator::Multiply => true,
                Operator::Divide => true,
            }
        }).and_then(|(index, _)| Some(index));

        match index {
            Some(index) => {
                let operator = operators.remove(index);
                let lhv = operands.remove(index);
                let rhv = operands.remove(index);

                operands.insert(index, Expression::MathOpearation { lhv: Box::new(lhv), rhv: Box::new(rhv), operator })
            },
            None => break,
        }
    }

    loop {
        let index = operators.iter().enumerate().find(|(_, op)| {
            match op {
                Operator::Plus => true,
                Operator::Minus => true,
                Operator::Multiply => false,
                Operator::Divide => false,
            }
        }).and_then(|(index, _)| Some(index));

        match index {
            Some(index) => {
                let operator = operators.remove(index);
                let lhv = operands.remove(index);
                let rhv = operands.remove(index);

                operands.insert(index, Expression::MathOpearation { lhv: Box::new(lhv), rhv: Box::new(rhv), operator });
            },
            None => break,
        }
    }
    Ok(operands.remove(0))
}

#[derive(Debug)]
pub struct SyntaxTree {
    pub externs: Vec<String>,
    pub functions: Vec<Function>
}
impl SyntaxTree {
    pub fn new() -> Self {
        Self {
            externs: Vec::new(),
            functions: Vec::new()
        }
    }
    pub fn push(&mut self, function: Function) {
        self.functions.push(function);
    }
    pub fn external(&mut self, external: String) {
        self.externs.push(external);
    }
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub closure: Closure
}

#[derive(Debug)]
pub enum Instruction {
    Assignment {
        id: String,
        value: Expression
    },
    Return(Expression),
    FunctionCall(FunctionCall),
}

#[derive(Debug)]
pub enum Expression {
    Value(Value),
    Variable(String),
    MathOpearation {
        lhv: Box<Expression>,
        rhv: Box<Expression>,
        operator: Operator
    },
    Closure(Closure),
    FunctionCall(FunctionCall)
}

#[derive(Debug)]
pub struct Closure {
    pub return_type: Type,
    pub parameters: Vec<(String, Type)>,
    pub instructions: Vec<Instruction>
}

#[derive(Debug)]
pub struct FunctionCall {
    pub function: String,
    pub parameters: Vec<Expression>
}
impl FunctionCall {
    pub fn new(function: String, parameters: Vec<Expression>) -> Self {
        Self { function, parameters }
    }
}