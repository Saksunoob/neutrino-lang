use std::{collections::HashMap, process::exit};

use crate::lexer::{self, Keyword, Operator, SpecialSymbol, Token, Tokens, Type, Value};

pub fn parse(mut tokens: Tokens) -> SyntaxTree {
    let mut syntax_tree = SyntaxTree::new();
    loop {
        match tokens.peek() {
            lexer::Token::EOF => break,
            lexer::Token::Keyword(lexer::Keyword::Function) => {
                syntax_tree.push(parse_function(&mut tokens))
            },
            token => {
                eprintln!("Unexpected token: {token}");
                exit(1);
            }
        }
    }

    return syntax_tree
}

pub fn parse_function(tokens: &mut Tokens) -> Function {
    // Consume Function token
    match tokens.next() {
        Token::Keyword(Keyword::Function) => (),
        token => { // Should never run as this is checked in parse
            eprintln!("Unexpected token: {token}");
            exit(1);
        }
    };

    // Get function name
    let name = match tokens.next() {
        Token::Identifier(id) => id,
        token => {
            eprintln!("Unexpected token after fn: {token}");
            exit(1);
        }
    };

    // Get function parameters
    let parameters = match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::OpenParen) => {
            let mut params = Vec::new();
            loop {
                match tokens.next() {
                    Token::Identifier(id) => {
                        if let Token::Type(type_) = tokens.next() {
                            params.push((id, type_));
                        }
                        match tokens.next() {
                            Token::SpecialSymbol(SpecialSymbol::Comma) => (),
                            token => {
                                eprintln!("Unexpected token in function parameters: {token}");
                                exit(1);
                            }
                        }
                    },
                    Token::SpecialSymbol(SpecialSymbol::CloseParen) => break,
                    token => {
                        eprintln!("Unexpected token in function parameters: {token}");
                        exit(1);
                    }
                }
            }
            params
        }
        token => {
            eprintln!("Unexpected token after function name: {token}");
            exit(1);
        }
    };

    let return_type = match tokens.next() {
        Token::Type(type_) => type_,
        token => {
            eprintln!("Unexpected token after function paramaters: {token}");
            exit(1);
        }
    };

    Function {
        name,
        closure: parse_closure(return_type, parameters, tokens),
    }
}

fn parse_closure(return_type: Type, parameters: Vec<(String, Type)>, tokens: &mut Tokens) -> Closure {
    match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::OpenBracket) => (),
        token => {
            eprintln!("Unexpected token at the start of a closure: {token}");
            exit(1);
        }
    };

    let mut variables: HashMap<String, Type> = parameters.iter().cloned().collect();
    let mut instructions = Vec::new();

    loop {
        if let Token::SpecialSymbol(SpecialSymbol::CloseBracket) = tokens.peek() {
            tokens.next();
            break;
        }
        instructions.push(parse_instruction(tokens, &mut variables));
    }

    return Closure {
        return_type,
        parameters,
        instructions,
    };
}

fn parse_instruction(tokens: &mut Tokens, variables: &mut HashMap<String, Type>) -> Instruction {
    let instruction = match tokens.next() {
        Token::Keyword(Keyword::Assignment) => {
            let id = match tokens.next() {
                Token::Identifier(id) => id,
                token => {
                    eprintln!("Unexpected token after let: {token}");
                    exit(1);
                }
            };

            match tokens.next() {
                Token::SpecialSymbol(SpecialSymbol::Equals) => (),
                token => {
                    eprintln!("Unexpected token after assignment variable: {token}");
                    exit(1);
                }
            };

            Instruction::Assignment { id, value: parse_expression(tokens, variables) }
        },
        Token::Keyword(Keyword::Return) => {
            Instruction::Return(parse_expression(tokens, variables))
        },
        Token::Identifier(id) => {
            if variables.contains_key(&id) {
                Instruction::Assignment { id, value: parse_expression(tokens, variables) }
            } else {
                Instruction::FunctionCall(parse_function_call(id, tokens, variables))
            }
        },
        token => {
            eprintln!("Unexpected token at the start of an instruction: {token}");
            exit(1);
        }
    };
    tokens.next();
    instruction
}

fn parse_function_call(function: String, tokens: &mut Tokens, variables: &mut HashMap<String, Type>) -> FunctionCall {
    let parameters = match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::OpenParen) => {
            let mut params = Vec::new();
            loop {
                params.push(parse_expression(tokens, variables));

                match tokens.next() {
                    Token::SpecialSymbol(SpecialSymbol::Comma) => (),
                    Token::SpecialSymbol(SpecialSymbol::CloseParen) => break,
                    token => {
                        eprintln!("Unexpected token in function parameters: {token}");
                        exit(1);
                    }
                }
            }
            params
        }
        token => {
            eprintln!("Unexpected token after function name: {token}");
            exit(1);
        }
    };
    FunctionCall::new(function, parameters)
}

fn parse_expression(tokens: &mut Tokens, variables: &mut HashMap<String, Type>) -> Expression {
    let mut operands = Vec::new();
    let mut operators = Vec::new();

    let mut last_element_was_operator = true;

    let in_paretheses = if let Token::SpecialSymbol(SpecialSymbol::OpenParen) = tokens.peek() {tokens.next(); true} else {false};

    loop {
        match tokens.peek() {
            Token::SpecialSymbol(SpecialSymbol::OpenParen) => {
                if !last_element_was_operator {
                    eprintln!("Expected operator");
                    exit(1);
                }
                parse_expression(tokens, variables);
                last_element_was_operator = false;
                continue;
            },
            Token::SpecialSymbol(SpecialSymbol::Terminator) => {
                if in_paretheses {
                    eprintln!("Unexpected terminator");
                    exit(1);
                }
                break;
            }
            _ => ()
        }

        match tokens.next() {
            Token::Value(value) => {
                operands.push(Expression::Value(value))
            },
            Token::Identifier(id) => {
                operands.push(match tokens.peek() {
                    Token::SpecialSymbol(SpecialSymbol::OpenParen) => Expression::FunctionCall(parse_function_call(id, tokens, variables)),
                    _ => Expression::Variable(id)
                });
                last_element_was_operator = false;
            },
            Token::SpecialSymbol(SpecialSymbol::CloseParen) => {
                if in_paretheses {
                    break;
                } else {
                    eprintln!("Unexpected closed paretheses");
                    exit(1);
                }
            },
            Token::Operator(op) => {
                if last_element_was_operator {
                    eprintln!("Unexpected operator after operator");
                    exit(1);
                }
                last_element_was_operator = true;
                operators.push(op);
            },
            token => {
                eprintln!("Unexpected token in expression: {token}");
                exit(1);
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
    operands.remove(0)
}

#[derive(Debug)]
pub struct SyntaxTree {
    pub functions: Vec<Function>
}
impl SyntaxTree {
    pub fn new() -> Self {
        Self {
            functions: Vec::new()
        }
    }
    pub fn push(&mut self, function: Function) {
        self.functions.push(function);
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