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

#[cfg(test)]
mod parse_extern_tests {
    use super::*;

    #[test]
    fn test_parse_extern_valid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::External),
            Token::Identifier("valid_module".to_string()),
            Token::SpecialSymbol(SpecialSymbol::Terminator)
        ]);

        let result = parse_extern(&mut tokens);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "valid_module");
    }

    #[test]
    fn test_parse_extern_invalid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::External),
            Token::Identifier("invalid_module".to_string())
            // Missing Terminator
        ]);

        let result = parse_extern(&mut tokens);
        assert!(result.is_err());
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

#[cfg(test)]
mod parse_function_tests {
    use super::*;

    #[test]
    fn test_parse_function_valid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Function),
            Token::Identifier("test_func".to_string()),
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Identifier("x".to_string()),
            Token::Type(Type::Integer),
            Token::SpecialSymbol(SpecialSymbol::Comma),
            Token::Identifier("y".to_string()),
            Token::Type(Type::Integer),
            Token::SpecialSymbol(SpecialSymbol::CloseParen),
            Token::Type(Type::Void),
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),
        ]);

        let result = parse_function(&mut tokens);
        assert!(result.is_ok());

        let function = result.unwrap();
        assert_eq!(function.name, "test_func");
        assert_eq!(function.closure.parameters.len(), 2);
    }

    #[test]
    fn test_parse_function_invalid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Function),
            Token::Identifier("test_func".to_string()),
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),
        ]);

        let result = parse_function(&mut tokens);
        assert!(result.is_err());
    }
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

#[cfg(test)]
mod parse_closure_tests {
    use super::*;
    use crate::lexer::{Type, SpecialSymbol, Token, Tokens};

    #[test]
    fn test_parse_closure_valid() {
        let return_type = Type::Integer;
        let parameters = vec![
            ("param1".to_string(), Type::Integer),
            ("param2".to_string(), Type::Float),
        ];
        let tokens = &mut Tokens::from_vec(vec![
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::Keyword(Keyword::Return),
            Token::Identifier("param1".to_string()),
            Token::SpecialSymbol(SpecialSymbol::Terminator),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),
        ]);

        let result = parse_closure(return_type, parameters.clone(), tokens);
        assert!(result.is_ok());
        let closure = result.unwrap();
        assert_eq!(closure.return_type, Type::Integer);
        assert_eq!(closure.parameters, parameters);
        assert_eq!(closure.instructions.len(), 1);
        match &closure.instructions[0] {
            Instruction::Return(Expression::Variable(param)) => assert_eq!(param, "param1"),
            _ => panic!("Invalid instruction"),
        }
    }

    #[test]
    fn test_parse_instruction_invalid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Assignment),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),  // Invalid token after assignment
        ]);
        let mut variables = HashMap::new();

        let result = parse_instruction(&mut tokens, &mut variables);
        assert!(result.is_err());
    }
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

#[cfg(test)]
mod parse_instruction_tests {
    use super::*;
    use crate::lexer::{Type, SpecialSymbol, Token, Tokens};

    #[test]
    fn test_parse_instruction_valid() {
        let mut variables = HashMap::new();
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Return),
            Token::Identifier("variable".to_string()),
            Token::SpecialSymbol(SpecialSymbol::Terminator),
        ]);

        variables.insert("variable".to_string(), Type::Integer);

        let result = parse_instruction(&mut tokens, &mut variables);
        assert!(result.is_ok());
        let instruction = result.unwrap();

        match instruction {
            Instruction::Return(Expression::Variable(var)) => assert_eq!(var, "variable"),
            _ => panic!("Invalid instruction"),
        }
    }

    #[test]
    fn test_parse_instruction_invalid() {
        let mut variables = HashMap::new();
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Function),
            Token::Identifier("something".to_string()),
            Token::SpecialSymbol(SpecialSymbol::Terminator),
        ]);

        let result = parse_instruction(&mut tokens, &mut variables);
        assert!(result.is_err());
    }
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

#[cfg(test)]
mod parse_function_call_tests {
    use super::*;
    use crate::lexer::{Token, SpecialSymbol, Type};

    #[test]
    fn test_parse_function_call_valid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Value(Value::Integer(5)),
            Token::SpecialSymbol(SpecialSymbol::Comma),
            Token::Value(Value::Integer(10)),
            Token::SpecialSymbol(SpecialSymbol::CloseParen)
        ]);

        let mut variables: HashMap<String, Type> = HashMap::new();

        let result = parse_function_call("test_function".to_string(), &mut tokens, &mut variables);
        assert!(result.is_ok());

        let function_call = result.unwrap();
        assert_eq!(function_call.function, "test_function");
        assert_eq!(function_call.parameters.len(), 2);
    }

    #[test]
    fn test_parse_function_call_invalid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Value(Value::Integer(5)),
            Token::SpecialSymbol(SpecialSymbol::Comma),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket)
        ]);

        let mut variables: HashMap<String, Type> = HashMap::new();

        let result = parse_function_call("test_function".to_string(), &mut tokens, &mut variables);
        assert!(result.is_err());
    }
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
                if !last_element_was_operator {
                    return Err(ParseError::new(format!("Expected operator")));
                }
                operands.push(Expression::Value(value));
                last_element_was_operator = false;
            },
            Token::Identifier(id) => {
                if !last_element_was_operator {
                    return Err(ParseError::new(format!("Expected operator")));
                }
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

    if operands.len() == 0 {
        return Err(ParseError::new(format!("Expected operand in expression")));
    }
    if operands.len() - operators.len() != 1 {
        return Err(ParseError::new(format!("Expected one more operand in expression")));
    }

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

#[cfg(test)]
mod parse_expression_tests {
    use super::*;
    use crate::lexer::{Token, SpecialSymbol};

    #[test]
    fn test_parse_expression_valid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Value(Value::Integer(5)),
            Token::Operator(Operator::Plus),
            Token::Value(Value::Integer(3)),
            Token::SpecialSymbol(SpecialSymbol::CloseParen)
        ]);
        let mut variables = HashMap::new();
        let result = parse_expression(&mut tokens, &mut variables);

        match result {
            Ok(expression) => {
                match expression {
                    Expression::MathOpearation { lhv, rhv, operator } => {
                        assert_eq!(*lhv, Expression::Value(Value::Integer(5)));
                        assert_eq!(operator, Operator::Plus);
                        assert_eq!(*rhv, Expression::Value(Value::Integer(3)));
                    },
                    _ => panic!("Unexpected expression type!")
                }
            },
            Err(err) => panic!("Parsing failed!\n{err}")
        }
        assert_eq!(tokens.next(), Token::SpecialSymbol(SpecialSymbol::CloseParen));
    }

    #[test]
    fn test_parse_expression_invalid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Value(Value::Integer(5)),
            Token::Operator(Operator::Plus),
            // Missing second operand
        ]);
        let mut variables = HashMap::new();
        let result = parse_expression(&mut tokens, &mut variables);

        assert!(result.is_err());
    }
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

#[derive(Debug, PartialEq)]
pub enum Instruction {
    Assignment {
        id: String,
        value: Expression
    },
    Return(Expression),
    FunctionCall(FunctionCall),
}

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
pub struct Closure {
    pub return_type: Type,
    pub parameters: Vec<(String, Type)>,
    pub instructions: Vec<Instruction>
}

#[derive(Debug, PartialEq)]
pub struct FunctionCall {
    pub function: String,
    pub parameters: Vec<Expression>
}
impl FunctionCall {
    pub fn new(function: String, parameters: Vec<Expression>) -> Self {
        Self { function, parameters }
    }
}