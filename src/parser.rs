use std::{collections::HashMap, error::Error, fmt::Display};

use crate::lexer::{self, Keyword, Operator, SpecialSymbol, Token, Tokens, Type, Value};

#[derive(Debug, Clone)]
pub struct ParseError{
    msg: String,
    pos: (usize, usize)
}
impl ParseError {
    pub fn new(msg: String, pos: (usize, usize)) -> Self {
        Self {
            msg,
            pos
        }
    }
}
impl Error for ParseError{}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Error compiling at {}:{}\n{}", self.pos.1, self.pos.0, self.msg)
    }
}

pub fn parse(mut tokens: Tokens) -> Result<SyntaxTree, ParseError> {
    let function_signatures = extract_function_signatures(&tokens)?;

    let mut syntax_tree = SyntaxTree::new();
    loop {
        match tokens.peek() {
            lexer::Token::EOF => break,
            lexer::Token::Keyword(lexer::Keyword::Function) => {
                syntax_tree.push(parse_function(&mut tokens, &function_signatures)?)
            },
            lexer::Token::Keyword(lexer::Keyword::External) => {
                syntax_tree.external(parse_extern(&mut tokens)?)
            },
            token => {
                return Err(ParseError::new(format!("Unexpected token: {token}"), tokens.get_curr_location()));
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
            return Err(ParseError::new(format!("Unexpected token: {token}"), tokens.get_prev_location()));
        }
    };

    // Get external module name
    let name = match tokens.next() {
        Token::Identifier(id) => id,
        token => {
            return Err(ParseError::new(format!("Unexpected token after extern: {token}"), tokens.get_prev_location()));
        }
    };

    // Consume signature
    if let Token::SpecialSymbol(SpecialSymbol::OpenParen) = tokens.next() {
        loop {
            match tokens.next() {
                Token::Type(_) => {
                    match tokens.next() {
                        Token::SpecialSymbol(SpecialSymbol::CloseParen) => {
                            match tokens.next() {
                                Token::Type(_) => break,
                                token => {
                                    return Err(ParseError::new(format!("Expected extern return type, got {token}"), tokens.get_prev_location()));   
                                }
                            }
                        },
                        Token::SpecialSymbol(SpecialSymbol::Comma) => (),
                        token => {
                            return Err(ParseError::new(format!("Unexpected token after type: {token}"), tokens.get_prev_location()));
                        }
                    }
                }
                token => {
                    return Err(ParseError::new(format!("Unexpected token after type: {token}"), tokens.get_prev_location()));
                }
            }
        }
    }
    

    // Consume terminator
    match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::Terminator) => Ok(name),
        token => {
            return Err(ParseError::new(format!("Unexpected token after extern: {token}"), tokens.get_prev_location()));
        }
    }
}

fn parse_function(tokens: &mut Tokens, function_signatures: &HashMap<String, FunctionSiganture>) -> Result<Function, ParseError> {
    // Consume Function token
    match tokens.next() {
        Token::Keyword(Keyword::Function) => (),
        token => { // Should never run as this is checked in parse
            return Err(ParseError::new(format!("Unexpected token: {token}"), tokens.get_prev_location()));
        }
    };

    // Get function name
    let name = match tokens.next() {
        Token::Identifier(id) => id,
        token => {
            return Err(ParseError::new(format!("Unexpected token after fn: {token}"), tokens.get_prev_location()));
        }
    };

    // Get function arguments
    let arguments = match tokens.next() {
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
                                    return Err(ParseError::new(format!("Function argument type not provided"), tokens.get_prev_location()));
                                }
                            },
                            token => {
                                return Err(ParseError::new(format!("Unexpected token in function arguments: {token}"), tokens.get_prev_location()));
                            }
                        }
        
                        match tokens.peek() {
                            Token::SpecialSymbol(SpecialSymbol::Comma) => (),
                            Token::SpecialSymbol(SpecialSymbol::CloseParen) => break,
                            token => {
                                return Err(ParseError::new(format!("Unexpected token in function arguments: {token}"), tokens.get_curr_location()));
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
            return Err(ParseError::new(format!("Unexpected token after function name: {token}"), tokens.get_prev_location()));
        }
    }?;

    let return_type = match tokens.next() {
        Token::Type(type_) => Ok(type_),
        token => {
            Err(ParseError::new(format!("Unexpected token after function paramaters: {token}"), tokens.get_prev_location()))
        }
    }?;

    let mut variables = arguments.iter().cloned().collect();

    Ok(Function {
        name,
        arguments,
        block: parse_block(tokens, return_type, &mut variables, function_signatures)?,
    })
}

fn parse_block(tokens: &mut Tokens, return_type: Type, variables: &mut HashMap<String, Type>, function_signatures: &HashMap<String, FunctionSiganture>) -> Result<Block, ParseError> {
    match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::OpenBracket) => Ok(()),
        token => {
            Err(ParseError::new(format!("Unexpected token at the start of a code block: {token}"), tokens.get_prev_location()))
        }
    }?;
    let mut instructions = Vec::new();

    loop {
        if let Token::SpecialSymbol(SpecialSymbol::CloseBracket) = tokens.peek() {
            tokens.next();
            break;
        }
        instructions.push(parse_instruction(tokens, variables, function_signatures, &return_type)?);
    }

    return Ok(Block {
        return_type,
        instructions,
    });
}

fn parse_instruction(tokens: &mut Tokens, variables: &mut HashMap<String, Type>, function_signatures: &HashMap<String, FunctionSiganture>, return_type: &Type) -> Result<Instruction, ParseError> {
    let mut expect_terminator = true;

    let instruction = match tokens.next() {
        Token::Keyword(Keyword::Declaration) => {
            let id = match tokens.next() {
                Token::Identifier(id) => Ok(id),
                token => {
                    return Err(ParseError::new(format!("Unexpected token after let: {token}"), tokens.get_prev_location()))
                }
            }?;

            match tokens.next() {
                Token::SpecialSymbol(SpecialSymbol::Equals) => Ok(()),
                token => {
                    Err(ParseError::new(format!("Unexpected token after assignment variable: {token}"), tokens.get_prev_location()))
                }
            }?;

            let value = parse_expression(tokens, variables, function_signatures)?;
            let type_ = value.get_type(variables, function_signatures).unwrap();
            variables.insert(id.clone(), type_);

            Ok(Instruction::Decleration { id, value })
        },
        Token::Keyword(Keyword::Return) => {
            if let Token::SpecialSymbol(SpecialSymbol::Terminator) = tokens.peek() {
                Ok(Instruction::Return(Expression::Value(Value::Void)))
            } else {
                let expression = parse_expression(tokens, variables, function_signatures)?;
                if expression.get_type(variables, function_signatures) != Some(*return_type) {
                    return Err(ParseError::new(format!("Expected return type {return_type:?} but found {expression:?}"), tokens.get_prev_location()));
                }
                Ok(Instruction::Return(expression))
            }
        },
        Token::Keyword(Keyword::If) => {
            expect_terminator = false;
            Ok(Instruction::If { condition: parse_expression(tokens, variables, function_signatures)?, block: parse_block(tokens, Type::Void, variables, function_signatures)? })
        },
        Token::Keyword(Keyword::While) => {
            expect_terminator = false;
            let condition = parse_expression(tokens, variables, function_signatures)?;
            let condition_type = condition.get_type(variables, function_signatures).unwrap();
            if condition_type != Type::Boolean {
                return Err(ParseError::new(format!("Expected condition type boolean but found {condition_type:?}"), tokens.get_prev_location()));
            }
            Ok(Instruction::While { condition, block: parse_block(tokens, Type::Void, variables, function_signatures)? })
        }
        Token::Identifier(id) => {
            if variables.contains_key(&id) {
                match tokens.next() {
                    Token::SpecialSymbol(SpecialSymbol::Equals) => (),
                    token => return Err(ParseError::new(format!("Unexpected token after variable name: {token}"), tokens.get_prev_location()))
                }
                Ok(Instruction::Assignment { id, value: parse_expression(tokens, variables, function_signatures)? })
            } else {
                Ok(Instruction::FunctionCall(parse_function_call(id, tokens, variables, function_signatures)?))
            }
        },
        token => {
            Err(ParseError::new(format!("Unexpected token at the start of an instruction: {token}"), tokens.get_prev_location()))
        }
    }?;
    if expect_terminator {
        match tokens.next() {
            Token::SpecialSymbol(SpecialSymbol::Terminator) => Ok(instruction),
            token => Err(ParseError::new(format!("Unexpected token after instruction: {token}"), tokens.get_prev_location())),
        }
    } else {
        Ok(instruction)
    }
}

fn parse_function_call(function: String, tokens: &mut Tokens, variables: &mut HashMap<String, Type>, function_signatures: &HashMap<String, FunctionSiganture>) -> Result<FunctionCall, ParseError> {
    let arguments = match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::OpenParen) => {
            let mut args = Vec::new();
            loop {
                args.push(parse_expression(tokens, variables, function_signatures)?);

                match tokens.next() {
                    Token::SpecialSymbol(SpecialSymbol::Comma) => Ok(()),
                    Token::SpecialSymbol(SpecialSymbol::CloseParen) => break,
                    token => {
                        Err(ParseError::new(format!("Unexpected token in function parameters: {token}"), tokens.get_prev_location()))
                    }
                }?
            }
            Ok(args)
        }
        token => {
            Err(ParseError::new(format!("Unexpected token after function name: {token}"), tokens.get_prev_location()))
        }
    }?;
    if let Some(signature) = function_signatures.get(&function) {
        if arguments.iter().enumerate().all(|(index, argument)| {
            signature.arguments.get(index).is_some_and(|type_| type_ == &argument.get_type(variables, function_signatures).unwrap())
        }) {
            Ok(FunctionCall::new(function, arguments))
        } else {
            Err(ParseError::new(format!("Function call has wrong arguments"), tokens.get_prev_location()))
        }
    } else {
        Err(ParseError::new(format!("Function {function} not found"), tokens.get_prev_location()))
    }
}

fn parse_expression(tokens: &mut Tokens, variables: &mut HashMap<String, Type>, function_signatures: &HashMap<String, FunctionSiganture>) -> Result<Expression, ParseError> {
    let mut operands = Vec::new();
    let mut operators = Vec::new();

    let mut last_element_was_operator = true;

    let in_paretheses = if let Token::SpecialSymbol(SpecialSymbol::OpenParen) = tokens.peek() {tokens.next(); true} else {false};

    loop {
        match tokens.peek() {
            Token::SpecialSymbol(SpecialSymbol::OpenParen) => {
                if !last_element_was_operator {
                    return Err(ParseError::new(format!("Expected operator"), tokens.get_curr_location()));
                }
                operands.push(parse_expression(tokens, variables, function_signatures)?);
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
                    return Err(ParseError::new(format!("Unexpected symbol in expression: {}", Token::SpecialSymbol(*symbol)), tokens.get_curr_location()))
                }
                break;
            }
            _ => Ok(())
        }?;

        match tokens.next() {
            Token::Value(value) => {
                if !last_element_was_operator {
                    return Err(ParseError::new(format!("Expected operator"), tokens.get_prev_location()));
                }
                operands.push(Expression::Value(value));
                last_element_was_operator = false;
            },
            Token::Identifier(id) => {
                if !last_element_was_operator {
                    return Err(ParseError::new(format!("Expected operator"), tokens.get_prev_location()));
                }
                operands.push(match tokens.peek() {
                    Token::SpecialSymbol(SpecialSymbol::OpenParen) => Expression::FunctionCall(parse_function_call(id, tokens, variables, function_signatures)?),
                    _ => Expression::Variable(id)
                });
                last_element_was_operator = false;
            },
            Token::SpecialSymbol(SpecialSymbol::CloseParen) => {
                break; // Checked earlier that we are in paretheses
            },
            Token::Operator(op) => {
                if last_element_was_operator {
                    return Err(ParseError::new(format!("Unexpected operator after operator"), tokens.get_prev_location()))
                }
                last_element_was_operator = true;
                operators.push(op);
            },
            token => {
                return Err(ParseError::new(format!("Unexpected token in expression: {token}"), tokens.get_prev_location()))
            },
        }
    };

    if operands.len() == 0 {
        return Err(ParseError::new(format!("Expected operand in expression"), tokens.get_curr_location()));
    }
    if operands.len() - operators.len() != 1 {
        return Err(ParseError::new(format!("Expected one more operand in expression"), tokens.get_curr_location()));
    }

    let mut current_operator = 0;

    loop {
        let index = operators.iter().enumerate().find(|(_, op)| {
            op.get_operation_order() == current_operator
        }).and_then(|(index, _)| Some(index));

        match index {
            Some(index) => {
                let operator = operators.remove(index);
                let lhv = operands.remove(index);
                let rhv = operands.remove(index);

                let lhv_type = lhv.get_type(variables, function_signatures);
                let rhv_type = rhv.get_type(variables, function_signatures);

                if lhv_type != rhv_type {
                    return Err(ParseError::new(format!("Expected same types in expression, got {:?}, {:?}", lhv_type.unwrap(), rhv_type.unwrap()), tokens.get_prev_location()));
                }

                operands.insert(index, Expression::MathOpearation { lhv: Box::new(lhv), rhv: Box::new(rhv), operator })
            },
            None => {
                if operands.len() == 1 {
                    break;
                } else {
                    current_operator += 1;
                }
            },
        }
    }
    Ok(operands.remove(0))
}

struct FunctionSiganture {
    name: String,
    arguments: Vec<Type>,
    return_type: Type
}
impl FunctionSiganture {
    pub fn new(name: String, arguments: Vec<Type>, return_type: Type) -> Self {
        Self { name, arguments, return_type }
    }
}

fn extract_function_signatures(tokens: &Tokens) -> Result<HashMap<String, FunctionSiganture>, ParseError> {
    let mut signatures = HashMap::new();
    let mut idx = 0;
    loop {
        match tokens.peek_nth(idx) {
            lexer::Token::EOF => break,
            lexer::Token::Keyword(lexer::Keyword::Function) |
            lexer::Token::Keyword(lexer::Keyword::External) => {
                let signature = extract_function_signature(tokens, idx).unwrap();
                signatures.insert(signature.name.clone(), signature);
            },
            _ => ()
        }
        idx += 1;
    }
    Ok(signatures)
}

// New function to extract the function signature
fn extract_function_signature(tokens: &Tokens, mut index: usize) -> Result<FunctionSiganture, ParseError> {
    match tokens.peek_nth(index) {
        lexer::Token::Keyword(lexer::Keyword::Function) => {
            index += 1;
            let name = if let lexer::Token::Identifier(name) = tokens.peek_nth(index) {
                name.clone()
            } else {
                return Err(ParseError::new("Expected function name".to_string(), tokens.get_location_nth(index)));
            };

            index += 1;
            let mut arguments = Vec::new();

            if let lexer::Token::SpecialSymbol(lexer::SpecialSymbol::OpenParen) = tokens.peek_nth(index) {
                loop {
                    index += 1;
                    match tokens.peek_nth(index) {
                        lexer::Token::SpecialSymbol(lexer::SpecialSymbol::CloseParen) => {
                            break;
                        },
                        lexer::Token::Identifier(_) => {
                            index += 1;
                            if let lexer::Token::Type(type_) = tokens.peek_nth(index) {
                                arguments.push(*type_);
                            }
                            if let lexer::Token::SpecialSymbol(lexer::SpecialSymbol::Comma) = tokens.peek_nth(index+1) {
                                index += 1;
                            }
                        }
                        token => {
                            return Err(ParseError::new(format!("Expected function argument, got {}", token).to_string(), tokens.get_location_nth(index)));
                        }
                    }
                }
            } else {
                return Err(ParseError::new("Expected function arguments".to_string(), tokens.get_location_nth(index)));
            };

            index += 1;
            let return_type = if let lexer::Token::Type(type_) = tokens.peek_nth(index) {
                *type_
            } else {
                return Err(ParseError::new("Expected function return type".to_string(), tokens.get_location_nth(index)));
            };

            Ok(FunctionSiganture::new(name, arguments, return_type))
        },
        lexer::Token::Keyword(lexer::Keyword::External) => {
            index += 1;
            let name = if let lexer::Token::Identifier(name) = tokens.peek_nth(index) {
                name.clone()
            } else {
                return Err(ParseError::new("Expected external function name".to_string(), tokens.get_location_nth(index)));
            };

            index += 1;
            let mut arguments = Vec::new();

            if let lexer::Token::SpecialSymbol(lexer::SpecialSymbol::OpenParen) = tokens.peek_nth(index) {
                loop {
                    index += 1;
                    match tokens.peek_nth(index) {
                        lexer::Token::SpecialSymbol(lexer::SpecialSymbol::CloseParen) => {
                            break;
                        },
                        lexer::Token::Type(type_) => {
                            arguments.push(*type_);
                            if let lexer::Token::SpecialSymbol(lexer::SpecialSymbol::Comma) = tokens.peek_nth(index+1) {
                                index += 1;
                            }
                        }
                        _ => {
                            return Err(ParseError::new("Expected external function argument".to_string(), tokens.get_location_nth(index)));
                        }
                    }
                }
            } else {
                return Err(ParseError::new("Expected external function arguments".to_string(), tokens.get_location_nth(index)));
            };

            index += 1;
            let return_type = if let lexer::Token::Type(type_) = tokens.peek_nth(index) {
                *type_
            } else {
                return Err(ParseError::new("Expected external function return type".to_string(), tokens.get_location_nth(index)));
            };

            Ok(FunctionSiganture::new(name, arguments, return_type))
        },
        _ => Err(ParseError::new("Expected function siganture".to_string(), tokens.get_location_nth(index)))
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
    pub arguments: Vec<(String, Type)>,
    pub block: Block
}

#[derive(Debug, PartialEq)]
pub enum Instruction {
    Decleration {
        id: String,
        value: Expression
    },
    Assignment {
        id: String,
        value: Expression
    },
    Return(Expression),
    FunctionCall(FunctionCall),
    If {
        condition: Expression,
        block: Block
    },
    While {
        condition: Expression,
        block: Block
    }
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
    FunctionCall(FunctionCall)
}

impl Expression {
    fn get_type(&self, variables: &mut HashMap<String, Type>, function_signatures: &HashMap<String, FunctionSiganture>) -> Option<Type> {
        match self {
            Expression::Value(value) => Some(value.get_type()),
            Expression::Variable(var) => variables.get(var).copied(),
            Expression::MathOpearation { lhv, rhv, operator } => {
                let lhv_type = lhv.get_type(variables, function_signatures);
                let rhv_type = rhv.get_type(variables, function_signatures);
                if lhv_type == rhv_type {
                    match operator {
                        Operator::Plus | Operator::Minus | Operator::Multiply | Operator::Divide => Some(lhv_type.unwrap()),
                        Operator::GreaterThan | Operator::LessThan | Operator::GreaterThanOrEqual | Operator::LessThanOrEqual | Operator::Equal | Operator::NotEqual => Some(Type::Boolean),
                    }
                } else {
                    return None
                }
            },
            Expression::FunctionCall(call) => {
                function_signatures.get(&call.function).and_then(|signature| Some(signature.return_type))
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Block {
    pub return_type: Type,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::{Token, Value, Operator, SpecialSymbol};

    fn empty_signature() -> HashMap<String, FunctionSiganture> {
            vec![("".to_string(),FunctionSiganture {
            name: "".to_string(),
            arguments: Vec::new(),
            return_type: Type::Void
        })].into_iter().collect()
    }
    
    #[test]
    fn test_parse_expression_valid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Value(Value::Integer(5)),
            Token::Operator(Operator::Plus),
            Token::Value(Value::Integer(3)),
            Token::SpecialSymbol(SpecialSymbol::CloseParen)
        ]);
        let mut variables = HashMap::new();
        let result = parse_expression(&mut tokens, &mut variables, &empty_signature());

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
        let result = parse_expression(&mut tokens, &mut variables, &empty_signature());

        assert!(result.is_err());
    }


    #[test]
    fn test_parse_function_call_valid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Value(Value::Integer(5)),
            Token::SpecialSymbol(SpecialSymbol::Comma),
            Token::Value(Value::Integer(10)),
            Token::SpecialSymbol(SpecialSymbol::CloseParen)
        ]);

        let signature = vec![("test_function".to_string(),FunctionSiganture {
            name: "test_function".to_string(),
            arguments: vec![Type::Integer, Type::Integer],
            return_type: Type::Void
        })].into_iter().collect();

        let mut variables: HashMap<String, Type> = HashMap::new();

        let result = parse_function_call("test_function".to_string(), &mut tokens, &mut variables, &signature);
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

        let result = parse_function_call("test_function".to_string(), &mut tokens, &mut variables, &empty_signature());
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_instruction_valid() {
        let mut variables = HashMap::new();
        variables.insert("variable".to_string(), Type::Integer);

        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Return),
            Token::Identifier("variable".to_string()),
            Token::SpecialSymbol(SpecialSymbol::Terminator),
        ]);

        variables.insert("variable".to_string(), Type::Integer);

        let result = parse_instruction(&mut tokens, &mut variables, &empty_signature(), &Type::Integer);
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

        let result = parse_instruction(&mut tokens, &mut variables, &empty_signature(), &Type::Void);
        assert!(result.is_err());
        }

    #[test]
    fn test_parse_closure_valid() {
        let return_type = Type::Integer;
        let mut variables = vec![
            ("param1".to_string(), Type::Integer),
            ("param2".to_string(), Type::Float),
        ].into_iter().collect();
        let tokens = &mut Tokens::from_vec(vec![
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::Keyword(Keyword::Return),
            Token::Identifier("param1".to_string()),
            Token::SpecialSymbol(SpecialSymbol::Terminator),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),
        ]);

        let result = parse_block(tokens, return_type, &mut variables, &empty_signature());
        println!("Result {:?}", result);
        assert!(result.is_ok());
        let closure = result.unwrap();
        assert_eq!(closure.return_type, Type::Integer);
        assert_eq!(closure.instructions.len(), 1);
        match &closure.instructions[0] {
            Instruction::Return(Expression::Variable(param)) => assert_eq!(param, "param1"),
            _ => panic!("Invalid instruction"),
        }
    }
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

        let result = parse_function(&mut tokens, &empty_signature());
        assert!(result.is_ok());

        let function = result.unwrap();
        assert_eq!(function.name, "test_func");
        assert_eq!(function.arguments, vec![("x".to_string(), Type::Integer), ("y".to_string(), Type::Integer)]);
    }

    #[test]
    fn test_parse_function_invalid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Function),
            Token::Identifier("test_func".to_string()),
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),
        ]);

        let result = parse_function(&mut tokens, &empty_signature());
        assert!(result.is_err());
    }
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

    #[test]
    fn test_generate_function_signatures() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Function),
            Token::Identifier("func1".to_string()),
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Identifier("x".to_string()),
            Token::Type(Type::Integer),
            Token::SpecialSymbol(SpecialSymbol::CloseParen),
            Token::Type(Type::Void),
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),
            Token::Keyword(Keyword::External),
            Token::Identifier("func2".to_string()),
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Type(Type::Float),
            Token::SpecialSymbol(SpecialSymbol::CloseParen),
            Token::Type(Type::Void),
            Token::SpecialSymbol(SpecialSymbol::Terminator),
        ]);

        let result = extract_function_signatures(&mut tokens);
        assert!(result.is_ok());

        let signatures = result.unwrap();
        assert_eq!(signatures.len(), 2);
        assert!(signatures.contains_key("func1"));
        assert_eq!(signatures.get("func1").unwrap().arguments, vec![Type::Integer]);
        assert!(signatures.contains_key("func2"));
        assert_eq!(signatures.get("func2").unwrap().arguments, vec![Type::Float]);
    }
}