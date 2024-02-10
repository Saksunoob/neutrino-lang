use std::{collections::HashMap, error::Error, fmt::Display};

use crate::lexer::{self, Keyword, NativeType, Operator, SpecialSymbol, Token, Tokens, NativeValue};

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
    let global_info = extract_global_info(&tokens)?;
    let mut syntax_tree = SyntaxTree::new();
    for external in &global_info.external_names {
        syntax_tree.external(external.clone());
    }

    loop {
        match tokens.peek() {
            lexer::Token::EOF => break,
            lexer::Token::Keyword(lexer::Keyword::Function) => {
                syntax_tree.push(parse_function(&mut tokens, &global_info)?)
            },
            lexer::Token::Keyword(lexer::Keyword::External) => {
                // Externals are handled in extract_global_info
                loop {
                    match tokens.next() {
                        Token::SpecialSymbol(SpecialSymbol::Terminator) => break,
                        _ => (),
                    }
                }
            },
            lexer::Token::Keyword(lexer::Keyword::Struct) => {
                // Structs are handled in extract_global_info
                loop {
                    match tokens.next() {
                        Token::SpecialSymbol(SpecialSymbol::CloseBracket) => break,
                        _ => (),
                    }
                }
            }
            token => {
                return Err(ParseError::new(format!("Unexpected token: {token}"), tokens.get_curr_location()));
            }
        }
    }

    return Ok(syntax_tree)
}

fn parse_function(tokens: &mut Tokens, global_info: &GlobalInfo) -> Result<Function, ParseError> {
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
                                let type_ = get_type_from_token(&tokens.next(), tokens.get_prev_location(), global_info)?;
                                params.push((id, type_));
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

    let return_type = get_type_from_token(&tokens.next(), tokens.get_prev_location(), global_info)?;

    let mut variables = arguments.iter().cloned().collect();
    let arguments = arguments.into_iter().map(|(name, type_)| (name, type_)).collect();

    Ok(Function {
        name,
        arguments,
        block: parse_block(tokens, return_type, &mut variables, global_info)?,
    })
}

fn parse_block(tokens: &mut Tokens, return_type: Type, variables: &mut HashMap<String, Type>, global_info: &GlobalInfo) -> Result<Block, ParseError> {
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
        instructions.push(parse_instruction(tokens, variables, global_info, &return_type)?);
    }

    return Ok(Block {
        return_type,
        instructions,
    });
}

fn parse_instruction(tokens: &mut Tokens, variables: &mut HashMap<String, Type>, global_info: &GlobalInfo, return_type: &Type) -> Result<Instruction, ParseError> {
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

            let value = parse_expression(tokens, variables, global_info)?;
            let type_ = value.get_type();
            variables.insert(id.clone(), type_);

            Ok(Instruction::Decleration { id, value })
        },
        Token::Keyword(Keyword::Return) => {
            if let Token::SpecialSymbol(SpecialSymbol::Terminator) = tokens.peek() {
                Ok(Instruction::Return(Expression::Value(Value::Native(NativeValue::Void))))
            } else {
                let expression = parse_expression(tokens, variables, global_info)?;
                if expression.get_type() != *return_type {
                    return Err(ParseError::new(format!("Expected return type {return_type:?} but found {expression:?}"), tokens.get_prev_location()));
                }
                Ok(Instruction::Return(expression))
            }
        },
        Token::Keyword(Keyword::If) => {
            expect_terminator = false;
            Ok(Instruction::If { condition: parse_expression(tokens, variables, global_info)?, block: parse_block(tokens, return_type.clone(), variables, global_info)? })
        },
        Token::Keyword(Keyword::While) => {
            expect_terminator = false;
            let condition = parse_expression(tokens, variables, global_info)?;
            let condition_type = condition.get_type();
            if condition_type != Type::Native(NativeType::Boolean) {
                return Err(ParseError::new(format!("Expected condition type boolean but found {condition_type:?}"), tokens.get_prev_location()));
            }
            Ok(Instruction::While { condition, block: parse_block(tokens, return_type.clone(), variables, global_info)? })
        }
        Token::Identifier(id) => {
            if variables.contains_key(&id) {
                let mut path = vec![id.clone()];
                loop {
                    match tokens.next() {
                        Token::SpecialSymbol(SpecialSymbol::Period) => {
                            match tokens.next() {
                                Token::Identifier(id) => {
                                    path.push(id);
                                },
                                token => {
                                    return Err(ParseError::new(format!("Unexpected token after variable: {token}"), tokens.get_prev_location()))
                                }
                            }
                        },
                        Token::SpecialSymbol(SpecialSymbol::Equals) => {
                            break;
                        },
                        token => {
                            return Err(ParseError::new(format!("Unexpected token after variable: {token}"), tokens.get_prev_location()))
                        },
                    }
                }
                let value = parse_expression(tokens, variables, global_info)?;
                Ok(Instruction::Assignment { id: path, value })
                
            } else {
                Ok(Instruction::FunctionCall(parse_function_call(id, tokens, variables, global_info)?))
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

fn parse_function_call(function: String, tokens: &mut Tokens, variables: &mut HashMap<String, Type>, global_info: &GlobalInfo) -> Result<FunctionCall, ParseError> {
    let arguments = match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::OpenParen) => {
            let mut args = Vec::new();
            loop {
                if let Token::SpecialSymbol(SpecialSymbol::CloseParen) = tokens.peek() {
                    tokens.next();
                    break;
                }
                args.push(parse_expression(tokens, variables, global_info)?);

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
    if let Some(signature) = global_info.get_function_signature(&function) {
        if arguments.iter().enumerate().all(|(index, argument)| {
            signature.arguments.get(index).is_some_and(|type_| type_ == &argument.get_type())
        }) {
            Ok(FunctionCall::new(function, arguments))
        } else {
            Err(ParseError::new(format!("Function call has wrong arguments\nExpected: {signature:?}\nFound: {arguments:?}"), tokens.get_prev_location()))
        }
    } else {
        Err(ParseError::new(format!("Function {function} not found"), tokens.get_prev_location()))
    }
}

fn parse_expression(tokens: &mut Tokens, variables: &mut HashMap<String, Type>, global_info: &GlobalInfo) -> Result<Expression, ParseError> {
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
                operands.push(parse_expression(tokens, variables, global_info)?);
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
                operands.push(Expression::Value(Value::Native(value)));
                last_element_was_operator = false;
            },
            Token::Identifier(id) => {
                if !last_element_was_operator {
                    return Err(ParseError::new(format!("Expected operator"), tokens.get_prev_location()));
                }
                operands.push(match tokens.peek() {
                    Token::SpecialSymbol(SpecialSymbol::OpenParen) => Expression::FunctionCall(
                        parse_function_call(id.clone(), tokens, variables, global_info)?, 
                        global_info.get_function_signature(&id).unwrap().return_type.clone()
                    ),
                    Token::SpecialSymbol(SpecialSymbol::OpenBracket) => Expression::Value(
                        Value::Struct(parse_new_struct(tokens, id, variables, global_info)?)
                    ),
                    _ => {
                        let mut path = vec![id.clone()];
                        loop {
                            match tokens.peek() {
                                Token::SpecialSymbol(SpecialSymbol::Period) => {
                                    tokens.next();
                                    match tokens.next() {
                                        Token::Identifier(id) => {
                                            path.push(id);
                                        },
                                        token => {
                                            return Err(ParseError::new(format!("Unexpected token in struct path: {token}"), tokens.get_prev_location()))
                                        }
                                    }
                                },
                                _ => break
                            }
                        }
                        Expression::Variable(path.clone(), variables.get(&id).unwrap().get_type(&path[1..].to_vec()))
                    },
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

                let lhv_type = lhv.get_type();
                let rhv_type = rhv.get_type();

                if lhv_type != rhv_type {
                    return Err(ParseError::new(format!("Expected same types in expression, got {:?}, {:?}", lhv_type, rhv_type), tokens.get_prev_location()));
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

fn parse_new_struct(tokens: &mut Tokens, name: String, variables: &mut HashMap<String, Type>, global_info: &GlobalInfo) -> Result<Struct, ParseError> {
    match tokens.next() {
        Token::SpecialSymbol(SpecialSymbol::OpenBracket) => Ok(()),
        token => Err(ParseError::new(format!("Unexpected token in struct definition: {token}"), tokens.get_prev_location())),
    }?;

    let expected_struct = match global_info.struct_signatures.get(&name) {
        Some(expected_struct) => {
            expected_struct
        }
        None => {
            return Err(ParseError::new(format!("Unknown struct {}", name), tokens.get_prev_location()));
        },
    };

    let mut field_values = Vec::new();
    loop {
        match tokens.next() {
            Token::SpecialSymbol(SpecialSymbol::CloseBracket) => {
                break;
            },
            Token::Identifier(id) => {
                let field = expected_struct.fields.get(&id);
                if let Some(field) = field {
                    match tokens.next() {
                        Token::SpecialSymbol(SpecialSymbol::Colon) => (),
                        token => {
                            return Err(ParseError::new(format!("Unexpected token in struct definition: {token}"), tokens.get_prev_location()));
                        }
                    }
                    let expression = parse_expression(tokens, variables, global_info)?;
                    if expression.get_type() != field.1 {
                        return Err(ParseError::new(format!("Expected field type {:?} but found {:?}", field.1, expression.get_type()), tokens.get_prev_location()));
                    }
                    field_values.push(expression);
                } else {
                    return Err(ParseError::new(format!("Unknown field: {id}"), tokens.get_prev_location()));
                }

                match tokens.peek() {
                    Token::SpecialSymbol(SpecialSymbol::Comma) => {
                        tokens.next();
                    },
                    _ => ()
                }
            },
            token => {
                return Err(ParseError::new(format!("Unexpected token in struct definition: {token}"), tokens.get_prev_location()));
            }
        }
    }
    Ok(Struct { signature: expected_struct.clone(), field_values })
}

fn get_type_from_token(token: &Token, token_pos: (usize, usize), global_info: &GlobalInfo) -> Result<Type, ParseError> {
    match token {
        Token::Type(type_) => Ok(Type::Native(*type_)),
        Token::Identifier(id) => {
            if let Some(struct_) = global_info.struct_signatures.get(id) {
                Ok(Type::Struct(struct_.clone()))
            } else {
                Err(ParseError::new(format!("Unknown struct: {id}"), token_pos))
            }
        }
        token => {
            Err(ParseError::new(format!("Unexpected token: {token}"), token_pos))
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Native(NativeType),
    Struct(StructSignature)
}
impl Type {
    pub fn get_size(&self) -> usize {
        match self {
            Type::Native(type_) => type_.get_size(),
            Type::Struct(struct_signature) => struct_signature.get_size(),
        }
    }
    pub fn get_offset(&self, path: &Vec<String>) -> usize {
        match self {
            Type::Native(_) => 0,
            Type::Struct(struct_signature) => {
                let field = struct_signature.fields.get(&path[0]).unwrap();
                return field.0 + field.1.get_offset(&path[1..].to_vec());
            }
        }
    }
    pub fn get_type(&self, path: &Vec<String>) -> Type {
        match self {
            Type::Native(_) => self.clone(),
            Type::Struct(struct_signature) => {
                let field = struct_signature.fields.get(&path[0]).unwrap();
                return field.1.get_type(&path[1..].to_vec());
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct TypeError {
    msg: String,
}
impl Error for TypeError{}
impl Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.msg)
    }
}

#[derive(Clone, PartialEq, Debug)]
enum InitialType {
    Native(NativeType),
    UnknownStruct(String)
}
impl InitialType {
    pub fn validate(&self, init_struct_signatures: &HashMap<String, Vec<(String, InitialType)>>, struct_signatures: &HashMap<String, StructSignature>) -> Result<Type, TypeError> {
        match self {
            InitialType::Native(type_) => Ok(Type::Native(*type_)),
            InitialType::UnknownStruct(name) => {
                if let Some(signature) = struct_signatures.get(name) {
                    Ok(Type::Struct(signature.clone()))
                } else {
                    if let Some(init_fields) = init_struct_signatures.get(name) {
                        let mut fields = HashMap::new();
                        let mut meme_loc = 0;
                        for (name, field) in init_fields.iter() {
                            let validated_field = field.validate(init_struct_signatures, struct_signatures)?;
                            let offset = validated_field.get_size();
                            fields.insert(name.clone(), (meme_loc, validated_field));
                            meme_loc += offset;
                        }
                        Ok(Type::Struct(StructSignature{ name: name.clone(), fields }))
                    } else {
                        Err(TypeError{ msg: format!("Unknown struct {}", name)})
                    }
                }
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Struct {
    pub signature: StructSignature,
    pub field_values: Vec<Expression>,
}
impl Struct {
    pub fn get_type(&self) -> Type {
        Type::Struct(self.signature.clone())
    }
}


struct GlobalInfo {
    pub function_signatures: HashMap<String, FunctionSignature>,
    pub struct_signatures: HashMap<String, StructSignature>,
    pub external_names: Vec<String>,
}
impl GlobalInfo {
    pub fn new() -> Self {
        Self {
            function_signatures: HashMap::new(),
            struct_signatures: HashMap::new(),
            external_names: Vec::new(),
        }
    }
    pub fn get_function_signature(&self, name: &str) -> Option<&FunctionSignature> {
        self.function_signatures.get(name)
    }
}
#[derive(Debug)]
struct FunctionSignature {
    name: String,
    arguments: Vec<Type>,
    return_type: Type
}
impl FunctionSignature {
    pub fn new(name: String, arguments: Vec<Type>, return_type: Type) -> Self {
        Self { name, arguments, return_type }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct StructSignature {
    pub name: String,
    pub fields: HashMap<String, (usize, Type)> // Hashmap connect each field to its offset and type
}
impl StructSignature {
    pub fn get_size(&self) -> usize {
        self.fields.iter().map(|(_, type_)| type_.1.get_size()).sum()
    }
}

fn extract_global_info(tokens: &Tokens) -> Result<GlobalInfo, ParseError> {
    let mut global_info = GlobalInfo::new();
    let mut function_signatures = HashMap::new();
    let mut init_struct_signatures = HashMap::new();
    let mut idx = 0;
    loop {
        match tokens.peek_nth(idx) {
            lexer::Token::EOF => break,
            lexer::Token::Keyword(lexer::Keyword::Function) 
            | lexer::Token::Keyword(lexer::Keyword::External) => {
                let signature = extract_function_signature(tokens, idx, &mut global_info.external_names)?;
                function_signatures.insert(signature.0.clone(), signature);
            }
            lexer::Token::Keyword(lexer::Keyword::Struct) => {
                let signature = extract_struct_signature(tokens, idx)?;
                init_struct_signatures.insert(signature.0, signature.1);
            }
            _ => ()
        }
        idx += 1;
    }

    for (name, struct_) in init_struct_signatures.iter() {
        let mut fields = HashMap::new();
        let mut mem_loc = 0;
        for (field_name, field_type) in struct_ {
            let field = field_type.validate(&init_struct_signatures, &mut global_info.struct_signatures).map_err(|err| {
                ParseError::new(err.msg, tokens.get_prev_location())
            })?;
            let offset = field.get_size();
            fields.insert(field_name.clone(), (mem_loc, field));
            mem_loc += offset;
        }

        global_info.struct_signatures.insert(name.clone(), StructSignature{ name: name.clone(), fields });
    }
    for (name, function_signature) in function_signatures.into_iter() {
        let arguments = function_signature.1.into_iter().map(|initial_value| initial_value.validate(&HashMap::new(), &global_info.struct_signatures).unwrap()).collect();
        let return_type = function_signature.2.validate(&HashMap::new(), &global_info.struct_signatures).map_err(|err| ParseError::new(err.msg, tokens.get_prev_location()))?;

        global_info.function_signatures.insert(name.clone(), FunctionSignature::new(name, arguments, return_type));
    }

    Ok(global_info)
}
fn extract_function_signature(tokens: &Tokens, mut index: usize, external_names: &mut Vec<String>) -> Result<(String, Vec<InitialType>, InitialType), ParseError> {
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
                                arguments.push(InitialType::Native(*type_));
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
            let return_type = match tokens.peek_nth(index) {
                lexer::Token::Type(type_) => {
                    InitialType::Native(*type_)
                },
                lexer::Token::Identifier(name) => {
                    InitialType::UnknownStruct(name.clone())
                },
                _ => {
                    return Err(ParseError::new("Expected function return type".to_string(), tokens.get_location_nth(index)));
                }
            };
                

            Ok((name, arguments, return_type))
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
                            arguments.push(InitialType::Native(*type_));
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
            let return_type = match tokens.peek_nth(index) {
                lexer::Token::Type(type_) => {
                    InitialType::Native(*type_)
                },
                lexer::Token::Identifier(name) => {
                    InitialType::UnknownStruct(name.clone())
                },
                _ => {
                    return Err(ParseError::new("Expected external function return type".to_string(), tokens.get_location_nth(index)));
                }
            };
            external_names.push(name.clone());
            Ok((name, arguments, return_type))
        },
        _ => Err(ParseError::new("Expected function siganture".to_string(), tokens.get_location_nth(index)))
    }
}
fn extract_struct_signature(tokens: &Tokens, mut index: usize) -> Result<(String, Vec<(String, InitialType)>), ParseError> {
    match tokens.peek_nth(index) {
        lexer::Token::Keyword(lexer::Keyword::Struct) => {
            index += 1;
        },
        _ => {
            return Err(ParseError::new("Expected struct".to_string(), tokens.get_location_nth(index)));
        }
    }

    let name = if let lexer::Token::Identifier(name) = tokens.peek_nth(index) {
        index += 1;
        name.clone()
    } else {
        return Err(ParseError::new("Expected struct name".to_string(), tokens.get_location_nth(index)));
    };

    match tokens.peek_nth(index) {
        lexer::Token::SpecialSymbol(lexer::SpecialSymbol::OpenBracket)=> {
            index += 1;
        },
        _ => {
            return Err(ParseError::new("Expected open bracket".to_string(), tokens.get_location_nth(index)));
        }
    }
    let mut fields = Vec::new();

    loop {
        match tokens.peek_nth(index) {
            lexer::Token::SpecialSymbol(lexer::SpecialSymbol::CloseBracket) => {
                break
            },
            lexer::Token::Identifier(field_name) => {
                index += 1;
                match tokens.peek_nth(index) {
                    Token::Type(type_) => {
                        fields.push((field_name.clone(), InitialType::Native(*type_)));
                    },
                    Token::Identifier(struct_name) => {
                        fields.push((field_name.clone(), InitialType::UnknownStruct(struct_name.clone())));
                    }
                    _ => {
                        return Err(ParseError::new("Expected field type".to_string(), tokens.get_location_nth(index)));
                    }
                }
                index += 1;
                if let lexer::Token::SpecialSymbol(lexer::SpecialSymbol::Comma) = tokens.peek_nth(index) {
                    index += 1;
                }
            },
            _ => {
                return Err(ParseError::new("Expected field name".to_string(), tokens.get_location_nth(index)));
            }
        }
    }
    Ok((name, fields))
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
        id: Vec<String>,
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
pub enum Value{
    Native(NativeValue),
    Struct(Struct)
}
impl Value {
    pub fn get_type(&self) -> Type {
        match self {
            Value::Native(native) => Type::Native(native.get_type()),
            Value::Struct(struct_) => struct_.get_type()
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Expression {
    Value(Value),
    Variable(Vec<String>, Type),
    MathOpearation {
        lhv: Box<Expression>,
        rhv: Box<Expression>,
        operator: Operator
    },
    FunctionCall(FunctionCall, Type)
}
impl Expression {
    pub fn get_type(&self) -> Type {
        match self {
            Expression::Value(value) => value.get_type(),
            Expression::Variable(_, type_) => type_.clone(),
            Expression::MathOpearation { lhv, rhv: _, operator } => {
                let lhv_type = lhv.get_type();
                match operator {
                    Operator::Plus | Operator::Minus | Operator::Multiply | Operator::Divide => lhv_type,
                    Operator::GreaterThan | Operator::LessThan | Operator::GreaterThanOrEqual | Operator::LessThanOrEqual | Operator::Equal | Operator::NotEqual => {
                        Type::Native(NativeType::Boolean)
                    },
                }
            },
            Expression::FunctionCall(_, ret) => {
                ret.clone()
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
    use crate::lexer::{Token, NativeValue, Operator, SpecialSymbol};

    fn empty_signature() -> GlobalInfo {
        extract_global_info(&Tokens::from_vec(vec![])).unwrap()
    }
    
    #[test]
    fn test_parse_expression_valid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Value(NativeValue::Integer(5)),
            Token::Operator(Operator::Plus),
            Token::Value(NativeValue::Integer(3)),
            Token::SpecialSymbol(SpecialSymbol::CloseParen)
        ]);
        let mut variables = HashMap::new();
        let result = parse_expression(&mut tokens, &mut variables, &empty_signature());

        match result {
            Ok(expression) => {
                match expression {
                    Expression::MathOpearation { lhv, rhv, operator } => {
                        assert_eq!(*lhv, Expression::Value(Value::Native(NativeValue::Integer(5))));
                        assert_eq!(operator, Operator::Plus);
                        assert_eq!(*rhv, Expression::Value(Value::Native(NativeValue::Integer(3))));
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
            Token::Value(NativeValue::Integer(5)),
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
            Token::Value(NativeValue::Integer(5)),
            Token::SpecialSymbol(SpecialSymbol::Comma),
            Token::Value(NativeValue::Integer(10)),
            Token::SpecialSymbol(SpecialSymbol::CloseParen)
        ]);

        let global_info = extract_global_info(&Tokens::from_vec(vec![
            Token::Keyword(Keyword::Function),
            Token::Identifier("test_function".to_string()),
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Identifier("x".to_string()),
            Token::Type(NativeType::Integer),
            Token::SpecialSymbol(SpecialSymbol::Comma),
            Token::Identifier("y".to_string()),
            Token::Type(NativeType::Integer),
            Token::SpecialSymbol(SpecialSymbol::CloseParen),
            Token::Type(NativeType::Void),
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),
        ])).unwrap();

        let mut variables: HashMap<String, Type> = HashMap::new();

        let result = parse_function_call("test_function".to_string(), &mut tokens, &mut variables, &global_info);
        assert!(result.is_ok());

        let function_call = result.unwrap();
        assert_eq!(function_call.function, "test_function");
        assert_eq!(function_call.parameters.len(), 2);
    }

    #[test]
    fn test_parse_function_call_invalid() {
        let mut tokens = Tokens::from_vec(vec![
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Value(NativeValue::Integer(5)),
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
        variables.insert("variable".to_string(), Type::Native(NativeType::Integer));

        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Return),
            Token::Identifier("variable".to_string()),
            Token::SpecialSymbol(SpecialSymbol::Terminator),
        ]);

        variables.insert("variable".to_string(), Type::Native(NativeType::Integer));

        let result = parse_instruction(&mut tokens, &mut variables, &empty_signature(), &Type::Native(NativeType::Integer));
        assert!(result.is_ok());
        let instruction = result.unwrap();

        match instruction {
            Instruction::Return(Expression::Variable(var, type_)) => {
                assert_eq!(var, vec!["variable"]); 
                assert_eq!(type_, Type::Native(NativeType::Integer));
            },
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

        let result = parse_instruction(&mut tokens, &mut variables, &empty_signature(), &Type::Native(NativeType::Void));
        assert!(result.is_err());
        }

    #[test]
    fn test_parse_closure_valid() {
        let return_type = Type::Native(NativeType::Integer);
        let mut variables = vec![
            ("param1".to_string(), Type::Native(NativeType::Integer)),
            ("param2".to_string(), Type::Native(NativeType::Float)),
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
        assert_eq!(closure.return_type, Type::Native(NativeType::Integer));
        assert_eq!(closure.instructions.len(), 1);
        match &closure.instructions[0] {
            Instruction::Return(Expression::Variable(param, type_)) => {
                assert_eq!(param, &vec!["param1".to_string()]); 
                assert_eq!(type_, &Type::Native(NativeType::Integer));
            },
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
            Token::Type(NativeType::Integer),
            Token::SpecialSymbol(SpecialSymbol::Comma),
            Token::Identifier("y".to_string()),
            Token::Type(NativeType::Integer),
            Token::SpecialSymbol(SpecialSymbol::CloseParen),
            Token::Type(NativeType::Void),
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),
        ]);

        let result = parse_function(&mut tokens, &empty_signature());
        assert!(result.is_ok());

        let function = result.unwrap();
        assert_eq!(function.name, "test_func");
        assert_eq!(function.arguments, vec![("x".to_string(), Type::Native(NativeType::Integer)), ("y".to_string(), Type::Native(NativeType::Integer))]);
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
    fn test_generate_function_signatures() {
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Function),
            Token::Identifier("func1".to_string()),
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Identifier("x".to_string()),
            Token::Type(NativeType::Integer),
            Token::SpecialSymbol(SpecialSymbol::CloseParen),
            Token::Type(NativeType::Void),
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket),
            Token::Keyword(Keyword::External),
            Token::Identifier("func2".to_string()),
            Token::SpecialSymbol(SpecialSymbol::OpenParen),
            Token::Type(NativeType::Float),
            Token::SpecialSymbol(SpecialSymbol::CloseParen),
            Token::Type(NativeType::Void),
            Token::SpecialSymbol(SpecialSymbol::Terminator),
        ]);

        let result = extract_global_info(&mut tokens);
        assert!(result.is_ok());

        let signatures = result.unwrap();
        assert_eq!(signatures.function_signatures.len(), 2);
        assert!(signatures.get_function_signature("func1").is_some());
        assert_eq!(signatures.get_function_signature("func1").unwrap().arguments, vec![Type::Native(NativeType::Integer)]);
        assert!(signatures.get_function_signature("func2").is_some());
        assert_eq!(signatures.get_function_signature("func2").unwrap().arguments, vec![Type::Native(NativeType::Float)]);
    }

    #[test]
    fn test_extract_structs() {
        // Create a mock Tokens object with relevant tokens representing a struct
        let mut tokens = Tokens::from_vec(vec![
            Token::Keyword(Keyword::Struct),
            Token::Identifier("TestStruct".to_string()),
            Token::SpecialSymbol(SpecialSymbol::OpenBracket),
            Token::Identifier("field1".to_string()),
            Token::Type(NativeType::Integer),
            Token::SpecialSymbol(SpecialSymbol::Comma),
            Token::Identifier("field2".to_string()),
            Token::Type(NativeType::Float),
            Token::SpecialSymbol(SpecialSymbol::CloseBracket)
        ]);

        // Parse the structs
        let result = extract_global_info(&mut tokens);
        
        // Check if result is okay
        assert!(result.is_ok());

        // Get the parsed structs
        let structs = result.unwrap().struct_signatures;

        // Check if the struct count is correct
        assert_eq!(structs.len(), 1);

        // Check if the struct name is correct
        assert_eq!(structs.get("TestStruct").unwrap().name, "TestStruct");

        // Check if the struct fields are correct
        assert_eq!(structs.get("TestStruct").unwrap().fields, vec![
            ("field1".to_string(), (0, Type::Native(NativeType::Integer))),
            ("field2".to_string(), (8, Type::Native(NativeType::Float))),
        ].into_iter().collect());
    }
}