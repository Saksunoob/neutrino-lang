use std::{collections::HashMap, fmt::{format, Display}};

use crate::{lexer::NativeType, parser::{Block, Expression, Function, FunctionCall, Instruction, SyntaxTree, Type}};

struct ASM {
    externs: Vec<String>,
    instructions: Vec<String>,
    counter: usize
}
impl ASM {
    /// Creates an empty ASM program
    pub fn new() -> Self {
        Self {
            externs: Vec::new(),
            instructions: Vec::new(),
            counter: 0
        }
    }

    /// Builds the ASM program into a string
    pub fn build(&self) -> String {
        let mut out = String::new();

        out += "bits 64\n";
        out += "default rel\n";

        for import in &self.externs {
            out += &format!("extern {import}\n");
        }
        out += "section .text\n";

        out += &self.instructions.join("\n");

        out
    }
    /// Adds a new external function to the ASM program
    pub fn new_extern(&mut self, name: impl Display) {
        self.externs.push(format!("{}", name));
    }
    /// Adds a new function to the ASM program by pushing a new label and a global declaration
    pub fn new_function(&mut self, name: impl Display) {
        self.instructions.push(format!("global {}", name));
        self.push_label(format!("{}", name));
    }
    /// Pushes an instruction to the ASM program
    pub fn push_instr(&mut self, instr: impl ToString) {
        self.instructions.push(format!("\t{}", instr.to_string()));
    }
    /// Pushes a comment to the ASM program
    pub fn push_comment(&mut self, comment: impl ToString) {
        self.instructions.push(format!("\t; {}", comment.to_string()));
    }
    /// Pushes a label to the ASM program
    pub fn push_label(&mut self, label: impl ToString) {
        self.instructions.push(format!("{}:", label.to_string()));
    }
    /// Returns a global counter for unique labels and increments it
    pub fn get_counter(&mut self) -> usize {
        self.counter += 1;
        self.counter - 1
    }
}

#[derive(Clone, Debug)]
struct Variable {
    pointer: usize,
    var_type: Type
}
impl Variable {
    pub fn new(pointer: usize, var_type: Type) -> Self {
        Self { pointer, var_type }
    }
    pub fn get_field(&self, field_path: &[String]) -> Variable {
        match &self.var_type {
            Type::Struct(name) => {
                let pointer = self.pointer-name.get_offset(field_path);
                let var_type = name.get_type(field_path);
                Variable::new(pointer, var_type)
            },
            Type::Native(type_) => {
                if field_path.len() == 0 {
                    return self.clone();
                }

                panic!("Cannot get field {:?} of native type {:?}", field_path, self.var_type)
            }
        }
    }
}

struct Scope {
    variables: HashMap<String, Variable>,
    stack_base: usize
}
impl Scope {
    pub fn new(stack_base: usize) -> Self {
        Self { variables: HashMap::new(), stack_base }
    }
}

struct Variables {
    scopes: Vec<Scope>,
    stack_pointer: usize
}
impl Variables {
    /// Creates a new set of variables for the given input parameters
    pub fn new(input_parameters: &Vec<(String, Type)>, asm: &mut ASM) -> Self {
        let mut variables = Variables {
            scopes: Vec::new(),
            stack_pointer: 40
        };

        // Add a new scope for the input parameters
        variables.new_scope();

        // Add the input parameters to the new scope
        for i in (0..input_parameters.len()).rev() {
            // First four arguments are passed in registers
            if i < 4 {
                let reg = match i {
                    0 => "RCX",
                    1 => "RDX",
                    2 => "R8",
                    3 => "R9",
                    _ => unreachable!(),
                };
                // Move the input parameter to the stack
                asm.push_instr(format!("MOV [RSP+{}], {reg}", i*8+8));
                variables.reg_variable(&input_parameters[i].0, &input_parameters[i].1);
            }
            else {
                variables.new_variable(&input_parameters[i].0, &input_parameters[i].1);
            }
        }

        // Add a new scope for the local variables
        variables.new_scope();

        return variables
    }

    /// Opens a new scope
    pub fn new_scope(&mut self) {
        self.scopes.push(Scope::new(self.stack_pointer))
    }

    /// Closes the current scope and moves the stack pointer back to the base of the scope
    pub fn close_scope(&mut self, asm: &mut ASM) {
        let scope = self.scopes.pop().unwrap();
        asm.push_instr(format!("ADD RSP, {}", self.stack_pointer-scope.stack_base));
        self.stack_pointer = scope.stack_base;
    }

    /// Pushes a new variable to the current scope and moves the compiler stack pointer.
    /// Panics if the size of the variable is larger than 8 bytes
    pub fn push_reg(&mut self, reg: &str, size: usize, asm: &mut ASM) {

        // Registers can't hold more than 8 bytes. So if we are trying to do this, the problem is somewhere else
        if size > 8 {
            panic!("Cannot push variable of size {size}");
        }

        if size == 8 {
            asm.push_instr(format!("PUSH {reg}"));
        } else {
            asm.push_instr(format!("SUB RSP, {size}"));
            let size_id = match size {
                1 => "BYTE",
                2 => "WORD",
                4 => "DWORD",
                _ => unreachable!(),
            };
            asm.push_instr(format!("MOV [RSP], {size_id} {reg}"));
        }
        self.stack_pointer += size;
    }

    /// Pushes a new variable from reg to the current scope and moves the compiler stack pointer
    pub fn push_variable(&mut self, name: &String, reg: &str, var_type: &Type, asm: &mut ASM) {
        self.push_reg(reg, var_type.get_size(), asm);
        self.reg_variable(name, var_type);
    }

    /// Adds a new variable to the current scope and moves the compiler stack pointer
    pub fn new_variable(&mut self, name: &String, var_type: &Type) {
        self.stack_pointer += var_type.get_size();
        self.reg_variable(name, var_type);
    }

    /// Registers a new variable to the current scope at the top of the stack
    /// Doesn't modify the stack pointer
    pub fn reg_variable(&mut self, name: &String, var_type: &Type) {
        self.scopes.last_mut().unwrap().variables.insert(name.to_string(), Variable::new(self.stack_pointer, var_type.clone()));
    }

    /// Returns the address of the variable relative to the stack pointer
    /// Panics if the variable is not found or variables doesn't have any scopes
    pub fn get_rel_var_addr(&self, name: &String) -> usize {
        let var = self.scopes.last().unwrap().variables.get(name).unwrap();
        self.stack_pointer - var.pointer
    }

    /// Return the stack size above the return address
    pub fn get_return_stack_add(&mut self) -> usize {
        self.stack_pointer - self.scopes[1].stack_base
    }

    /// Pops a value from the stack to the specified register
    pub fn pop_to_reg(&mut self, reg: &str, type_: &Type, asm: &mut ASM) {
        let size = type_.get_size();

        // Registers can't hold more than 8 bytes. So if we are trying to do this, the problem is somewhere else
        if size > 8 {
            panic!("Cannot pop variable of size {size}");
        }

        if size == 8 {
            asm.push_instr(format!("POP {reg}"));
        } else {
            // If the size is not 8, the value must be popped manually
            let size_id = match size {
                1 => "BYTE",
                2 => "WORD",
                4 => "DWORD",
                _ => unreachable!(),
            };
            asm.push_instr(format!("MOVZX {reg}, {size_id} [RSP]"));
            asm.push_instr(format!("ADD RSP, {size}"));
        }
        self.stack_pointer -= size;
    }

    /// Loads a value from a stack address to the specified register.
    pub fn load_addr_to_reg(&mut self, addr: usize, reg: &str, size: usize, asm: &mut ASM) {

        // Registers can't hold more than 8 bytes. So if we are trying to do this, the problem is somewhere else
        if size > 8 {
            panic!("Cannot load variable of size {size}");
        }

        if size == 8 {
            asm.push_instr(format!("MOV {reg}, [RSP+{addr}]"));
        } else {
            let size_id = match size {
                1 => "BYTE",
                2 => "WORD",
                4 => "DWORD",
                _ => unreachable!(),
            };
            asm.push_instr(format!("MOVZX {reg}, {size_id} [RSP+{addr}]"));
        }
    }

    /// Returns variable information.
    /// Panics if the variable is not found
    pub fn get_variable(&self, name: &String) -> &Variable {
        for scope in self.scopes.iter().rev() {
            if let Some(variable) = scope.variables.get(name) {
                return variable;
            }
        }
        panic!("Variable {name} not found")
    }
}

/// Generates the ASM program from the syntax tree.
/// Does not check if the syntax tree is valid
/// Panics or generates invalid code if the syntax tree is invalid
pub fn generate(syntax_tree: SyntaxTree) -> String {
    let mut asm = ASM::new();

    // Generate externs
    syntax_tree.externs.into_iter().for_each(|external| asm.new_extern(external));

    // Generate functions
    syntax_tree.functions.into_iter().for_each(|function| {
        generate_function(&mut asm, &function);
    });

    asm.build()
}

/// Generates the ASM program of a function
fn generate_function(asm: &mut ASM, function: &Function) {
    asm.new_function(&function.name);
    let mut function_variables = Variables::new(&function.arguments, asm);

    generate_block(asm, &function.block, &mut function_variables);
}

/// Generates the ASM program of a block of instructions
fn generate_block(asm: &mut ASM, block: &Block, variables: &mut Variables) {
    variables.new_scope();

    for instruction in &block.instructions {
        generate_instruction(asm, instruction, variables);
    }

    variables.close_scope(asm);
}

/// Generates the ASM program of an instruction
fn generate_instruction(asm: &mut ASM, instruction: &Instruction, variables: &mut Variables) {
    match instruction {
        Instruction::Decleration { id, value } => {
            generate_expression(asm, value, variables);
            let value_type = value.get_type();
            match value_type {
                Type::Native(_) => {
                    variables.push_variable(&id, "RAX", &value_type, asm);
                },
                Type::Struct(_) => {
                    variables.reg_variable(&id, &value_type)
                }
            }
        },
        Instruction::Assignment { id, value } => {
            generate_expression(asm, value, variables);
            match value.get_type() {
                Type::Native(_) => {
                    let parent = variables.get_variable(&id[0]);
                    let field = parent.get_field(&id[1..]);
                    let addr = field.pointer;
                    asm.push_instr(format!("MOV [RSP+{addr}], RAX"));
                },
                Type::Struct(_) => {
                    unimplemented!()
                }
            }
        },
        Instruction::Return(return_value) => {
            generate_expression(asm, return_value, variables);
            let return_stack_add = variables.get_return_stack_add();
            asm.push_instr(format!("ADD RSP, {}", return_stack_add));
            asm.push_instr("RET 32");
        },
        Instruction::FunctionCall(_) => todo!(),
        Instruction::If { condition, block } => todo!(),
        Instruction::While { condition, block } => todo!(),
    }
}

/// Generates the ASM program of an expression.
/// Leaves the result in RAX
fn generate_expression(asm: &mut ASM, expression: &Expression, variables: &mut Variables) {
    match expression {
        Expression::Pointer(id, inner_type) => {

            let pointer_addr = variables.get_rel_var_addr(&id[0]);

            let offset = match inner_type {
                Type::Native(_) => 0,
                Type::Struct(signature) => signature.get_offset(&id[1..]),
            };

            variables.load_addr_to_reg(pointer_addr+offset, "RAX", 8, asm);
        },
        Expression::Value(value) => {
            match value {
                crate::parser::Value::Native(native_value) => {
                    match native_value {
                        crate::lexer::NativeValue::Void => asm.push_instr("MOV RAX, 0"),
                        crate::lexer::NativeValue::Integer(i) => asm.push_instr(format!("MOV RAX, {i}")),
                        crate::lexer::NativeValue::Float(_) => todo!(),
                        crate::lexer::NativeValue::Boolean(b) => asm.push_instr(format!("MOV RAX, {}", *b as i32)),
                    }
                },
                crate::parser::Value::Struct(struct_value) => {
                    for value in struct_value.field_values.iter().rev() {
                        generate_expression(asm, value, variables);
                        match value.get_type() {
                            Type::Native(_) => variables.push_reg("RAX", value.get_type().get_size().min(8), asm),
                            Type::Struct(_) => ()
                        }
                        
                    }
                    variables.reg_variable(&struct_value.signature.name, &struct_value.get_type())
                },
            }
        },
        Expression::Variable(id, _) => {
            let var = variables.get_variable(&id[0]); // Get the parent variable
            let field = var.get_field(&id[1..]);
            let field_addr = variables.stack_pointer - field.pointer;

            variables.load_addr_to_reg(field_addr, "RAX", field.var_type.get_size(), asm);
        },
        Expression::MathOpearation { lhv, rhv, operator } => {
            generate_expression(asm, rhv, variables);
            variables.push_reg("RAX", rhv.get_type().get_size(), asm);
            
            generate_expression(asm, lhv, variables);
            variables.pop_to_reg("RBX", &rhv.get_type(), asm);

            match operator {
                crate::lexer::Operator::Plus => asm.push_instr("ADD RAX, RBX"),
                crate::lexer::Operator::Minus => asm.push_instr("SUB RAX, RBX"),
                crate::lexer::Operator::Multiply => asm.push_instr("IMUL RAX, RBX"),
                crate::lexer::Operator::Divide => {
                    asm.push_instr("MOV RDX, 0");
                    asm.push_instr("IDIV RBX")
                },
                crate::lexer::Operator::LessThan => {
                    asm.push_instr("CMP RAX, RBX");
                    asm.push_instr("SETL AL");
                    asm.push_instr("MOVZX RAX, AL");
                },
                crate::lexer::Operator::GreaterThan => {
                    asm.push_instr("CMP RAX, RBX");
                    asm.push_instr("SETG AL");
                    asm.push_instr("MOVZX RAX, AL");
                },
                crate::lexer::Operator::LessThanOrEqual => {
                    asm.push_instr("CMP RAX, RBX");
                    asm.push_instr("SETLE AL");
                    asm.push_instr("MOVZX RAX, AL");
                },
                crate::lexer::Operator::GreaterThanOrEqual => {
                    asm.push_instr("CMP RAX, RBX");
                    asm.push_instr("SETGE AL");
                    asm.push_instr("MOVZX RAX, AL");
                },
                crate::lexer::Operator::Equal => {
                    asm.push_instr("CMP RAX, RBX");
                    asm.push_instr("SETE AL");
                    asm.push_instr("MOVZX RAX, AL");
                },
                crate::lexer::Operator::NotEqual => {
                    asm.push_instr("CMP RAX, RBX");
                    asm.push_instr("SETNE AL");
                    asm.push_instr("MOVZX RAX, AL");
                },
            }
        },
        Expression::FunctionCall(_, _) => todo!(),
    }
}