use std::{collections::HashMap, process::exit};

use crate::{lexer::Type, parser::{Block, Expression, Function, FunctionCall, Instruction, SyntaxTree}};

struct ASM {
    externs: Vec<String>,
    instructions: Vec<String>,
    counter: usize
}
impl ASM {
    pub fn new() -> Self {
        Self {
            externs: Vec::new(),
            instructions: Vec::new(),
            counter: 0
        }
    }
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
    pub fn new_function(&mut self, name: &String) {
        self.instructions.push(format!("global {}", name));
        self.push_label(format!("{}", name));
    }
    pub fn push_instr(&mut self, instr: impl ToString) {
        self.instructions.push(format!("\t{}", instr.to_string()));
    }
    pub fn push_label(&mut self, label: impl ToString) {
        self.instructions.push(format!("{}:", label.to_string()));
    }
    pub fn get_counter(&mut self) -> usize {
        self.counter += 1;
        self.counter - 1
    }
}

struct Variables {
    scopes: Vec<HashMap<String, usize>>,
    stack_pointer: usize
}
impl Variables {
    pub fn new(input_parameters: Vec<(String, Type)>, asm: &mut ASM) -> Self {
        let mut call_scope = HashMap::new();

        for i in 0..input_parameters.len() {
            match i {
                0 => asm.push_instr("MOV RCX, [RSP+8]"),
                1 => asm.push_instr("MOV RDX, [RSP+16]"),
                2 => asm.push_instr("MOV R8, [RSP+24]"),
                3 => asm.push_instr("MOV R9, [RSP+32]"),
                _ => ()
            }
            call_scope.insert(input_parameters[i].0.clone(), input_parameters.len() - i);
        }

        let stack_pointer = input_parameters.len()+1; // +1 for return address

        Variables { scopes: vec![call_scope, HashMap::new()], stack_pointer }
    }
    pub fn new_scope(&mut self) {
        self.scopes.push(HashMap::new())
    }
    pub fn close_scope(&mut self, asm: &mut ASM) {
        let vars = self.scopes.pop().unwrap();
        self.stack_pointer -= vars.len();

        asm.push_instr(format!("ADD RSP, {}", vars.len()*8));
    }
    pub fn new_variable(&mut self, name: &String) {
        self.stack_pointer += 1;
        self.scopes.last_mut().unwrap().insert(name.to_string(), self.stack_pointer);
    }
    pub fn get_var_addr(&self, name: &String) -> usize {
        for scope in self.scopes.iter().rev() {
            if let Some(pointer) = scope.get(name) {
                return (self.stack_pointer-pointer)*8;
            }
        }
        eprintln!("Variable {name} not found");
        exit(1)
    }
    pub fn pop(&mut self) {
        let last = self.scopes.last_mut().unwrap();

        let var = last.iter().find(|(_, pointer)| **pointer == self.stack_pointer);
        if var.is_some() {
            let var = var.unwrap().0.clone();
            last.remove(&var);
        }

        self.stack_pointer -= 1;
    }
    pub fn push(&mut self) {
        self.stack_pointer += 1;
    }
    pub fn get_return_stack_add(&mut self) -> usize {
        let scopes = &self.scopes[1..];
        let variable_amount: usize = scopes.iter().map(|scope| scope.len()).sum();
        variable_amount*8
    }
}

pub fn generate(syntax_tree: SyntaxTree) -> String {
    let mut asm = ASM::new();
    
    for external in syntax_tree.externs {
        asm.externs.push(external);
    }

    for function in syntax_tree.functions {
        generate_function(&mut asm, function);
    }

    asm.build()
}

fn generate_function(asm: &mut ASM, function: Function) {
    asm.new_function(&function.name);

    let mut variables = Variables::new(function.arguments, asm);

    generate_block(asm, function.block, &mut variables);
}

fn generate_block(asm: &mut ASM, block: Block, variables: &mut Variables) {
    variables.new_scope();
    // Generate instructions
    for instruction in block.instructions {
        generate_instruction(asm, instruction, variables)
    }
    variables.close_scope(asm);
}

fn generate_instruction(asm: &mut ASM, instruction: Instruction, variables: &mut Variables) {
    match instruction {
        Instruction::Assignment { id, value } => {
            generate_expression(asm, value, variables);
            let addr = variables.get_var_addr(&id);
            asm.push_instr(format!("MOV [RSP+{addr}], RAX"));
        },
        Instruction::Return(expr) => {
            generate_expression(asm, expr, variables);
            let return_stack_add = variables.get_return_stack_add();
            asm.push_instr(format!("ADD RSP, {}", return_stack_add));
            asm.push_instr("RET 32");
        },
        Instruction::FunctionCall(call) => {
            generate_function_call(asm, call, variables)
        },
        Instruction::Decleration { id, value } => {
            generate_expression(asm, value, variables);
            asm.push_instr(format!("PUSH RAX"));
            variables.new_variable(&id);
        },
        Instruction::If { condition, block } => generate_if(asm, variables, condition, block),
        Instruction::While { condition, block } => generate_while(asm, variables, condition, block),
    }
}

fn generate_expression(asm: &mut ASM, expression: Expression, variables: &mut Variables) {
    match expression {
        Expression::Value(value) => {
            match value {
                crate::lexer::Value::Integer(i) => {
                    asm.push_instr(format!("MOV RAX, {i}"));
                },
                crate::lexer::Value::Boolean(b) => {
                    asm.push_instr(format!("MOV RAX, {}", b as i32));
                },
                crate::lexer::Value::Float(_) => todo!(),
                crate::lexer::Value::Void => (),
            }
        },
        Expression::Variable(var) => {
            asm.push_instr(format!("MOV RAX, [RSP+{}]", variables.get_var_addr(&var)));
        },
        Expression::MathOpearation { lhv, rhv, operator } => {
            generate_expression(asm, *rhv, variables);
            asm.push_instr("PUSH RAX");
            variables.push();
            
            generate_expression(asm, *lhv, variables);
            asm.push_instr("POP RBX");
            variables.pop();

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
        Expression::FunctionCall(call) => {
            generate_function_call(asm, call, variables)
        },
    }
}

fn generate_if(asm: &mut ASM, variables: &mut Variables, condition: Expression, block: Block) {
    generate_expression(asm, condition, variables);
    let counter = asm.get_counter();

    asm.push_instr("CMP RAX, 0");
    asm.push_instr(format!("JNE if_{counter}"));
    asm.push_instr(format!("JMP end_{counter}"));
    asm.push_label(format!("if_{counter}"));
    generate_block(asm, block, variables);
    asm.push_instr(format!("JMP end_{counter}"));
    asm.push_label(format!("end_{counter}"));
}

fn generate_while(asm: &mut ASM, variables: &mut Variables, condition: Expression, block: Block) {
    let counter = asm.get_counter();

    asm.push_label(format!("eval_{counter}"));
    generate_expression(asm, condition, variables); 
    asm.push_instr("CMP RAX, 0");
    asm.push_instr(format!("JNE while_{counter}"));
    asm.push_instr(format!("JMP end_{counter}"));
    asm.push_label(format!("while_{counter}"));
    generate_block(asm, block, variables);
    asm.push_instr(format!("JMP eval_{counter}"));
    asm.push_label(format!("end_{counter}"));

}

fn generate_function_call(asm: &mut ASM, call: FunctionCall, variables: &mut Variables) {
    // All function calls follow the Windows calling convention for x86 (https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention)
    let params = call.parameters.len();
    for param in call.parameters.into_iter().rev() {
        generate_expression(asm, param, variables);
        asm.push_instr("PUSH RAX");
        variables.push();
    }
    for i in 0..params { // Move first four arguments to registers
        match i {
            0 => asm.push_instr("POP RCX"),
            1 => asm.push_instr("POP RDX"),
            2 => asm.push_instr("POP R8"),
            3 => asm.push_instr("POP R9"),
            _ => ()
        }
        variables.pop();
    }
    asm.push_instr("SUB RSP, 32");
    asm.push_instr(format!("CALL {}", call.function));
    asm.push_instr(format!("ADD RSP, {}", params.min(4)*8));
}