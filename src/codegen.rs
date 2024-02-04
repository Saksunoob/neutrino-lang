use std::{cmp::min, collections::HashMap, process::exit};

use crate::{lexer::Type, parser::{Closure, Expression, FunctionCall, Instruction, SyntaxTree}};

struct ASM {
    externs: Vec<String>,
    functions: Vec<(String, Vec<String>)>
}
impl ASM {
    pub fn new() -> Self {
        Self {
            externs: Vec::new(),
            functions: Vec::new(),
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

        for function in &self.functions {
            out += &format!("global {}\n", function.0);
            out += &format!("{}:\n", function.0);

            for instruction in &function.1 {
                out += &format!("\t{}\n", instruction);
            }
        }

        out
    }
    pub fn new_function(&mut self, name: &String) {
        self.functions.push((name.to_string(), Vec::new()))
    }
    pub fn push_instr(&mut self, instr: impl ToString) {
        self.functions.last_mut().unwrap().1.push(instr.to_string())
    }
}

struct Variables {
    scopes: Vec<HashMap<String, usize>>,
    stack_pointer: usize,
    function_arguments: usize
}
impl Variables {
    pub fn new(input_parameters: Vec<(String, Type)>, asm: &mut ASM) -> Self {
        let function_arguments = if input_parameters.len() > 4 {input_parameters.len()-4} else {0};
        let mut call_scope = HashMap::new();

        let mut stack_pointer = 0;

        for i in (4..input_parameters.len()).rev() {
            stack_pointer += 1;
            call_scope.insert(input_parameters[i].0.clone(), stack_pointer);
        }

        asm.push_instr("POP RAX"); // Pop return address
        asm.push_instr("ADD RSP, 32"); // Remove padding by Windows call convention
        asm.push_instr("PUSH RAX"); // Push return address

        stack_pointer += 1; // Account for return address

        let mut param_scope = HashMap::new();

        for i in 0..min(input_parameters.len(), 4) {
            match i {
                0 => asm.push_instr("PUSH RCX"),
                1 => asm.push_instr("PUSH RDX"),
                2 => asm.push_instr("PUSH R8"),
                3 => asm.push_instr("PUSH R9"),
                _ => panic!("Invalid index") // Should never run as usize is >= 0 and we have constrained it to be <= 4
            }
            stack_pointer += 1;
            param_scope.insert(input_parameters[i].0.clone(), stack_pointer);
        }
        Variables { scopes: vec![call_scope, param_scope], stack_pointer, function_arguments }
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
    pub fn close_scopes_to(&mut self, depth: usize, asm: &mut ASM) {
        let scopes = self.scopes.drain(depth..);
        let variable_amount: usize = scopes.map(|scope| scope.len()).sum();
        self.stack_pointer -= variable_amount;
        asm.push_instr(format!("ADD RSP, {}", variable_amount*8));
    }
}

pub fn generate(syntax_tree: SyntaxTree) -> String {
    let mut asm = ASM::new();
    
    for external in syntax_tree.externs {
        asm.externs.push(external);
    }

    for function in syntax_tree.functions {
        asm.new_function(&function.name);

        generate_function(&mut asm, function.closure);
    }

    asm.build()
}

fn generate_function(asm: &mut ASM, closure: Closure) {

    let mut variables = Variables::new(closure.parameters, asm);

    variables.new_scope();
    
    // Generate instructions
    for instruction in closure.instructions {
        generate_instruction(asm, instruction, &mut variables)
    }
    variables.close_scope(asm);
}

fn generate_instruction(asm: &mut ASM, instruction: Instruction, variables: &mut Variables) {
    match instruction {
        Instruction::Assignment { id, value } => {
            generate_expression(asm, value, variables);
            let addr = variables.get_var_addr(&id)*8;
            asm.push_instr(format!("MOV [RSP+{addr}], RAX"));
        },
        Instruction::Return(expr) => {
            generate_expression(asm, expr, variables);
            variables.close_scopes_to(1, asm);
            asm.push_instr(format!("RET {}", variables.function_arguments*8));
        },
        Instruction::FunctionCall(call) => {
            generate_function_call(asm, call, variables)
        },
        Instruction::Decleration { id, value } => {
            generate_expression(asm, value, variables);
            asm.push_instr(format!("PUSH RAX"));
            variables.new_variable(&id);
        },
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
            }
        },
        Expression::FunctionCall(call) => {
            generate_function_call(asm, call, variables)
        },
    }
}

fn generate_function_call(asm: &mut ASM, call: FunctionCall, variables: &mut Variables) {
    // All function calls follow the Windows calling convention for x86 (https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention)
    let params = call.parameters.len();
    for param in call.parameters.into_iter().rev() {
        generate_expression(asm, param, variables);
        asm.push_instr("PUSH RAX");
        variables.push();
    }
    for i in 0..params {
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
}