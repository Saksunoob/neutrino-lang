use std::{cmp::{max, min}, collections::HashMap, process::exit};

use crate::parser::{Closure, Expression, FunctionCall, Instruction, SyntaxTree};

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
}
impl Variables {
    pub fn new() -> Self {
        Variables { scopes: Vec::new(), stack_pointer: 0 }
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
}

pub fn generate(syntax_tree: SyntaxTree) -> String {
    let mut asm = ASM::new();
    
    for external in syntax_tree.externs {
        asm.externs.push(external);
    }

    for function in syntax_tree.functions {
        asm.new_function(&function.name);

        let mut variables = Variables::new();

        generate_closure(&mut asm, function.closure, &mut variables);
    }

    asm.build()
}

fn generate_closure(asm: &mut ASM, closure: Closure, variables: &mut Variables) {
    variables.new_scope();
    for i in max(5, closure.parameters.len())..5 {
        variables.new_variable(&closure.parameters[i].0);
    }
    for i in 0..min(closure.parameters.len(), 4) {
        match i {
            0 => asm.push_instr("PUSH RCX"),
            1 => asm.push_instr("PUSH RDX"),
            2 => asm.push_instr("PUSH R8"),
            3 => asm.push_instr("PUSH R9"),
            _ => panic!("Invalid index") // Should never run as usize is >= 0 and we have constrained it to be <= 4
        }
        variables.new_variable(&closure.parameters[i].0);
    }
    

    for instruction in closure.instructions {
        generate_instruction(asm, instruction, variables)
    }
    variables.close_scope(asm);
}

fn generate_instruction(asm: &mut ASM, instruction: Instruction, variables: &mut Variables) {
    match instruction {
        Instruction::Assignment { id, value } => {
            generate_expression(asm, value, variables);
            asm.push_instr(format!("PUSH RAX"));
            variables.new_variable(&id);
        },
        Instruction::Return(expr) => {
            generate_expression(asm, expr, variables);
            asm.push_instr(format!("ADD RSP, {}", variables.stack_pointer*8));
            asm.push_instr("POP RBX");
            asm.push_instr("ADD RSP, 32");
            asm.push_instr("PUSH RBX");
            asm.push_instr("RET");
        },
        Instruction::FunctionCall(call) => {
            generate_function_call(asm, call, variables)
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
        Expression::Closure(closure) => generate_closure(asm, closure, variables),
        Expression::FunctionCall(call) => {
            generate_function_call(asm, call, variables)
        },
    }
}

fn generate_function_call(asm: &mut ASM, call: FunctionCall, variables: &mut Variables) {
    // All function calls follow the Windows calling convention for x86 (https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention)

    let params_in_regs = min(call.parameters.len(), 4);

    for param in call.parameters.into_iter().rev() {
        generate_expression(asm, param, variables);
        asm.push_instr("PUSH RAX");
        variables.push();
    }
    for i in 0..params_in_regs {
        match i {
            0 => asm.push_instr("POP RCX"),
            1 => asm.push_instr("POP RDX"),
            2 => asm.push_instr("POP R8"),
            3 => asm.push_instr("POP R9"),
            _ => panic!("Invalid index") // Should never run as usize is >= 0 and we have constrained it to be <= 4
        }
        variables.pop();
    }
    asm.push_instr("SUB RSP, 32");
    asm.push_instr(format!("CALL {}", call.function));
}