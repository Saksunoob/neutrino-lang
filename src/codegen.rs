use std::{cmp::min, collections::HashMap, process::exit};

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

        asm.push_instr(format!("add rsp, {}", vars.len()*8));
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
    asm.externs.push("ExitProcess".to_string());

    for function in syntax_tree.functions {
        asm.new_function(&function.name);

        let mut variables = Variables::new();

        generate_closure(&mut asm, function.closure, &mut variables);
    }

    asm.build()
}

fn generate_closure(asm: &mut ASM, closure: Closure, variables: &mut Variables) {
    variables.new_scope();
    for parameter in closure.parameters {
        variables.new_variable(&parameter.0);
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
            asm.push_instr(format!("push rax"));
            variables.new_variable(&id);
        },
        Instruction::Return(expr) => {
            generate_expression(asm, expr, variables);
            // Temporary to check if the assembly is correct
            asm.push_instr("mov rcx, rax");
            asm.push_instr("call ExitProcess");
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
                    asm.push_instr(format!("mov rax, {i}"));
                },
                crate::lexer::Value::Boolean(b) => {
                    asm.push_instr(format!("mov rax, {}", b as i32));
                },
                crate::lexer::Value::Float(_) => todo!(),
            }
        },
        Expression::Variable(var) => {
            asm.push_instr(format!("mov rax, [rsp+{}]", variables.get_var_addr(&var)));
        },
        Expression::MathOpearation { lhv, rhv, operator } => {
            generate_expression(asm, *rhv, variables);
            asm.push_instr("push rax");
            variables.push();
            
            generate_expression(asm, *lhv, variables);
            asm.push_instr("pop rbx");
            variables.pop();

            match operator {
                crate::lexer::Operator::Plus => asm.push_instr("add rax, rbx"),
                crate::lexer::Operator::Minus => asm.push_instr("sub rax, rbx"),
                crate::lexer::Operator::Multiply => asm.push_instr("imul rax, rbx"),
                crate::lexer::Operator::Divide => {
                    asm.push_instr("mov rdx, 0");
                    asm.push_instr("idiv rbx")
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

    asm.push_instr("push rbp");
    asm.push_instr("mov rbp, rsp");

    for param in call.parameters.into_iter().rev() {
        generate_expression(asm, param, variables);
        asm.push_instr("push rax");
        variables.push();
    }
    for i in 0..params_in_regs {
        match i {
            0 => asm.push_instr("pop rcx"),
            1 => asm.push_instr("pop rdx"),
            2 => asm.push_instr("pop r8x"),
            3 => asm.push_instr("pop r9x"),
            _ => panic!("Invalid index") // Should never run as usize is >= 0 and we have constrained it to be <= 4
        }
        variables.pop();
    }
    asm.push_instr("sub rsp, 32");
    asm.push_instr(format!("call {}", call.function));
}