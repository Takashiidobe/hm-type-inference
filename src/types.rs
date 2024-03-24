use std::fmt;
use std::ops::Add;

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Op {
    Add,
    Sub,
    Less,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Op::Add => "+",
                Op::Sub => "-",
                Op::Less => "<",
            }
        )
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Type {
    Number,
    String,
    Bool,
    Function(FunType),
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct FunType {
    pub input: Box<Type>,
    pub output: Box<Type>,
}

impl FunType {
    pub fn new(input: Type, output: Type) -> Self {
        Self {
            input: Box::new(input),
            output: Box::new(output),
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Expr {
    Number(i64),
    Bool(bool),
    Variable(char),
    Binary(BinExpr),
    Conditional(IfExpr),
    Function(FunExpr),
    Call(CallExpr),
}

impl From<i64> for Expr {
    fn from(num: i64) -> Self {
        Expr::Number(num)
    }
}

impl From<bool> for Expr {
    fn from(value: bool) -> Self {
        Expr::Bool(value)
    }
}

impl Add for Expr {
    type Output = Expr;

    fn add(self, other: Self) -> Self::Output {
        Expr::Binary(BinExpr::new(self, Op::Add, other))
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Number(n) => write!(f, "{n}"),
            Expr::Binary(e) => write!(f, "{e}"),
            Expr::Function(e) => write!(f, "{e}"),
            Expr::Call(e) => write!(f, "{e}"),
            Expr::Variable(c) => write!(f, "{c}"),
            Expr::Conditional(e) => write!(f, "{e}"),
            Expr::Bool(b) => write!(f, "{b}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct BinExpr {
    pub left: Box<Expr>,
    pub op: Op,
    pub right: Box<Expr>,
}

impl fmt::Display for BinExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, self.op, self.right)
    }
}

impl BinExpr {
    pub fn new(left: Expr, op: Op, right: Expr) -> Self {
        Self {
            left: Box::new(left),
            op,
            right: Box::new(right),
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct IfExpr {
    pub condition: Box<Expr>,
    pub then: Box<Expr>,
    pub r#else: Box<Expr>,
}

impl IfExpr {
    pub fn new(cond: Expr, then: Expr, r#else: Expr) -> Self {
        Self {
            condition: Box::new(cond),
            then: Box::new(then),
            r#else: Box::new(r#else),
        }
    }
}

impl fmt::Display for IfExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "if {} {{{}}} else {{{}}}",
            self.condition, self.then, self.r#else
        )
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct FunExpr {
    pub argument: Box<Expr>,
    pub arg_type: Type,
    pub body: Box<Expr>,
}

impl FunExpr {
    pub fn new(argument: Expr, arg_type: Type, body: Expr) -> Self {
        Self {
            argument: Box::new(argument),
            arg_type,
            body: Box::new(body),
        }
    }
}

impl fmt::Display for FunExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(lambda({}) {})", self.argument, self.body)
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct CallExpr {
    pub caller: Box<Expr>,
    pub callee: Box<Expr>,
}

impl fmt::Display for CallExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Call<{}({})>", self.caller, self.callee)
    }
}

impl CallExpr {
    pub fn new(ler: Expr, lee: Expr) -> Self {
        Self {
            caller: Box::new(ler),
            callee: Box::new(lee),
        }
    }
}
