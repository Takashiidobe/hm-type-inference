use crate::types::*;
use std::fmt;

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum Term {
    Expr(Expr), // variable
    Var(char),  // variable
    Num,        // constant
    Bool,
    Arrow(ArrowType), // function application
}

impl Term {
    fn is_ident(&self) -> bool {
        matches!(self, Term::Expr(_) | Term::Var(_))
    }

    pub fn make_arrow(domain: Term, range: Term) -> Self {
        Term::Arrow(ArrowType {
            domain: Box::new(domain),
            range: Box::new(range),
        })
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct ArrowType {
    domain: Box<Term>,
    range: Box<Term>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Substitution {
    var: Term,
    is: Term,
}

impl Substitution {
    pub fn new(var: Term, is: Term) -> Self {
        Self { var, is }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Constraint {
    lhs: Term,
    rhs: Term,
}

impl Constraint {
    fn new(lhs: Term, rhs: Term) -> Self {
        Constraint { lhs, rhs }
    }
}

pub fn infer_types(expr: &Expr) -> Option<Vec<Substitution>> {
    let mut constraints = generate_constraints(expr).unwrap();
    for constraint in &constraints {
        println!("Constraint: {constraint}");
    }
    unify(&mut constraints, &mut vec![])
}

fn generate_constraints(expr: &Expr) -> Option<Vec<Constraint>> {
    match expr {
        Expr::Number(_) => {
            // When the expression is a number, we expect the type
            // of the expression to be numeric:
            Some(vec![Constraint {
                lhs: Term::Expr(expr.clone()),
                rhs: Term::Num,
            }])
        }
        Expr::Variable(s) => Some(vec![Constraint {
            lhs: Term::Expr(expr.clone()),
            rhs: Term::Var(*s),
        }]),
        Expr::Bool(_) => Some(vec![Constraint {
            lhs: Term::Expr(expr.clone()),
            rhs: Term::Bool,
        }]),
        Expr::Binary(BinExpr { left, op: _, right }) => {
            // generate left constraints
            // then right constraints
            let mut left_constraints = generate_constraints(left)?;
            let right_constraints = generate_constraints(right)?;
            // then all of the other constraints
            let consequent = vec![
                Constraint::new(Term::Expr(*left.clone()), Term::Num),
                Constraint::new(Term::Expr(*right.clone()), Term::Num),
                Constraint::new(Term::Expr(expr.clone()), Term::Num),
            ];
            left_constraints.extend(right_constraints);
            left_constraints.extend(consequent);
            Some(left_constraints)
        }
        Expr::Conditional(IfExpr {
            condition,
            then,
            r#else,
        }) => {
            let mut condition_constraints = generate_constraints(condition)?;
            let then_constraints = generate_constraints(then)?;
            let else_constraints = generate_constraints(r#else)?;

            let rest = vec![
                Constraint::new(Term::Expr(*condition.clone()), Term::Bool),
                Constraint::new(Term::Expr(expr.clone()), Term::Expr(*then.clone())),
                Constraint::new(Term::Expr(expr.clone()), Term::Expr(*r#else.clone())),
            ];

            condition_constraints.extend(then_constraints);
            condition_constraints.extend(else_constraints);
            condition_constraints.extend(rest);

            Some(condition_constraints)
        }
        Expr::Function(FunExpr {
            argument,
            arg_type: _,
            body,
        }) => {
            let mut body_constraints = generate_constraints(body)?;

            let Expr::Variable(a) = **argument else {
                return None;
            };
            let consequent = Constraint {
                lhs: Term::Expr(expr.clone()),
                rhs: Term::Arrow(ArrowType {
                    domain: Box::new(Term::Var(a)),
                    range: Box::new(Term::Expr(*body.clone())),
                }),
            };
            body_constraints.push(consequent);

            Some(body_constraints)
        }
        Expr::Call(CallExpr {
            caller: function,
            callee: args,
        }) => {
            let mut fn_constraints = generate_constraints(function)?;
            let arg_constraints = generate_constraints(args)?;
            let consequent = Constraint::new(
                Term::Expr(*function.clone()),
                Term::Arrow(ArrowType {
                    domain: Box::new(Term::Expr(*args.clone())),
                    range: Box::new(Term::Expr(expr.clone())),
                }),
            );
            fn_constraints.extend(arg_constraints);
            fn_constraints.push(consequent);

            Some(fn_constraints)
        }
    }
}

fn occurs_check(left: &Term, right: &Term) -> bool {
    match left {
        Term::Arrow(ArrowType { domain, range }) => {
            occurs_check(left, domain) || occurs_check(left, range)
        }
        _ => left == right,
    }
}

fn replace(left: &Term, term: &Term, right: &Term) -> Term {
    match term {
        Term::Arrow(ArrowType { domain, range }) => Term::Arrow(ArrowType {
            domain: Box::new(replace(left, domain, right)),
            range: Box::new(replace(left, range, right)),
        }),
        _ => {
            if left == term {
                right.clone()
            } else {
                term.clone()
            }
        }
    }
}

fn replace_all(left: &Term, right: &Term, consts: &mut [Constraint], subst: &mut [Substitution]) {
    if !occurs_check(left, right) {
        for c in consts.iter_mut() {
            c.lhs = replace(left, &c.lhs, right);
            c.rhs = replace(left, &c.rhs, right);
        }

        for s in subst.iter_mut() {
            s.var = replace(left, &s.var, right);
            s.is = replace(left, &s.is, right);
        }
    } else {
        panic!("Occurs check failed.");
    }
}

fn unify(consts: &mut [Constraint], subs: &mut Vec<Substitution>) -> Option<Vec<Substitution>> {
    if consts.is_empty() {
        Some(subs.to_vec())
    } else {
        let (first, rest) = consts.split_at_mut(1);
        let first = first.first().unwrap();

        let left = first.lhs.clone();
        let right = first.rhs.clone();

        if left == right {
            unify(&mut rest.to_vec(), subs)
        } else if left.is_ident() {
            replace_all(&left, &right, rest, subs);
            subs.push(Substitution::new(left, right));
            unify(&mut rest.to_vec(), subs)
        } else if right.is_ident() {
            replace_all(&right, &left, rest, subs);
            subs.push(Substitution::new(right, left));
            unify(&mut rest.to_vec(), subs)
        } else {
            match (&left, &right) {
                (
                    Term::Arrow(ArrowType {
                        domain: d_one,
                        range: r_one,
                    }),
                    Term::Arrow(ArrowType {
                        domain: d_two,
                        range: r_two,
                    }),
                ) => {
                    let mut new_rest = rest.to_vec();
                    new_rest.extend(vec![
                        Constraint::new(*d_one.clone(), *d_two.clone()),
                        Constraint::new(*r_one.clone(), *r_two.clone()),
                    ]);
                    unify(&mut new_rest, subs)
                }
                _ => {
                    for sub in subs {
                        println!("Found: {sub}");
                    }
                    eprintln!("{left} and {right} do not unify.");
                    None
                }
            }
        }
    }
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} :: {}", self.var, self.is)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(c) => write!(f, "{c}"),
            Term::Num => write!(f, "Number"),
            Term::Bool => write!(f, "Bool"),
            Term::Arrow(a_type) => {
                write!(f, "{} -> {}", a_type.domain, a_type.range)
            }
            Term::Expr(e) => write!(f, "{e}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test(expr: &Expr, expected: &[Substitution]) -> Option<bool> {
        let output = infer_types(expr)?;
        for e in expected {
            if !output.contains(e) {
                return None;
            }
        }
        Some(true)
    }

    fn assert_some(input: Option<bool>) {
        assert!(input.is_some_and(|x| x == true));
    }

    #[test]
    fn test_number() {
        let exp = Expr::Number(1);
        let subs = Substitution::new(Term::Expr(exp.clone()), Term::Num);
        assert_some(test(&exp, &[subs]))
    }

    #[test]
    fn test_binary() {
        let exp = Expr::Number(1) + Expr::Number(2);
        let subs = [
            Substitution::new(Term::Expr(Expr::Number(1)), Term::Num),
            Substitution::new(Term::Expr(Expr::Number(2)), Term::Num),
            Substitution::new(Term::Expr(exp.clone()), Term::Num),
        ];
        assert_some(test(&exp, &subs))
    }

    #[test]
    fn test_function() {
        let l = Expr::Variable('x');
        let r = Expr::Number(2);
        let add = l.clone() + r;
        let f = Expr::Function(FunExpr {
            argument: Box::new(l), // a = x
            arg_type: Type::Number,
            body: Box::new(add.clone()), // x + 2
        });
        let subs = [
            Substitution::new(Term::Expr(Expr::Variable('x')), Term::Num),
            Substitution::new(Term::Expr(Expr::Number(2)), Term::Num),
            Substitution::new(Term::Expr(add), Term::Num),
            Substitution::new(
                Term::Expr(f.clone()),
                Term::make_arrow(Term::Num, Term::Num),
            ),
        ];
        assert_some(test(&f, &subs))
    }

    #[test]
    fn test_function_call() {
        let a = Expr::Variable('x');
        let r = Expr::Number(2);
        let l = Expr::Variable('x');
        let n = l + r;
        let f = Expr::Function(FunExpr {
            argument: Box::new(a), // a = x
            arg_type: Type::Number,
            body: Box::new(n.clone()), // x + 2
        });
        let arg1 = Expr::Number(10);
        let c1 = Expr::Call(CallExpr {
            caller: Box::new(f.clone()),
            callee: Box::new(arg1),
        }); // ((lambda(x) x + 2) (5))

        let subs = [
            Substitution::new(Term::Expr(Expr::Variable('x')), Term::Num),
            Substitution::new(Term::Expr(Expr::Number(2)), Term::Num),
            Substitution::new(Term::Expr(n), Term::Num),
            Substitution::new(Term::Expr(f), Term::make_arrow(Term::Num, Term::Num)),
            Substitution::new(Term::Expr(Expr::Number(10)), Term::Num),
            Substitution::new(Term::Expr(c1.clone()), Term::Num),
        ];
        assert_some(test(&c1, &subs))
    }

    #[test]
    fn test_function_parameters() {
        let two = Expr::Number(2);
        let five = Expr::Number(5);
        let var_x = Expr::Variable('x');

        let call_five = Expr::Call(CallExpr {
            caller: Box::new(var_x),
            callee: Box::new(five),
        }); // x(5)

        let add = call_five.clone() + two;
        let first_lambda = Expr::Function(FunExpr {
            argument: Box::new(Expr::Variable('x')),
            arg_type: Type::Number,
            body: Box::new(add.clone()),
        }); // (lambda(x) x(5) + 2)

        let add_five = Expr::Variable('y') + Expr::Number(5);
        let second_lambda = Expr::Function(FunExpr {
            argument: Box::new(Expr::Variable('y')),
            arg_type: Type::Number,
            body: Box::new(add_five.clone()),
        }); // (lambda(y) y + 5)

        let c1 = Expr::Call(CallExpr {
            caller: Box::new(first_lambda.clone()),
            callee: Box::new(second_lambda.clone()),
        }); // (lambda(x) x(5) + 2)((lambda(x) x + 5))

        let subs = [
            Substitution::new(
                Term::Expr(Expr::Variable('x')),
                Term::make_arrow(Term::Num, Term::Num),
            ),
            Substitution::new(Term::Expr(Expr::Number(5)), Term::Num),
            Substitution::new(Term::Expr(Expr::Number(2)), Term::Num),
            Substitution::new(Term::Expr(call_five), Term::Num),
            Substitution::new(Term::Expr(add), Term::Num),
            Substitution::new(
                Term::Expr(first_lambda),
                Term::make_arrow(Term::make_arrow(Term::Num, Term::Num), Term::Num),
            ),
            Substitution::new(Term::Expr(Expr::Variable('y')), Term::Num),
            Substitution::new(Term::Expr(add_five), Term::Num),
            Substitution::new(
                Term::Expr(second_lambda),
                Term::make_arrow(Term::Num, Term::Num),
            ),
            Substitution::new(Term::Expr(c1.clone()), Term::Num),
        ];
        assert_some(test(&c1, &subs))
    }

    #[test]
    fn test_incorrect_argument() {
        let two = Expr::Number(2);
        let five = Expr::Number(5);
        let var_x = Expr::Variable('x');

        let call_five = Expr::Call(CallExpr {
            caller: Box::new(var_x),
            callee: Box::new(five),
        }); // x(5)

        let add = call_five + two; // x(5) + 2

        let first_lambda = Expr::Function(FunExpr {
            argument: Box::new(Expr::Variable('x')),
            arg_type: Type::Number,
            body: Box::new(add),
        }); // (lambda(x) x(5) + 2)

        let number = Expr::Number(2);
        let c1 = Expr::Call(CallExpr {
            caller: Box::new(first_lambda),
            callee: Box::new(number),
        }); // (lambda(x) x(5) + 2)(2)

        assert_eq!(infer_types(&c1), None);
    }

    #[test]
    fn test_conditional() {
        let exp = Expr::Conditional(IfExpr::new(true.into(), 1.into(), 2.into()));
        let subs = [
            Substitution::new(Term::Expr(Expr::Bool(true)), Term::Bool),
            Substitution::new(Term::Expr(Expr::Number(1)), Term::Num),
            Substitution::new(Term::Expr(Expr::Number(2)), Term::Num),
            Substitution::new(Term::Expr(exp.clone()), Term::Num),
        ];
        assert_some(test(&exp, &subs))
    }

    #[test]
    fn test_incorrect_condition() {
        let exp = Expr::Conditional(IfExpr::new(1.into(), 1.into(), 2.into()));
        infer_types(&exp);
        assert_eq!(infer_types(&exp), None);
    }

    #[test]
    fn test_mismatched_branch_types() {
        let exp = Expr::Conditional(IfExpr::new(true.into(), false.into(), 2.into()));
        assert_eq!(infer_types(&exp), None);
    }
}
