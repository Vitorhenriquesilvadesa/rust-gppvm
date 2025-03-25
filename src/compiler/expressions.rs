use std::{ fmt::{ self, Display }, rc::Rc };

use super::lexer::Token;

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Literal(Token),
    Unary(Token, Rc<Expression>),
    Arithmetic(Rc<Expression>, Token, Rc<Expression>),
    Logical(Rc<Expression>, Token, Rc<Expression>),
    Ternary(Rc<Expression>, Rc<Expression>, Rc<Expression>),
    Assign(Token, Rc<Expression>),
    Lambda,
    Get(Rc<Expression>, Token),
    Variable(Token),
    Set(Rc<Expression>, Token, Rc<Expression>),
    Call(Rc<Expression>, Token, Vec<Expression>),
    Tuple(Vec<Rc<Expression>>),
    List(Vec<Rc<Expression>>),
    TypeComposition(Vec<Token>),
    Attribute(Token, Vec<Rc<Expression>>),
    Group(Rc<Expression>),
    Void,
}

impl Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Literal(token) => write!(f, "{}", token),
            Expression::Unary(op, expr) => write!(f, "({} {})", op, expr),
            Expression::Arithmetic(left, op, right) => write!(f, "({} {} {})", left, op, right),
            Expression::Logical(left, op, right) => write!(f, "({} {} {})", left, op, right),
            Expression::Ternary(cond, then_expr, else_expr) => {
                write!(f, "Ternary({} ? {} : {})", cond, then_expr, else_expr)
            }
            Expression::Assign(var, expr) => write!(f, "({} = {})", var, expr),
            Expression::Lambda => write!(f, "(lambda)"),
            Expression::Get(object, field) => write!(f, "Get({}.{})", object, field),
            Expression::Set(object, field, value) => {
                write!(f, "Set({}.{} = {})", object, field, value)
            }
            Expression::Variable(name) => write!(f, "Variable({})", name),
            Expression::Call(callee, _, args) => write!(f, "Call({:?}, {:?})", callee, args),
            Expression::Tuple(values) => write!(f, "Tuple({:?})", values),
            Expression::List(values) => write!(f, "List({:?})", values),
            Expression::Group(expr) => write!(f, "Group({:?})", expr),
            Expression::Attribute(name, args) => write!(f, "Attribute({:?}, {:?})", name, args),
            Expression::Void => write!(f, "Void()"),
            Expression::TypeComposition(tokens) => write!(f, "TypeComposition"),
        }
    }
}
