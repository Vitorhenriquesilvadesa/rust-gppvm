# GPPVM Script Gramar

## Keywords

```
<import> ::= 'import' <identifier>
<variable_decl> ::= 'let' <identifier> ('=' <expression>)? ';'
<for_each> ::= 'for' <identifier> 'in' <expression> <scope>
<while> ::= 'while' <expression> <scope>
<if_stmt> ::= 'if' <expression> <scope> ('else' <scope>)?
<expr_statement> ::= <expression> ';'
<scope> ::= '{' <declaration>* '}'

<expression> ::= <assignment>
<assignment> ::= <ternary> ('=' <assignment>)?
<ternary> ::= <or> 'if' <expression> 'else' <expression>
<or> ::= <and> ('or' <and>)*
<and> ::= <equality> ('and' <equality>)*
<equality> ::= <comparison> (('==' | '!=') <comparison>)*
<comparison> ::= <term> (('>' | '<' | '>=' | '<=') <term>)?
<term> ::= <factor> (('+' | '-') <term>)*
<factor> ::= <unary> (('*' | '/') <factor>)*
<unary> ::= (('-' | '!') <unary>) | <call>
<call> ::= (<literal> '(' <arguments> ')') | <literal>
<arguments> ::= (<expr> (','<expr>)*) | λ
<literal> ::= <int> | <float> | <boolean> | <string> | <group> | <list> | <tuple> | <identifier>

<int> ::= [0-9]+
<float> ::= [0-9]+ '.' [0-9]+
<boolean> ::= 'true' | 'false'
<string> ::= '"' ([a-z] | [A-Z] | [0-9])* '"'
<group> ::= '(' <expr> ')'
<list> ::= '[' (<expr> | <expr>(',' <expr>)*) ']'
<tuple> ::='(' (<expr> | <expr>(',' <expr>)*) ')'
<identifier> ::= [a-zA-Z] ([a-zA-Z0-9] | '_')
```