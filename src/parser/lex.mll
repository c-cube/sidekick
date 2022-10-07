

{

open Parse

}

let num = ['0' - '9']
let alpha = ['a' - 'z' 'A' - 'Z']
let alphanum = alpha | num
let alphanum_under = alpha | num | ['_']
let whitespace = [' ' '\t' '\n']
let sym = '_' | '=' | '+' | '-' | '*' | '^' | '%' | '$' | '#' | '@' | '!' | '>' | '<' | '[' | ']'

let id = (alpha | '_') alphanum_under*
let int = '-'? num+
let symbol = sym+
let hash = '#' alphanum_under+

rule token = parse
| whitespace { token lexbuf }
| ";" { SEMICOLON }
| ":" { COLON }
| "(" { LPAREN }
| ")" { RPAREN }
| ":=" { EQDEF }
| "->" { ARROW }
| "." { DOT }
| "pi" { PI }
| "fn" { FUNCTION }
| "let" { LET }
| "in" { IN }
| "and" { AND }
| "def" { DEF }
| "have" { HAVE }
| "theorem" { THEOREM }
| "by" { BY }
| "exact" { EXACT }
| "have" { HAVE }
| int { INT(Lexing.lexeme lexbuf) }
| id { ID (Lexing.lexeme lexbuf) }
| symbol { SYMBOL (Lexing.lexeme lexbuf) }
| hash { HASH (Lexing.lexeme lexbuf) }
| eof { EOF }
| _ as c { ERROR(String.make 1 c) }





