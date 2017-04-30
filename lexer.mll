{
 open Parser
 exception Eof
 exception LexicalError
 let comment_depth = ref 0
 let keyword_tbl = Hashtbl.create 31
 let _ = List.iter (fun (keyword,tok) -> Hashtbl.add keyword_tbl keyword tok)
           [
            ("skip", SKIP); 
            ("true", TRUE);
            ("false", FALSE);
            ("if", IF);
            ("then", THEN);
            ("else", ELSE); 
            ("while", WHILE);
            ("fun", FUN);
            ("return", RETURN);
            ("none", NONE);
           ]
} 

let blank = [' ' '\n' '\t' '\r']+
let id = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '\'' '0'-'9' '_']*
let number = ['0'-'9']+

rule start = parse
     | blank { start lexbuf }
     | "(*" { comment_depth :=1;
              comment lexbuf;
              start lexbuf }
     | "Examples" {EXAMPLES}
     | "Int Comps" {INTCOMPS}
     | "Int Var Comps" {INTVARCOMPS}
     | "Array Var Comps" {ARRVARCOMPS}
     | "Partial Program" {PARTIALPGM}
     | "+" {PLUS}
     | "-" {MINUS}
     | "*" {MUL}
     | "/" {DIV}
     | "%" {MOD}
     | "=" {EQUAL}
     | ">" {GT}
     | "<" {LT}
     | "==" {EQUALEQUAL}
     | "!" {NOT}
     | "&&" {AND}
     | "||" {OR}
     | "?" {HOLE}
     | "->" {MAPSTO}
     | "," {COMMA}
     | ";" {SEMICOLON}
     | "(" {LPAREN}
     | ")" {RPAREN}
     | "{" {LBRACE}
     | "}" {RBRACE}
     | "[" {LBRACKET}
     | "]" {RBRACKET}
     | id {let id = Lexing.lexeme lexbuf in
             try
               Hashtbl.find keyword_tbl id
             with _ -> VAR id 
          }
     | number {INT (int_of_string (Lexing.lexeme lexbuf))}
     | eof   {EOF}
     | _ { raise LexicalError }

and comment = parse
     "(*" {comment_depth := !comment_depth+1; comment lexbuf}
   | "*)" {comment_depth := !comment_depth-1;
           if !comment_depth > 0 then comment lexbuf }
   | eof {raise Eof}
   | _   {comment lexbuf}
