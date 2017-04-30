%{
  open Imp 
%}

%token <int> INT 
%token <string> VAR
%token EXAMPLES
%token INTCOMPS
%token INTVARCOMPS
%token ARRVARCOMPS
%token PARTIALPGM
%token FUN

%token SKIP
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token WHILE

%token PLUS 
%token MINUS
%token MUL
%token DIV 
%token MOD
%token EQUAL
%token GT
%token LT
%token EQUALEQUAL
%token NOT
%token AND
%token OR
%token HOLE
%token RETURN

%token MAPSTO
%token COMMA
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET
%token SEMICOLON
%token NONE
%token EOF

%left SEMICOLON COMMA  
%left GT LT EQUALEQUAL NOT AND OR 
%left PLUS MINUS MUL DIV MOD

%start resource
%type <Imp.example list * Imp.pgm * int list * Imp.var list * Imp.var list> resource
%%

resource:
  | EXAMPLES examples PARTIALPGM pgm INTCOMPS integers INTVARCOMPS variables ARRVARCOMPS variables EOF {$2, $4, $6, $8, $10}
  | EXAMPLES examples PARTIALPGM pgm INTCOMPS integer INTVARCOMPS variables ARRVARCOMPS variables EOF {$2, $4, [$6], $8, $10} 
  ; 

examples:
  | example examples {$1::$2}
  | example {[$1]}
  ;

example:
  | input MAPSTO output SEMICOLON {($1,$3)}
  ;

input:
  | value COMMA input {$1::$3}
  | value {[$1]}
  ;

output:
  | value {$1}
  ;

value: 
  | arr {Imp.VArr ($1)}
  | integer {Imp.VInt ($1)}
  ;

arr:
  | LBRACE integer RBRACE {[$2]}
  | LBRACE integers RBRACE {$2}
  ;

integer:
  | MINUS INT {($2*(-1))}
  | INT {($1)}
  ;

integers:
  | integer COMMA integers {$1::$3}
  | integer COMMA integer {[$1;$3]}
  ;

variable:
  | VAR {($1)}
  ;

variables:
  | NONE {[]}
  | variable COMMA variables {$1::$3}
  | variable {[$1]}
  ;

pgm: 
  | FUN variables MAPSTO cmd RETURN VAR SEMICOLON {($2,$4,$6)}  
  ;

aexp: 
  | integer {Imp.Int $1}
  | lv {Imp.Lv $1}
  | lv bop lv {Imp.BinOpLv ($2,$1,$3)}
  | lv bop integer {Imp.BinOpN ($2,$1,$3)}
  | HOLE {Imp.ahole ()} 
  ;

lv:
  | VAR {Imp.Var $1}
  | VAR LBRACKET VAR RBRACKET {Imp.Arr ($1,$3)}

bexp:
  | TRUE {Imp.True}
  | FALSE {Imp.False}
  | lv GT lv {Imp.GtLv ($1,$3)}
  | lv GT integer {Imp.GtN ($1,$3)}
  | lv LT lv {Imp.LtLv ($1,$3)}
  | lv LT integer {Imp.LtN ($1,$3)}
  | lv EQUALEQUAL lv {Imp.EqLv ($1,$3)}
  | lv EQUALEQUAL integer {Imp.EqN ($1,$3)}
  | NOT bexp {Imp.Not $2}
  | bexp OR bexp {Imp.Or ($1,$3)}
  | bexp AND bexp {Imp.And ($1,$3)}
  | HOLE {Imp.bhole ()}
  ;

cmd:
  | cmd SEMICOLON cmd {Imp.Seq ($1, $3)}
  | cmd SEMICOLON {$1}
  | SKIP {Imp.Skip}
  | lv EQUAL aexp {Imp.Assign ($1, $3)}
  | IF LPAREN bexp RPAREN LBRACE cmd RBRACE ELSE LBRACE cmd RBRACE {Imp.If ($3,$6,$10)}
  | IF LPAREN bexp RPAREN LBRACE cmd RBRACE {Imp.If ($3,$6,Imp.Skip)} 
  | WHILE LPAREN bexp RPAREN LBRACE cmd RBRACE {Imp.While ($3,$6)}
  | HOLE {Imp.chole ()} 
  ;

bop:
  | PLUS {Imp.Plus}
  | MINUS {Imp.Minus}
  | MUL {Imp.Mult}
  | DIV {Imp.Div}
  | MOD {Imp.Mod}
  ;

%%
