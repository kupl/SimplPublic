open Imp
open Vocab

type t = 
  | Top
  | Bot
  | Sym of sym
and sym =
  | SInt of int
  | SVar of id
  | SBinOp of bop * sym * sym 
and id = string

let top = Top 
let bot = Bot

let rec to_string : t -> string
= fun v ->
  match v with
  | Top -> "symbolic top"
  | Bot -> "symbolic bot"
  | Sym s -> sstring s 

and sstring : sym -> string
= fun s ->
  match s with
  | SInt n -> string_of_int n
  | SVar id -> "symbol_" ^ id
  | SBinOp (bop,s1,s2) -> 
    (match bop with
     | Plus  -> "(" ^ (sstring s1) ^ " + " ^ (sstring s2) ^ ")"
     | Minus -> "(" ^ (sstring s1) ^ " - " ^ (sstring s2) ^ ")"
     | Mult  -> "(" ^ (sstring s1) ^ " * " ^ (sstring s2) ^ ")"
     | Div   -> "(" ^ (sstring s1) ^ " / " ^ (sstring s2) ^ ")"
     | Mod   -> "(" ^ (sstring s1) ^ " % " ^ (sstring s2) ^ ")")

let le : t -> t -> bool
= fun s1 s2 ->
  if s1 = Bot then true else
  if s2 = Top then true else
  if s1 = s2 then true
  else false

let join : t -> t -> t
= fun s1 s2 ->
  if le s1 s2 then s2 else
  if le s2 s1 then s1
  else Top

let meet : t -> t -> t
= fun s1 s2 ->
  if le s1 s2 then s1 else
  if le s2 s1 then s2
  else Top

let splus : sym -> sym -> sym
= fun s1 s2 ->
  match s1,s2 with
  | SInt n1,SInt n2 -> SInt (n1+n2)
  | s1,SInt 0 -> s1 (* added 170228 *)
  | _ -> SBinOp (Plus,s1,s2) 

let plus : t -> t -> t
= fun v1 v2 ->
  match v1,v2 with
  | Bot,_
  | _,Bot -> Bot
  | Top,_  
  | _,Top -> Top
  | Sym s1,Sym s2 -> Sym (splus s1 s2) 

let sminus : sym -> sym -> sym
= fun s1 s2 ->
  match s1,s2 with
  | SInt n1,SInt n2 -> SInt (n1-n2)
  | s1,SInt 0 -> s1 (* added 170228 *)
  | _ -> SBinOp (Minus,s1,s2) 

let minus : t -> t -> t
= fun v1 v2 ->
  match v1,v2 with
  | Bot,_
  | _,Bot -> Bot
  | Top,_  
  | _,Top -> Top
  | Sym s1,Sym s2 -> Sym (sminus s1 s2) 

let stimes : sym -> sym -> sym
= fun s1 s2 ->
  match s1,s2 with
  | SInt n1,SInt n2 -> SInt (n1*n2)
  | SInt 0,_ -> SInt 0 (* added 170228 *)
  | _,SInt 0 -> SInt 0 (* added 170228 *)
  | _ -> SBinOp (Mult,s1,s2)

let times : t -> t -> t
= fun v1 v2 ->
  match v1,v2 with
  | Bot,_
  | _,Bot -> Bot
  | Top,_ 
  | _,Top -> Top
  | Sym s1,Sym s2 -> Sym (stimes s1 s2)

let sdivide : sym -> sym -> sym
= fun s1 s2 ->
  match s1,s2 with
  | SInt n1,SInt n2 ->
    if n2 = 0 then raise Division_by_zero 
    else SInt (n1/n2)
  | SInt 0,_ -> SInt 0 (* added 170228 *)
  | _ -> SBinOp (Div,s1,s2)

let divide : t -> t -> t
= fun v1 v2 ->
  match v1,v2 with
  | Bot,_
  | _,Bot -> Bot
  | Top,_ 
  | _,Top -> Top
  | Sym s1, Sym s2 -> Sym (sdivide s1 s2)

let smodulo : sym -> sym -> sym
= fun s1 s2 ->
  match s1,s2 with
  | SInt n1,SInt n2 ->
    if n2 = 0 then raise Division_by_zero 
    else SInt (n1 mod n2)
  | SInt 0,_ -> SInt 0 (* added 170228 *) 
  | _ -> SBinOp (Mod,s1,s2)

let modulo : t -> t -> t
= fun v1 v2 ->
  match v1,v2 with
  | Bot,_
  | _,Bot -> Bot
  | Top,_ 
  | _,Top -> Top
  | Sym s1, Sym s2 -> Sym (smodulo s1 s2)

let sat_le : t -> t -> bool
= fun o r ->
  match o,r with
  | Bot,_ -> true
  | _,Top -> true
  | Sym (SInt o),Sym (SBinOp (Plus,s1,s2)) when s1=s2 -> o mod 2 = 0
  | Sym (SInt o),Sym (SBinOp (Mult,SVar _,SInt n)) when n!=0 -> o mod n = 0
  | _ -> true
