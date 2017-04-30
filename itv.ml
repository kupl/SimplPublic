open Vocab

type t' = 
  | V of int
  | PInf 
  | NInf

type t = Itv of t' * t' | Bot  

let top = Itv (NInf, PInf)
let bot = Bot

let int2itv : int -> t
= fun n -> Itv (V n, V n)

let to_string' : t' -> string
= fun v -> 
  match v with
  | V n -> string_of_int n
  | PInf -> "+oo"
  | NInf -> "-oo"

let to_string : t -> string
= fun itv ->
  match itv with
  | Itv (l,u) -> "[" ^ (to_string' l) ^ ", " ^ (to_string' u) ^"]"
  | Bot -> "bot"

let le' : t' -> t' -> bool
= fun v1 v2 ->
  match v1,v2 with
  | NInf,_ -> true
  | _,PInf -> true
  | V n1,V n2 -> n1<=n2
  | _,_ -> false

let eq' : t' -> t' -> bool
= fun v1 v2 ->
  match v1,v2 with
  | NInf,NInf 
  | PInf,PInf -> true
  | V n1,V n2 -> n1=n2
  | _,_ -> false

let lt' : t' -> t' -> bool
= fun v1 v2 -> le' v1 v2 && not (eq' v1 v2)

let gt' : t' -> t' -> bool
= fun v1 v2 -> not (le' v1 v2) (* check *) 

let ge' : t' -> t' -> bool
= fun v1 v2 -> not (lt' v1 v2) 

let min' : t' -> t' -> t' 
= fun v1 v2 -> if le' v1 v2 then v1 else v2

let max' : t' -> t' -> t'
= fun v1 v2 -> if le' v1 v2 then v2 else v1 

let plus' : t' -> t' -> t' 
= fun v1 v2 ->
  match v1,v2 with
  | V n1,V n2 -> V (n1+n2)
  | PInf,NInf -> raise (Failure "itv.ml : plus'")
  | NInf,PInf -> raise (Failure "itv.ml : plus'")
  | PInf,_ -> PInf
  | NInf,_ -> NInf
  | _,PInf -> PInf
  | _,NInf -> NInf

let minus' : t' -> t' -> t'
= fun v1 v2 ->
  match v1,v2 with
  | V n1,V n2 -> V (n1-n2)
  | PInf,PInf -> raise (Failure "itv.ml : minus'")
  | NInf,NInf -> raise (Failure "itv.ml : minus'")
  | PInf,_ -> PInf
  | NInf,_ -> NInf
  | _,PInf -> NInf
  | _,NInf -> PInf 

let times' : t' -> t' -> t'
= fun v1 v2 ->
  match v1,v2 with 
  | V n1,V n2 -> V (n1*n2)
  | PInf,PInf
  | NInf,NInf -> PInf
  | PInf,NInf
  | NInf,PInf -> NInf
  | PInf,V n
  | V n,PInf ->
    if n>0 then PInf else 
    if n<0 then NInf else
                V 0
  | NInf,V n
  | V n,NInf ->
    if n>0 then NInf else 
    if n<0 then PInf else
                V 0

let divide' : t' -> t' -> t'
= fun v1 v2 ->
  match v1,v2 with
  | V n1, V n2 ->
    if n2=0 then raise (Failure "itv.ml : divide'1") else V (n1/n2)
  | PInf,PInf
  | NInf,NInf -> PInf
  | NInf,PInf
  | PInf,NInf -> NInf
  | NInf,V n ->
    if n<0 then PInf else
    if n>0 then NInf else
      raise (Failure "itv.ml : divide'2") 
  | PInf,V n ->
    if n<0 then NInf else
    if n>0 then PInf else
      raise (Failure "itv.ml : divide'3")
  | V _,PInf
  | V _,NInf -> V 0

let modulo' : t' -> t' -> t'
= fun v1 v2 ->
  match v1,v2 with
  | V n1, V n2 ->
    if n2=0 then raise (Failure "itv.ml : divide'2") else V (n1 mod n2) 
  | PInf,PInf 
  | PInf,NInf -> PInf
  | NInf,PInf
  | NInf,NInf -> NInf
  | NInf,V n ->
    if n<0 then V (n+1) else
    if n>0 then V (-n+1) else
      raise (Failure "itv.ml : modulo'2")
  | PInf,V n ->
    if n<0 then V (-(n+1)) else  
    if n>0 then V (n-1) else
      raise (Failure "itv.ml : modulo'3")
  | V n,PInf
  | V n,NInf -> V n

let lower_widen' : t' -> t' -> t'
= fun v1 v2 ->
  if lt' v2 v1 then NInf 
  else v1
  
let upper_widen' : t' -> t' -> t'
= fun v1 v2 ->
  if gt' v2 v1 then PInf
  else v1

let lower_narrow' : t' -> t' -> t'
= fun v1 v2 ->
  if v1 = NInf then v2
  else v1

let upper_narrow' : t' -> t' -> t'
= fun v1 v2 ->
  if v1 = PInf then v2
  else v1

let is_const : t -> bool
= fun itv ->
  match itv with
  | Itv (V n1,V n2) when n1=n2 -> true
  | _ -> false

let is_bot : t -> bool
= fun itv ->
  match itv with
  | Bot -> true
  | Itv (l,u) -> l = PInf || u = NInf || not (le' l u)

let itv2int : t -> int
= fun itv ->
  match itv with
  | Itv (V n1,V n2) when n1=n2 -> n1
  | _ -> raise (Failure "itv.ml : itv2int")

let plus : t -> t -> t
= fun itv1 itv2 ->
  if is_bot itv1 || is_bot itv2 then Bot else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> Itv (plus' l1 l2, plus' u1 u2) 
    | _ -> raise (Failure "itv.ml : plus") 

let minus : t -> t -> t
= fun itv1 itv2 ->
  if is_bot itv1 || is_bot itv2 then Bot else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> Itv (minus' l1 u2, minus' u1 l2) (* Note : order *)
    | _ -> raise (Failure "itv.ml : minus")

let times : t -> t -> t
= fun itv1 itv2 ->
  if is_bot itv1 || is_bot itv2 then Bot else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> 
      let x1 = times' l1 l2 in
      let x2 = times' l1 u2 in
      let x3 = times' u1 l2 in
      let x4 = times' u1 u2 in 
      let l = min' (min' x1 x2) (min' x3 x4) in
      let u = max' (max' x1 x2) (max' x3 x4) in
      Itv (l,u)
    | _ -> raise (Failure "itv.ml : times")

let le : t -> t -> bool
= fun itv1 itv2 ->
  if is_bot itv1 then true else
  if is_bot itv2 then false 
  else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> le' l2 l1 && le' u1 u2
    | _ -> raise (Failure "itv.ml : le")

let eq : t -> t -> bool
= fun itv1 itv2 ->
  if is_bot itv1 && is_bot itv2 then true else
  if is_bot itv1 || is_bot itv2 then false
  else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> eq' l1 l2 && eq' u1 u2
    | _ -> raise (Failure "itv.ml : eq")

let divide : t -> t -> t 
= fun itv1 itv2 -> (* itv1/itv2 *)
  if is_bot itv1 || is_bot itv2 then bot else
  if eq (Itv (V 0,V 0)) itv2 then raise Division_by_zero else 
  if le (Itv (V 0,V 0)) itv2 then top else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) ->
      let x1 = divide' l1 l2 in
      let x2 = divide' l1 u2 in
      let x3 = divide' u1 l2 in
      let x4 = divide' u1 u2 in
      let l = min' (min' x1 x2) (min' x3 x4) in
      let u = max' (max' x1 x2) (max' x3 x4) in
      Itv (l,u)
    | _ -> raise (Failure "itv.ml : divide")

let modulo : t -> t -> t
= fun itv1 itv2 -> (* itv1 mod itv2 *)
  if is_bot itv1 || is_bot itv2 then bot else
  if eq (Itv (V 0,V 0)) itv2 then raise Division_by_zero else 
  if le (Itv (V 0,V 0)) itv2 then top else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) ->
      let x1 = modulo' l1 l2 in
      let x2 = modulo' l1 u2 in
      let x3 = modulo' u1 l2 in
      let x4 = modulo' u1 u2 in
      let l = min' (min' x1 x2) (min' x3 x4) in
      let u = max' (max' x1 x2) (max' x3 x4) in
      Itv (l,u)
    | _ -> raise (Failure "itv.ml : modulo")

let times : t -> t -> t
= fun itv1 itv2 ->
  if is_bot itv1 || is_bot itv2 then Bot else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> 
      let x1 = times' l1 l2 in
      let x2 = times' l1 u2 in
      let x3 = times' u1 l2 in
      let x4 = times' u1 u2 in 
      let l = min' (min' x1 x2) (min' x3 x4) in
      let u = max' (max' x1 x2) (max' x3 x4) in
      Itv (l,u)
    | _ -> raise (Failure "itv.ml : times")

let join : t -> t -> t
= fun itv1 itv2 ->
  if le itv1 itv2 then itv2 else
  if le itv2 itv1 then itv1 else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> Itv (min' l1 l2, max' u1 u2)  
    | _ -> raise (Failure "itv.ml : join")

let meet : t -> t -> t
= fun itv1 itv2 ->
  if le itv1 itv2 then itv1 else (* bot related op is included in le *) 
  if le itv2 itv1 then itv2 else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> Itv (max' l1 l2, min' u1 u2)  
    | _ -> raise (Failure "itv.ml : meet") 

let widen : t -> t -> t
= fun itv1 itv2 ->
  if is_bot itv1 then itv2 else
  if is_bot itv2 then itv1 else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> 
      Itv (lower_widen' l1 l2, upper_widen' u1 u2) 
    | _ -> raise (Failure "itv.ml : widen") 

let narrow : t -> t -> t
= fun itv1 itv2 ->
  if is_bot itv1 then itv1 else
  if is_bot itv2 then itv2 else (* may not happen *)
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> 
      Itv (lower_narrow' l1 l2, upper_narrow' u1 u2)
    | _ -> raise (Failure "itv.ml : narrow") 

let concrete_lt : t -> t -> bool
= fun itv1 itv2 ->
  if is_bot itv1 then false else
  if is_bot itv2 then false else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> lt' u1 l2 
    | _ -> raise (Failure "itv.ml : concrete_lt")

let concrete_le : t -> t -> bool
= fun itv1 itv2 ->
  if is_bot itv1 then false else
  if is_bot itv2 then false else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> le' u1 l2  
    | _ -> raise (Failure "itv.ml : concrete_le")

let concrete_gt : t -> t -> bool
= fun itv1 itv2 ->
  if is_bot itv1 then false else
  if is_bot itv2 then false else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> gt' l1 u2
    | _ -> raise (Failure "itv.ml : concrete_gt")

let concrete_ge : t -> t -> bool
= fun itv1 itv2 ->
  if is_bot itv1 then false else
  if is_bot itv2 then false else
    match itv1,itv2 with
    | Itv (l1,u1),Itv (l2,u2) -> ge' l1 u2
    | _ -> raise (Failure "itv.ml : concrete_ge") 

let concrete_neq : t -> t -> bool
= fun itv1 itv2 -> is_bot (meet itv1 itv2) 

let lower_to_pinf : t -> t
= fun itv ->
  if is_bot itv then raise (Failure "itv.ml : lower_to_pinf")
  else
    match itv with
    | Itv (l,u) -> Itv (l,PInf) 
    | _ -> raise (Failure "itv.ml : lower_to_pinf")

let ninf_to_upper : t -> t
= fun itv -> 
  if is_bot itv then raise (Failure "itv.ml : ninf_to_upper")
  else
    match itv with
    | Itv (l,u) -> Itv (NInf,u) 
    | _ -> raise (Failure "itv.ml : ninf_to_upper")

let itv_inc_one : t -> t 
= fun itv ->
  if is_bot itv then raise (Failure "itv.ml : itv_plus_one") else
    match itv with
    | Itv (l,u) -> Itv (plus' l (V 1), plus' u (V 1))
    | _ -> raise (Failure "itv.ml : itv_plus_one")

let itv_dec_one : t -> t 
= fun itv ->
  if is_bot itv then raise (Failure "itv.ml : itv_plus_one") else
    match itv with
    | Itv (l,u) -> Itv (minus' l (V 1), minus' u (V 1))
    | _ -> raise (Failure "itv.ml : itv_plus_one")

