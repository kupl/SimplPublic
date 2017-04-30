open Imp
open Itv
open Vocab
open Abs

(***********************
 ***********************
 EXPRESSION SIMPLIFICATION 
 **********************
 **********************)

let rec simple_aexp : aexp -> aexp
= fun aexp ->
  match aexp with
  | BinOpLv (Minus,lv1,lv2) when lv1 = lv2 -> Int 0
  (* Note : Both 2 below does not impair completeness *)
  | BinOpLv (Div,lv1,lv2) when lv1 = lv2 -> Int 1
  | BinOpLv (Mod,lv1,lv2) when lv1 = lv2 -> Int 0
  | BinOpN (Plus,lv,0)  -> Lv lv
  | BinOpN (Minus,lv,0) -> Lv lv
  | BinOpN (Mult,lv,1)  -> Lv lv
  | BinOpN (Mult,lv,0)  -> Int 0
  | BinOpN (Div, lv,1)  -> Lv lv
  | BinOpN (Mod, lv,1)  -> Int 0
  | _ -> aexp

let rec simple_bexp : bexp -> bexp
= fun bexp ->
  match bexp with
  | GtLv (lv1,lv2) when lv1=lv2 -> False
  | LtLv (lv1,lv2) when lv1=lv2 -> False
  | EqLv (lv1,lv2) when lv1=lv2 -> True
  | Not True -> False
  | Not False -> True
  | Not (Not b) -> simple_bexp b
  | Not b -> Not (simple_bexp b)
  | Or (b1,b2) ->
    if true_exists (Or (b1,b2)) then True else
    if all_false (Or (b1,b2)) then False 
    else Or (simple_bexp b1, simple_bexp b2)
  | And (b1,b2) -> 
    if false_exists (And (b1,b2)) then False else
    if all_true (And (b1,b2)) then True 
    else And (simple_bexp b1, simple_bexp b2)
  | _ -> bexp

and all_true : bexp -> bool
= fun bexp ->
  match bexp with
  | True -> true
  | Or (b1,b2) -> all_true b1 && all_true b2
  | And (b1,b2) -> all_true b1 && all_true b2
  | Not b -> all_true b
  | _ -> false

and true_exists : bexp -> bool
= fun bexp ->
  match bexp with
  | True -> true
  | Or (b1,b2) -> true_exists b1 || true_exists b2
  | And (b1,b2) -> true_exists b1 || true_exists b2
  | Not b -> true_exists b
  | _ -> false

and all_false : bexp -> bool
= fun bexp ->
  match bexp with
  | False -> true
  | Or (b1,b2) -> all_false b1 && all_false b2
  | And (b1,b2) -> all_false b1 && all_false b2
  | Not b -> all_false b
  | _ -> false

and false_exists : bexp -> bool
= fun bexp ->
  match bexp with
  | False -> true
  | Or (b1,b2) -> false_exists b1 || false_exists b2
  | And (b1,b2) -> false_exists b1 || false_exists b2
  | Not b -> false_exists b
  | _ -> false

let rec simple_cmd : cmd -> cmd
= fun cmd ->
  match cmd with
  | Assign (lv,aexp) -> Assign (lv, simple_aexp aexp) 
  | Skip -> cmd
  | Seq (c1,c2) -> Seq (simple_cmd c1, simple_cmd c2)
  | If (b,c1,c2) -> If (simple_bexp b, simple_cmd c1, simple_cmd c2)
  | While (b,c) -> While (simple_bexp b, simple_cmd c)
  | CHole _ -> cmd

let expression_simplification : pgm -> pgm
= fun (args,cmd,res) -> 
  let cmd' = simple_cmd cmd in
    (args,cmd',res)


(***********************
 ***********************
 CONSTANT PROPAGATION ANALYSIS 
 **********************
 **********************)

type constloc = var
and constval = 
  | ConstTop 
  | Const of int 
  | ConstBot

module ConstMem = struct
  type t = (constloc,constval) BatMap.t
  let add = BatMap.add
  let find = BatMap.find
  let empty = BatMap.empty

  let const_le : constval -> constval -> bool
  = fun v1 v2 ->
    if v1 = v2 then true
    else 
      match v1,v2 with
      | ConstBot,_ -> true 
      | _,ConstTop -> true
      | Const n1, Const n2 when n1=n2 -> true
      | _ -> false

  let const_join : constval -> constval -> constval
  = fun v1 v2 -> 
    if const_le v1 v2 then v2 else
    if const_le v2 v1 then v1 
    else ConstTop

  let join : t -> t -> t
  = fun cmem1 cmem2 ->
    let join' key opt_d1 opt_d2 = 
      match opt_d1,opt_d2 with
      | None,None -> None
      | None,Some v
      | Some v,None -> Some v
      | Some v1,Some v2 -> Some (const_join v1 v2) 
    in BatMap.merge join' cmem1 cmem2

  let le : t -> t -> bool 
  = fun cmem1 cmem2 ->
    if cmem1 = cmem2 then true 
    else
      let enum1 = BatMap.enum cmem1 in
      let enum2 = BatMap.enum cmem2 in
      let rec loop : (constloc * constval) option -> (constloc * constval) option -> bool
      = fun e1 e2 ->
        match e1,e2 with
        | Some (k1,d1),Some (k2,d2) ->
          if k1=k2 && const_le d1 d2 
            then loop (BatEnum.get enum1) (BatEnum.get enum2)
          else false
        | Some (k,d),None -> false
        | None,Some (k,d) -> true
        | None,None -> true in
    loop (BatEnum.get enum1) (BatEnum.get enum2)
end

(********************************
  Semantic function 
  for constant propagation analysis
*********************************)

let rec constp_aexp : aexp -> ConstMem.t -> constval
= fun aexp cmem ->
  match aexp with
  | Int n -> Const n
  | Lv lv -> ConstMem.find (constp_loc_of_lv lv) cmem
  | BinOpLv (bop,lv1,lv2) -> constp_bop bop (constp_aexp (Lv lv1) cmem) (constp_aexp (Lv lv2) cmem)
  | BinOpN (bop,lv,n) -> constp_bop bop (constp_aexp (Lv lv) cmem) (constp_aexp (Int n) cmem)
  | AHole _ -> ConstTop

and constp_loc_of_lv : lv -> constloc
= fun lv ->
  match lv with | Var x | Arr (x,_) -> x

and constp_bop : bop -> constval -> constval -> constval
= fun bop v1 v2 ->
  match v1,v2 with
  | ConstBot,_ 
  | _,ConstBot -> ConstBot
  | ConstTop,_
  | _,ConstTop -> ConstTop
  | Const n1,Const n2 ->
    (match bop with
     | Plus  -> Const (n1+n2)
     | Minus -> Const (n1-n2) 
     | Mult  -> Const (n1*n2)
     | Div   -> Const (n1/n2)
     | Mod   -> Const (n1 mod n2))

let rec constp_cmd : lv list -> cmd -> ConstMem.t -> ConstMem.t
= fun lv_comps cmd cmem ->
  match cmd with
  | Assign (Var x,aexp) -> ConstMem.add (constp_loc_of_lv (Var x)) (constp_aexp aexp cmem) cmem
  | Assign (Arr (x,y),aexp) -> 
    let past = ConstMem.find (constp_loc_of_lv (Arr (x,y))) cmem in
    let cur = constp_aexp aexp cmem in
      ConstMem.add (constp_loc_of_lv (Arr (x,y))) (ConstMem.const_join past cur) cmem 
  | Skip -> cmem
  | Seq (c1,c2) -> constp_cmd lv_comps c2 (constp_cmd lv_comps c1 cmem)
  | If (_,c1,c2) -> constp_cond lv_comps (c1,c2) cmem 
  | While (b,c) ->
    let next = constp_cond lv_comps (c,Skip) cmem in
      if ConstMem.le next cmem then cmem
      else constp_cmd lv_comps (While (b,c)) next 
  | CHole _ -> 
    let cmem' = List.fold_left (fun cmem lv -> match lv with | Var x | Arr (x,_) -> ConstMem.add x ConstTop cmem) cmem lv_comps in
      cmem'

and constp_cond :lv list -> (cmd * cmd) -> ConstMem.t -> ConstMem.t
= fun lv_comps (c1,c2) cmem ->
  ConstMem.join (constp_cmd lv_comps c1 cmem) (constp_cmd lv_comps c2 cmem) 

(********************************
  Transformation functions 
  for constant propagation analysis
*********************************) 

let rec trans_constp_aexp : aexp -> ConstMem.t -> aexp
= fun aexp cmem ->
  match constp_aexp aexp cmem with
  | Const n -> Int n (* total *)
  | _ -> (* partial *)
   (match aexp with 
    | BinOpLv (bop,lv1,lv2) -> 
      (match constp_aexp (Lv lv1) cmem, constp_aexp (Lv lv2) cmem with
       | Const n1, _ -> BinOpN (bop,lv2,n1)
       | _, Const n2 -> BinOpN (bop,lv1,n2)
       | _ -> aexp)
    | _ -> aexp)

and const2int : constval -> int
= fun cv ->
  match cv with
  | Const n -> n
  | _ -> raise (Failure "normalize.ml -const2int : cannot be transformed into integer ")

let rec trans_constp_bexp : bexp -> ConstMem.t -> bexp
= fun bexp cmem -> 
  match bexp with
  | GtLv (lv1,lv2) -> 
    (match constp_aexp (Lv lv1) cmem, constp_aexp (Lv lv2) cmem with
     | Const n1, Const n2 -> if n1>n2 then True else False
     | _,Const n2 -> GtN (lv1,n2)
     | _ -> bexp)
  | LtLv (lv1,lv2) ->
    (match constp_aexp (Lv lv1) cmem, constp_aexp (Lv lv2) cmem with
     | Const n1, Const n2 -> if n1<n2 then True else False
     | _,Const n2 -> LtN (lv1,n2)
     | _ -> bexp)
  | EqLv (lv1,lv2) ->
    (match constp_aexp (Lv lv1) cmem, constp_aexp (Lv lv2) cmem with
     | Const n1, Const n2 -> if n1=n2 then True else False
     | _,Const n2 -> EqN (lv1,n2)
     | _ -> bexp)
  | GtN (lv,n) ->
    (match constp_aexp (Lv lv) cmem with
     | Const n' -> if n'>n then True else False
     | _ -> bexp)
  | LtN (lv,n) ->
    (match constp_aexp (Lv lv) cmem with
     | Const n' -> if n'<n then True else False
     | _ -> bexp)
  | EqN (lv,n) ->
    (match constp_aexp (Lv lv) cmem with
     | Const n' -> if n'=n then True else False
     | _ -> bexp)
  | Not b -> Not (trans_constp_bexp b cmem)
  | Or (b1,b2) -> Or (trans_constp_bexp b1 cmem, trans_constp_bexp b2 cmem)
  | And (b1,b2) -> And (trans_constp_bexp b1 cmem, trans_constp_bexp b2 cmem)
  | _ -> bexp

let rec trans_constp_cmd : lv list -> cmd -> ConstMem.t -> (cmd * ConstMem.t)
= fun lv_comps cmd cmem ->
  match cmd with
  | Assign (lv, aexp) -> (Assign (lv, trans_constp_aexp aexp cmem), constp_cmd lv_comps cmd cmem)
  | Skip -> (cmd, constp_cmd lv_comps cmd cmem) 
  | Seq (c1,c2) -> 
    let (c1', cmem1') = trans_constp_cmd lv_comps c1 cmem in
    let (c2', cmem2') = trans_constp_cmd lv_comps c2 cmem1' in
      (Seq (c1',c2'), cmem2')
  | If (b,c1,c2) ->
    let b' = trans_constp_bexp b cmem in
    let (c1', cmem1') = trans_constp_cmd lv_comps c1 cmem in
    let (c2', cmem2') = trans_constp_cmd lv_comps c2 cmem in
      (If (b',c1',c2'), ConstMem.join cmem1' cmem2') 
  | While (b,c) ->
    let resulting_mem = constp_cmd lv_comps cmd cmem in
    let b' = trans_constp_bexp b resulting_mem in
    let c' = fst (trans_constp_cmd lv_comps c resulting_mem) in
      (While (b',c'), resulting_mem)
  | CHole _ -> (cmd, constp_cmd lv_comps cmd cmem)

let constant_propagation : lv list -> pgm -> pgm
= fun lv_comps (args,cmd,res) ->
  let init_cmem = List.fold_left (fun cmem x -> ConstMem.add x ConstTop cmem) ConstMem.empty args in
  let (cmd',mem) = trans_constp_cmd lv_comps cmd init_cmem in
    (args,cmd',res)

(***********************
 ***********************
 COPY PROPAGATION ANALYSIS 
 **********************
 **********************)
type coploc = var
and copval = 
  | CopyTop 
  | CopyVal of lv 
  | CopyBot

module CopyMem = struct 
  type t = (coploc,copval) BatMap.t

  (* Delete previous binding if the updated variable (x) was used as index variable *) 
  let add x v m =
    let m' = 
      BatMap.filterv 
        (fun d -> match d with | CopyVal (Arr (_,idx)) -> not (BatString.equal x idx) |  _ -> true) m 
    in BatMap.add x v m'    
  
  let find = BatMap.find 
  let empty = BatMap.empty

  let copy_le : copval -> copval -> bool
  = fun v1 v2 ->
    if v1=v2 then true
    else 
      match v1,v2 with
      | CopyBot,_ -> true 
      | _,CopyTop -> true
      | _,_ -> false

  let copy_join : copval -> copval -> copval
  = fun v1 v2 -> 
    if copy_le v1 v2 then v2 else
    if copy_le v2 v1 then v1 
    else CopyTop

  let join : t -> t -> t
  = fun cpmem1 cpmem2 ->
    let join' key opt_d1 opt_d2 =
      match opt_d1,opt_d2 with
      | None,None -> None
      | None,Some v 
      | Some v,None -> Some v
      | Some v1,Some v2 -> Some (copy_join v1 v2)
    in BatMap.merge join' cpmem1 cpmem2

  let le : t -> t -> bool 
  = fun vmem1 vmem2 ->
    if vmem1 = vmem2 then true 
    else
      let enum1 = BatMap.enum vmem1 in
      let enum2 = BatMap.enum vmem2 in
      let rec loop : (coploc * copval) option -> (coploc * copval) option -> bool
      = fun e1 e2 ->
        match e1,e2 with
        | Some (k1,d1),Some (k2,d2) ->
          if k1=k2 && copy_le d1 d2 
            then loop (BatEnum.get enum1) (BatEnum.get enum2)
          else false
        | Some (k,d),None -> false
        | None,Some (k,d) -> true
        | None,None -> true in
    loop (BatEnum.get enum1) (BatEnum.get enum2)
end

(********************************
  Semantic function 
  for copy propagation analysis
*********************************)

let rec copyp_aexp : aexp -> CopyMem.t -> copval
= fun aexp cpmem -> 
  match aexp with
  | Int n -> CopyBot 
  | Lv lv -> CopyVal lv
  | BinOpLv _ -> CopyTop
  | BinOpN _  -> CopyTop
  | AHole _ -> CopyTop

and copyp_loc_of_lv : lv -> coploc
= fun lv ->
  match lv with | Var x | Arr (x,_) -> x 

let rec copyp_cmd : lv list -> cmd -> CopyMem.t -> CopyMem.t 
= fun lv_comps cmd cpmem ->
  match cmd with
  | Assign (Var x,aexp) -> CopyMem.add (copyp_loc_of_lv (Var x)) (copyp_aexp aexp cpmem) cpmem
  | Assign (lv,aexp) -> 
    let past = CopyMem.find (copyp_loc_of_lv lv) cpmem in
    let cur = copyp_aexp aexp cpmem in
      CopyMem.add (copyp_loc_of_lv lv) (CopyMem.copy_join past cur) cpmem 
  | Skip -> cpmem
  | Seq (c1,c2) -> copyp_cmd lv_comps c2 (copyp_cmd lv_comps c1 cpmem) 
  | If (_,c1,c2) -> copyp_cond lv_comps (c1,c2) cpmem
  | While (b,c) ->
    let next = copyp_cond lv_comps (c,Skip) cpmem in
      if CopyMem.le next cpmem then cpmem
      else copyp_cmd lv_comps (While (b,c)) next 
  | CHole _ -> 
   let cpmem' = List.fold_left (fun cpmem lv -> match lv with | Var x | Arr (x,_) -> CopyMem.add x CopyTop cpmem) cpmem lv_comps in
      cpmem'

and copyp_cond : lv list -> (cmd * cmd) -> CopyMem.t -> CopyMem.t
= fun lv_comps (c1,c2) cpmem ->
  CopyMem.join (copyp_cmd lv_comps c1 cpmem) (copyp_cmd lv_comps c2 cpmem)

(********************************
  Transformation functions 
  for copy propagation analysis
*********************************) 

let rec trans_copyp_aexp : aexp -> CopyMem.t -> aexp
= fun aexp cpmem ->
  match copyp_aexp aexp cpmem with
  | CopyVal lv -> Lv lv (* total *)
  | _ -> (* partial *)
    (match aexp with
     | BinOpLv (bop,lv1,lv2) -> BinOpLv (bop, aexp2lv (trans_copyp_aexp (Lv lv1) cpmem), aexp2lv (trans_copyp_aexp (Lv lv2) cpmem))
     | BinOpN (bop,lv,n) -> BinOpN (bop, aexp2lv (trans_copyp_aexp (Lv lv) cpmem), n) 
     | _ -> aexp)

and aexp2lv : aexp -> lv
= fun aexp ->
  match aexp with
  | Lv lv -> lv
  | _ -> raise (Failure "normalize.ml : aexp2lv")  

let rec trans_copyp_bexp : bexp -> CopyMem.t -> bexp
= fun bexp cpmem ->
  match bexp with
  | GtLv (lv1,lv2) -> GtLv (aexp2lv (trans_copyp_aexp (Lv lv1) cpmem), aexp2lv (trans_copyp_aexp (Lv lv2) cpmem))
  | LtLv (lv1,lv2) -> LtLv (aexp2lv (trans_copyp_aexp (Lv lv1) cpmem), aexp2lv (trans_copyp_aexp (Lv lv2) cpmem))
  | EqLv (lv1,lv2) -> EqLv (aexp2lv (trans_copyp_aexp (Lv lv1) cpmem), aexp2lv (trans_copyp_aexp (Lv lv2) cpmem))
  | GtN (lv,n) -> GtN (aexp2lv (trans_copyp_aexp (Lv lv) cpmem), n) 
  | LtN (lv,n) -> LtN (aexp2lv (trans_copyp_aexp (Lv lv) cpmem), n) 
  | EqN (lv,n) -> EqN (aexp2lv (trans_copyp_aexp (Lv lv) cpmem), n) 
  | Not b -> Not (trans_copyp_bexp b cpmem)
  | Or (b1,b2) -> Or   (trans_copyp_bexp b1 cpmem, trans_copyp_bexp b2 cpmem)
  | And (b1,b2) -> And (trans_copyp_bexp b1 cpmem, trans_copyp_bexp b2 cpmem)
  | _ -> bexp

let rec trans_copyp_cmd : lv list -> cmd -> CopyMem.t -> (cmd * CopyMem.t)
= fun lv_comps cmd cpmem ->
  match cmd with
  | Assign (lv, aexp) -> (Assign (lv, trans_copyp_aexp aexp cpmem), copyp_cmd lv_comps cmd cpmem) 
  | Skip -> (cmd, copyp_cmd lv_comps cmd cpmem) 
  | Seq (c1,c2) -> 
    let (c1', cpmem1') = trans_copyp_cmd lv_comps c1 cpmem in
    let (c2', cpmem2') = trans_copyp_cmd lv_comps c2 cpmem1' in 
      (Seq (c1',c2'), cpmem2')
  | If (b,c1,c2) ->
    let b' = trans_copyp_bexp b cpmem in
    let (c1', cpmem1') = trans_copyp_cmd lv_comps c1 cpmem in
    let (c2', cpmem2') = trans_copyp_cmd lv_comps c2 cpmem in
      (If (b',c1',c2'), CopyMem.join cpmem1' cpmem2')
  | While (b,c) ->
    let resulting_mem = copyp_cmd lv_comps cmd cpmem in
    let b' = trans_copyp_bexp b resulting_mem in
    let c' = fst (trans_copyp_cmd lv_comps c resulting_mem) in
      (While (b',c'), resulting_mem)
  | CHole _ -> (cmd, copyp_cmd lv_comps cmd cpmem) 

let copy_propagation : lv list -> pgm -> pgm
= fun lv_comps (args,cmd,res) ->
  let init_cpmem = List.fold_left (fun cpmem x -> CopyMem.add x CopyBot cpmem) CopyMem.empty args in
  let cmd' = fst (trans_copyp_cmd lv_comps cmd init_cpmem) in
    (args,cmd',res)

(***********************
 ***********************
 DEAD CODE ELIMINATION
 **********************
 **********************)

(* functions for collecting use set *)
let rec uses_aexp : lv list -> aexp -> lv BatSet.t 
= fun lv_comps aexp ->
  match aexp with
  | Int n -> BatSet.empty
  | Lv lv -> uses_lv lv
  | BinOpLv (bop,lv1,lv2) -> BatSet.union (uses_lv lv1) (uses_lv lv2)
  | BinOpN (bop,lv,n) -> uses_lv lv
  | AHole _ -> BatSet.of_list lv_comps 

and uses_lv : lv -> lv BatSet.t 
= fun lv ->
  match lv with
  | Var x -> BatSet.singleton (Var x)
  | Arr (x,y) -> BatSet.add (Var y) (BatSet.singleton (Arr (x,y))) 

let rec uses_bexp : lv list -> bexp -> lv BatSet.t 
= fun lv_comps bexp ->
  match bexp with
  | True | False -> BatSet.empty
  | GtLv (lv1,lv2) 
  | LtLv (lv1,lv2) 
  | EqLv (lv1,lv2) -> BatSet.union (uses_lv lv1) (uses_lv lv2)
  | GtN (lv,n) 
  | LtN (lv,n) 
  | EqN (lv,n) -> uses_lv lv
  | Not b -> uses_bexp lv_comps b
  | Or (b1,b2) 
  | And (b1,b2) -> BatSet.union (uses_bexp lv_comps b1) (uses_bexp lv_comps b2) 
  | BHole _ -> BatSet.of_list lv_comps

let rec uses_cmd : lv list -> cmd -> lv BatSet.t 
= fun lv_comps cmd ->
  match cmd with
  | Assign (Var _,aexp) -> uses_aexp lv_comps aexp  
  | Assign (Arr (_,y),aexp) -> BatSet.add (Var y) (uses_aexp lv_comps aexp)
  | Skip -> BatSet.empty
  | Seq (c1,c2) -> BatSet.union (uses_cmd lv_comps c1) (uses_cmd lv_comps c2)
  | If (b,c1,c2) ->
    BatSet.union (uses_bexp lv_comps b)
                 (BatSet.union (uses_cmd lv_comps c1) (uses_cmd lv_comps c2))
  | While (b,c) -> BatSet.union (uses_bexp lv_comps b) (uses_cmd lv_comps c)
  | CHole _ -> BatSet.of_list lv_comps 

(* Definition of Definition set : l-values to be updated *) 

(* Remove dead code *)
(* Note : 2nd rule - Remove previous array value if idx is updated *)
(* eg. read backward
   arr[i] = ... ; // Dead code !
   i = ... ;      // used = empty set, arr[i] is not used
   ... = arr[i];  // used = {arr[i]}
 *)
let rec remove_deadcode : lv list -> cmd -> lv BatSet.t -> (cmd * lv BatSet.t) 
= fun lv_comps cmd used ->
  match cmd with
  | Assign (lv1, Lv lv2) when lv1 = lv2 -> (Skip, used)
  | Assign (lv, aexp) ->
    if not (BatSet.mem lv used) then (Skip, used)
    else
    (* used := (used - def) U use *)
      let used' = 
        (match lv with
        | Var x ->  
          (* error : arr_inc_one *)
          (*let used' = BatSet.filter (fun lv -> match lv with | ArrV (_,y) -> not (BatString.equal x y) | _ -> true) used in*)
            BatSet.union (uses_aexp lv_comps aexp) (BatSet.diff used (BatSet.singleton (Var x))) 
        | Arr (x,y) ->
          let new_uses = BatSet.add (Var y) (uses_aexp lv_comps aexp) in
            BatSet.union new_uses (BatSet.diff used (BatSet.singleton (Arr (x,y)))))
      in (cmd, used')
  | Skip -> (cmd, used)
  | Seq (c1,c2) -> 
    let (c2', used2') = remove_deadcode lv_comps c2 used in
    let (c1', used1') = remove_deadcode lv_comps c1 used2' in
      (Seq (c1',c2'), used1')
  | If (True,c1,_) -> remove_deadcode lv_comps c1 used  
  | If (False,_,c2) -> remove_deadcode lv_comps c2 used
  | If (b,c1,c2) ->
    let usedb = uses_bexp lv_comps b in 
    let (c1',used1') = remove_deadcode lv_comps c1 used in
    let (c2',used2') = remove_deadcode lv_comps c2 used in
      (If (b,c1',c2'), BatSet.union usedb (BatSet.union used1' used2'))
  | While (False,_) -> (Skip, used)
  | While (b,c) ->
    let loop_used = uses_cmd lv_comps cmd in
    let used' = BatSet.union used loop_used in
    let (c',used'') = remove_deadcode lv_comps c used' in
      (* BUG CHECK : used'' or used' ? *)
      (While (b,c'), used')
  | CHole _ -> (cmd, BatSet.of_list lv_comps) 

let deadcode_elimination : lv list -> pgm -> pgm
= fun lv_comps (args,cmd,res) ->
  let init_used = BatSet.singleton (Var res) in
  let (cmd',_) = remove_deadcode lv_comps cmd init_used in
    (args,cmd',res)

(******************************
 ******************************
    EXPRESSION REORDERING 
 ******************************
 ******************************)

let rec exp_reorder_aexp : aexp -> aexp
= fun aexp -> 
  match aexp with
  | BinOpLv (bop,lv1,lv2) when bop = Plus || bop = Mult -> 
    (match lv1,lv2 with
     | Var x,Var y when x > y -> BinOpLv (bop,lv2,lv1)
     | Arr (p,q),Arr (r,s) when BatString.equal p r && q > s -> BinOpLv (bop,lv2,lv1)
     | Arr (p,q),Arr (r,s) when p > r -> BinOpLv (bop,lv2,lv1) 
     | _ -> aexp)
  | _ -> aexp  

and exp_reorder_bexp : bexp -> bexp
= fun bexp -> 
  match bexp with
  | EqLv (lv1,lv2) ->
    (match lv1,lv2 with
     | Var x,Var y when x > y -> EqLv (lv2,lv1)
     | Arr (p,q),Arr (r,s) when BatString.equal p r && q > s -> EqLv (lv2,lv1)
     | Arr (p,q),Arr (r,s) when p > r -> EqLv (lv2,lv1)   
     | _ -> bexp)
  | Not b -> Not (exp_reorder_bexp b)
  | Or (b1,b2) -> Or (exp_reorder_bexp b1, exp_reorder_bexp b2)
  | And (b1,b2) -> And (exp_reorder_bexp b1, exp_reorder_bexp b2)
  | _ -> bexp

and exp_reorder_cmd : cmd -> cmd
= fun cmd ->
  match cmd with
  | Assign (lv,aexp) -> Assign (lv, exp_reorder_aexp aexp)
  | Skip -> Skip
  | Seq (c1,c2) -> Seq (exp_reorder_cmd c1, exp_reorder_cmd c2)
  | If (b,c1,c2) -> If (exp_reorder_bexp b, exp_reorder_cmd c1, exp_reorder_cmd c2)
  | While (b,c) -> While (exp_reorder_bexp b, exp_reorder_cmd c)
  | CHole n -> CHole n

let expression_reorder : pgm -> pgm
= fun (args,cmd,res) -> (args, exp_reorder_cmd cmd, res)  

let onestep_equivalence : lv list -> pgm -> pgm
= fun lv_comps pgm ->
  let pgm' = expression_simplification pgm in
  let pgm' = constant_propagation lv_comps pgm' in
  let pgm' = copy_propagation lv_comps pgm' in
  let pgm' = deadcode_elimination lv_comps pgm' in
  let pgm' = expression_reorder pgm' in
    pgm'

let rec equivalence : lv list -> pgm -> pgm 
= fun lv_comps pgm ->
    let (args,_,res) = pgm in
    try
      let pgm' = onestep_equivalence lv_comps pgm in
        if BatString.equal (ts_pgm_onerow pgm') (ts_pgm_onerow pgm) then pgm'
        else equivalence lv_comps pgm'
    with 
      | Not_found -> (args,Skip,res)
      | Division_by_zero -> (args,Skip,res)
