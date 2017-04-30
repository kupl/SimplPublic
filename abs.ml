open Imp
open Itv
open Vocab
open Symbolic

(* Complete Lattice : interval domain *)

type absloc = var
type absval = Itv.t * Symbolic.t  

let v_top = (Itv.top, Symbolic.top)

module State = struct 
  type t = (absloc,absval) BatMap.t

  let bot = BatMap.empty 

  let add = BatMap.add

  (*
  let find x s =
    try BatMap.find x s with _ -> raise Not_found *)
  let find x s =
    try BatMap.find x s with _ -> (Itv.bot, Symbolic.bot)

  let weak_add x v s =
    let (i1,s1) = find x s in 
    let (i2,s2) = v in
    let res = (Itv.join i1 i2, Symbolic.join s1 s2) in
      add x res s

  let fst_of_val (itv,_) = itv
  let snd_of_val (_,sym) = sym

  let join : t -> t -> t
  = fun state1 state2 -> 
    let join' key opt_d1 opt_d2 = 
      match opt_d1,opt_d2 with
      | None,None -> None
      | None,Some (itv,sym)
      | Some (itv,sym),None -> Some (itv,sym)
      | Some (itv1,sym1),Some (itv2,sym2) -> Some (Itv.join itv1 itv2, Symbolic.join sym1 sym2)
    in BatMap.merge join' state1 state2

  let widen : t -> t -> t
  = fun state1 state2 ->
    let widen' key opt_d1 opt_d2 =
      match opt_d1,opt_d2 with
      | None,None -> None
      | None,Some (itv,sym)
      | Some (itv,sym),None -> Some (itv,Symbolic.top) (* 170208 : should be updated into git *)
      | Some (itv1,sym1),Some (itv2,sym2) -> Some (Itv.widen itv1 itv2, Symbolic.join sym1 sym2)
    in BatMap.merge widen' state1 state2

  let meet : t -> t -> t
  = fun state1 state2 ->
    let meet' key opt_d1 opt_d2 =
      match opt_d1,opt_d2 with
      | None,None 
      | None,Some _
      | Some _,None -> None
      | Some (itv1,sym1),Some (itv2,sym2) -> Some (Itv.meet itv1 itv2, Symbolic.meet sym1 sym2)
    in BatMap.merge meet' state1 state2

  let le : t -> t -> bool 
  = fun state1 state2 ->
    if state1 == state2 then true else
      let enum1 = BatMap.enum state1 in
      let enum2 = BatMap.enum state2 in
      let rec loop : (absloc * absval) option -> (absloc * absval) option -> bool
      = fun e1 e2 ->
        match e1,e2 with
        | Some (k1, (itv1,sym1)),Some (k2, (itv2,sym2)) ->
            if k1 = k2 && Itv.le itv1 itv2 && Symbolic.le sym1 sym2  
              then loop (BatEnum.get enum1) (BatEnum.get enum2) 
            else false 
        | Some _,None -> false
        | None,Some _ -> true
        | None,None -> true in
    loop (BatEnum.get enum1) (BatEnum.get enum2)
end

type buf = int

let dump = Hashtbl.create 30 (* memory for array size *) 

let add_dump : var -> value -> unit
= fun x v ->
  match v with
  | VInt _ -> ()
  | VArr lst -> Hashtbl.add dump x (List.length lst)

let reset_dump = Hashtbl.reset dump

let rec absloc_of_lv : lv -> State.t -> absloc
= fun lv state -> 
  match lv with 
  | Var x -> x 
  | Arr (x,y) -> 
    let buf = Hashtbl.find dump x in 
    let idx = State.fst_of_val (State.find (absloc_of_lv (Var y) state) state) in
      (match idx with
      | Itv (lb,_) -> if Itv.le' (V buf) lb then raise BufferOverFlow else x
      | _ -> raise (Failure "abs.ml - idx value is bottom"))
      
(***************************************
 ***************************************
 Semantic functions for Interval domain 
 ***************************************
 ***************************************)

let rec itv_eval_aexp : aexp -> State.t -> Itv.t
= fun aexp state ->
  match aexp with
  | Int n -> Itv.int2itv n 
  | Lv lv -> State.fst_of_val (State.find (absloc_of_lv lv state) state)
  | BinOpLv (bop, lv1, lv2) -> itv_eval_bop bop (itv_eval_aexp (Lv lv1) state) (itv_eval_aexp (Lv lv2) state)
  | BinOpN  (bop, lv, n)    -> itv_eval_bop bop (itv_eval_aexp (Lv lv) state)  (itv_eval_aexp (Int n) state)
  | AHole _ -> Itv.top

and itv_eval_bop : bop -> Itv.t -> Itv.t -> Itv.t
= fun bop v1 v2 ->
  match bop with
  | Plus  -> Itv.plus   v1 v2
  | Minus -> Itv.minus  v1 v2
  | Mult  -> Itv.times  v1 v2
  | Div   -> Itv.divide v1 v2
  | Mod   -> Itv.modulo v1 v2

(***************************************
 ***************************************
 Semantic functions for Interval domain 
 ***************************************
 ***************************************)

let rec sym_eval_aexp : aexp -> State.t -> Symbolic.t
= fun aexp state ->
  match aexp with
  | Int n -> Sym (SInt n)
  | Lv lv -> State.snd_of_val (State.find (absloc_of_lv lv state) state) 
  | BinOpLv (bop, lv1, lv2) -> sym_eval_bop bop (sym_eval_aexp (Lv lv1) state) (sym_eval_aexp (Lv lv2) state)
  | BinOpN  (bop, lv,  n)   -> sym_eval_bop bop (sym_eval_aexp (Lv lv) state) (sym_eval_aexp (Int n) state) 
  | AHole _ -> Symbolic.top 

and sym_eval_bop : bop -> Symbolic.t -> Symbolic.t -> Symbolic.t
= fun bop v1 v2 ->
  match bop with
  | Plus  -> Symbolic.plus   v1 v2
  | Minus -> Symbolic.minus  v1 v2
  | Mult  -> Symbolic.times  v1 v2 
  | Div   -> Symbolic.divide v1 v2
  | Mod   -> Symbolic.modulo v1 v2


(***************************************
 ***************************************
 Component wise aexp semantics 
 ***************************************
 ***************************************)

let rec abs_eval_aexp : aexp -> State.t -> absval
= fun aexp state -> (itv_eval_aexp aexp state, sym_eval_aexp aexp state) 

type absbool = BTop | BTrue | BFalse | BBot 

let rec abs_eval_bexp : bexp -> State.t -> absbool
= fun bexp state ->
  match bexp with
  | True -> BTrue
  | False -> BFalse
  | GtLv (lv1,lv2) ->
    (try
      let lv1_itv = State.fst_of_val (abs_eval_aexp (Lv lv1) state) in
      let lv2_itv = State.fst_of_val (abs_eval_aexp (Lv lv2) state) in
        if Itv.concrete_le lv1_itv lv2_itv then BFalse else
        if Itv.concrete_gt lv1_itv lv2_itv then BTrue 
        else BTop
    with
      | Not_found -> BBot) 
  | GtN (lv,n) ->
    (try 
      let lv_itv = State.fst_of_val (abs_eval_aexp (Lv lv) state) in 
      let n_itv = State.fst_of_val (abs_eval_aexp (Int n) state) in
        if Itv.concrete_le lv_itv n_itv then BFalse else
        if Itv.concrete_gt lv_itv n_itv then BTrue
        else BTop
     with
       | Not_found -> BBot)
  | LtLv (lv1,lv2) ->
    (try
      let lv1_itv = State.fst_of_val (abs_eval_aexp (Lv lv1) state) in
      let lv2_itv = State.fst_of_val (abs_eval_aexp (Lv lv2) state) in
        if Itv.concrete_ge lv1_itv lv2_itv then BFalse else
        if Itv.concrete_lt lv1_itv lv2_itv then BTrue 
        else BTop 
     with
       | Not_found -> BBot)
  | LtN (lv,n) -> 
    (try
       let lv_itv = State.fst_of_val (abs_eval_aexp (Lv lv) state) in
       let n_itv = State.fst_of_val (abs_eval_aexp (Int n) state) in  
         if Itv.concrete_ge lv_itv n_itv then BFalse else
         if Itv.concrete_lt lv_itv n_itv then BTrue 
         else BTop
     with
       | Not_found -> BBot)
  | EqLv (lv1,lv2) ->
    (try
      let lv1_itv = State.fst_of_val (abs_eval_aexp (Lv lv1) state) in
      let lv2_itv = State.fst_of_val (abs_eval_aexp (Lv lv2) state) in
        if Itv.concrete_neq lv1_itv lv2_itv then BFalse 
        else BTop
     with 
       | Not_found -> BBot)
  | EqN (lv,n) ->
    (try
      let lv_itv = State.fst_of_val (abs_eval_aexp (Lv lv) state) in
      let n_itv = State.fst_of_val (abs_eval_aexp (Int n) state) in
        if Itv.concrete_neq lv_itv n_itv then BFalse 
        else BTop
     with
       | Not_found -> BBot)
  | Not b -> neg_abs_eval_bexp b state
  | Or (b1,b2) ->
    (match abs_eval_bexp b1 state, abs_eval_bexp b2 state with
     | BBot,_
     | _,BBot -> BBot
     | BTrue,_ -> BTrue
     | _,BTrue -> BTrue
     | BFalse,BFalse -> BFalse
     | _ -> BTop)
  | And (b1,b2) ->
    (match abs_eval_bexp b1 state, abs_eval_bexp b2 state with
     | BBot,_
     | _,BBot -> BBot
     | BFalse,_
     | _,BFalse -> BFalse
     | BTrue,BTrue -> BTrue
     | _ -> BTop)
  | BHole _ -> BTop 

and neg_abs_eval_bexp : bexp -> State.t -> absbool
= fun bexp state ->
  match bexp with
  | True           -> abs_eval_bexp False state
  | False          -> abs_eval_bexp True state
  | GtLv (lv1,lv2) -> abs_eval_bexp (Or (LtLv (lv1,lv2), EqLv (lv1,lv2))) state 
  | GtN  (lv,n)    -> abs_eval_bexp (Or (LtN (lv,n), EqN (lv,n))) state 
  | LtLv (lv1,lv2) -> abs_eval_bexp (Or (GtLv (lv1,lv2), EqLv (lv1,lv2))) state 
  | LtN  (lv,n)    -> abs_eval_bexp (Or (GtN (lv,n), EqN (lv,n))) state 
  | EqLv (lv1,lv2) -> abs_eval_bexp (Or (GtLv (lv1,lv2), LtLv (lv1,lv2))) state 
  | EqN  (lv,n)    -> abs_eval_bexp (Or (GtN (lv,n), LtN (lv,n))) state 
  | Not  b         -> abs_eval_bexp b state
  | Or   (b1,b2)   -> abs_eval_bexp (And (Not b1, Not b2)) state 
  | And  (b1,b2)   -> abs_eval_bexp (Or (Not b1, Not b2)) state  
  | BHole n        -> abs_eval_bexp (BHole n) state

let rec prune_by : bexp -> State.t -> State.t 
= fun bexp state ->
  match abs_eval_bexp bexp state with
  | BBot -> State.bot
  | BFalse -> State.bot
  | BTrue -> state
  | BTop -> 
    (match bexp with
     | True -> state
     | False -> State.bot 
     | GtLv (lv1,lv2) ->
       let (lv1_itv, lv1_sym) = abs_eval_aexp (Lv lv1) state in
       let (lv2_itv, lv2_sym) = abs_eval_aexp (Lv lv2) state in
       let meet_lv1 = Itv.meet lv1_itv (Itv.lower_to_pinf (Itv.itv_inc_one lv2_itv)) in
       let meet_lv2 = Itv.meet lv2_itv (Itv.ninf_to_upper (Itv.itv_dec_one lv1_itv)) in
       let state' = State.add (absloc_of_lv lv1 state) (meet_lv1, lv1_sym) state in
       let state'' = State.add (absloc_of_lv lv2 state) (meet_lv2, lv2_sym) state' in
         state''
     | GtN (lv,n) ->
       let (lv_itv, lv_sym) = abs_eval_aexp (Lv lv) state in
       let n_itv = State.fst_of_val (abs_eval_aexp (Int n) state) in
       let meet = Itv.meet lv_itv (Itv.lower_to_pinf (Itv.itv_inc_one n_itv)) in
       let state' = State.add (absloc_of_lv lv state) (meet, lv_sym) state in
         state'
     | LtLv (lv1,lv2) ->
       let (lv1_itv, lv1_sym) = abs_eval_aexp (Lv lv1) state in
       let (lv2_itv, lv2_sym) = abs_eval_aexp (Lv lv2) state in
       let meet_lv1 = Itv.meet lv1_itv (Itv.ninf_to_upper (Itv.itv_dec_one lv2_itv)) in
       let meet_lv2 = Itv.meet lv2_itv (Itv.lower_to_pinf (Itv.itv_inc_one lv1_itv)) in
       let state' = State.add (absloc_of_lv lv1 state) (meet_lv1, lv1_sym) state in
       let state'' = State.add (absloc_of_lv lv2 state) (meet_lv2, lv2_sym) state' in
         state''
     | LtN (lv,n) ->
       let (lv_itv, lv_sym) = abs_eval_aexp (Lv lv) state in
       let n_itv = State.fst_of_val (abs_eval_aexp (Int n) state) in
       let meet = Itv.meet lv_itv (Itv.ninf_to_upper (Itv.itv_dec_one n_itv)) in
       let state' = State.add (absloc_of_lv lv state) (meet, lv_sym) state in
         state'
     | EqLv (lv1,lv2) ->
       let (lv1_itv, lv1_sym) = abs_eval_aexp (Lv lv1) state in
       let (lv2_itv, lv2_sym) = abs_eval_aexp (Lv lv2) state in
       let meet = Itv.meet lv1_itv lv2_itv in
       let state' = State.add (absloc_of_lv lv1 state) (meet, lv1_sym) state in
       let state'' = State.add (absloc_of_lv lv2 state) (meet, lv2_sym) state' in
         state''
     | EqN (lv,n) ->
       let (lv_itv, lv_sym) = abs_eval_aexp (Lv lv) state in
       let n_itv = State.fst_of_val (abs_eval_aexp (Int n) state) in
       let meet = Itv.meet lv_itv n_itv in
       let state' = State.add (absloc_of_lv lv state) (meet, lv_sym) state in
         state'
     | Not b -> neg_prune_by b state 
     | Or (b1,b2) -> State.join (prune_by b1 state) (prune_by b2 state)
     | And (b1,b2) -> State.meet (prune_by b1 state) (prune_by b2 state)
     | BHole _ -> state)

and neg_prune_by : bexp -> State.t -> State.t 
= fun bexp state ->
  match bexp with
  | True           -> prune_by False state
  | False          -> prune_by True state
  | GtLv (lv1,lv2) -> prune_by (Or (LtLv (lv1,lv2), EqLv (lv1,lv2))) state 
  | GtN  (lv,n)    -> prune_by (Or (LtN (lv,n), EqN (lv,n))) state 
  | LtLv (lv1,lv2) -> prune_by (Or (GtLv (lv1,lv2), EqLv (lv1,lv2))) state 
  | LtN  (lv,n)    -> prune_by (Or (GtN (lv,n), EqN (lv,n))) state 
  | EqLv (lv1,lv2) -> prune_by (Or (GtLv (lv1,lv2), LtLv (lv1,lv2))) state 
  | EqN  (lv,n)    -> prune_by (Or (GtN (lv,n), LtN (lv,n))) state 
  | Not  b         -> prune_by b state
  | Or   (b1,b2)   -> prune_by (And (Not b1, Not b2)) state 
  | And  (b1,b2)   -> prune_by (Or (Not b1, Not b2)) state  
  | BHole n        -> prune_by (BHole n) state

type upperop = Join | Widen 

let rec abs_eval_cmd : lv list -> int -> cmd -> State.t -> State.t
= fun lv_comps cnt cmd state ->
  match cmd with
  | Assign (lv,AHole _) ->
    (match lv with
     | Var x -> State.add (absloc_of_lv lv state) (Itv.top,Sym (SVar x)) state
     | Arr (x,y) -> State.weak_add (absloc_of_lv lv state) (Itv.top,Symbolic.top) state)
  | Assign (lv,aexp) -> 
    (match lv with
     | Var x -> State.add (absloc_of_lv lv state) (abs_eval_aexp aexp state) state
     | Arr (x,y) -> State.weak_add (absloc_of_lv lv state) (abs_eval_aexp aexp state) state) (* must be weak update *)
  | Seq (c1,c2) -> abs_eval_cmd lv_comps cnt c2 (abs_eval_cmd lv_comps cnt c1 state)
  | If (b,c1,c2) -> cond lv_comps (2, b, c1, c2) state 
  | While (b,c) ->
    let next = cond lv_comps (cnt, b, c, Skip) state in
    (*let _ = BatMap.iter (fun x (itv,sym) -> print_endline (x ^ " -> " ^ (Itv.to_string itv) ^ ", " ^ (Symbolic.to_string sym))) next in*)
      if State.le next state then prune_by (Not b) next 
      else abs_eval_cmd lv_comps (cnt-1) (While (b,c)) next 
  | Skip -> state
  | CHole _ -> 
    List.fold_left (fun state lv ->
      match lv with
      | Var x -> State.add x (Itv.top, Sym (SVar x)) state
      | Arr (x,y) -> State.weak_add x (Itv.top,Symbolic.top) state) state lv_comps

and cond : lv list -> (int * bexp * cmd * cmd) -> State.t -> State.t
= fun lv_comps (cnt,b,c1,c2) state ->
  match abs_eval_bexp b state with
  | BBot -> State.bot
  | BFalse -> abs_eval_cmd lv_comps cnt c2 (prune_by (Not b) state)
  | BTrue ->
    if cnt>=0 then abs_eval_cmd lv_comps cnt c1 (prune_by b state)
    else
      State.widen 
       (abs_eval_cmd lv_comps cnt c2 (prune_by (Not b) state)) 
       (abs_eval_cmd lv_comps cnt c1 (prune_by b state))
    (*
       let s1 =  (abs_eval_cmd lv_comps cnt c2 state) in
       let s2 = (abs_eval_cmd lv_comps cnt c1  state) in
       let w = State.widen s1 s2 in  
       let _ = BatMap.iter (fun x (itv,sym) -> print_endline (x ^ " ->1 " ^ (Itv.to_string itv) ^ ", " ^ (Symbolic.to_string sym))) (prune_by (Not b) state) in
       let _ = BatMap.iter (fun x (itv,sym) -> print_endline (x ^ " ->2 " ^ (Itv.to_string itv) ^ ", " ^ (Symbolic.to_string sym))) s2 in
       let _ = BatMap.iter (fun x (itv,sym) -> print_endline (x ^ " ->3 " ^ (Itv.to_string itv) ^ ", " ^ (Symbolic.to_string sym))) w in
       let _ = print_endline "" in
       w
   *)
  | BTop ->
    if cnt>=0 then
      State.join
        (abs_eval_cmd lv_comps cnt c2 (prune_by (Not b) state))
        (abs_eval_cmd lv_comps cnt c1 (prune_by b state))
    else
      State.widen
        (abs_eval_cmd lv_comps cnt c2 (prune_by (Not b) state))
        (abs_eval_cmd lv_comps cnt c1 (prune_by b state))

let value2absval : value -> absval
= fun v ->
  match v with
  | VInt n -> (Itv (V n, V n), Sym (SInt n)) 
  | VArr lst ->
    let min, max = min lst, max lst in
      (Itv (V min, V max), Symbolic.top)

let loop_counter = 3

let abs_run : pgm -> value list -> lv list -> absval 
= fun (args,cmd,res) input_params lv_comps ->
  let _ = List.iter2 (fun x v -> add_dump x v) args input_params in 
  let init_state = List.fold_left2 (fun state x v -> State.add x (value2absval v) state) BatMap.empty args input_params in
  let final = State.find res (abs_eval_cmd lv_comps loop_counter cmd init_state) in
  let _ = reset_dump in
    final

let absval_profile : pgm -> absval -> absval -> unit
= fun pgm (goal_itv,goal_sym) (res_itv,res_sym) ->
  print_endline (ts_pgm_onerow pgm);
  print_endline ("Goal itv : " ^ (Itv.to_string goal_itv));
  print_endline ("Result itv : " ^ (Itv.to_string res_itv));
  print_endline ("Goal sym : " ^ (Symbolic.to_string goal_sym));
  print_endline ("Result sym " ^ (Symbolic.to_string res_sym));
  print_endline "" 

let rec hopeless : pgm -> example list -> lv list -> bool
= fun pgm examples lv_comps ->
  List.exists (fun (i,o) ->
    try
      let goal = value2absval o in
      let (goal_itv,goal_sym) = goal in
      let res = abs_run pgm i lv_comps in
      let (res_itv,res_sym) = res in
        if not (Itv.le goal_itv res_itv) then true else
        if not (Symbolic.sat_le goal_sym res_sym) then true else
          false 
    with
      | Not_found -> true
      | BufferOverFlow -> true
      | Division_by_zero -> true 
      | _ -> false
  ) examples
