open Vocab
open Imp
open Abs
open Normalize

let iter = ref 0

type hole = A of aexp | B of bexp | C of cmd

module Workset = struct
  type work = pgm 
  
  module OrderedType = struct
    type t = work
    let compare (p1) (p2) =
    let c1,c2 = cost p1,cost p2 in
      if c1=c2 then 0 else
      if c1>c2 then 1
      else -1 
  end
  
  module Heap = BatHeap.Make (OrderedType)
  
  (* type of workset : heap * (string set) *)
  type t = Heap.t * string BatSet.t
  let empty = (Heap.empty, BatSet.empty)
  
  let explored : pgm -> t -> bool
  = fun pgm (_,sset) -> BatSet.mem (ts_pgm_onerow pgm) sset
  
  let add : work -> t -> t
  = fun pgm (heap,sset) -> 
    if explored pgm (heap,sset) then (heap,sset)
    else
      (Heap.add pgm heap, BatSet.add (ts_pgm_onerow pgm) sset)
  
  let choose : t -> (work * t) option
  = fun (heap,sset) ->
    try 
      let elem = Heap.find_min heap in
      Some (elem, (Heap.del_min heap, sset))
    with
      | _ -> None
  
  let workset_info : t -> string
  = fun (heap,sset) ->
    "To explore : " ^ (string_of_int (Heap.size heap)) ^
    " Explored : " ^ (string_of_int (BatSet.cardinal sset))
end

let is_solution : pgm -> example list -> bool
= fun pgm examples -> 
  List.for_all (fun (i,o) ->
    try
      Imp.run pgm i = o
    with
      | _ -> false
  ) examples
 
let gen_acandidates : int list -> lv list -> aexp BatSet.t
= fun int_comps lv_comps ->
  let s1 = List.fold_left (fun acc n -> BatSet.add (Int n) acc) BatSet.empty int_comps in
  let s2 = List.fold_left (fun acc lv -> BatSet.add (Lv lv) acc) BatSet.empty lv_comps in 
  let s3 =
    List.fold_left (fun acc1 lv1 ->
      BatSet.union acc1 (List.fold_left (fun acc2 lv2 -> BatSet.add (BinOpLv (Plus,lv1,lv2)) acc2) BatSet.empty lv_comps)
    ) BatSet.empty lv_comps in
  let s4 =
    List.fold_left (fun acc1 lv1 ->
      BatSet.union acc1 (List.fold_left (fun acc2 lv2 -> BatSet.add (BinOpLv (Minus,lv1,lv2)) acc2) BatSet.empty lv_comps)
    ) BatSet.empty lv_comps in
  let s5 =
    List.fold_left (fun acc1 lv1 ->
      BatSet.union acc1 (List.fold_left (fun acc2 lv2 -> BatSet.add (BinOpLv (Mult,lv1,lv2)) acc2) BatSet.empty lv_comps)
    ) BatSet.empty lv_comps in
  let s6 =
    List.fold_left (fun acc1 lv1 ->
      BatSet.union acc1 (List.fold_left (fun acc2 lv2 -> BatSet.add (BinOpLv (Div,lv1,lv2)) acc2) BatSet.empty lv_comps)
    ) BatSet.empty lv_comps in
  let s7 =
    List.fold_left (fun acc1 lv1 ->
      BatSet.union acc1 (List.fold_left (fun acc2 lv2 -> BatSet.add (BinOpLv (Mod,lv1,lv2)) acc2) BatSet.empty lv_comps)
    ) BatSet.empty lv_comps in
  let s8 =
    List.fold_left (fun acc1 lv ->
      BatSet.union acc1 (List.fold_left (fun acc2 n -> BatSet.add (BinOpN (Plus,lv,n)) acc2) BatSet.empty int_comps)
    ) BatSet.empty lv_comps in
  let s9 =
    List.fold_left (fun acc1 lv ->
      BatSet.union acc1 (List.fold_left (fun acc2 n -> BatSet.add (BinOpN (Minus,lv,n)) acc2) BatSet.empty int_comps)
    ) BatSet.empty lv_comps in
  let s10 =
    List.fold_left (fun acc1 lv ->
      BatSet.union acc1 (List.fold_left (fun acc2 n -> BatSet.add (BinOpN (Mult,lv,n)) acc2) BatSet.empty int_comps)
    ) BatSet.empty lv_comps in
  let s11 =
    List.fold_left (fun acc1 lv ->
      BatSet.union acc1 (List.fold_left (fun acc2 n -> BatSet.add (BinOpN (Div,lv,n)) acc2) BatSet.empty int_comps)
    ) BatSet.empty lv_comps in
  let s12 =
    List.fold_left (fun acc1 lv ->
      BatSet.union acc1 (List.fold_left (fun acc2 n -> BatSet.add (BinOpN (Mod,lv,n)) acc2) BatSet.empty int_comps)
    ) BatSet.empty lv_comps in
   BatSet.union s1 (BatSet.union s2 (BatSet.union s3 (BatSet.union s4 
  (BatSet.union s5 (BatSet.union s6 (BatSet.union s7 (BatSet.union s8 
  (BatSet.union s9 (BatSet.union s10 (BatSet.union s11 s12))))))))))

let gen_bcandidates : int list -> lv list -> bexp BatSet.t
= fun int_comps lv_comps -> 
  let s1 =
    List.fold_left (fun acc1 lv1 ->
      BatSet.union acc1 (List.fold_left (fun acc2 lv2 -> BatSet.add (GtLv (lv1,lv2)) acc2) BatSet.empty lv_comps)
    ) BatSet.empty lv_comps in
  let s2 =
    List.fold_left (fun acc1 lv1 ->
      BatSet.union acc1 (List.fold_left (fun acc2 lv2 -> BatSet.add (LtLv (lv1,lv2)) acc2) BatSet.empty lv_comps)
    ) BatSet.empty lv_comps in
  let s3 =
    List.fold_left (fun acc1 lv1 ->
      BatSet.union acc1 (List.fold_left (fun acc2 lv2 -> BatSet.add (EqLv (lv1,lv2)) acc2) BatSet.empty lv_comps)
    ) BatSet.empty lv_comps in
  let s4 =
    List.fold_left (fun acc1 lv ->
      BatSet.union acc1 (List.fold_left (fun acc2 n -> BatSet.add (GtN (lv,n)) acc2) BatSet.empty int_comps)
    ) BatSet.empty lv_comps in
  let s5 =
    List.fold_left (fun acc1 lv ->
      BatSet.union acc1 (List.fold_left (fun acc2 n -> BatSet.add (LtN (lv,n)) acc2) BatSet.empty int_comps)
    ) BatSet.empty lv_comps in
  let s6 =
    List.fold_left (fun acc1 lv ->
      BatSet.union acc1 (List.fold_left (fun acc2 n -> BatSet.add (EqN (lv,n)) acc2) BatSet.empty int_comps)
    ) BatSet.empty lv_comps in
  (BatSet.add True
  (BatSet.add False
  (BatSet.add (Not (bhole ()))
  (BatSet.add (Or (bhole (), bhole ()))  
  (BatSet.add (And (bhole (), bhole ())) 
  (BatSet.union s1 (BatSet.union s2 (BatSet.union s3 (BatSet.union s4 (BatSet.union s5 s6))))))))))

let gen_ccandidates : lv list -> cmd BatSet.t
= fun lv_comps ->
  let assign_set = List.fold_left (fun acc lv -> BatSet.add (Assign (lv,ahole ())) acc) BatSet.empty lv_comps in
  BatSet.add Skip (BatSet.add (Seq (chole (), chole ())) 
 (BatSet.add (If (bhole (),chole (),chole ())) 
 (BatSet.add (While (bhole (),chole ())) assign_set)))

let replace_a : pgm -> aexp -> aexp -> pgm 
= fun (args,cmd,res) ah acandi ->
  let rec replace_a' : cmd -> aexp -> aexp -> cmd
  = fun cmd ah acandi ->
    match cmd with
    | Assign (lv,aexp) when aexp = ah -> Assign (lv,acandi)
    | Seq (c1,c2) -> Seq (replace_a' c1 ah acandi, replace_a' c2 ah acandi)
    | If (b,c1,c2) -> If (b,replace_a' c1 ah acandi, replace_a' c2 ah acandi)
    | While (b,c) -> While (b, replace_a' c ah acandi)
    | _ -> cmd
  in (args,(replace_a' cmd ah acandi),res)

let replace_b : pgm -> bexp -> bexp -> pgm 
= fun (args,cmd,res) bh bcandi -> 
  let rec replace_b' : cmd -> bexp -> bexp -> cmd
  = fun cmd bh bcandi ->
    match cmd with
    | If (b,c1,c2) when b = bh -> If (bcandi,c1,c2)
    | If (b,c1,c2) -> If (b, replace_b' c1 bh bcandi, replace_b' c2 bh bcandi)
    | While (b,c) when b = bh -> While (bcandi,c)
    | While (b,c) -> While (b, replace_b' c bh bcandi)
    | Seq (c1,c2) -> Seq (replace_b' c1 bh bcandi, replace_b' c2 bh bcandi)
    | _ -> cmd
  in (args,(replace_b' cmd bh bcandi),res)

let replace_c : pgm -> cmd -> cmd -> pgm 
= fun (args,cmd,res) ch ccandi ->
  let rec replace_c' : cmd -> cmd -> cmd -> cmd
  = fun cmd ch ccandi ->
    match cmd with
    | CHole n when cmd = ch -> ccandi
    | Seq (c1,c2) -> Seq (replace_c' c1 ch ccandi, replace_c' c2 ch ccandi)
    | If (b,c1,c2) -> If (b,replace_c' c1 ch ccandi, replace_c' c2 ch ccandi)
    | While (b,c) -> While (b,replace_c' c ch ccandi)
    | _ -> cmd
  in (args,(replace_c' cmd ch ccandi),res)

let gen_nextstates_a : aexp BatSet.t -> (pgm * aexp) -> pgm BatSet.t  
= fun candidates (p,ah) -> 
  BatSet.fold (fun acandi acc -> 
    BatSet.add (replace_a p ah acandi) acc
  ) candidates BatSet.empty

let gen_nextstates_b : bexp BatSet.t -> (pgm * bexp) -> pgm BatSet.t 
= fun candidates (p,bh) ->
  BatSet.fold (fun bcandi acc -> 
    BatSet.add (replace_b p bh bcandi) acc
  ) candidates BatSet.empty

let gen_nextstates_c : cmd BatSet.t -> (pgm * cmd) -> pgm BatSet.t 
= fun candidates (p,ch) ->
  BatSet.fold (fun ccandi acc -> 
    BatSet.add (replace_c p ch ccandi) acc
  ) candidates BatSet.empty

let nextof_a : int list -> lv list -> pgm * aexp -> pgm BatSet.t
= fun int_comps lv_comps (p,ah) ->
  let candidates = gen_acandidates int_comps lv_comps in (* determined by transition rule *)
    gen_nextstates_a candidates (p,ah) 

let nextof_b : int list -> lv list -> pgm * bexp -> pgm BatSet.t
= fun int_comps lv_comps (p,bh) ->
  let candidates = gen_bcandidates int_comps lv_comps in
    gen_nextstates_b candidates (p,bh) 

let nextof_c : lv list -> pgm * cmd -> pgm BatSet.t 
= fun lv_comps (p,ch) ->
  let candidates = gen_ccandidates lv_comps in
    gen_nextstates_c candidates (p,ch) 
 
let nextof : int list -> lv list -> pgm * hole -> pgm BatSet.t 
= fun int_comps lv_comps (p,h) ->
  match h with
  | A ah -> nextof_a int_comps lv_comps (p,ah)
  | B bh -> nextof_b int_comps lv_comps (p,bh) 
  | C ch -> nextof_c lv_comps (p,ch)

let rec infinite_possible : pgm -> bool
= fun (_,cmd,_) -> infinite cmd

and infinite : cmd -> bool
= fun cmd ->
  match cmd with
  | Seq (c1,c2) 
  | If (_,c1,c2) -> infinite c1 || infinite c2
  | While (b,c) ->
    let cmd_list = list_of_cmd c in
    let (remaining_cmd,last_cmd) = BatList.split_at (List.length cmd_list - 1) cmd_list in
    let last_cmd = List.hd last_cmd in 
      cntvar_redefined b remaining_cmd || not (permitted_last b last_cmd) || infinite c
  | _ -> false 

(* if cannot be dtermined -> say true : to be conservative *)  
and permitted_last : bexp -> cmd -> bool
= fun bexp cmd ->
  match bexp, cmd with
  | BHole _,_
  | GtN _,CHole _ 
  | LtLv _,CHole _ -> true (* to wait *)
  | GtN (Var x,_),Assign (Var x',AHole _) 
    when BatString.equal x x' -> true (* to wait *) 
  | GtN (Var x,_),Assign (Var x',BinOpN (Minus, Var x'', n)) 
    when BatString.equal x x' && BatString.equal x' x'' && n>0 -> true
  | GtN (Var x,n),Assign (Var x',BinOpN (Div, Var x'', n'))
    when BatString.equal x x' && BatString.equal x' x'' && n>=0 && n'>1 -> true
  | LtLv (Var x,Var _),Assign (Var x',AHole _)
    when BatString.equal x x' -> true (* to wait *)
  | LtLv (Var x,Var _),Assign (Var x',BinOpN (Plus, Var x'', n))
    when BatString.equal x x' && BatString.equal x' x'' && n>0 -> true 
  | _ -> false

and cntvar_redefined : bexp -> cmd list -> bool
= fun bexp cmdlist ->
  let assign_set = List.fold_left (fun acc cmd ->
    match cmd with
    | Assign _ -> BatSet.add cmd acc
    | Seq (c1,c2)     
    | If (_,c1,c2) -> BatSet.union acc (BatSet.union (set_of_assign c1) (set_of_assign c2))
    | While (_,c) -> BatSet.union (set_of_assign c) acc
    | _ -> acc
  ) BatSet.empty cmdlist in
    begin
     match bexp with
      | GtN (lv,_) -> BatSet.exists (fun cmd -> match cmd with | Assign (lv',_) when lv = lv' -> true | _ -> false) assign_set 
      | LtLv (lv1,lv2) -> BatSet.exists (fun cmd -> match cmd with | Assign (lv,_) when lv = lv1 || lv = lv2 -> true | _ -> false) assign_set
      | _ -> false
    end

and set_of_assign : cmd -> cmd BatSet.t 
= fun cmd ->
  match cmd with
  | Assign _ -> BatSet.singleton cmd
  | Seq (c1,c2) 
  | If (_,c1,c2) -> BatSet.union (set_of_assign c1) (set_of_assign c2)
  | While (_,c) -> set_of_assign c
  | _ -> BatSet.empty

and list_of_cmd : cmd -> cmd list 
= fun cmd -> 
  match cmd with
  | Seq (c1,c2) -> (list_of_cmd c1)@(list_of_cmd c2)
  | _ -> [cmd]

let aholes : pgm -> aexp BatSet.t 
= fun (_,cmd,_) ->
  let rec aholes' : cmd -> aexp BatSet.t
  = fun cmd ->
    match cmd with
    | Assign (_,AHole n) -> BatSet.singleton (AHole n)
    | If (_,c1,c2)
    | Seq (c1,c2) -> BatSet.union (aholes' c1) (aholes' c2)
    | While (_,c) -> aholes' c
    | _ -> BatSet.empty
  in aholes' cmd


(* 2017.11.30. 
   Logical, small error fix. 
   It has little impact on the performance of the sas 2017 paper. *)

let bholes : pgm -> bexp BatSet.t
= fun (_,cmd,_) ->
  let rec bholes' : cmd -> bexp BatSet.t
  = fun cmd ->
    match cmd with
    | Seq (c1,c2) -> BatSet.union (bholes' c1) (bholes' c2)
    | If (b,c1,c2) -> BatSet.union (bholes'' b) (BatSet.union (bholes' c1) (bholes' c2)) 
    | While (b,c) -> BatSet.union (bholes'' b) (bholes' c)
    | _ -> BatSet.empty 
  and bholes'' : bexp -> bexp BatSet.t
  = fun bexp ->
    match bexp with 
    | Not b -> bholes'' b
    | Or (b1,b2) | And (b1,b2) -> BatSet.union (bholes'' b1) (bholes'' b2)
    | BHole _ -> BatSet.singleton bexp 
    | _ -> BatSet.empty 
  in bholes' cmd

let choles : pgm -> cmd BatSet.t
= fun (_,cmd,_) ->
  let rec choles' : cmd -> cmd BatSet.t 
  = fun cmd ->
    match cmd with
    | Seq (c1,c2) 
    | If (_,c1,c2) -> BatSet.union (choles' c1) (choles' c2)
    | While (_,c) -> choles' c
    | CHole n -> BatSet.singleton (CHole n)
    | _ -> BatSet.empty
  in choles' cmd

let next : int list -> lv list -> pgm -> pgm BatSet.t 
= fun int_comps lv_comps pgm ->
  let aholes = aholes pgm in
  let bholes = bholes pgm in
  let choles = choles pgm in
  let next_a = BatSet.fold (fun ah acc -> BatSet.union acc (nextof_a int_comps lv_comps (pgm,ah))) aholes BatSet.empty in
  let next_b = BatSet.fold (fun bh acc -> BatSet.union acc (nextof_b int_comps lv_comps (pgm,bh))) bholes BatSet.empty in
  let next_c = BatSet.fold (fun ch acc -> BatSet.union acc (nextof_c lv_comps (pgm,ch))) choles BatSet.empty in
    BatSet.union next_a (BatSet.union next_b next_c)

let is_closed : pgm -> bool
= fun pgm -> BatSet.is_empty (aholes pgm) && BatSet.is_empty (bholes pgm) && BatSet.is_empty (choles pgm)

let start_time = ref (Sys.time ())

let rec work : example list -> int list -> lv list -> Workset.t -> pgm option
= fun examples int_comps lv_comps workset ->
  iter := !iter + 1;
  if !iter mod 10000 = 0 && not !Options.simple
  then
    begin 
      print_string ("Iter : " ^ (string_of_int !iter) ^ " ");
      print_endline ((Workset.workset_info workset) ^ (" Total elapsed : " ^ (string_of_float (Sys.time () -. !start_time))))
    end;
  if Sys.time () -. !start_time > 3600.0 then None
  else
  match Workset.choose workset with
  | None -> None
  | Some (pgm, remaining_workset) ->
    if is_closed pgm then
      if is_solution pgm examples then Some (equivalence lv_comps pgm)
      else work examples int_comps lv_comps remaining_workset
    else 
      if Abs.hopeless pgm examples lv_comps then work examples int_comps lv_comps remaining_workset
      else 
        let nextstates = next int_comps lv_comps pgm in
        let nextstates = BatSet.filter (fun ns -> not (infinite_possible ns)) nextstates in
        let nextstates = BatSet.map (fun ns -> equivalence lv_comps ns) nextstates in
        let new_workset = BatSet.fold Workset.add nextstates remaining_workset in 
          work examples int_comps lv_comps new_workset
   
let synthesize : example list -> pgm -> int list -> lv list -> pgm option
= fun examples pgm int_comps lv_comps ->
  let workset = Workset.add pgm Workset.empty in
    work examples int_comps lv_comps workset
