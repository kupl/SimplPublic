open Imp
open Vocab
open Options

let string_of_example : example -> string
= fun (input,output) ->
  let last = List.length input - 1 in
  let (_,str) = 
  List.fold_left (fun (cur,acc) value -> 
    if cur = last then (cur, acc ^ (value2str value))
    else (cur+1,acc ^ (value2str value) ^ ", ")) (0,"") input in
  str ^
  " -> " ^ value2str output

let print_examples exs =
  List.iter (fun ex -> print_endline (string_of_example ex)) exs

let make_lv_list : var list -> var list -> int list -> lv list
= fun int_var_comps arr_var_comps int_comps -> 
  List.fold_left (fun acc x -> (Var x)::acc) [] int_var_comps @
  List.fold_left (fun acc1 x ->
    acc1@(List.fold_left (fun acc2 y -> (Arr (x,y))::acc2) [] int_var_comps)
  ) [] arr_var_comps 

let main () =
  let usageMsg = "./main.native -input filename" in
  let _ = Arg.parse options (fun s->()) usageMsg in
  let file_channel = open_in !inputfile in
  let lexbuf = Lexing.from_channel file_channel in
  let (examples, pgm, int_comps, int_var_comps, arr_var_comps) = Parser.resource Lexer.start lexbuf in
  let lv_comps = make_lv_list int_var_comps arr_var_comps int_comps in
  if not !Options.simple then
    let _ = 
      print_endline "========== EXAMPLES ==========";
      print_examples examples;
      print_endline "===== INCOMPLETE PROGRAM =====";
      print_endline (ts_pgm_rows pgm);
      print_endline "========== PROCESSING =========" in
    let t0 = Sys.time () in
    let pgm = Synthesizer.synthesize examples pgm int_comps lv_comps in  
    let t1 = Sys.time () in
      begin
        match pgm with
        | None -> print_endline "Fail to Synthesize"
        | Some pgm -> 
          print_endline "========== EXAMPLES ==========";
          print_examples examples;
          print_endline "====== COMPLETE PROGRAM ======";
          print_endline (ts_pgm_rows pgm);
          print_endline "========== REPORT ==========";
          print_endline ("Iter : " ^ string_of_int !Synthesizer.iter);
          print_endline ("Time : " ^ string_of_float (t1 -. t0) ^ "seconds\n")
      end
  else
    let t0 = Sys.time () in
    let pgm = Synthesizer.synthesize examples pgm int_comps lv_comps in
    let t1 = Sys.time () in
      match pgm with
      | None -> print_endline "Fail to Synthesize"
      | Some pgm -> 
        print_endline ("Time : " ^ string_of_float (t1 -. t0) ^ "seconds\n")

let _ = main ()
