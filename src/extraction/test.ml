open Axioms32

(* TODO: projected runtime *)

type backtrace 
  = Cause of string
  | Assignment of string * string * backtrace
exception CounterExample of backtrace

let foundCounterExample bt = raise (CounterExample bt)

let wordsize = 8
let min_int = - (1 lsl (wordsize - 1))
let max_int = (1 lsl (wordsize - 1) - 1)

let print_config () =
  Printf.printf "Wordsize: %d\nMin. int: %d\nMax. int: %d\n\n" wordsize min_int max_int

let step_count = 1 lsl 20


let make_display () =
  let count = ref 0 in
  (fun i ->
      if i mod step_count = 0 then
        begin
          incr count;
(*          Printf.printf "%d/1024\n%!" !count; *)
        end)
  
let assign (v: string)(a: 'a)(p: 'a -> string)(k : 'a -> unit): unit =
  try
    k a
  with
  | CounterExample s -> foundCounterExample (Assignment (v, p a, s))
  

let forall var k =
  let progress = make_display () in
  for i = min_int to max_int do
    progress i;
    assign var i string_of_int k
  done

let rec ppbits xs = 
  match xs with
  | [] -> ""
  | true :: xs -> "1" ^ ppbits xs
  | false :: xs -> "0" ^ ppbits xs

let forall_bits var k =
  let rec help n acc k =
    match n with
    | 0 ->
       assign var acc ppbits k
    | _ -> 
       begin
         help (n-1) (true :: acc) k; 
         help (n-1) (false :: acc) k
       end
  in help wordsize [] k
    
let equal pp ls l r rs =
  if l <> r then
    foundCounterExample (Cause (Printf.sprintf "%s = %s != %s = %s" ls (pp l) (pp r) rs))

let fromInt32_cancel () =
  Printf.printf "forall i : Int32, toInt32 (fromInt32 i) = i";
  let progress = make_display () in
  forall "i" (fun i ->
    equal string_of_int "toInt32 (fromInt32 i)" (toInt32 (fromInt32 i)) i "i");
  Printf.printf "\nSuccess!\n"

let toInt32_cancel () =
  Printf.printf "forall bs : BITS 32, fromInt32 (toInt32 bs) = bs";
  forall_bits "bs" (fun bs -> 
    equal ppbits "fromInt32 (toInt32 bs)" (fromInt32 (toInt32 bs)) bs "bs");
  Printf.printf "\nSuccess!\n"

let native_reprP ls l r rs =
  if not (native_repr l r) then
    foundCounterExample (Cause (ls ^ " <> " ^ rs))

let zero_repr () =
  Printf.printf "native_repr 0 #0";
  native_reprP "0" 0 (fromNat Axioms32.wordsize O) "#0";
  Printf.printf "\nSuccess!\n"

let one_repr () =
  Printf.printf "native_repr 1 #1";
  native_reprP "1" 1 (fromNat Axioms32.wordsize (S O)) "#1";
  Printf.printf "\nSuccess!\n"

let succ i = if i = 127 then -128 else i + 1

let succ_repr () =
  Printf.printf "forall (i: Int8)(bs: BITS 8), native_repr i bs -> native_repr (succ i) (incB bs)";
  forall "i" (fun i ->
    let bs = fromInt32 i in
    native_reprP "succ i" (succ i)
                 (incB Axioms32.wordsize bs) "incB (fromInt32 i)");
  Printf.printf "\nSuccess!\n"

let comp_repr () =
  Printf.printf "forall (i i': Int8)(bs bs': BITS 8), native_repr i bs -> native_repr i' bs' -> (i = i') = (bs = bs')";
  forall "i" (fun i ->
    forall "i'" (fun i' ->
      List.iter (fun (lname, lcomp, compB, nameB) ->
        let bs = fromInt32 i in
        let bs' = fromInt32 i' in
        equal string_of_bool
          ("(i " ^ lname ^ " i')") (lcomp i i') 
          (compB bs bs') ("(fromInt32 i " ^ nameB ^ " fromInt32 i')"))
      [("<", (<), ltB Axioms32.wordsize, "ltB");
       ("=", (=), (=), "==")]));
  Printf.printf "\nSuccess!\n"

let neg x = if x = -128 then -128 else -x

let dec x = if x = -128 then 127 else x-1

let unop_repr () =
  Printf.printf "forall (i: Int8)(bs: BITS 8), native_repr i bs -> forall lop opB, native_repr (lop i) (opB bs)";
  forall "i" (fun i ->
    let bs = fromInt32 i in
    List.iter (fun (lname, lop, opB, name) ->
      native_reprP (lname ^ " i") (lop i) 
        (opB bs) (name ^ "(fromInt32 i)"))
      [("not", lnot, invB Axioms32.wordsize, "invB");
       ("neg", neg, negB Axioms32.wordsize, "negB");
       ("dec", dec, decB Axioms32.wordsize, "decB")]);
  Printf.printf "\nSuccess!\n"

let add_int8 x y = 
  let s = x + y in
  if s < -128 then 
    s + 256
  else if s > 127 then
    s - 256
  else 
    s

let binop_repr () =
  Printf.printf "forall (i i': Int8)(bs bs': BITS 8), native_repr i bs -> native_repr i' bs' -> forall lop opB, native_repr (lop i i') (opB bs bs')";
  forall "i" (fun i ->
    forall "i'" (fun i' ->
      let bs = fromInt32 i in
      let bs' = fromInt32 i' in
      List.iter (fun (lname, lop, opB, name) -> 
        native_reprP (lname ^ " i i'") (lop i i')
                     (opB bs bs') (name ^ " i i'"))
        [("(land)", (land), andB Axioms32.wordsize, "andB");
         ("(lor)", (lor), orB  Axioms32.wordsize, "orB");
         ("(lxor)", (lxor), xorB Axioms32.wordsize, "xorB");
         ("(+)", add_int8, (fun x y -> snd (adcB Axioms32.wordsize false x y)), "addB");
        ]));
  Printf.printf "\nSuccess!\n"

let forall_nat32 var k =
  let rec help acc = function
    | 0 -> 
       assign var (acc O) (fun _ -> "32") k
    | x ->
       begin
         assign var (acc O) (fun _ -> string_of_int (32 - x)) k;
         help (fun x -> S (acc x)) (x - 1)
       end
  in
  help (fun x -> x) 32
       

let shift_repr () =
  Printf.printf "forall (i: Int8)(bs: BITS 8)(n: nat), native_repr i bs -> forall lshift shiftB, native_repr (lshift l #n) (shiftB l n)";
  forall "i" (fun i ->
    forall_nat32 "n" (fun n ->
      let bs = fromInt32 i in
      let nInt = toInt32 (fromNat Axioms32.wordsize n) in
      List.iter (fun (lname, lop, opB, nameB) ->
        native_reprP (lname ^ " i n") (lop i nInt)
                    (opB bs n) (nameB ^ " i n"))
        [("(lsr)", (lsr), shrBn Axioms32.wordsize, "shrBn");
         ("(lsl)", (lsl), shlBn Axioms32.wordsize, "shlBn")]));
  Printf.printf "\nSuccess!\n"

let rec pprint_bt = function
  | Cause s -> Printf.printf "%s\n" s
  | Assignment (x, v, bt) -> 
     begin
       pprint_bt bt;
       Printf.printf "with %s = %s\n" x v;
     end



let _ =
  print_config();
  try
    fromInt32_cancel ();
    toInt32_cancel ();
    zero_repr ();
    one_repr ();
    succ_repr ();
    leq_repr ();
    unop_repr ();
    binop_repr ();
  with
  | CounterExample bt -> pprint_bt bt
  
