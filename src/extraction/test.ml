(*
 * To try with 8, 16, 32bit, only these lines need to be replaced.
 * Note some definitions exported by Coq may need to be hidden.
 *)
open Axioms16
let bits_wordsize = wordsize
let wordsize = 16
let bitsFromInt = bitsFromInt16
let bitsToInt = bitsToInt16

type backtrace 
  = Cause of string
  | Assignment of string * string * backtrace
exception CounterExample of backtrace

let foundCounterExample bt = raise (CounterExample bt)

let min_int = 0
let max_int = (1 lsl wordsize) - 1
let wordmask = max_int

let print_config () =
  Printf.printf "Wordsize: %d\nMin. int: %d\nMax. int: %d\n\n" wordsize min_int max_int

let step_count = 1 lsl (wordsize - 7)

let make_display () =
  let count = ref 0 in
  (fun i ->
      if i mod step_count = 0 then
        begin
          incr count;
          (*Printf.printf "%d/128\n" !count;*)
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

let bitsToIntK_test () =
  Printf.printf "bitsToIntK_test";
  forall_bits "bs" (fun bs -> 
    equal ppbits "bitsFromInt (bitsToInt bs)" (bitsFromInt (bitsToInt bs)) bs "bs");
  Printf.printf "\nSuccess!\n"; flush stdout

let bitsFromInt_inj () =
  Printf.printf "bitsFromInt_inj";
  forall "i" (fun i ->
    forall "i'" (fun i' ->
      let bs = bitsFromInt i in
      let bs' = bitsFromInt i' in
      if (bs = bs' && i <> i') then
        foundCounterExample (Cause (Printf.sprintf "bs = bs' -> i = %s != %s = i'" (string_of_int i) (string_of_int i')))));
  Printf.printf "\nSuccess!\n"; flush stdout

let native_reprP ls l r rs =
  if not (native_repr l r) then
    foundCounterExample (Cause (ls ^ " <> " ^ rs))

let zero_repr () =
  Printf.printf "native_repr 0 #0";
  native_reprP "0" 0 (fromNat bits_wordsize O) "#0";
  Printf.printf "\nSuccess!\n"; flush stdout

let one_repr () =
  Printf.printf "native_repr 1 #1";
  native_reprP "1" 1 (fromNat bits_wordsize (S O)) "#1";
  Printf.printf "\nSuccess!\n"; flush stdout

let succ = fun x -> (x + 1) land wordmask

let neg = fun x -> (-x) land wordmask

let not_int = fun x -> (lnot x) land wordmask

let dec = fun x -> (x - 1) land wordmask

let unop_repr () =
  Printf.printf "forall (i: Int8)(bs: BITS 8), native_repr i bs -> forall lop opB, native_repr (lop i) (opB bs)";
  forall "i" (fun i ->
    let bs = bitsFromInt i in
    List.iter (fun (lname, lop, opB, name) ->
      native_reprP (lname ^ " i") (lop i) 
        (opB bs) (name ^ "(bitsFromInt i)"))
      [("succ", succ, incB bits_wordsize, "incB");
       ("not", not_int, invB bits_wordsize, "invB");
       ("neg", neg, negB bits_wordsize, "negB");
       ("dec", dec, decB bits_wordsize, "decB")]);
  Printf.printf "\nSuccess!\n"; flush stdout

let add_int = fun x y -> (x + y) land wordmask

let binop_repr () =
  Printf.printf "forall (i i': Int8)(bs bs': BITS 8), native_repr i bs -> native_repr i' bs' -> forall lop opB, native_repr (lop i i') (opB bs bs')";
  forall "i" (fun i ->
    forall "i'" (fun i' ->
      let bs = bitsFromInt i in
      let bs' = bitsFromInt i' in
      List.iter (fun (lname, lop, opB, name) -> 
        native_reprP (lname ^ " i i'") (lop i i')
                     (opB bs bs') (name ^ " i i'"))
        [("(land)", (land), andB bits_wordsize, "andB");
         ("(lor)", (lor), orB  bits_wordsize, "orB");
         ("(lxor)", (lxor), xorB bits_wordsize, "xorB");
         ("(+)", add_int, (fun x y -> snd (adcB bits_wordsize false x y)), "addB");
        ]));
  Printf.printf "\nSuccess!\n"; flush stdout

let forall_nat var k =
  let rec help acc = function
    | 0 -> 
       assign var (acc O) (fun _ -> string_of_int wordsize) k
    | x ->
       begin
         assign var (acc O) (fun _ -> string_of_int (wordsize - x)) k;
         help (fun x -> S (acc x)) (x - 1)
       end
  in
  help (fun x -> x) wordsize

let lsl_int = fun x y -> (x lsl y) land wordmask

let shift_repr () =
  Printf.printf "forall (i: Int8)(bs: BITS 8)(n: nat), native_repr i bs -> forall lshift shiftB, native_repr (lshift l #n) (shiftB l n)";
  forall "i" (fun i ->
    forall_nat "n" (fun n ->
      let bs = bitsFromInt i in
      let nInt = bitsToInt (fromNat bits_wordsize n) in
      List.iter (fun (lname, lop, opB, nameB) ->
        native_reprP (lname ^ " i n") (lop i nInt)
                    (opB bs n) (nameB ^ " i n"))
        [("(lsr)", (lsr), shrBn bits_wordsize, "shrBn");
         ("(lsl)", lsl_int, shlBn bits_wordsize, "shlBn")]));
  Printf.printf "\nSuccess!\n"; flush stdout

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
    bitsToIntK_test ();
    bitsFromInt_inj ();
    zero_repr ();
    one_repr ();
    unop_repr ();
    binop_repr ();
    shift_repr ()
  with
  | CounterExample bt -> pprint_bt bt
  
