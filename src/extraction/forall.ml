exception TestFailure of int ;;

let forall_int wordsize k =
  try
    for i = 0 to (1 lsl wordsize) - 1 do
      if (not (k i)) then
        raise (TestFailure i)
    done;
    true
  with (TestFailure i) -> Printf.printf "failed %d\n" i; false

let forall_int8 = forall_int 8
let forall_int16 = forall_int 16
let forall_int32 = forall_int 32

