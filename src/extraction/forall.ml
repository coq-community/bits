exception TestFailure of int ;;

let forall_int wordsize k =
  try
    for i = 0 to (1 lsl wordsize) - 1 do
      if (not (k i)) then
        raise (TestFailure i)
    done;
    true
  with (TestFailure i) -> Printf.printf "failed %d\n" i; false
