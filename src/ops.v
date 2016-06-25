Module Logical.
Module Op.

Class not_of int := not_op : int -> int.
Class or_of int := or_op : int -> int -> int.
Class and_of int := and_op : int -> int -> int.
Class xor_of int := xor_op : int -> int -> int.
Class shl_of int := shl_op : int -> int -> int.
Class shr_of int := shr_op : int -> int -> int.

End Op.
End Logical.

Import Logical.Op.

Typeclasses Transparent not_of or_of and_of xor_of shl_of shr_of.

Notation "~%C"    := not_op.
Notation "~ x"    := (not_op x)     : computable_scope.
Notation "||%C"   := or_op.
Notation "x || y" := (or_op x y)   : computable_scope.
Notation "&&%C"   := and_op.
Notation "x && y" := (and_op x y)   : computable_scope.
Notation "^^%C"    := xor_op.
Notation "x ^^ y"  := (xor_op x y)
 (at level 30, right associativity) : computable_scope.
Notation ">>%C"    := shr_op.
Notation "x >> y"  := (shr_op x y) 
 (at level 30, right associativity) : computable_scope.
Notation "<<%C"    := shl_op.
Notation "x << y"  := (shl_op x y) 
 (at level 30, right associativity) : computable_scope.

