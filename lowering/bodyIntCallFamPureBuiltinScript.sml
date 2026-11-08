(* Seam 2 joint induction, a family leaf of the pure step: builtins other than array/tuple literals, and type builtins. *)
Theory bodyIntCallFamPureBuiltin
Ancestors
  bodyIntCallJointContract

Theorem intcall_pure_builtin_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ((?a b args. e = Builtin a b args /\ !t n. b <> MakeArray t n) \/
   (?a tb ty args. e = TypeBuiltin a tb ty args)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
