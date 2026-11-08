(* Seam 2 joint induction, a family leaf of the pure step: names, top-level names, flag members, literals and ternaries. *)
Theory bodyIntCallFamPureAtom
Ancestors
  bodyIntCallJointContract

Theorem intcall_pure_atom_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ((?ty x. e = Name ty x) \/ (?ty n. e = TopLevelName ty n) \/
   (?ty n m. e = FlagMember ty n m) \/ (?ty l. e = Literal ty l) \/
   (?ty c e1 e2. e = IfExp ty c e1 e2)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
