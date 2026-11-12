(* Exact access boundary for word comparisons; no scalar-provenance
   invariant is assumed. *)
Theory bodyPtrWordBuiltinsComparison
Ancestors
  ptrDiscipline venomInstProofs finite_map words contextCodegenRel codegenRel

Theorem access_ok_eq_vars:
  inst.inst_opcode = EQ /\ inst.inst_operands = [Var u; Var w] ==>
  (access_ok lo G fn inst s <=>
   (u NOTIN FDOM G /\ w NOTIN FDOM G) \/
   (?b sz x y.
      FLOOKUP G u = SOME (b,sz) /\ FLOOKUP G w = SOME (b,sz) /\
      0 < sz /\
      eval_operand (Var u) s = SOME x /\
      eval_operand (Var w) s = SOME y /\
      b <= w2n x /\ w2n x <= b + sz /\
      b <= w2n y /\ w2n y <= b + sz))
Proof
  strip_tac >>
  simp[access_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  metis_tac[]
QED

Theorem access_ok_eq_literal:
  inst.inst_opcode = EQ /\ inst.inst_operands = [Lit k; op] ==>
  access_ok lo G fn inst s
Proof
  simp[access_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def]
QED

Theorem access_ok_eq_shared_region:
  inst.inst_opcode = EQ /\ inst.inst_operands = [Var u; Var w] /\
  FLOOKUP G u = SOME (b,sz) /\ FLOOKUP G w = SOME (b,sz) /\
  0 < sz /\
  eval_operand (Var u) s = SOME x /\
  eval_operand (Var w) s = SOME y /\
  b <= w2n x /\ w2n x <= b + sz /\
  b <= w2n y /\ w2n y <= b + sz ==>
  access_ok lo G fn inst s
Proof
  strip_tac >> drule_all access_ok_eq_vars >>
  disch_then (fn th => rewrite_tac[th]) >> metis_tac[]
QED
