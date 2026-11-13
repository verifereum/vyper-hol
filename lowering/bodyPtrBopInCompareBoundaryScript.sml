Theory bodyPtrBopInCompareBoundary
Ancestors
  ptrDiscipline finite_map

(* Comparison of provenance-bearing operands requires one common site. *)
Theorem different_sites_comparison_access_rejected:
  !lo G fn inst s u w b1 sz1 b2 sz2.
    (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
     inst.inst_opcode = EQ) /\
    inst.inst_operands = [Var u; Var w] /\
    FLOOKUP G u = SOME (b1,sz1) /\
    FLOOKUP G w = SOME (b2,sz2) /\
    (b1,sz1) <> (b2,sz2) ==> ~access_ok lo G fn inst s
Proof
  rpt strip_tac >>
  fs[access_ok_def] >>
  `u IN FDOM G` by metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  first_x_assum (qspecl_then [`u`, `w`] mp_tac) >> simp[]
QED
