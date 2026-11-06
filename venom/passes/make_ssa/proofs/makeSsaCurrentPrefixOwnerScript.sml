Theory makeSsaCurrentPrefixOwner
Ancestors
  makeSsaCurrentPrefixMaps

Theorem current_prefix_pull_owner:
  current_prefix_functional owner /\
  (!z x. R z x ==> owner z x) /\
  (!d src. inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [d] /\
    inst.inst_operands = [Var src] ==> ?v. owner d v /\ owner src v) ==>
  !z x. current_prefix_pull inst R z x ==> owner z x
Proof
  simp[current_prefix_pull_def, current_prefix_functional_def] >> metis_tac[]
QED

Theorem current_prefix_back_owner:
  !xs M owner.
  current_prefix_functional owner /\
  (!z x. FLOOKUP M z = SOME x ==> owner z x) /\
  (!inst d src. MEM inst xs /\ inst.inst_opcode = ASSIGN /\
    inst.inst_outputs = [d] /\ inst.inst_operands = [Var src] ==>
    ?v. owner d v /\ owner src v) ==>
  !z x. current_prefix_back xs M z x ==> owner z x
Proof
  Induct >> simp[current_prefix_back_def] >> rpt strip_tac >>
  drule current_prefix_pull_owner >>
  disch_then irule >> qexistsl_tac [`current_prefix_back xs M`, `h`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!M owner. current_prefix_functional owner /\ _ ==> _` irule >> simp[] >>
  conj_tac >- metis_tac[] >> qexists `M` >> simp[]
QED
