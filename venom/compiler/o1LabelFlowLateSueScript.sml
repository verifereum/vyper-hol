Theory o1LabelFlowLateSue
Ancestors
  singleUseExpansionDefs singleUseExpansionSupplyProofs
  singleUseExpansionSupplySim list rich_list

(* The existing operand provenance and supply-prefix theorems cover both
   variable and literal wrappers.  This boundary exposes those same witnesses
   as the actual prefix and final instruction of an expanded segment. *)
Theorem sue_expand_inst_supply_precise_provenance:
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  EVERY (\a. ?op v. MEM op inst.inst_operands /\
    ((?w. op = Var w) \/ (?w. op = Lit w)) /\
    a.inst_opcode = ASSIGN /\ a.inst_operands = [op] /\
    a.inst_outputs = [v]) (BUTLAST out) /\
  LIST_REL (\op nop. nop = op \/ ?a v.
    MEM a (BUTLAST out) /\ a.inst_opcode = ASSIGN /\
    a.inst_operands = [op] /\ a.inst_outputs = [v] /\
    nop = Var v /\ ((?w. op = Var w) \/ (?w. op = Lit w)))
    inst.inst_operands (LAST out).inst_operands
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- (gvs[sue_expand_inst_supply_def] >>
      simp[LIST_REL_EL_EQN]) >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  drule sue_expand_ops_supply_copies >> strip_tac >>
  drule sue_expand_ops_supply_provenance >> simp[FRONT_APPEND]
QED

(* ASSIGN is a skip opcode, so existing seed-to-copy edges are unchanged. *)
Theorem sue_assign_unchanged:
  inst.inst_opcode = ASSIGN ==>
  sue_expand_inst_supply dfg s inst = ([inst],s)
Proof
  simp[sue_expand_inst_supply_def, sue_should_skip_def]
QED

(* The seed's first operand may itself be wrapped (including a literal),
   but its output and label position are never changed. *)
Theorem sue_label_tail_preserved:
  sue_expand_inst_supply dfg s inst = (out,s') /\
  inst.inst_operands = [op; Label lbl] ==>
  ?nop. (LAST out).inst_opcode = inst.inst_opcode /\
    (LAST out).inst_outputs = inst.inst_outputs /\
    (LAST out).inst_operands = [nop; Label lbl] /\
    (nop = op \/ ?a v. MEM a (BUTLAST out) /\
      a.inst_opcode = ASSIGN /\ a.inst_operands = [op] /\
      a.inst_outputs = [v] /\ nop = Var v /\
      ((?w. op = Var w) \/ (?w. op = Lit w)))
Proof
  strip_tac >> drule sue_expand_inst_supply_last >> strip_tac >>
  drule sue_expand_inst_supply_precise_provenance >>
  simp[] >> strip_tac >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  Cases_on `(LAST out).inst_operands` >> simp[] >>
  rename1 `LIST_REL _ [op; Label lbl] (h::t)` >>
  Cases_on `t` >> simp[] >>
  rename1 `LIST_REL _ [Label lbl] (h'::t')` >>
  Cases_on `t'` >> simp[] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
