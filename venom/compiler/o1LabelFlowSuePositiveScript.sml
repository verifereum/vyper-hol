Theory o1LabelFlowSuePositive
Ancestors
  o1LabelFlowLateSue codegenSymRel unitLabelMapIdentity
  singleUseExpansionDefs singleUseExpansionSupplySim

Theorem sue_positive_insts_segment:
  !xs s ys t i.
  sue_expand_insts_supply dfg s xs = (ys,t) /\ MEM i xs ==>
  ?si sj seg. sue_expand_inst_supply dfg si i = (seg,sj) /\
    (!j. MEM j seg ==> MEM j ys)
Proof
  Induct >> simp[sue_expand_insts_supply_def] >> rpt gen_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r xs` >>
  simp[] >> strip_tac >> gvs[]
  >- (qexistsl_tac [`s`,`r`,`q`] >> simp[]) >>
  first_x_assum drule >> disch_then (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`si`,`sj`,`seg`] >> simp[]
QED

Theorem sue_positive_function_segment:
  sue_expand_function_supply s f = (g,t) /\ MEM i (fn_insts f) ==>
  ?si sj seg. sue_expand_inst_supply (dfg_build_function f) si i = (seg,sj) /\
    (!j. MEM j seg ==> MEM j (fn_insts g))
Proof
  Cases_on `sue_expand_blocks_supply (dfg_build_function f) s f.fn_blocks` >>
  simp[sue_expand_function_supply_def] >> strip_tac >> gvs[] >>
  fs[fn_insts_MEM] >>
  drule_all sue_expand_blocks_supply_member_forward >> strip_tac >>
  Cases_on `sue_expand_insts_supply (dfg_build_function f) si bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def] >>
  drule_all sue_positive_insts_segment >> strip_tac >>
  qexistsl_tac [`si'`,`sj`,`seg`] >> simp[] >>
  rpt strip_tac >> qexists_tac `bb with bb_instructions := q'` >> simp[]
QED

Theorem sue_positive_code_end_var:
  !f x. code_end_var f x ==>
  !s g t. sue_expand_function_supply s f = (g,t) ==> code_end_var g x
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- (drule_all sue_positive_function_segment >> strip_tac >>
      drule sue_label_tail_preserved >> simp[] >> strip_tac >>
      irule (cj 1 code_end_var_rules) >>
      qexistsl_tac [`LAST seg`,`nop`] >> simp[] >>
      first_x_assum irule >>
      metis_tac[sue_expand_inst_supply_nonempty,
                rich_listTheory.MEM_LAST_NOT_NIL]) >>
  rpt strip_tac >> irule (cj 2 code_end_var_rules) >>
  qexistsl_tac [`inst`,`x'`] >> simp[] >>
  conj_tac
  >- (irule sue_expand_function_supply_skip_member >>
      simp[sue_should_skip_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem sue_positive_insts_segment_back:
  !xs s ys t j.
  sue_expand_insts_supply dfg s xs = (ys,t) /\ MEM j ys ==>
  ?i si sj seg. MEM i xs /\
    sue_expand_inst_supply dfg si i = (seg,sj) /\ MEM j seg /\
    (!a. MEM a seg ==> MEM a ys)
Proof
  Induct >> simp[sue_expand_insts_supply_def] >> rpt gen_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r xs` >>
  simp[] >> strip_tac >> gvs[]
  >- (qexistsl_tac [`h`,`s`,`r`,`q`] >> simp[]) >>
  first_x_assum drule >> disch_then (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`i`,`si`,`sj`,`seg`] >> simp[]
QED

Theorem sue_positive_function_segment_back:
  sue_expand_function_supply s f = (g,t) /\ MEM j (fn_insts g) ==>
  ?i si sj seg. MEM i (fn_insts f) /\
    sue_expand_inst_supply (dfg_build_function f) si i = (seg,sj) /\
    MEM j seg /\ (!a. MEM a seg ==> MEM a (fn_insts g))
Proof
  Cases_on `sue_expand_blocks_supply (dfg_build_function f) s f.fn_blocks` >>
  simp[sue_expand_function_supply_def] >> strip_tac >> gvs[] >>
  fs[fn_insts_MEM] >>
  drule_all sue_expand_blocks_supply_member >> strip_tac >>
  Cases_on `sue_expand_insts_supply (dfg_build_function f) si bb'.bb_instructions` >>
  gvs[sue_expand_block_supply_def] >>
  drule_all sue_positive_insts_segment_back >> strip_tac >>
  qexistsl_tac [`i`,`si'`,`sj`,`seg`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> qexists_tac `bb' with bb_instructions := q'` >> simp[]
QED

Theorem sue_positive_segment_nonassign:
  sue_expand_inst_supply dfg s i = (seg,t) /\
  MEM j seg /\ j.inst_opcode <> ASSIGN ==> j = LAST seg
Proof
  strip_tac >> drule sue_expand_inst_supply_precise_provenance >>
  strip_tac >> drule sue_expand_inst_supply_nonempty >> strip_tac >>
  `MEM j (FRONT seg) \/ j = LAST seg` by
    metis_tac[listTheory.APPEND_FRONT_LAST, listTheory.MEM_APPEND, listTheory.MEM] >>
  fs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_positive_operand_source:
  (nop = op \/ ?a v. MEM a (FRONT seg) /\ a.inst_opcode = ASSIGN /\
    a.inst_operands = [op] /\ a.inst_outputs = [v] /\ nop = Var v /\
    ((?w. op = Var w) \/ (?w. op = Lit w))) /\
  (!a. MEM a seg ==> MEM a (fn_insts g)) /\ seg <> [] /\
  (op = Label "runtime_begin" \/ ?x. op = Var x /\ code_end_var g x) ==>
  (nop = Label "runtime_begin" \/ ?x. nop = Var x /\ code_end_var g x)
Proof
  rpt strip_tac >> gvs[] >>
  irule (cj 2 code_end_var_rules) >>
  qexistsl_tac [`a`,`w`] >> simp[] >>
  first_x_assum irule >>
  metis_tac[listTheory.APPEND_FRONT_LAST, listTheory.MEM_APPEND]
QED

Theorem sue_positive_three_operands[local]:
  LIST_REL R [dst;src;sz] ops ==>
  ?d s z. ops = [d;s;z] /\ R src s
Proof
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem sue_positive_codecopy_source:
  sue_expand_function_supply s f = (g,t) /\
  label_flow_ok (ctx with ctx_functions := [f]) /\
  MEM j (fn_insts g) /\ j.inst_opcode = CODECOPY ==>
  ?dst src sz. j.inst_operands = [dst;src;sz] /\
    (src = Label "runtime_begin" \/ ?x. src = Var x /\ code_end_var g x)
Proof
  strip_tac >> drule_all sue_positive_function_segment_back >> strip_tac >>
  `j = LAST seg` by
    (irule sue_positive_segment_nonassign >> simp[] >> metis_tac[]) >>
  drule sue_expand_inst_supply_last >> strip_tac >>
  `i.inst_opcode = CODECOPY` by metis_tac[] >>
  `?dst src sz. i.inst_operands = [dst;src;sz] /\
     (src = Label "runtime_begin" \/ ?x. src = Var x /\ code_end_var f x)` by
    (fs[label_flow_ok_def] >> metis_tac[]) >>
  `!x. code_end_var f x ==> code_end_var g x` by
    metis_tac[sue_positive_code_end_var] >>
  drule sue_expand_inst_supply_precise_provenance >> strip_tac >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  pure_asm_rewrite_tac [] >> disch_tac >>
  drule sue_positive_three_operands >>
  disch_then (qx_choose_then `d` (qx_choose_then `source`
    (qx_choose_then `z` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
  simp[] >> irule sue_positive_operand_source >>
  metis_tac[sue_expand_inst_supply_nonempty]
QED
