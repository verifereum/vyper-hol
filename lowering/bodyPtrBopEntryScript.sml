Theory bodyPtrBopEntry
Ancestors
  bodyPtrBopOperandContract bodyPtrBopSource bodyPtrBopPairOutcome
  exprSimSource exprSimWordArgs exprBopSimProps exprSimDefs
  emitHelperProps localPtrsProps fragExec bodyPtrDefs compileEnv
  exprLoweringProps freshWrites list rich_list

Theorem bop_operand_entry_prefix:
  bop_operand_entry d ctx func cenv cx st0 parent es ca cz op t G tn /\
  cs_extends ca c1 /\ cs_extends c1 cz /\
  expr_body_pre cenv cx env child es ==>
  bop_operand_entry d ctx func cenv cx st0 child es ca c1 x t G tn
Proof
  simp[bop_operand_entry_def] >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[fn_has_code_mid, cs_extends_refl] >>
  metis_tac[expr_body_pre_gas_admissible]
QED

Theorem bop_operand_entry_next:
  bop_operand_entry d ctx func cenv cx st0 parent es ca cz op t0 G0 tn0 /\
  (?H. valid_horizon cx st0 H es1.storage_trace) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    bop_operand_post H d ctx func cenv cx child es ca c1 x t0 G0 tn0
      v es1 t1 G1 tn1) /\
  cs_extends ca c1 /\ cs_extends c1 c2 /\ cs_extends c2 cz /\
  ca.cs_next_var <= c1.cs_next_var /\
  expr_body_pre cenv cx env next_child es1 /\ ~t1.vs_halted ==>
  bop_operand_entry d ctx func cenv cx st0 next_child es1 c1 c2 y t1 G1 tn1
Proof
  simp[bop_operand_entry_def, bop_operand_post_def] >> strip_tac >>
  `t1.vs_current_bb = c1.cs_current_bb /\
   t1.vs_inst_idx = LENGTH c1.cs_current_insts` by metis_tac[] >>
  simp[] >> rpt conj_tac
  >- metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl]
  >- metis_tac[local_ptrs_reserved_next_var]
  >- metis_tac[not_fresh_at_mono]
  >- metis_tac[not_fresh_at_mono]
  >- metis_tac[expr_body_pre_gas_admissible] >>
  qx_gen_tac `H2` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ es1.storage_trace ==> _`
    (qspec_then `H2` mp_tac) >>
  simp[loweringPostsTheory.expr_post_def]
QED

Theorem bop_pair_word_inputs:
  bop_operand_post H d ctx func cenv cx e1 es ca c1 x t0 G0 tn0
    v1 es1 t1 G1 tn1 /\
  bop_operand_post H d ctx func cenv cx e2 es1 c1 c2 y t1 G1 tn1
    v2 es2 t2 G2 tn2 /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  (!z. x = Var z ==> not_fresh_at c1 z) /\ (!l. x <> Label l) ==>
  op_prov G2 x = NONE /\ op_taint tn2 x = {} /\
  op_prov G2 y = NONE /\ op_taint tn2 y = {} /\
  !w. eval_operand x t1 = SOME w ==> eval_operand x t2 = SOME w
Proof
  simp[bop_operand_post_def] >> strip_tac >>
  fs[loweringPostsTheory.post_value_type_word] >>
  `op_prov G2 x = op_prov G1 x /\ op_taint tn2 x = op_taint tn1 x` by
    (Cases_on `x` >> gvs[ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def, ghost_kept_def]) >>
  simp[] >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {} /\
   op_prov G2 y = NONE /\ op_taint tn2 y = {}` by
    metis_tac[ptr_val_ok_def] >> simp[] >> rpt strip_tac >>
  irule eval_operand_frame >> simp[] >>
  qexistsl_tac [`c1`, `t1`] >> simp[] >>
  metis_tac[loweringPostsTheory.expr_post_def]
QED

Theorem bop_suffix_placement:
  fn_has_code c2 cz func /\ same_blocks c2 cz /\
  cz.cs_current_insts = c2.cs_current_insts ++ code /\
  t.vs_current_bb = c2.cs_current_bb /\
  t.vs_inst_idx = LENGTH c2.cs_current_insts ==>
  ?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX code (DROP t.vs_inst_idx bb.bb_instructions)
Proof
  simp[fn_has_code_def, same_blocks_def] >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >> simp[DROP_APPEND]
QED
