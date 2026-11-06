Theory fnLineageInvLiteral
Ancestors stackPlanGen stackPlanOps stackModel dfgDefs venomInst

Theorem literal_pair_reorder_first:
  !dfg x y ps. x <> y ==>
  reorder_one dfg [Lit x; Lit y] 0 (Lit x)
    (ps with ps_stack := ps.ps_stack ++ [Lit y; Lit x]) =
  ([SOSwap 1], ps with ps_stack := ps.ps_stack ++ [Lit x; Lit y])
Proof
  rpt strip_tac >>
  simp[reorder_one_def, stack_get_unfixed_depth_def,
    stack_get_depth_def, stack_find_def, listTheory.REVERSE_APPEND,
    stack_peek_def, listTheory.EL_APPEND_EQN,
    dfgDefsTheory.operand_equiv_def, dfgDefsTheory.normalize_operand_def,
    do_swap_def, stack_swap_def, rich_listTheory.LUPDATE_APPEND2] >>
  simp[listTheory.LUPDATE_compute]
QED

Theorem literal_pair_reorder_noops:
  !dfg x y ps. x <> y ==>
  reorder_one dfg [Lit x; Lit y] 1 (Lit y)
    (ps with ps_stack := ps.ps_stack ++ [Lit x; Lit y]) =
  ([], ps with ps_stack := ps.ps_stack ++ [Lit x; Lit y]) /\
  reorder_one dfg [Lit y; Lit x] 0 (Lit y)
    (ps with ps_stack := ps.ps_stack ++ [Lit y; Lit x]) =
  ([], ps with ps_stack := ps.ps_stack ++ [Lit y; Lit x]) /\
  reorder_one dfg [Lit y; Lit x] 1 (Lit x)
    (ps with ps_stack := ps.ps_stack ++ [Lit y; Lit x]) =
  ([], ps with ps_stack := ps.ps_stack ++ [Lit y; Lit x])
Proof
  rpt strip_tac >>
  simp[reorder_one_def, stack_get_unfixed_depth_def,
    stack_get_depth_def, stack_find_def, listTheory.REVERSE_APPEND,
    stack_peek_def, listTheory.EL_APPEND_EQN,
    listTheory.FIND_thm] >>
  `LENGTH ps.ps_stack + 2 = SUC (SUC (LENGTH ps.ps_stack))` by decide_tac >>
  asm_rewrite_tac[] >>
  once_rewrite_tac[listTheory.GENLIST_CONS] >>
  pure_rewrite_tac[listTheory.FIND_thm, combinTheory.I_THM] >>
  BETA_TAC >> simp[NoAsms] >>
  asm_rewrite_tac[] >>
  once_rewrite_tac[listTheory.GENLIST_CONS] >>
  pure_rewrite_tac[listTheory.FIND_thm, combinTheory.I_THM] >>
  BETA_TAC >> simp[NoAsms, listTheory.EL_APPEND_EQN] >>
  asm_rewrite_tac[] >>
  once_rewrite_tac[listTheory.GENLIST_CONS] >>
  pure_rewrite_tac[listTheory.FIND_thm, combinTheory.I_THM] >>
  BETA_TAC >> simp[NoAsms, listTheory.EL_APPEND_EQN]
QED

Theorem literal_add_regular_plan:
  !x y out nl dfg iid nt ps optops q lv (cfg:cfg_analysis) fn lbl.
  x <> y /\ MEM out nl /\
  optimistic_swap_plan dfg (mk_inst iid ADD [Lit x; Lit y] [out]) nl nt
    (ps with ps_stack := ps.ps_stack ++ [Var out]) = (optops,q) ==>
  generate_regular_inst_plan lv dfg cfg fn
    (mk_inst iid ADD [Lit x; Lit y] [out]) nl F nt lbl ps =
  ([SOPush (Lit y); SOPush (Lit x); SOEmit "ADD"] ++ optops,
    release_dead_spills nl q)
Proof
  rpt strip_tac >>
  simp[generate_regular_inst_plan_def, mk_inst_def,
    compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def,
    venomEffectsTheory.is_commutative_def,
    emit_input_plan_two, emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
    stack_push_def, listTheory.SNOC_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  simp[reorder_plan_def,
    listTheory.FOLDL, pairTheory.UNCURRY_DEF,
    literal_pair_reorder_first, literal_pair_reorder_noops] >>
  gvs[reorder_cost_def, generate_emit_ops_def, mk_inst_def,
    stack_pop_def, popmany_plan_def, rich_listTheory.TAKE_APPEND,
    asmIRTheory.venom_to_evm_name_def]
QED

Theorem literal_add_inst_plan:
  !x y out nl dfg iid nt ps optops q lv (cfg:cfg_analysis) fn lbl.
  x <> y /\ MEM out nl /\
  optimistic_swap_plan dfg (mk_inst iid ADD [Lit x; Lit y] [out]) nl nt
    (ps with ps_stack := ps.ps_stack ++ [Var out]) = (optops,q) ==>
  generate_inst_plan lv dfg cfg fn
    (mk_inst iid ADD [Lit x; Lit y] [out]) nl F nt lbl ps =
  SOME ([SOPush (Lit y); SOPush (Lit x); SOEmit "ADD"] ++ optops,
    release_dead_spills nl q)
Proof
  rpt strip_tac >>
  drule_all literal_add_regular_plan >>
  simp[generate_inst_plan_def, mk_inst_def, is_pre_codegen_opcode_def,
    is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
    is_raw_fmp_opcode_def, is_param_opcode_def]
QED
