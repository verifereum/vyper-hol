(* FlagMember is an actual code-free constant producer. *)
Theory bodyFlagMemberMemory
Ancestors
  exprSimSource exprSimMemoryValues fragGasPathMem fragGasSeqMem gasCount gasContext
  exprSimMemoryStack bodyMemoryDefs bodyMemoryPreds exprSimProps exprSimHypsDefs
  exprSimDefs exprLowering exprLoweringProps fragExecMem compileEnv valueEncoding
  vyperAST vyperInterpreter vyperState vyperTyping vyperValueOperation
  vyperTypeSystem vyperValue venomState loweringSlice
  gasNormalPrefix gasSummary fragGasMode loweringPosts

Theorem body_flag_member_mem_prefix[local]:
  expr_body_pre cenv cx env (FlagMember ann nsid mid) es /\
  lower_value compile_expr cenv ty (FlagMember ann nsid mid) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx (FlagMember ann nsid mid)) (read_result cx))
    expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?marks v ee t. gas_value_prefix T (ctx,func,cenv,cx)
    (ty,FlagMember ann nsid mid) (sa,sb,op) (es,s0) marks (v,ee,t)
Proof
  strip_tac >> PairCases_on `nsid` >>
  drule eval_expr_flag_member_gas >> strip_tac >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0, nsid1)) mid = i` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0, nsid1)` by gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      unwrap_value_def] >>
  qexistsl_tac [`[]`,
    `FlagV (2 ** cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid)`,
    `es`, `s0`] >>
  simp[gas_value_prefix_def, lower_value_def, compile_expr_def,
       comp_bind_def, comp_return_def, unwrap_value_def] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def, is_word_type_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def]
QED

Theorem compile_flag_member_body_sim_mem:
  !ctx func cenv cx env ty ann nsid mid es.
    expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
    expr_sim_mem ctx func cenv cx ty (FlagMember ann nsid mid) es
Proof
  rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_values >> reverse conj_tac
  >- (`ann = FlagT nsid` by
        (PairCases_on `nsid` >> gvs[expr_body_pre_def, well_typed_expr_def]) >>
      simp[vyperASTTheory.expr_type_def, is_word_type_def]) >>
  rpt gen_tac >> strip_tac >>
  irule body_flag_member_mem_prefix >> metis_tac[]
QED

(* Prior successful uncounted proof, retained for reference.
Proof
  rpt gen_tac >> strip_tac >> rw[expr_sim_mem_def] >> PairCases_on `nsid` >>
  drule_all eval_expr_flag_member >> strip_tac >> gvs[] >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0, nsid1)) mid = i` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0, nsid1)` by gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      unwrap_value_def] >>
  irule frag_exec_mem_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def, is_word_type_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def]
QED
*)

Theorem compile_flag_member_body_vv_sim_mem:
  !ctx func cenv cx env ty ann nsid mid es.
    expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
    expr_vv_sim_mem ctx func cenv cx ty (FlagMember ann nsid mid) es
Proof
  rpt gen_tac >> strip_tac >> `is_word_type (expr_type (FlagMember ann nsid mid))` by
    (`ann = FlagT nsid` by
        (PairCases_on `nsid` >> gvs[expr_body_pre_def, well_typed_expr_def]) >>
      simp[vyperASTTheory.expr_type_def, is_word_type_def]) >>
  drule_then irule body_expr_vv_sim_mem_stack_word >>
  conj_tac >- simp[compile_expr_def] >>
  conj_tac
  >- (PairCases_on `nsid` >> rpt gen_tac >>
      simp[Once evaluate_def, lookup_flag_mem_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> simp[raise_def, return_def]) >> rw[]) >>
  irule compile_flag_member_body_sim_mem >> metis_tac[]
QED

Theorem body_flag_member_mem_case:
  !cx ann nsid mid. body_expr_mem_ok cx (FlagMember ann nsid mid)
Proof
  rpt gen_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  metis_tac[compile_flag_member_body_sim_mem,
            compile_flag_member_body_vv_sim_mem]
QED

