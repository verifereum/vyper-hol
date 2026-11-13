(*
 * The pointer twin of S1's FlagMember case (exprSimFlagWord): the
 * constant 2 ** id, no code, so the path is empty and the ghost stays.
 *
 * TOP-LEVEL:
 *   flag_member_expr_sim_ptr
 *)
Theory exprSimPtrFlagMember
Ancestors
  exprSimPtrProps bodyPtrDefs fragGasPathPtr ptrDiscipline exprSimHypsDefs
  exprSimProps exprSimDefs loweringPosts exprLowering exprLoweringProps
  gasSummary loweringSlice compileEnv vyperAST vyperInterpreter vyperState vyperContext
  vyperValueOperation valueEncoding vyperTypeSystem venomState list

Theorem flag_member_lower_sim_ptr[local]:
  expr_sim_pre cenv cx env (FlagMember ann nsid mid) es ==>
  expr_sim_ptr d ctx PG func cenv cx ty (FlagMember ann nsid mid) es
Proof
  rw[expr_sim_ptr_def] >> PairCases_on `nsid` >>
  drule eval_expr_flag_member_gas >> strip_tac >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0, nsid1)) mid = i` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0, nsid1)` by gvs[expr_sim_pre_def, well_typed_expr_def] >>
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      unwrap_value_def] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
       mp_tac) >>
     qpat_x_assum `s0.vs_inst_idx = _` kall_tac >> simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [
    `INL (FlagV (2 ** cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid))`,
    `es`, `G0`, `tn0`, `OK s0`] >>
  simp[gas_explicit_def, gas_path_ptr_rules] >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def, locals_kept_def,
      vyperASTTheory.expr_type_def, eval_operand_def, is_word_type_def,
      typed_val_to_w256_word_value, word_value_def, val_to_w256_def,
      ghost_inv_def, ptr_val_ok_def, op_taint_def, op_prov_def,
      ghost_kept_def] >>
  metis_tac[]
QED

Theorem flag_member_expr_sim_ptr:
  !d PG ctx func cenv cx env ty ann nsid mid es.
    expr_sim_pre cenv cx env (FlagMember ann nsid mid) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty (FlagMember ann nsid mid) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty (FlagMember ann nsid mid) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx ty (FlagMember ann nsid mid) es` by
    metis_tac[flag_member_lower_sim_ptr] >>
  simp[] >> irule expr_vv_sim_ptr_stack >> simp[] >> conj_tac
  >~ [`compile_expr`] >- simp[compile_expr_def, comp_return_def] >>
  PairCases_on `nsid` >> rpt gen_tac >>
  simp[Once evaluate_def, lookup_flag_mem_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[raise_def, return_def]) >>
  rw[]
QED
