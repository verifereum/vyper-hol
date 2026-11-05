(* Counted simulation for flag members. *)
Theory exprSimFlagWord
Ancestors
  exprSimHypsDefs exprSimProps exprSimDefs exprSimStack exprSimValues
  gasNormalPrefix gasSummary fragGasMode fragGasPath loweringPosts
  list rich_list finite_map pred_set fragExec varsExt loweringSlice
  localPtrsProps venomMemDefs exprLowering exprLoweringProps
  compileEnv vyperInterpreter vyperState vyperContext
  vyperValueOperation valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState

(* A flag member is the literal 2 ** id, id its index in its flag's
   declaration by expr_sim_inv's flag members clause. *)
Theorem compile_flag_member_word_sim:
  !cenv ann nsid mid. expr_sim_ok cenv (FlagMember ann nsid mid)
Proof
  rw[expr_sim_ok_def] >> irule expr_sim_values >> rpt strip_tac >>
  PairCases_on `nsid` >>
  drule eval_expr_flag_member_gas >> strip_tac >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0, nsid1)) mid = i` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0, nsid1)` by gvs[expr_sim_pre_def, well_typed_expr_def] >>
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      unwrap_value_def] >>
  qexistsl_tac [`[]`,
    `FlagV (2 ** cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid)`,
    `es`, `s0`] >>
  simp[gas_value_prefix_def, lower_value_def, compile_expr_def,
       comp_bind_def, comp_return_def, unwrap_value_def] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     qpat_x_assum `s0.vs_inst_idx = _` kall_tac >> simp[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, locals_kept_def,
       vyperASTTheory.expr_type_def, eval_operand_def, is_word_type_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def]
QED

Theorem compile_flag_member_case_sim:
  !cenv ann nsid mid. expr_ok cenv (FlagMember ann nsid mid)
Proof
  rpt gen_tac >> irule expr_ok_stack >>
  simp[compile_flag_member_word_sim, compile_expr_def] >>
  PairCases_on `nsid` >> rpt gen_tac >>
  simp[Once evaluate_def, lookup_flag_mem_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[raise_def, return_def]) >> rw[]
QED

Theorem compile_flag_member_sim:
  !cenv ann nsid mid. expr_vv_ok cenv (FlagMember ann nsid mid)
Proof
  metis_tac[compile_flag_member_case_sim, expr_ok_def]
QED


