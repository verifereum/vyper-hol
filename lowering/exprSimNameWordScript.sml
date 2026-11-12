(* Counted simulation for a word local. *)
Theory exprSimNameWord
Ancestors
  exprSimProps
  gasNormalPrefix gasSummary fragGasPath fragGasMode gasCount venomExecProofs
  exprSimDefs exprSimStack exprSimValues
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState
  vyperLookupStorage vyperStorageBackend

Theorem compile_name_word_path:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  is_word_type ann /\
  lookup_scopes id es.scopes = SOME entry /\ word_value entry.value /\
  lower_value compile_expr cenv ty (Name ann id) sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out. op = Var out /\ emit_op MLOAD [Var p] sa = (Var out,sb) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    gas_path ctx func s0 0
      (OK (update_var out (val_to_w256 entry.value)
        (s0 with vs_inst_idx := LENGTH sb.cs_current_insts)))
Proof
  strip_tac >> drule_all lower_value_name_word >> strip_tac >>
  `?out n. op = Var out /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ [mk_inst n MLOAD [Var p] [out]]`
    by (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
            comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
        metis_tac[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `step_inst 0 ctx (mk_inst n MLOAD [Var p] [out]) s0 =
    OK (update_var out (val_to_w256 entry.value) s0)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     drule_all step_name_word >> simp[mk_inst_def]) >>
  `gas_path_edge ctx func s0 0
    (OK (update_var out (val_to_w256 entry.value)
      (s0 with vs_inst_idx := SUC s0.vs_inst_idx)))` by
    (rewrite_tac[gas_path_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[gas_count_step_def, mk_inst_def, is_terminator_def, update_var_def] >>
     gvs[update_var_def]) >>
  drule gas_path_edge_normal >> strip_tac >>
  gvs[arithmeticTheory.ADD1] >>
  drule (cj 2 gas_path_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_rules, arithmeticTheory.ADD1]
QED

Theorem name_word_post:
  emit_op MLOAD [Var p] sa = (Var out,sb) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  is_word_type ann /\ word_value entry.value ==>
  expr_post ctx func cenv cx (Name ann id) es sa sb s0
    (es with gas_obs := []) entry.value (Var out)
    (update_var out (val_to_w256 entry.value)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `out = STRCAT "%" (toString sa.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >>
  `not_local_ptr cenv (es with gas_obs := []).scopes out` by
    (gvs[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
    (update_var out (val_to_w256 entry.value)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule stmt_state_rel_update_var >> simp[] >>
     drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`,
                            `LENGTH sb.cs_current_insts`, `[]`] mp_tac) >> simp[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, typed_val_to_w256_word_value,
       locals_kept_mem] >>
  rpt strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) <> x` by
    (strip_tac >> gvs[not_fresh_at_def]) >> simp[]
QED

Theorem compile_name_word_sim:
  !ctx func cenv cx ty ann id es p sz entry.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type ann /\
    lookup_scopes id es.scopes = SOME entry /\ word_value entry.value ==>
    expr_sim ctx func cenv cx ty (Name ann id) es
Proof
  rpt strip_tac >> irule expr_sim_values >>
  rpt strip_tac >>
  drule_all compile_name_word_path >> strip_tac >> gvs[] >>
  qexistsl_tac [`[]`, `entry.value`, `es`,
    `update_var out (val_to_w256 entry.value)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[gas_value_prefix_def] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_explicit_def,
           gas_marked_path_def] >>
      gen_tac >>
      qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := tail`, `entry`]
        mp_tac eval_name_word >> simp[] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  conj_tac >- (irule name_word_post >> simp[] >> metis_tac[]) >>
  simp[update_var_def]
QED

