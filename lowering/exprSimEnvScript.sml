(* Counted simulation for gas-independent environment reads. *)
Theory exprSimEnv
Ancestors
  exprSimProps gasContext fragGasPath gasCount gasNormalPrefix gasSummary fragGasMode
  exprSimDefs exprSimStack exprSimValues
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState
  vyperLookupStorage vyperStorageBackend

Theorem env_source_all_tails:
  item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item /\
  gas_admissible
    ((do result <- eval_expr cx (Builtin ann (Env item) []); read_result cx result od))
    expr_res_ok es ==>
  ?v. evaluate_builtin cx es.accounts ann (Env item) [] [] = INL v /\
      !tail. (do result <- eval_expr cx (Builtin ann (Env item) []); read_result cx result od)
        (es with gas_obs := tail) = (INL v, es with gas_obs := tail)
Proof
  strip_tac >>
  Cases_on `(do result <- eval_expr cx (Builtin ann (Env item) []); read_result cx result od)
    (es with gas_obs := [])` >>
  `expr_res_ok q` by (fs[gas_admissible_def] >> metis_tac[]) >>
  drule_all eval_expr_env >> strip_tac >> gvs[] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def, read_result_def] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def] >>
  Cases_on `item` >>
  gvs[evaluate_builtin_def, env_item_type_def, return_def, raise_def,
      read_result_def]
QED


Theorem env_target_prefix:
  item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item /\
  lower_value compile_expr cenv ty (Builtin ann (Env item) []) sa = (op, sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  evaluate_builtin cx es.accounts ann (Env item) [] [] = INL v ==>
  ?t. gas_path ctx func s0 0 (OK t) /\
      expr_post ctx func cenv cx (Builtin ann (Env item) []) es sa sb s0
        (es with gas_obs := []) v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `is_word_type (env_item_type item) /\
   !tv. evaluate_type (get_tenv cx) (env_item_type item) = SOME tv ==>
        typed_val_to_w256 tv v = val_to_w256 v` by
    (Cases_on `item` >>
     gvs[evaluate_builtin_def, env_item_type_def, is_word_type_def,
         vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
         val_to_w256_def] >>
     simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []) >>
  drule lower_value_env >> strip_tac >>
  `?opc. emit_op opc [] sa = (op, sb) /\ opc <> GAS /\ opc <> INVOKE /\
    ~is_terminator opc /\
    !out. step_inst_base (mk_inst sa.cs_next_id opc [] [out]) s0 =
          OK (update_var out (val_to_w256 v) s0)` by
    (Cases_on `item` >>
     gvs[compile_env_var_def, evaluate_builtin_def] >>
     goal_assum (drule_at Any) >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, exec_read0_def,
          venomInstTheory.mk_inst_def] >>
     fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
        val_to_w256_address, val_to_w256_def, integer_wordTheory.i2w_def]) >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qexists_tac `update_var out (val_to_w256 v) s0 with
                vs_inst_idx := SUC s0.vs_inst_idx` >>
  conj_tac
  >- (drule_all emit_op_zero_path >> simp[Abbr `out`]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `stmt_state_rel ctx func cenv cx es
      (update_var out (val_to_w256 v) s0)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  drule msg_gas_state_frame >>
  disch_then (qspecl_then [
    `(update_var out (val_to_w256 v) s0).vs_gas_readings`,
    `SUC s0.vs_inst_idx`, `[]`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, locals_kept_mem,
       stmt_state_rel_inst_idx, update_var_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, Abbr `out`] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem compile_env_sim:
  !ctx func cenv cx ty ann item es.
    item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Env item) []) es
Proof
  rpt strip_tac >> irule expr_sim_values >> rpt strip_tac >>
  gvs[] >>
  `?v. evaluate_builtin cx es.accounts (env_item_type item) (Env item) [] [] = INL v /\
       !tail. bind (eval_expr cx (Builtin (env_item_type item) (Env item) []))
         (read_result cx) (es with gas_obs := tail) =
         (INL v, es with gas_obs := tail)` by
    metis_tac[PURE_REWRITE_RULE [ETA_THM] env_source_all_tails] >>
  `?t. gas_path ctx func s0 0 (OK t) /\
       expr_post ctx func cenv cx (Builtin (env_item_type item) (Env item) [])
         es sa sb s0 (es with gas_obs := []) v op t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    metis_tac[env_target_prefix] >>
  qexistsl_tac [`[]`, `v`, `es`, `t`] >>
  simp[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def,
       GSYM ETA_THM]
QED

