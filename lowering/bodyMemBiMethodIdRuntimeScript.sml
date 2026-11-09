(* Counted MethodId composition at the operand/suffix boundary. *)
Theory bodyMemBiMethodIdRuntime
Ancestors
  bodyMemBiMethodIdEndpoint bodyMemBiMethodIdSuffix bodyMemBiMethodIdLiteral bodyExprForceMemory
  stmtReasonVvMemory exprSimHash exprSimMemDefs exprSimHyps exprSimSource
  exprSimProps exprLoweringProps gasOutcome gasSummary gasContext
  fragGasMode fragGasPathMem entrySinkExtraction venomExecSemantics venomState
  bodyLiteralBufferMemory valueEncoding valueEncodingDefs vyperTypeBytesCrypto vfmConstants list
  exprLowering compileEnv vyperAST vyperInterpreter vyperState
  vyperValue vyperTyping loweringPosts context exprSimDefs exprSimHypsDefs vyperTypeSystem builtinHashing vyperContext

Theorem method_id_runtime_vv_sim_mem:
  expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es /\
  method_id_literal e = NONE ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann MethodId [e]) es
Proof
  strip_tac >>
  `is_bytes_or_string_type (expr_type e) /\
    (ann <> BaseT (BytesT (Dynamic 4)) ==> ann = BaseT (BytesT (Fixed 4)))` by
    (mp_tac (SRULE [] (Q.INST [`b` |-> `MethodId`,
       `ty` |-> `ann`, `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     (impl_tac >- gvs[expr_body_pre_def, well_typed_expr_def]) >> metis_tac[]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  qabbrev_tac `fixed = (ann = BaseT (BytesT (Fixed 4)))` >>
  `ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))` by
    (gvs[Abbr `fixed`] >> metis_tac[]) >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt strip_tac >>
  `?x sm op. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
     compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
     vv = (if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory))` by
    (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     simp[compile_method_id_singleton_runtime] >>
     pairarg_tac >> simp[] >>
     Cases_on `compile_method_id_runtime (expr_type e) v fixed sm` >>
     Cases_on `fixed` >> gvs[as_stack_val_def, as_ptr_val_def] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> gvs[expr_body_pre_def]) >>
  `cs_appends (compile_method_id_runtime (expr_type e) x fixed)` by
    simp[cj 5 hash_suffix_appends] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `eval_expr cx (Builtin ann MethodId [e]) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v es. ((case builtin_result cx es.accounts ann MethodId [expr_type e] [v] of
                 INL w => INL (Value w) | INR exc => INR exc), es))` by
    (irule eval_expr_unary_builtin_action >> simp[builtin_args_length_ok_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `x`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  asm_rewrite_tac[] >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL v, mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_base_result) >>
  disch_then (qspecl_then [`env`, `cenv`] mp_tac) >> simp[] >> strip_tac >>
  `evaluate_type (get_tenv cx) (BaseT bty) = SOME (BaseTV bty)` by
    (drule expr_body_pre_type_evaluates >>
     simp[evaluate_type_def] >> Cases_on `bty` >> gvs[AllCaseEqs()] >>
     rename1 `expr_type e = BaseT (BytesT bd)` >> Cases_on `bd` >> gvs[AllCaseEqs()]) >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV)
      exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  drule method_id_runtime_typed_post_run_mem_any_block >>
  disch_then (qspecl_then [`sb`, `op`, `fixed`, `bty`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
     drule gas_path_mem_exec >> simp[fragExecTheory.exit_result_def] >> metis_tac[]) >>
  `alloca_inv t` by fs[expr_post_def, stmt_state_rel_def] >>
  `same_blocks sm sb /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb)` by
    (irule method_id_typed_suffix_shape >> simp[] >> metis_tac[]) >>
  `gas_marked_path T ctx func t
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb)))
      (OK (t' with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (t' with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule method_id_run_path_mem >>
     simp[] >> fs[same_blocks_def] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `REPLICATE (LENGTH (FILTER (\i. i.inst_opcode = GAS)
    (emitted_insts sm sb))) F` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value r)`, `mid`,
    `OK (t' with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[gas_marked_exec_def] >>
  `t'.vs_current_bb = sb.cs_current_bb` by
    (drule_all run_inst_seq_preserves_entry_control >> fs[same_blocks_def]) >>
  `vv_post ctx func cenv cx
    (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
    es sa sb s0 (mid with gas_obs := []) (Value r)
    (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
     LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) t'` by
    (Cases_on `fixed` >> fs[] >> irule vv_post_pointer_cong >>
     goal_assum (drule_at Any) >> simp[mk_ptr_def]) >>
  Cases_on `fixed` >>
  gvs[expr_type_def, lowered_value_type_def, vv_store_bound_def,
      eval_operand_def, mk_ptr_def, is_word_type_def] >>
  metis_tac[]
QED

Theorem method_id_literal_dynamic_vv_sim_mem:
  IS_SOME (method_id_literal (Literal la l)) ==>
  expr_vv_sim_mem ctx func cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es
Proof
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  irule literal_buffer_vv_sim_mem >>
  conj_tac >- simp[expr_type_def, is_word_type_def] >>
  qexistsl_tac [`TAKE 4 (Keccak_256_w64 x)`,
    `BaseTV (BytesT (Dynamic 4))`, `BytesV (TAKE 4 (Keccak_256_w64 x))`] >>
  `LENGTH (TAKE 4 (Keccak_256_w64 x)) = 4` by
    simp[LENGTH_TAKE, LENGTH_Keccak_256_w64] >>
  simp[expr_type_def, is_word_type_def, evaluate_type_def,
    val_footprint_def, val_store_size_def, val_wf_def, val_in_memory_def,
    type_memory_size_def, lowered_value_type_def] >>
  conj_tac
  >- (rpt gen_tac >>
      drule compile_expr_method_id_literal >>
      disch_then (qspecl_then [`cenv`, `ty`, `BaseT (BytesT (Dynamic 4))`, `sa`] mp_tac) >>
      simp[compile_literal_vv_def, is_word_type_def, comp_bind_def, comp_return_def] >>
      Cases_on `compile_bytelike_literal (TAKE 4 (Keccak_256_w64 x)) 4 sa` >>
      simp[] >> metis_tac[]) >>
  conj_tac
  >- (gen_tac >> Cases_on `eval_expr cx
        (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) st` >>
      drule_all eval_expr_method_id_literal >> simp[]) >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED
