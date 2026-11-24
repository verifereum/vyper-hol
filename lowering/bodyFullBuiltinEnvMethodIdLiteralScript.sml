(* Literal-folded MethodId, with one full origin/pointer witness. *)
Theory bodyFullBuiltinEnvMethodIdLiteral
Ancestors
  bodyFullBuiltinEnvMethodIdPost bodyFullBuiltinEnvMethodIdCompose
  bodyFullLiteralBuffer bodyFullExprGeneric bodyFullPreds bodyFullGhostFrame
  bodyFullEmptyLeafData exprSimFullBundleProps
  bodySimFull exprSimMemDefs fragGasOriginPtr ptrDiscipline venomState vyperStorageFootprint
  exprSimPrecompiles exprSimVVFrame loweringStateRelDefs exprSimWordArgs
  gasOutcomeFullCompose exprSimHash exprSimSource exprSimProps exprLoweringProps
  exprSimLiteralBuffer exprSimMemoryStack loweringPosts bodyPtrDefs
  exprLowering compileEnv vyperAST vyperInterpreter vyperState vyperValue
  vyperContext valueEncoding vyperTypeBytesCrypto words list

(* Compile and evaluate the folded selector without changing either state. *)
Theorem method_id_literal_fixed_nil:
  method_id_literal (Literal la l) = SOME bs /\
  expr_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx ty
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es
    (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
  sb = sa /\
  (!tail. bind (eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]))
      (read_result cx) (es with gas_obs := tail) =
    (INL (BytesV (TAKE 4 (Keccak_256_w64 bs))),es with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    expr_sim_full_post (DF,lo,d,ctx,func) cenv cx
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])
      (es,sa,sb,s0,op,G0,tn0) H (INL (BytesV (TAKE 4 (Keccak_256_w64 bs))) : value + exception)
      (es with gas_obs := []) G0 tn0 s0)
Proof
  simp[expr_sim_full_hypotheses_def] >> strip_tac >>
  `!st. eval_expr cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) st =
    (INL (Value (BytesV (TAKE 4 (Keccak_256_w64 bs)))),st)` by
    (gen_tac >> Cases_on `eval_expr cx
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) st` >>
     drule_all eval_expr_method_id_literal >> simp[]) >>
  drule compile_expr_method_id_literal >>
  disch_then (qspecl_then [`cenv`, `ty`, `BaseT (BytesT (Fixed 4))`, `sa`] assume_tac) >>
  qpat_x_assum `lower_value _ _ _ _ sa = _` mp_tac >>
  simp[lower_value_def, compile_literal_vv_def,
       comp_bind_def, unwrap_value_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[bind_def, read_result_def, return_def, expr_sim_full_post_def,
       expr_sim_full_endpoint_def, post_value_type_def] >>
  qx_gen_tac `H` >> strip_tac >> first_x_assum drule >> strip_tac >>
  simp[expr_store_bound_def, expr_type_def, is_word_type_def,
       ptr_val_ok_def, op_taint_def, ghost_kept_at_def] >>
  conj_tac
  >- (irule expr_post_typed_stack_intro >>
      simp[expr_type_def, is_word_type_def, evaluate_type_def,
           eval_operand_def, stmt_state_rel_gas_obs, wb_frame_refl,
           pure_frame_def, storage_well_formed_on_def] >>
      gvs[storage_well_formed_on_def] >> rpt gen_tac >> strip_tac >>
      first_x_assum drule >> Cases_on `b` >>
      simp[vyperStorageBackendTheory.get_storage_def]) >>
  gvs[ghost_inv_at_def] >> metis_tac[]
QED

Theorem method_id_literal_fixed_sim_full:
  method_id_literal (Literal la l) = SOME bs ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es
Proof
  strip_tac >> conj_asm1_tac
  >- (rw[expr_sim_full_via_bundle] >>
      drule_all method_id_literal_fixed_nil >> strip_tac >>
      irule gas_outcome_full_unchanged >>
      (reverse conj_tac >- fs[expr_sim_full_hypotheses_def]) >>
      qexists_tac `INL (BytesV (TAKE 4 (Keccak_256_w64 bs)))` >>
      gvs[]) >>
  irule expr_vv_sim_stack_full >>
  simp[expr_type_def, is_word_type_def] >> conj_tac
  >- (gen_tac >> drule compile_expr_method_id_literal >>
      disch_then (qspecl_then [`cenv`, `ty`, `BaseT (BytesT (Fixed 4))`, `sa`] assume_tac) >>
      simp[compile_literal_vv_def, comp_return_def]) >>
  metis_tac[eval_expr_builtin_value]
QED
