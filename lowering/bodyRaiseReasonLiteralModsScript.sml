(* A string literal reason neither evaluates a compiled operand nor reads gas.
   The message buffer and the revert encoder are successive parts of one run. *)
Theory bodyRaiseReasonLiteralMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyReasonLiteralEntryMods
  bodyReasonLiteralEncoderMods gasOutcomeFullPostMods reasonCompilerProps
  reasonSourceProps reasonResourcesPtr stringUnwrapLayout stateRelProj
  exprSimHyps allocLimits bodySim exprLoweringProps fragGasOriginPtrLoop
  stmtSimDefs exprSimDefs bodyPtrDefs loweringPosts vyperTypeSystem vyperAST vyperValue
  words vfmConstants

Theorem compile_raise_reason_literal_frag_full_mods:
  type_stmt env ty (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))) = SOME env' /\
  stmt_exprs_ok cenv (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))) ==>
  stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
    shadow_action
    (eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))) es
Proof
  strip_tac >>
  `LENGTH str <= ml` by
    gvs[type_stmt_raise_reason, well_typed_expr_def, well_typed_literal_def] >>
  `alloc_limits_expr cenv (Literal (BaseT (StringT ml)) (StringL str))` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_raise_def] >>
  `type_alloc_ok cenv (BaseT (StringT ml))` by
    (drule alloc_limits_expr_type_alloc_ok >> simp[expr_type_def]) >>
  drule_then assume_tac reason_encoder_allocation_limit >>
  `32+32*word_size ml < dimword(:256)` by
    (fs[string_memory_bytes_slots, type_slot_size_def] >> decide_tac) >>
  pure_rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule compile_raise_reason_parts >> strip_tac >>
  drule compile_reason_message_cases >> strip_tac >> gvs[] >>
  drule_all raise_reason_compiler_code >> strip_tac >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "run" >>
  irule gas_outcome_full_mods_bad_nil >> simp[eval_raise_string_literal_reason]
QED

Resume compile_raise_reason_literal_frag_full_mods[run]:
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qspecl_then [`MAP (n2w o ORD) str`,`ml`,`sa`] mp_tac
       ci_mono_compile_bytelike_literal >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `32 + 32 * word_size ml < dimword(:256)` by decide_tac >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    reason_literal_message_entry_mods) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`t`,`p`,`G1`,`tn1`] strip_assume_tac)) >>
  suspend "revert"
QED

Resume compile_raise_reason_literal_frag_full_mods[revert]:
  qpat_x_assum `compile_revert_with_reason _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [expr_type_def]) >>
  `64 + type_memory_bytes cenv (BaseT (StringT ml)) < dimword(:256)` by decide_tac >>
  `?z Gf tnf. !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (Abort Revert_abort z,Gf,tnf)` by
    (irule reason_literal_encoder_origin_ptr_mods >>
     qpat_assum `compile_revert_with_reason _ _ _ _ _ = _` (irule_at Any) >>
     simp[] >>
     qexistsl_tac [`sa`,`s0`,`d`] >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  irule gas_outcome_full_mods_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`es`,`Abort Revert_abort z`,`INR (AssertException str)`,`tnf`] >>
  simp[eval_raise_string_literal_reason, fragExecTheory.exit_result_def,
       stmt_exit_ptr_def, expr_exit_def, halt_exit_def] >>
  rpt strip_tac >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`G1`,`t`,`tn1`] >>
  conj_tac >> first_x_assum drule >> simp[]
QED

Finalise compile_raise_reason_literal_frag_full_mods
