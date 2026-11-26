(* Join both bound cases at the reached key, keeping the stored array Value. *)
Theory bodyArraySelectValueMods
Ancestors
  bodyArrayNoCopyCutsMods bodySubscriptArrayRouteDefsMods
  bodyArrayOwnedSourceKeyMods bodyArrayOwnedMemoryAtKeyMods
  bodyArrayNoCopyKeyFramesMods bodyArrayFixedCountedPathMods
  bodyArrayOwnedFixedReplayMods bodyArrayOwnedDynamicReplayMods
  bodyArraySelectReadonlyMods bodyArrayOwnedSelectViewMods
  bodyFullShadowBodyInv bodyPtrDefs freshWrites exprLoweringProps
  exprLowering compileEnv context vyperAST vyperStorageFootprint

Theorem array_select_value_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  subscript_array_unframed_case_mods cenv cx obj idx et bd /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = Value v ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx ann obj idx et bd st0
    (es,s0,G0,tn0) (sa,sb,dst,loc) (raw,key) (fin,it,Gi,tni)
Proof
  strip_tac >> drule_all_then strip_assume_tac array_owned_source_key_mods >>
  qpat_x_assum `raw = Value v` SUBST_ALL_TAC >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  qhdtm_x_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  drule_all_then strip_assume_tac array_owned_memory_at_key_mods >>
  qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
  drule_then (qspec_then `et` strip_assume_tac) array_nocopy_key_prefix_frames_mods >>
  qhdtm_x_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  `sa.cs_next_var <= st2.cs_next_var /\ s0.vs_alloca_next <= it.vs_alloca_next` by decide_tac >>
  `!x. vv_operand bvv = Var x ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by
    (strip_tac >> qpat_assum `ctx_has_dalloca ctx ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `st2.cs_next_id <= sb.cs_next_id` by
    (`ci_mono st2 sb` suffices_by simp[ci_mono_def] >>
     qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load]) >>
  `allocas_from lo it` by
    (`valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. _ ==> expr_post_mods H ctx func cenv cx idx mid sm st2 s fin _ iop it /\ _`
       (drule_then strip_assume_tac) >>
     fs[ghost_inv_at_mods_def]) >>
  `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory =
     (\op. emit_op MLOAD [op])` by simp[FUN_EQ_THM, compile_ptr_load_def] >>
  qpat_assum `type_memory_bytes cenv et = type_memory_size etv` (fn size =>
    qpat_assum `compile_ptr_load _ _ LocMemory = _` (fn load =>
      qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
        (assume_tac o SIMP_RULE (srw_ss())
           [elem_size_in_location_def, is_slot_addressed_def, word_scale_def, size, load]))) >>
  irule array_owned_run_outcome_mods >> simp[IgnAsm `i = if _ then _ else _`] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ fin it /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qexists `st2` >> simp[IgnAsm `i = if _ then _ else _`] >>
  Cases_on `bd` >> fs[IgnAsm `i = if _ then _ else _`]
  >- suspend "fixed"
  >> suspend "dynamic"
QED

Resume array_select_value_mods[fixed]:
  `eval_operand (vv_operand bvv) it = SOME a /\ op_taint tni (vv_operand bvv) = {}` by
    fs[array_owned_memory_view_mods_def] >>
  drule_all array_fixed_counted_path_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac) >>
  drule_all array_owned_fixed_replay_mods >> simp[]
QED

Resume array_select_value_mods[dynamic]:
  drule_all array_owned_dynamic_replay_mods >> simp[]
QED

Finalise array_select_value_mods
