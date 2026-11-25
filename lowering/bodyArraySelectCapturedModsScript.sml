(* The index must not replace the local entry from which Pop captured
   a subarray.  This protects its popped history, not all local scopes. *)
Theory bodyArraySelectCapturedMods
Ancestors
  bodyArrayNoCopyCutsMods bodySubscriptArrayRouteDefsMods
  exprSimHypsDefs allocLimits targetOverlapAccess vyperLocalAccessFrame
  vyperSubscriptOverlap vyperInterpreter vyperState vyperAST
  bodyArrayCapturedSourceMods bodyArrayCapturedOperandsMods bodyArrayCapturedAtKeyMods
  bodyArrayCapturedFixedChildMods bodyArrayCapturedFixedResponseMods
  bodyArrayFixedCountedPathMods bodyArrayNoCopyKeyFramesMods bodyArraySelectReadonlyMods
  gasOutcomeFullPostMods exprLoweringProps freshWrites vyperStatePreservation
  vyperStorageFootprint bodyFullShadowBodyInv bodyFullTargetArrayLoad
  loweringPosts bodyFullPostsMods ptrDiscipline exprSimDefs fragExec
  context exprLowering compileEnv venomState words

Theorem captured_read_local_ref[local]:
  MEM (ReadAcc (LocalRef id)) accs ==>
  MEM (LocalRef id) (nonconstant_reads mods accs)
Proof
  qid_spec_tac `accs` >> qid_spec_tac `mods` >>
  recInduct nonconstant_reads_ind >> rw[nonconstant_reads_def] >>
  rpt (CASE_TAC >> gvs[]) >> metis_tac[]
QED

Theorem captured_pop_index_local_mods[local]:
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  eval_expr cx obj (es with gas_obs := gs1) = (INL (PlaceR (MemoryPlace id path)),mid) /\
  is_ArrayT (expr_type obj) /\ base_from_pop obj /\
  eval_expr cx idx (mid with gas_obs := gs2) = (res,fin) ==>
  lookup_scopes id fin.scopes = lookup_scopes id mid.scopes
Proof
  strip_tac >>
  `MEM (LocalRef id)
    (nonconstant_reads cenv.ce_modules (expr_accesses cenv.ce_modules obj))` by
    (irule captured_read_local_ref >> simp[expr_accesses_def] >>
     drule eval_expr_memory_access >> simp[]) >>
  `~MEM (WriteAcc (LocalRef id)) (accesses_expr idx)` suffices_by
    (strip_tac >> drule_all eval_expr_unwritten_local >> simp[]) >>
  strip_tac >>
  `pop_subscript_overlap cenv.ce_modules obj idx` by
    (simp[pop_subscript_overlap_def, any_written_MEM] >>
     conj_tac >- (strip_tac >> gvs[]) >>
     disj1_tac >> qexists `LocalRef id` >> simp[expr_accesses_def]) >>
  fs[expr_body_pre_mods_def, alloc_limits_expr_def]
QED

Theorem array_select_captured_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  subscript_array_unframed_case_mods cenv cx obj idx et bd /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  bd = Fixed n /\ raw = PlaceR (MemoryPlace id path) /\ base_from_pop obj ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx ann obj idx et bd st0
    (es,s0,G0,tn0) (sa,sb,dst,loc) (raw,key) (fin,it,Gi,tni)
Proof
  strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac (SIMP_RULE std_ss [] (Q.INST [`raw` |-> `PlaceR (MemoryPlace id path)`] array_captured_source_mods)) >>
  drule_all_then strip_assume_tac (SIMP_RULE std_ss [] (Q.INST [`raw` |-> `PlaceR (MemoryPlace id path)`] array_captured_operands_mods)) >>
  drule_then (qspec_then `ann` strip_assume_tac) (GEN_ALL array_nocopy_key_prefix_frames_mods) >>
  qpat_x_assum `ann = et` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
  qpat_x_assum `bvv = LocatedValue _ _` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  `lookup_scopes id fin.scopes = lookup_scopes id mid.scopes` by
    (qpat_assum `bind (eval_expr cx idx) _ _ = _` (mp_tac o MATCH_MP bind_split) >>
     simp[] >> rpt strip_tac >> drule read_result_state >> disch_then SUBST_ALL_TAC >>
     irule captured_pop_index_local_mods >>
     goal_assum (drule_at (Pat `eval_expr cx obj _ = _`)) >>
     goal_assum (drule_at (Pat `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _`)) >>
     goal_assum (drule_at (Pat `eval_expr cx idx _ = _`)) >> simp[is_ArrayT_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  `post_value_type cenv obj = ArrayT ann (Fixed n) /\
   lowered_value_type cenv obj = ArrayT ann (Fixed n)` by simp[] >>
  drule_all_then strip_assume_tac array_captured_at_key_mods >>
  suspend "counted"
QED

Resume array_select_captured_mods[counted]:
  `allocas_from lo it` by
    (qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ fin it /\ _`
       (drule_then strip_assume_tac) >> fs[ghost_inv_at_mods_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [vv_operand_def,elem_size_in_location_def,is_slot_addressed_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by simp[] >>
  drule_all (GEN_ALL array_fixed_counted_path_mods) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `IntV i` >>
  `i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))` by simp[Abbr `i`] >>
  drule_all_then (strip_assume_tac o CONV_RULE (DEPTH_CONV BETA_CONV) o
                   REWRITE_RULE [LET_THM]) array_captured_fixed_response_mods >>
  qpat_x_assum `Abbrev (i = _)` kall_tac >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)`
  >- suspend "success" >>
  qpat_x_assum `~idx_in_range _ _ _ ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _` mp_tac >>
  simp[] >> strip_tac >>
  pure_rewrite_tac[array_select_outcome_mods_def,LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  irule gas_outcome_full_mods_exit >>
  conj_tac >-
    (qexistsl [`Gq`,`fin`,`Abort Revert_abort q`,`INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tq`] >>
     simp[exit_result_def,expr_exit_def,halt_exit_def]) >>
  simp[]
QED

Resume array_select_captured_mods[success]:
  qpat_x_assum `idx_in_range _ _ _ ==> ?v. _` (drule_then strip_assume_tac) >>
  qpat_x_assum `idx_in_range _ _ _ ==> ~q.vs_halted /\ _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _` mp_tac >> simp[] >> strip_tac >>
  `st2.cs_next_id <= sb.cs_next_id` by
    (`ci_mono st2 sb` suffices_by simp[ci_mono_def] >>
     qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[ci_mono_compile_array_subscript,ci_mono_compile_ptr_load]) >>
  `n * type_memory_size etv <> 0 ==>
    w2n w + n * type_memory_size etv <= it.vs_alloca_next /\
    ?b sz. op_prov Gi p.ptr_operand = SOME (b,sz) /\ b <= w2n w /\
           w2n w + n * type_memory_size etv <= b + sz` by
    (strip_tac >> `0 < n * type_memory_size etv` by decide_tac >>
     qpat_assum `0 < n * type_memory_size etv ==> _` (drule_then strip_assume_tac) >>
     simp[] >> qexistsl [`b`,`sz`] >> simp[op_prov_def]) >>
  qpat_assum `type_memory_bytes cenv ann = _` (fn size =>
    qpat_x_assum `eval_operand dst q = _` (assume_tac o REWRITE_RULE [size])) >>
  qabbrev_tac `r' = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))` >>
  qabbrev_tac `childvv = LocatedValue ann (mk_ptr dst LocMemory)` >>
  `vv_at cenv cx ann sa sb fin r' childvv q /\
   vv_place_ptr cenv cx fin q r' childvv /\ vv_holds cenv cx ann r' childvv fin q /\
   ptr_vv_ok cx ann r' childvv fin Gq tq q /\ vv_store_bound cx ann ann fin r' childvv q /\
   ptr_buf_ok cenv (Subscript ann obj idx) dst Gq q` by
    (unabbrev_all_tac >>
     irule (CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE [LET_THM]
              (Q.INST [`esz` |-> `type_memory_size etv`] array_captured_fixed_child_mods))) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `vv_at _ _ _ sa st2 fin _ _ it`)) >>
     goal_assum (drule_at (Pat `array_length_frame st2 it Gi tni q Gq tq`)) >>
     goal_assum (drule_at (Pat `read_result cx (PlaceR (MemoryPlace id (_ ++ _))) fin = (INL v,fin)`)) >>
     goal_assum (drule_at (Pat `place_ptr_rel cenv cx it _ w _ _`)) >>
     goal_assum (drule_at (Pat `array_index _ (SArrayV kvs) i = SOME v`)) >>
     goal_assum (drule_at (Pat `eval_operand dst q = SOME (w + iw * _)`)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[array_select_outcome_mods_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gq`,`fin`,`INL r'`,`q`,`tq`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >> conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H` ACCEPT_TAC)) >>
  suspend "post"
QED

Resume array_select_captured_mods[post]:
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ fin it /\ _`
    (drule_then strip_assume_tac) >>
  `sa.cs_next_var <= st2.cs_next_var /\ s0.vs_alloca_next <= it.vs_alloca_next` by decide_tac >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `q.vs_alloca_next = it.vs_alloca_next /\ q.vs_memory = it.vs_memory /\
   q.vs_allocas = it.vs_allocas /\ (allocas_below_fmp it ==> allocas_below_fmp q)` by
    (qpat_assum `array_length_frame st2 _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[array_length_frame_def,venom_state_component_equality,allocas_below_fmp_def] >>
     rw[]) >>
  (* The suffix's internal theorem does not require equality of absent
     variables across the prefix.  Use that weaker interface here. *)
  FAIL_TAC "waiting for the weaker readonly suffix interface" >>
  qexists `r'` >> unabbrev_all_tac >>
  qpat_assum `wb_frame cenv es fin sa s0 q`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  simp[mk_ptr_def,vv_location_def,expr_type_def,lowered_value_type_def,
       vv_post_mods_def,vv_holds_mods_def,vv_place_ptr_mods_def] >>
  rpt conj_tac >- decide_tac >>
  strip_tac >> drule_then (fn th => simp[th]) pure_frame_state_cong
QED

Finalise array_select_captured_mods
