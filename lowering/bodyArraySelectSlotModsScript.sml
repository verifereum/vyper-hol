(* Package the reached slot selection, retaining its one counted endpoint. *)
Theory bodyArraySelectSlotMods
Ancestors
  bodyArraySlotReachedRegionMods bodyArraySlotReachedOperandsMods
  bodyArrayObservedSlotOperandMods bodyArraySlotSelectReplayMods
  bodyArraySlotElementLandingMods bodyArrayNoCopyKeyFramesMods bodyArraySelectReadonlyMods
  bodyArrayNoCopyCutsMods bodySubscriptArrayRouteDefsMods
  gasOutcomeFullPostMods targetSubscriptStorage bodyFullTargetArrayLoad
  vyperStorageFootprint vyperLookupStorage vyperStorage vyperStorageBackend
  bodyFullShadowBodyInv bodyFullPostsMods loweringPosts exprSimDefs fragExec freshWrites
  ptrDiscipline exprLowering compileEnv context vyperState vyperAST integer_word words

Theorem array_select_slot_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  subscript_array_unframed_case_mods cenv cx obj idx et bd /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = PlaceR (StoragePlace tr slot vt) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx ann obj idx et bd st0
    (es,s0,G0,tn0) (sa,sb,dst,loc) (raw,key) (fin,it,Gi,tni)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac array_slot_reached_region_mods >>
  drule_all_then strip_assume_tac array_slot_reached_operands_mods >>
  drule_then (qspec_then `et` strip_assume_tac) (GEN_ALL array_nocopy_key_prefix_frames_mods) >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `loc = slot_loc tr` SUBST_ALL_TAC >>
  qpat_x_assum `vt = ArrayTV _ _` SUBST_ALL_TAC >>
  qpat_x_assum `raw = PlaceR _` SUBST_ALL_TAC >>
  qhdtm_x_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  suspend "replay"
QED

Resume array_select_slot_mods[replay]:
  qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ fin it /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. _ ==> (?off root path delta. _) /\ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `?off root path delta. _` kall_tac >>
  qpat_x_assum `bvv = LocatedValue _ _` SUBST_ALL_TAC >>
  qpat_x_assum `slot_loc tr = case _ of NONE => _ | SOME _ => _` kall_tac >>
  `allocas_from lo it` by fs[ghost_inv_at_mods_def] >>
  `!x. vv_operand (LocatedValue (ArrayT et bd) p) = Var x ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `!cap. bd = Dynamic cap ==>
    key_taint (if tr then tni.t_trans else tni.t_stor) slot = {}` by
    (rpt strip_tac >>
     qpat_assum `!H. dead_lo_ok_mods _ _ _ _ _`
       (qspec_then `H0` assume_tac) >>
     `eval_operand p.ptr_operand it = SOME slot /\ op_taint tni p.ptr_operand = {}` by
       fs[vv_operand_def] >>
     drule_all (Q.INST [`p` |-> `p`, `ty` |-> `ArrayT et bd`, `ann` |-> `et`]
       array_observed_slot_operand_mods) >> simp[]) >>
  `!cap. bd = Dynamic cap ==>
    (if tr then tload slot it else sload slot it) = lookup_storage slot (get_storage cx fin tr) /\
    w2n (lookup_storage slot (get_storage cx fin tr)) <= cap` by
    (rpt strip_tac >> qpat_x_assum `bd = Dynamic _` SUBST_ALL_TAC
     >- (drule_all (cj 2 target_storage_array_len_ok) >> simp[])
     >- (qpat_x_assum `slots_in_range _ _ _` mp_tac >>
         PURE_REWRITE_TAC [slots_in_range_def,read_slot_def,LET_THM,n2w_w2n] >>
         Cases_on `w2n (lookup_storage slot (get_storage cx fin tr)) <= cap` >> simp[])) >>
  qpat_assum `word_scale (slot_loc tr) = 1` (fn scale =>
    qpat_assum `elem_size_in_location cenv (slot_loc tr) et = _` (fn size =>
      qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
        (assume_tac o REWRITE_RULE [scale,size]))) >>
  qabbrev_tac `dyn = case bd of Fixed _ => F | Dynamic _ => T` >>
  qabbrev_tac `cnt = case bd of Fixed n => n | Dynamic _ => 0` >>
  qabbrev_tac `nw = if dyn then (if tr then tload slot it else sload slot it) else n2w cnt` >>
  `(dyn ==> key_taint (if tr then tni.t_trans else tni.t_stor) slot = {})` by
    (strip_tac >> Cases_on `bd` >> fs[Abbr `dyn`]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by simp[] >>
  qunabbrev_tac `dyn` >> qunabbrev_tac `cnt` >>
  drule_at (Pat `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE [LET_THM] array_slot_select_replay_mods)) >>
  disch_then (drule_at (Pat `fn_has_code st2 sb func`)) >>
  disch_then (drule_at (Pat `eval_operand (vv_operand _) it = _`)) >>
  disch_then (drule_at (Pat `eval_operand iop it = _`)) >>
  disch_then (drule_at (Pat `op_prov Gi iop = NONE`)) >>
  disch_then (drule_at (Pat `op_taint tni iop = _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain cx st0 fin.storage_trace`)) >>
  disch_then (drule_at (Pat `key = IntV i`)) >>
  disch_then (drule_at (Pat `allocas_from lo it`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca ctx ==> allocas_below_fmp it`)) >>
  disch_then (qspecl_then [`nw`,`gas_explicit_sites ctx shadow_ctx`,`et`,`PG`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[Abbr `nw`])) >>
  disch_then (qx_choosel_then [`res`,`q`,`Gq`,`tq`] (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw nw` >- suspend "success" >>
  qpat_assum `~idx_in_range _ _ _ ==> _` (drule_then strip_assume_tac) >>
  pure_rewrite_tac[array_select_outcome_mods_def,LET_THM] >> BETA_TAC >>
  irule gas_outcome_full_mods_exit_revert >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gq`,`fin`,`res`,`tq`,`q`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_def] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `~idx_in_range _ _ _` (fn test =>
    qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
      (qspec_then `DF H` (ACCEPT_TAC o REWRITE_RULE [test])))
QED

Resume array_select_slot_mods[success]:
  qpat_assum `idx_in_range _ _ _ ==> _` (drule_then strip_assume_tac) >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  `sa.cs_next_var <= st2.cs_next_var /\ s0.vs_alloca_next <= it.vs_alloca_next` by decide_tac >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `((if (case bd of Fixed _ => F | Dynamic _ => T) then 1 else 0):num) =
    (case bd of Fixed _ => 0 | Dynamic _ => 1)` by (Cases_on `bd` >> simp[]) >>
  qpat_assum `(if (case bd of Fixed _ => F | Dynamic _ => T) then 1 else 0) = _` (fn th =>
    qpat_x_assum `res = INL _` (assume_tac o REWRITE_RULE [th]) >>
    qpat_x_assum `eval_operand dst q = _` (assume_tac o REWRITE_RULE [th])) >>
  pure_rewrite_tac[array_select_outcome_mods_def,LET_THM] >> BETA_TAC >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gq`,`fin`,`res`,`q`,`tq`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >> conj_tac
  >- (qpat_assum `idx_in_range _ _ _` (fn test =>
        qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
          (qspec_then `DF H` (ACCEPT_TAC o REWRITE_RULE [test])))) >>
  suspend "landing"
QED

Resume array_select_slot_mods[landing]:
  qpat_assum `!h. _ ==> stmt_state_rel h _ _ _ _ fin it /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. _ ==> (?off root path delta. _) /\ _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `?off root path delta. _` kall_tac >>
  drule_all_then strip_assume_tac
    (Q.INST [`H` |-> `H`, `D` |-> `DF H`] array_select_readonly_suffix_mods) >>
  `~expr_has_effect (Subscript et obj idx) ==> pure_frame cenv func es sa s0 q` by
    (strip_tac >> qpat_assum `pure_frame _ _ _ _ _ it ==> _` irule >> simp[]) >>
  drule_all_then strip_assume_tac
    (Q.INST [`H` |-> `H`, `sb` |-> `sb`, `obj` |-> `obj`, `idx` |-> `idx`]
      (CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE [LET_THM] array_slot_element_landing_mods))) >>
  qpat_x_assum `!b. storage_place_observed _ _ /\ _`
    (qspec_then `sb` strip_assume_tac) >>
  qpat_assum `!H. dead_lo_ok_mods _ _ _ _ _` (qspec_then `H` assume_tac) >>
  `ptr_vv_ok cx et (PlaceR (StoragePlace tr
     (slot + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + Num i * type_slot_size etv)) etv))
     (LocatedValue et (mk_ptr dst (slot_loc tr))) fin Gq tq q` by
    (irule (CONJUNCT1 (REWRITE_RULE [IMP_CONJ_THM] array_observed_slot_operand_mods)) >>
     ntac 4 (conj_tac >- simp[mk_ptr_def]) >>
     qexistsl [`DF H`,`H`,`cenv`,`d`,`lo`] >> asm_rewrite_tac[]) >>
  `slot_loc tr <> LocCode /\ slot_loc tr <> LocMemory` by (Cases_on `tr` >> simp[slot_loc_def]) >>
  `s0.vs_alloca_next <= q.vs_alloca_next` by asm_rewrite_tac[] >>
  qpat_x_assum `i = _` kall_tac >>
  asm_rewrite_tac[] >>
  fs[mk_ptr_def,vv_location_def,post_value_type_def,expr_type_def,lowered_value_type_def]
QED

Finalise array_select_slot_mods
