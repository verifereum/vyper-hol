Theory bodyLogSavedRowAdvanceMods
Ancestors
  bodyAbiEncodePackedPostMods bodyLogSavedValueFrameMods
  bodyLogSavedMemoryPtrFrameMods bodyLogSavedNonmemoryPtrMods
  bodyExtSavedCtorReadMods bodyExtOwnedRowEndpointMods
  exprSimSubscriptArrayFrame targetPurePostTransport
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs
  stateRelProj stateRelProjStorage loweringPosts loweringShapeDefs
  exprLoweringProps compileEnv venomState context words arithmetic

Theorem log_saved_row_advance_mods:
  abi_encode_saved_row_mods lo ce cx origin front e sv v si sm ss vv copy H ee G tn s /\
  (!x. vv_operand sv = Var x ==> not_fresh_at front x) /\
  (!l. vv_operand sv <> Label l) /\
  front.cs_next_id <= a.cs_next_id /\
  front.cs_next_var <= a.cs_next_var /\
  local_ptrs_reserved ce front /\
  wb_frame ce ee ee front s u /\
  ghost_kept_at lo ce ee front G tn s Gu tu /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  stmt_state_rel H ctx func ce cx ee s /\
  stmt_state_rel H ctx func ce cx ee u /\
  immutable_frame_mods func ce cx ee u /\
  ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u /\
  dead_lo_ok_mods H (DF H) lo ce cx /\
  contract_inv mods exps ctx ce cx /\
  expr_sim_inv_mods mods ce cx env ee ==>
  abi_encode_saved_row_mods lo ce cx origin a e sv v si sm ss vv copy H ee Gu tu u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  simp[abi_encode_saved_row_mods_def] >>
  rpt (conj_tac THEN1 (first_assum ACCEPT_TAC)) >>
  `wb_frame ce ee ee ss s u` by
    (qpat_assum `wb_frame ce ee ee front s u`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     simp[wb_frame_def] >> conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at front x` by
           metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
         qpat_assum `!y w. not_fresh_at front y /\ lookup_var y s = SOME w ==>
                         lookup_var y u = SOME w`
           (qspecl_then [`x`,`w`] mp_tac) >>
         disch_tac >>
         qpat_assum `not_fresh_at front x /\ lookup_var x s = SOME w ==>
                         lookup_var x u = SOME w` (drule_then assume_tac) >>
         qpat_assum `lookup_var x s = SOME w ==> lookup_var x u = SOME w`
           (drule_then ACCEPT_TAC))
     >- (rpt strip_tac >>
         `aid < front.cs_next_id` by
           simp[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
         qpat_assum `!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
             aid < front.cs_next_id /\
             (!n b sz'. local_region ce ee.scopes s n b sz' ==>
                off + sz <= b \/ b + sz' <= off) ==>
             mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory`
           (qspecl_then [`aid`,`off`,`sz`] (drule_all_then ACCEPT_TAC)))) >>
  `ghost_kept_at lo ce ee ss G tn s Gu tu` by
    (irule wordArgsPtrTheory.ghost_kept_at_trans >>
     qexistsl [`G`,`ee`,`s`,`front`,`tn`] >>
     conj_tac >- simp[wordArgsPtrTheory.ghost_kept_at_refl] >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     conj_tac >- simp[ghost_kept_at_def] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel H ctx func ce cx ee s`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  `!n b sz. local_region ce ee.scopes u n b sz <=>
      local_region ce ee.scopes s n b sz` by
    (rpt gen_tac >> irule local_region_wb_frame >> metis_tac[]) >>
  qpat_assum `wb_frame ce ee ee front s u`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  qpat_x_assum `?raw. read_result cx raw ee = _ /\ _`
    (qx_choose_then `raw` (map_every assume_tac o CONJUNCTS)) >>
  conj_tac >-
    (disch_tac >>
     qpat_assum `copy /\ ~is_word_type (lowered_value_type ce e)` strip_assume_tac >>
     qpat_assum `copy /\ ~is_word_type (lowered_value_type ce e) ==> _` mp_tac >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
     disch_then (qx_choosel_then [`p`,`w`,`tv`]
       (map_every assume_tac o CONJUNCTS)) >>
     qexistsl [`p`,`w`,`tv`] >>
     asm_rewrite_tac[] >>
     `eval_operand (vv_operand sv) u = SOME w` by
       (drule_all_then ACCEPT_TAC exprBopSimPropsTheory.eval_operand_frame) >>
     qpat_assum `vv_operand sv = Var p`
       (fn th => rule_assum_tac (PURE_REWRITE_RULE[th])) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
         FLOOKUP u.vs_allocas aid = SOME b`
       (qspecl_then [`sm.cs_next_id`,`(w2n w,type_memory_size tv)`]
         (drule_then ACCEPT_TAC)))
  >> `?w. eval_operand (vv_operand sv) s = SOME w` by
       (Cases_on `sv`
        >- (gvs[vv_holds_mods_def, vv_holds_def, expr_val_rel_def, vv_operand_def] >>
            first_assum ACCEPT_TAC)
        >- (rename1 `LocatedValue ty p` >>
            qpat_assum `vv_holds_mods _ _ _ _ _ _ _`
              (fn th => rule_assum_tac
                (PURE_REWRITE_RULE[vv_holds_mods_def, vv_holds_def,
                                   expr_val_rel_def, vv_operand_def])) >>
            Cases_on `p.ptr_location` >> gvs[vv_operand_def] >>
            first_assum ACCEPT_TAC))
  >> `eval_operand (vv_operand sv) u = SOME w` by
       (drule_all_then ACCEPT_TAC exprBopSimPropsTheory.eval_operand_frame) >>
  `eval_operand (vv_operand sv) u = eval_operand (vv_operand sv) s` by simp[] >>
  `vv_holds_mods ce cx (lowered_value_type ce e) raw sv ee u /\
   vv_at ce cx (lowered_value_type ce e) si ss ee raw sv u /\
   vv_storage_live H cx sv ee u` by
    (irule bodyLogSavedValueFrameModsTheory.log_saved_value_frame_mods >>
     qexistsl_tac [`ctx`,`front`,`func`,`s`] >>
     rpt (conj_tac THEN1 first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `!q. not_fresh_at front q ==>
      FLOOKUP Gu q = FLOOKUP G q /\
      op_taint tu (Var q) = op_taint tn (Var q)` by
    (rpt strip_tac >>
     qpat_assum `ghost_kept_at lo ce ee front G tn s Gu tu`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `!x. not_fresh_at front x ==> _`
       (qspec_then `q` mp_tac) >> simp[]) >>
  `!x. vv_operand sv = Var x ==> FLOOKUP Gu x = FLOOKUP G x` by
    (rpt strip_tac >>
     qpat_assum `!q. not_fresh_at front q ==> _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `op_taint tu (vv_operand sv) = op_taint tn (vv_operand sv)` by
    (Cases_on `vv_operand sv` >> simp[ptrDisciplineTheory.op_taint_def] >>
     rename1 `vv_operand sv = Var x` >>
     qpat_assum `!q. not_fresh_at front q ==> _`
       (qspec_then `x` mp_tac) >>
     simp[ptrDisciplineTheory.op_taint_def]) >>
  `op_prov Gu (vv_operand sv) = op_prov G (vv_operand sv)` by
    (Cases_on `vv_operand sv` >> simp[ptrDisciplineTheory.op_prov_def]) >>
  `vv_location sv = SOME LocMemory ==> ~is_word_type (lowered_value_type ce e)` by
    (qpat_assum `(?tag op0. sv = StackValue tag op0) \/ _` mp_tac >>
     strip_tac >> gvs[vv_location_def]) >>
  conj_tac >-
    (qexists_tac `raw` >>
     rpt (conj_tac THEN1 first_assum ACCEPT_TAC) >>
     conj_tac
     >- (Cases_on `vv_location sv = NONE \/ vv_location sv = SOME LocMemory`
         >- (drule_all_then ACCEPT_TAC log_saved_memory_ptr_frame) >>
         qpat_x_assum `(?tag op0. sv = StackValue tag op0) \/ _` strip_assume_tac >>
         gvs[Excl "vv_storage_live_def", vv_location_def, vv_operand_def] >>
         qpat_x_assum `ptr_vv_ok _ _ _ _ _ G tn s`
           (strip_assume_tac o REWRITE_RULE [ptr_vv_ok_def]) >>
         `op_taint tu p.ptr_operand = {}` by simp[] >>
         `p.ptr_location = LocCode ==> op_prov Gu p.ptr_operand = NONE` by simp[] >>
         drule_all_then ACCEPT_TAC log_saved_nonmemory_ptr_mods) >>
     drule_all exprSimMemDefsTheory.vv_store_bound_frame_mem_src >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `ptr_buf_ok ce e (vv_operand sv) G s ==> ptr_buf_ok ce e (vv_operand sv) Gu u` by
    (strip_tac >> irule logValueFramePtrTheory.ptr_buf_ok_frame >>
     qexistsl_tac [`G`,`s`] >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> gvs[vv_operand_def]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> gvs[vv_operand_def]) >>
  strip_tac >>
  qpat_x_assum `(?tag op0. sv = StackValue tag op0) \/ _` strip_assume_tac >>
  gvs[vv_location_def, vv_operand_def] >>
  drule ext_saved_ctor_read_linked >>
  disch_then (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `dead_lo_ok_mods _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
  disch_then (qspecl_then [`v`,`expr_type e`,`p`] mp_tac) >>
  `?raw. read_result cx raw ee = (INL v,ee) /\
     vv_holds_mods ce cx (expr_type e) raw (LocatedValue (expr_type e) p) ee u`
    suffices_by (disch_tac >> simp[]) >>
  qexists_tac `raw` >> simp[]
QED
