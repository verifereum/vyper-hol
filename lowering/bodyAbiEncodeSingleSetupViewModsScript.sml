(* The standalone encoder sees one saved operand at the setup landing. *)
Theory bodyAbiEncodeSingleSetupViewMods
Ancestors
  bodyAbiEncodePackedPostMods bodyPtrIfExpAllocSource bodyMemoryDefs bodyFullPostsMods
  stateRelProj typedMemoryCopy logValueFramePtr revertReasonPrefixPtr
  valueEncodingTyping valueEncodingDefs bodyPtrDefs exprSimProps exprSimMemDefs exprLoweringProps freshWrites
  context loweringStateRelDefs loweringPosts ptrDiscipline venomMemDefs
  venomState finite_map pred_set arithmetic list pair

Theorem setup_saved_operand[local]:
  (!x. op = Var x ==> not_fresh_at st x) /\
  (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s /\
     FLOOKUP Gpre x = FLOOKUP G x /\ op_taint tnpre (Var x) = op_taint tn (Var x)) /\
  pre.vs_labels = s.vs_labels ==>
  eval_operand op pre = eval_operand op s /\
  op_taint tnpre op = op_taint tn op /\
  op_prov Gpre op = op_prov G op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_taint_def, op_prov_def] >>
  metis_tac[op_taint_def]
QED

Theorem setup_region_kept[local]:
  local_ptrs_reserved ce st /\ st.cs_next_var <= allocated.cs_next_var /\
  (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s) /\
  typed_copy_state_frame allocated off n u pre ==>
  (local_region ce scopes pre name b sz <=> local_region ce scopes s name b sz) /\
  (local_region ce scopes pre name b sz <=> local_region ce scopes u name b sz)
Proof
  strip_tac >> conj_tac >> irule local_region_lookup_cong
  >- (rpt strip_tac >> first_x_assum irule >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  rpt strip_tac >> fs[typed_copy_state_frame_def] >>
  qpat_assum `!x. not_fresh_at allocated x ==> _` irule >>
  irule not_fresh_at_mono >> qexists `st` >> simp[] >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem setup_saved_memory_window[local]:
  stmt_state_rel H ctx func ce cx ee s /\
  expr_val_at ce cx ty si ss ee v op s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\ ss.cs_next_id <= st.cs_next_id /\
  (!aid b n. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
     regions_disjoint p N b n) /\
  (!name b n. local_region ce ee.scopes s name b n ==> regions_disjoint p N b n) ==>
  val_wf tv v /\
  (val_footprint tv v = 0 \/ w2n w + val_footprint tv v <= s.vs_alloca_next) /\
  (val_footprint tv v = 0 \/ regions_disjoint p N (w2n w) (val_footprint tv v))
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  simp[] >> strip_tac >> gvs[]
  >- (`aid < st.cs_next_id` by decide_tac >>
      `regions_disjoint p N b sz` by metis_tac[] >>
      `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
      fs[alloca_inv_def, alloca_next_valid_def] >>
      `b + sz <= s.vs_alloca_next` by metis_tac[] >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `regions_disjoint p N b sz` by metis_tac[] >>
  drule_all_then assume_tac body_local_region_frontier >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem setup_preserves_window[local]:
  val_wf tv v /\ 32+write_len <= N /\
  (val_footprint tv v = 0 \/ a + val_footprint tv v <= s.vs_alloca_next) /\
  (val_footprint tv v = 0 \/ regions_disjoint p N a (val_footprint tv v)) /\
  (!b n. b+n <= p+32 \/ p+32+write_len <= b ==>
     mem_bytes_at b n pre.vs_memory = mem_bytes_at b n s.vs_memory) /\
  (!i. i < s.vs_alloca_next /\ i IN tnpre.t_mem ==> i IN tn.t_mem) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v a m) ==>
  !m. mem_agree_outside tnpre.t_mem pre.vs_memory m ==> val_in_memory tv v a m
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> disch_tac >> irule robust_val_in_memory_footprint_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`s.vs_memory`,`pre.vs_memory`,`tn.t_mem`,`tnpre.t_mem`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  Cases_on `val_footprint tv v = 0` >- simp[mem_bytes_at_def] >>
  first_x_assum irule >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem setup_saved_ptr[local]:
  ptr_mem_ok cx ty v op G tn s /\
  eval_operand op pre = eval_operand op s /\ op_prov Gpre op = op_prov G op /\
  (!tv w. evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op s = SOME w ==>
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
    !m. mem_agree_outside tnpre.t_mem pre.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
  ptr_mem_ok cx ty v op Gpre tnpre pre
Proof
  Cases_on `op` >> simp[ptr_mem_ok_def, op_prov_def] >> metis_tac[]
QED

Theorem setup_saved_stack[local]:
  ~is_word_type ty /\ read_result cx raw ee = (INL v,ee) /\
  vv_holds_mods ce cx ty raw (StackValue tag op) ee s /\
  ptr_vv_ok cx ty raw (StackValue tag op) ee G tn s /\
  eval_operand op pre = eval_operand op s /\ op_prov Gpre op = op_prov G op /\
  op_taint tnpre op = op_taint tn op /\
  (!tv w. evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op s = SOME w ==>
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
    !m. mem_agree_outside tnpre.t_mem pre.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
  vv_holds_mods ce cx ty raw (StackValue tag op) ee pre /\
  ptr_vv_ok cx ty raw (StackValue tag op) ee Gpre tnpre pre
Proof
  simp[vv_holds_mods_def, vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def, expr_val_rel_def] >>
  strip_tac >> gvs[] >>
  `ptr_mem_ok cx ty v op Gpre tnpre pre` by
    (irule setup_saved_ptr >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `ptr_mem_ok _ _ _ _ _ _ pre` (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
  disch_then (qspecl_then [`tv`,`w`] mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `!m. mem_agree_outside _ _ m ==> _`
    (qspec_then `pre.vs_memory` mp_tac) >> simp[mem_agree_outside_def]
QED

Theorem setup_saved_read[local]:
  ~is_word_type ty /\ read_result cx raw ee = (INL v,ee) /\
  vv_holds_mods ce cx ty raw (LocatedValue tag q) ee s /\
  ptr_vv_ok cx ty raw (LocatedValue tag q) ee G tn s /\
  eval_operand q.ptr_operand pre = eval_operand q.ptr_operand s /\
  op_prov Gpre q.ptr_operand = op_prov G q.ptr_operand /\
  op_taint tnpre q.ptr_operand = op_taint tn q.ptr_operand /\
  tnpre.t_stor = tn.t_stor /\ tnpre.t_trans = tn.t_trans /\
  pre.vs_accounts = s.vs_accounts /\ pre.vs_transient = s.vs_transient /\
  pre.vs_call_ctx = s.vs_call_ctx /\
  (q.ptr_location = LocMemory ==>
   !tv w. evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand q.ptr_operand s = SOME w ==>
     (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
     !m. mem_agree_outside tnpre.t_mem pre.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
  vv_holds_mods ce cx ty raw (LocatedValue tag q) ee pre /\
  ptr_vv_ok cx ty raw (LocatedValue tag q) ee Gpre tnpre pre
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `q.ptr_location = LocMemory`
  >- (`ptr_mem_ok cx ty v q.ptr_operand G tn s` by gvs[ptr_vv_ok_def] >>
      `ptr_mem_ok cx ty v q.ptr_operand Gpre tnpre pre` by
        (irule setup_saved_ptr >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
      conj_tac
      >- (gvs[vv_holds_mods_def, vv_holds_def] >>
          rpt strip_tac >> rename1 `evaluate_type _ ty = SOME tv` >>
          qpat_assum `ptr_mem_ok _ _ _ _ _ _ pre`
            (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
          disch_then (qspecl_then [`tv`,`w`] mp_tac) >> simp[] >> strip_tac >>
          qpat_assum `!m. mem_agree_outside _ _ m ==> _`
            (qspec_then `pre.vs_memory` mp_tac) >> simp[mem_agree_outside_def]) >>
      gvs[ptr_vv_ok_def]) >>
  conj_tac
  >- (Cases_on `q.ptr_location` >>
      fs[vv_holds_mods_def, vv_holds_def, immutable_holds_mods_def,
         immutable_holds_def, storage_holds_def, contract_storage_def, contract_transient_def] >>
      metis_tac[]) >>
  irule ptr_vv_ok_nonmemory_frame >> simp[] >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]
QED

Theorem setup_saved_code_wf[local]:
  vv_holds_mods ce cx ty raw (LocatedValue tag q) ee s /\ q.ptr_location = LocCode /\
  read_result cx raw ee = (INL v,ee) /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
  val_wf tv v
Proof
  simp[vv_holds_mods_def, immutable_holds_mods_def, immutable_holds_def] >>
  strip_tac >> gvs[] >> drule_then ACCEPT_TAC (cj 1 value_has_type_val_wf)
QED

(* Keep the setup result fixed: the output row refers to this very pre/Gpre/tnpre. *)
Theorem abi_encode_single_setup_view_mods:
  single /\ ~is_word_type (lowered_value_type ce e) /\
  abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
    [e] [sv] sa st es s0 G0 tn0 H (INL [v]) ee G tn s /\
  local_ptrs_reserved ce st /\ st.cs_next_var <= allocated.cs_next_var /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP pre.vs_allocas aid = SOME entry) /\
  (!aid b n. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
     regions_disjoint p N b n) /\
  (!name b n. local_region ce ee.scopes u name b n ==> regions_disjoint p N b n) /\
  (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s /\
     FLOOKUP Gpre x = FLOOKUP G x /\ op_taint tnpre (Var x) = op_taint tn (Var x)) /\
  lo <= s.vs_alloca_next /\ s.vs_alloca_next <= pre.vs_alloca_next /\
  lo <= p /\ 32+write_len <= N /\
  typed_copy_state_frame allocated (p+32) write_len u pre /\
  (!b n. b+n <= p+32 \/ p+32+write_len <= b ==>
     mem_bytes_at b n pre.vs_memory = mem_bytes_at b n s.vs_memory) /\
  (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < p+N)) /\
  tnpre.t_mem = tu.t_mem DIFF {i | p+32 <= i /\ i < p+32+write_len} /\
  tnpre.t_stor = tn.t_stor /\ tnpre.t_trans = tn.t_trans /\
  pre.vs_accounts = s.vs_accounts /\ pre.vs_transient = s.vs_transient /\
  pre.vs_call_ctx = s.vs_call_ctx /\ pre.vs_labels = s.vs_labels ==>
  ?si sm ss vv copy raw.
    abi_encode_saved_row_mods lo ce cx sa st e sv v si sm ss vv copy H ee G tn s /\
    abi_encode_saved_row_mods lo ce cx sa ready e sv v si sm ss vv copy H ee Gpre tnpre pre /\
    (!x. vv_operand sv = Var x ==> not_fresh_at ready x) /\
    read_result cx raw ee = (INL v,ee) /\
    vv_holds_mods ce cx (lowered_value_type ce e) raw sv ee pre /\
    vv_at ce cx (lowered_value_type ce e) si ss ee raw sv pre /\
    ptr_vv_ok cx (lowered_value_type ce e) raw sv ee Gpre tnpre pre /\
    vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw sv pre
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_encode_packed_post_mods` mp_tac >>
  simp[abi_encode_packed_post_mods_def] >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`] assume_tac)
    (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  qpat_x_assum `?raw. read_result _ raw _ = _ /\ _`
    (qx_choose_then `raw` (map_every assume_tac o CONJUNCTS)) >>
  `!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s` by simp[] >>
  `!name b n. (local_region ce ee.scopes pre name b n <=> local_region ce ee.scopes s name b n) /\
              (local_region ce ee.scopes pre name b n <=> local_region ce ee.scopes u name b n)` by
    (rpt gen_tac >> irule setup_region_kept >>
     qpat_assum `typed_copy_state_frame _ _ _ _ _` (irule_at Any) >> qexists `st` >> simp[]) >>
  `!name b n. local_region ce ee.scopes s name b n ==> regions_disjoint p N b n` by
    (rpt gen_tac >> disch_tac >>
     `local_region ce ee.scopes u name b n` by metis_tac[] >>
     first_x_assum drule >> simp[]) >>
  `!i. i < s.vs_alloca_next /\ i IN tnpre.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> gvs[IN_DIFF, GSPECIFICATION] >>
     qpat_assum `!i. i IN tu.t_mem <=> _` (qspec_then `i` mp_tac) >> simp[]) >>
  `eval_operand (vv_operand sv) pre = eval_operand (vv_operand sv) s /\
   op_taint tnpre (vv_operand sv) = op_taint tn (vv_operand sv) /\
   op_prov Gpre (vv_operand sv) = op_prov G (vv_operand sv)` by
    (irule setup_saved_operand >> simp[] >> qexists `st` >> simp[]) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at ready x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `st` >> simp[]) >>
  `!n b sz. local_region ce ee.scopes pre n b sz <=> local_region ce ee.scopes s n b sz` by simp[] >>
  `vv_at ce cx (lowered_value_type ce e) si ss ee raw sv pre` by
    (irule vv_at_alloc_map_frame >> qexistsl_tac [`s`,`ss`] >> simp[]) >>
  `vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw sv pre` by
    (irule vv_store_bound_frame_mem_src >> qexists `s` >> simp[]) >>
  suspend "observe"
QED

Resume abi_encode_single_setup_view_mods[observe]:
  `vv_location sv = NONE \/ vv_location sv = SOME LocMemory ==>
     expr_val_at ce cx (lowered_value_type ce e) si ss ee v (vv_operand sv) s` by
    (Cases_on `sv` >> simp[vv_location_def, vv_operand_def]
     >- fs[vv_at_def] >> strip_tac >> drule_all_then ACCEPT_TAC vv_at_memory_val_at) >>
  `vv_location sv = NONE \/ vv_location sv = SOME LocMemory ==>
   !tv w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
          eval_operand (vv_operand sv) s = SOME w ==>
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
    !m. mem_agree_outside tnpre.t_mem pre.vs_memory m ==> val_in_memory tv v (w2n w) m` by
    (disch_tac >> rpt gen_tac >> disch_then strip_assume_tac >> disch_tac >>
     `expr_val_at ce cx (lowered_value_type ce e) si ss ee v (vv_operand sv) s` by
       (qpat_assum `_ ==> expr_val_at _ _ _ _ _ _ _ _ _` (drule_then ACCEPT_TAC)) >>
     drule_all_then (map_every assume_tac o CONJUNCTS) setup_saved_memory_window >>
     gen_tac >> disch_tac >> drule_all_then ACCEPT_TAC setup_preserves_window) >>
  `vv_holds_mods ce cx (lowered_value_type ce e) raw sv ee pre /\
   ptr_vv_ok cx (lowered_value_type ce e) raw sv ee Gpre tnpre pre` by
    (Cases_on `sv` >> rule_assum_tac (SIMP_RULE (srw_ss()) [vv_location_def,vv_operand_def])
     >- drule_all_then ACCEPT_TAC setup_saved_stack >>
     drule_all_then ACCEPT_TAC setup_saved_read) >>
  suspend "assemble"
QED

Resume abi_encode_single_setup_view_mods[assemble]:
  `vv_storage_live H cx sv ee pre` by
    (Cases_on `sv` >> fs[vv_storage_live_def,vv_operand_def]) >>
  `ptr_buf_ok ce e (vv_operand sv) G s ==> ptr_buf_ok ce e (vv_operand sv) Gpre pre` by
    (disch_tac >> irule ptr_buf_ok_frame >> qexistsl_tac [`G`,`s`] >>
     simp[] >> rpt strip_tac >> fs[op_prov_def]) >>
  `sm.cs_next_var <= ready.cs_next_var /\ sm.cs_next_id <= ready.cs_next_id /\
   ss.cs_next_var <= ready.cs_next_var /\ ss.cs_next_id <= ready.cs_next_id` by decide_tac >>
  qexistsl_tac [`si`,`sm`,`ss`,`vv`,`copy`,`raw`] >> asm_rewrite_tac[] >>
  asm_rewrite_tac[abi_encode_saved_row_mods_def] >>
  conj_tac
  >- (disch_tac >>
      qpat_assum `copy /\ _ ==> ?p w tv. _` (drule_all_then strip_assume_tac) >>
      `FLOOKUP pre.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv)` by
        (qpat_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _`
          (drule_then ACCEPT_TAC)) >>
      qexistsl_tac [`p'`,`w`,`tv`] >> asm_rewrite_tac[]) >>
  conj_tac >- (qexists `raw` >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `ptr_buf_ok ce e op G s` by
        (qpat_assum `!tag op. sv = StackValue tag op /\ _ ==> _`
          (drule_all_then ACCEPT_TAC)) >>
      `vv_operand sv = op` by simp[vv_operand_def] >>
      qpat_assum `vv_operand sv = _` (fn th =>
        qpat_assum `ptr_buf_ok ce e (vv_operand sv) G s ==> _`
          (drule_then ACCEPT_TAC o REWRITE_RULE [th]))) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rename1 `sv = LocatedValue tag q` >>
      `ptr_buf_ok ce e q.ptr_operand G s` by
        (qpat_assum `!tag p. sv = LocatedValue tag p /\ _ ==> _`
          (drule_all_then ACCEPT_TAC)) >>
      `vv_operand sv = q.ptr_operand` by simp[vv_operand_def] >>
      qpat_assum `vv_operand sv = _` (fn th =>
        qpat_assum `ptr_buf_ok ce e (vv_operand sv) G s ==> _`
          (drule_then ACCEPT_TAC o REWRITE_RULE [th]))) >>
  disch_then strip_assume_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `ce.ce_is_ctor /\ vv_location sv = SOME LocCode ==> _` (drule_all_then strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `val_wf rt v` by
    (Cases_on `sv` >> fs[vv_location_def] >> drule_all_then ACCEPT_TAC setup_saved_code_wf) >>
  `val_footprint rt v <= type_memory_size rt` by (irule val_footprint_le >> simp[]) >>
  `(val_footprint rt v = 0 \/ w2n w + val_footprint rt v <= s.vs_alloca_next) /\
   (val_footprint rt v = 0 \/ regions_disjoint p N (w2n w) (val_footprint rt v))`
    suffices_by (disch_then (map_every assume_tac o CONJUNCTS) >>
                 gen_tac >>
                 qpat_assum `tnpre.t_mem = _` (fn th =>
                   disch_then (assume_tac o REWRITE_RULE [SYM th])) >>
                 drule_all_then ACCEPT_TAC setup_preserves_window) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Finalise abi_encode_single_setup_view_mods
