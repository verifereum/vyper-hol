(* Transport the linked normal post to the destination of the typed store. *)
Theory bodyExtKeywordDefaultLandingMods
Ancestors
  bodyIfExpTypedImmFrameMods bodyIfExpTypedGhostMods exprSimIfExpWidenedCounted
  bodyFullPostsMods bodyFullPathHistory bodyMemoryDefs exprSimCopy
  exprSimWordArgs exprSimProps exprSimAlloc loweringHalt exprLoweringProps
  stateRelProj typedMemoryCopy loweringStateRelDefs
  loweringPosts bodyPtrDefs ptrDiscipline freshWrites vyperStorageTrace vyperStorageFootprint
  venomState venomInst compileEnv words finite_map

Theorem default_landing_root_frames[local]:
  wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\
  sa.cs_next_var <= sc.cs_next_var /\
  (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x z /\
    FLOOKUP Gfin x = FLOOKUP Gz x /\ op_taint tt (Var x) = op_taint tz (Var x)) /\
  t.vs_allocas = z.vs_allocas /\ typed_copy_frame b n z.vs_memory t.vs_memory /\
  (!i. ~(b <= i /\ i < b+n) ==> (i IN tt.t_mem <=> i IN tz.t_mem)) /\
  (!aid a len. FLOOKUP s0.vs_allocas aid = SOME (a,len) /\ aid < sa.cs_next_id ==>
    a+len <= b \/ b+n <= a) /\
  (!name a len. local_region ce es.scopes s0 name a len ==>
    a+len <= b \/ b+n <= a) ==>
  wb_frame ce es ee sa s0 t /\ ghost_kept_at lo ce es sa Gi ti s0 Gfin tt
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    metis_tac[not_fresh_at_mono] >>
  `!a len. a+len <= b \/ b+n <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len z.vs_memory` by
    fs[typed_copy_frame_def] >>
  `!a len i. (a+len <= b \/ b+n <= a) /\ a <= i /\ i < a+len /\
     i IN tt.t_mem ==> i IN tz.t_mem` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `~(b <= i /\ i < b+n)` by decide_tac >>
     qpat_assum `!j. ~(b <= j /\ _) ==> _`
       (qspec_then `i` (mp_tac o UNDISCH)) >>
     simp[]) >>
  conj_tac
  >- (`locals_kept ce es ee s0 t` by
        (irule locals_kept_regions_tail >> qexists `z` >> fs[wb_frame_def] >>
         rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
      fs[wb_frame_def] >> rpt strip_tac >> metis_tac[]) >>
  fs[ghost_kept_at_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem default_landing_payload[local]:
  dt = lowered_value_type ce e /\ ~is_word_type dt /\
  evaluate_type (get_tenv cx) dt = SOME ltv /\ val_wf ltv v /\
  type_memory_bytes ce dt = type_memory_size ltv /\ lookup_var q t = SOME dw /\
  FLOOKUP Gfin q = SOME (w2n dw,type_memory_size ltv) /\ op_taint tt (Var q) = {} /\
  (!mem. mem_agree_outside tt.t_mem t.vs_memory mem ==>
    val_in_memory ltv v (w2n dw) mem) /\
  w2n dw + type_memory_size ltv <= t.vs_alloca_next ==>
  ptr_val_ok cx dt v (Var q) Gfin tt t /\ ptr_mem_ok cx dt v (Var q) Gfin tt t /\
  ptr_buf_ok ce e (Var q) Gfin t /\
  (!w. eval_operand (Var q) t = SOME w /\ type_memory_bytes ce dt <> 0 ==>
    w2n w + type_memory_bytes ce dt <= t.vs_alloca_next)
Proof
  strip_tac >>
  `ptr_mem_ok cx dt v (Var q) Gfin tt t` by
    simp[ptr_mem_ok_def,eval_operand_def,val_store_size_le] >>
  conj_tac >- simp[ptr_val_ok_def] >>
  qpat_x_assum `dt = lowered_value_type ce e` SUBST_ALL_TAC >>
  simp[ptr_buf_ok_def,eval_operand_def]
QED

Theorem ext_kw_default_owned_landing_mods:
  dt = lowered_value_type ce e /\ ~is_word_type dt /\
  evaluate_type (get_tenv cx) dt = SOME ltv /\ val_wf ltv v /\
  type_memory_bytes ce dt = type_memory_size ltv /\
  compile_alloc_buffer (type_memory_size ltv) sm = (buf,sn) /\
  buf.buf_operand = Var q /\ fn_has_code sm sn func /\
  compile_store_memory ce src (Var q) dt dt sc = ((),sb) /\ ci_mono sn sc /\
  sa.cs_next_id <= sm.cs_next_id /\ sa.cs_next_var <= sc.cs_next_var /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n dw) (type_memory_size ltv) b len) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sc /\ not_fresh_at sc q /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e es sa sc s0 ee v src z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
  ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\ return_buf_frame d ce sa s0 /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\ z.vs_labels = s0.vs_labels /\
  alloca_history func z /\ allocas_from lo z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  lookup_var q z = SOME dw /\ ptr_covers Gz tz q z (type_memory_size ltv) /\
  FLOOKUP Gz q = SOME (w2n dw,type_memory_size ltv) /\
  FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size ltv) /\
  w2n dw + type_memory_size ltv <= z.vs_alloca_next /\
  (!name b len. local_region ce ee.scopes z name b len ==>
    regions_disjoint (w2n dw) (type_memory_size ltv) b len) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK t,Gfin,tt)) /\
  (!mem. mem_agree_outside tt.t_mem t.vs_memory mem ==>
    val_in_memory ltv v (w2n dw) mem) /\
  typed_copy_state_frame sc (w2n dw) (type_memory_size ltv) z t /\
  (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x z /\
    FLOOKUP Gfin x = FLOOKUP Gz x /\ op_taint tt (Var x) = op_taint tz (Var x)) /\
  (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size ltv) ==>
       (i IN tt.t_mem <=> i IN tz.t_mem)) /\
  tt.t_stor = tz.t_stor /\ tt.t_trans = tz.t_trans /\ tt.t_imm = tz.t_imm /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ~t.vs_halted ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gfin tt t) /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ~t.vs_halted /\ alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_kept_at lo ce es sa Gi ti s0 Gfin tt /\
  return_buf_frame d ce sb t /\ wb_frame ce es ee sa s0 t /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  t.vs_labels = s0.vs_labels /\ not_fresh_at sb q /\ dt = lowered_value_type ce e /\
  ptr_val_ok cx dt v (Var q) Gfin tt t /\ ptr_mem_ok cx dt v (Var q) Gfin tt t /\
  ptr_buf_ok ce e (Var q) Gfin t /\
  (!w. eval_operand (Var q) t = SOME w /\ type_memory_bytes ce dt <> 0 ==>
    w2n w + type_memory_bytes ce dt <= t.vs_alloca_next) /\
  eval_operand (Var q) t = SOME dw /\ evaluate_type (get_tenv cx) dt = SOME ltv /\
  val_wf ltv v /\
  FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size ltv) /\
  sm.cs_next_id < sb.cs_next_id /\
  (!name b len. local_region ce ee.scopes t name b len ==>
    regions_disjoint (w2n dw) (type_memory_size ltv) b len)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size ltv))] [q])
     (fn_insts func)` by
    (qpat_assum `compile_alloc_buffer _ sm = _` (mp_then Any mp_tac buffer_alloc_code) >>
     disch_then (qspec_then `func` (drule_then mp_tac)) >>
     qpat_assum `compile_alloc_buffer _ sm = _`
       (mp_then Any mp_tac compile_alloc_buffer_parts) >>
     disch_then (mp_tac o cj 1) >>
     qpat_assum `buf.buf_operand = Var q` (fn th =>
       simp[NoAsms,th,operand_11] >> disch_then SUBST1_TAC >> simp[])) >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size ltv))] [q]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sm.cs_next_id` by simp[Abbr `inst`,mk_inst_def] >>
  `FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size ltv)` by simp[] >>
  suspend "static"
QED

Resume ext_kw_default_owned_landing_mods[static]:
  `sm.cs_next_id < sn.cs_next_id` by
    (drule_then mp_tac compile_alloc_buffer_parts >> simp[]) >>
  `ci_mono sc sb` by
    (qpat_assum `compile_store_memory _ _ _ _ _ sc = _`
       (SUBST1_TAC o SYM o SRULE [] o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     simp[ci_mono_compile_store_memory]) >>
  `sm.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
   sc.cs_next_var <= sb.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `not_fresh_at sb q` by metis_tac[not_fresh_at_mono] >>
  `t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
   t.vs_labels = z.vs_labels /\ t.vs_initial_fmp = z.vs_initial_fmp /\
   t.vs_fmp = z.vs_fmp` by
    fs[typed_copy_state_frame_def,venom_state_component_equality] >>
  `typed_copy_frame (w2n dw) (type_memory_size ltv) z.vs_memory t.vs_memory` by
    fs[typed_copy_state_frame_def] >>
  `lookup_var q t = SOME dw /\ FLOOKUP Gfin q = SOME (w2n dw,type_memory_size ltv) /\
   op_taint tt (Var q) = {}` by
    (qpat_assum `ptr_covers Gz tz q z _`
       (assume_tac o cj 1 o REWRITE_RULE [ptr_covers_def]) >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `w2n dw + type_memory_size ltv <= t.vs_alloca_next` by simp[] >>
  drule_all_then strip_assume_tac default_landing_payload >>
  `!name b len. local_region ce ee.scopes t name b len <=>
    local_region ce ee.scopes z name b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `sc` >>
     simp[]) >>
  `!name b len. local_region ce ee.scopes z name b len ==>
    w2n dw + type_memory_size ltv <= b \/ b+len <= w2n dw` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name b len. local_region ce ee.scopes z name b len ==> _`
       (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `lo <= w2n dw` by
    (qhdtm_assum `allocas_from` (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def])) >>
  suspend "root"
QED

Resume ext_kw_default_owned_landing_mods[root]:
  drule_then assume_tac expr_post_frame >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee z` by
    (qhdtm_assum `expr_post` (ACCEPT_TAC o cj 1 o REWRITE_RULE [expr_post_def])) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `!aid a len. FLOOKUP s0.vs_allocas aid = SOME (a,len) /\ aid < sa.cs_next_id ==>
    a+len <= w2n dw \/ w2n dw + type_memory_size ltv <= a` by
    (rpt strip_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (a,len)` by simp[] >>
     `aid < sm.cs_next_id` by decide_tac >>
     qpat_assum `!id b len. id < sm.cs_next_id /\ _ ==> _` (drule_all_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
  `!name a len. local_region ce es.scopes s0 name a len ==>
    a+len <= w2n dw \/ w2n dw + type_memory_size ltv <= a` by
    (rpt strip_tac >> `local_region ce ee.scopes z name a len` by
       (irule local_region_frame_fwd >> qexistsl [`s0`,`sa`,`es.scopes`] >>
        fs[wb_frame_def]) >>
     qpat_assum `!n b len. local_region ce ee.scopes z n b len ==> _ \/ _`
       (drule_then mp_tac) >> simp[DISJ_COMM]) >>
  drule_all_then strip_assume_tac default_landing_root_frames >>
  `return_buf_frame d ce sb t` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s0`,`sa`] >> fs[wb_frame_def]) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK t,Gfin,tt)`
      (qspec_then `DF (storage_trace_horizon ee.storage_trace)` assume_tac) >>
     drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (simp[allocas_below_fmp_def] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp z`
       (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])) >>
  conj_tac
  >- suspend "horizon" >>
  qpat_assum `wb_frame ce es ee sa s0 t`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  simp[eval_operand_def] >> rpt strip_tac >>
  qpat_assum `!name b len. local_region ce ee.scopes z name b len ==> regions_disjoint _ _ b len`
    (drule_then ACCEPT_TAC)
QED

Resume ext_kw_default_owned_landing_mods[horizon]:
  gen_tac >> disch_tac >>
  qpat_assum `!J. valid_horizon _ _ J _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def])) >>
  conj_tac >- (drule_all_then ACCEPT_TAC typed_copy_semantic_frame) >>
  conj_tac >- (drule_all_then ACCEPT_TAC ifexp_typed_immutable_frame_mods) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `local_ptrs_rel func ce ee.scopes z` by fs[stmt_state_rel_local_ptrs_alloca] >>
  `!x. not_fresh_at sc x ==> FLOOKUP Gfin x = FLOOKUP Gz x /\
     op_taint tt (Var x) = op_taint tz (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  drule_all_then ACCEPT_TAC ifexp_typed_copy_ghost_mods
QED

Finalise ext_kw_default_owned_landing_mods
