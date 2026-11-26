(* Unwrap the reached default operand after allocating its destination.
   The unwrap can allocate its own scratch, at the later compiler cursor. *)
Theory bodyExtKeywordDefaultUnwrapMods
Ancestors
  bodyIfExpArmUnwrapMods bodyPtrIfExpAllocSource reasonEndpointResourcesPtr
  bodyFullPostsMods bodyFullShadowBodyInv exprLoweringProps exprOperandVar exprSimCopy
  exprSimIfExpWidenedAdapter
  freshWrites loweringHalt exprSimMemUnwrap exprLowering compileEnv
  fragGasOriginPtr fragGasPathPtr fragGasPathFrameMem stateRelProj
  ptrDiscipline bodyPtrDefs loweringPosts loweringStateRelDefs
  vyperStorageFootprint venomMemDefs context words finite_map arithmetic

Theorem default_unwrap_disjoint[local]:
  alloca_inv z /\ FLOOKUP z.vs_allocas dst = SOME (d,n) /\
  (!name b len. local_region ce ee.scopes z name b len ==>
    regions_disjoint d n b len) /\
  (f = 0 \/
   (?aid b len. aid <> dst /\ FLOOKUP z.vs_allocas aid = SOME (b,len) /\
      b <= i /\ i + f <= b + len) \/
   (?name b len. local_region ce ee.scopes z name b len /\
      b <= i /\ i + f <= b + len)) ==>
  f = 0 \/ regions_disjoint d n i f
Proof
  strip_tac >- simp[] >> disj2_tac >> pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >-
    (fs[alloca_inv_def,allocas_non_overlapping_def] >>
     qpat_assum `!a1 a2 b1 sz1 b2 sz2. _ ==> _`
       (drule_all_then strip_assume_tac) >> decide_tac) >>
  qpat_assum `!name b len. local_region _ _ _ _ _ _ ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  decide_tac
QED

Theorem default_unwrap_identity_region[local]:
  vv_at ce cx ty sa sm ee tv vv s /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!name b len. local_region ce ee.scopes u name b len <=>
                local_region ce ee.scopes s name b len) /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  read_result cx tv ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ ~is_word_type ty /\
  eval_operand (vv_operand vv) u = SOME sw /\
  (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) /\
  0 < val_footprint ptv v ==>
  (?aid b len. FLOOKUP u.vs_allocas aid = SOME (b,len) /\ aid < sm.cs_next_id /\
      b <= w2n sw /\ w2n sw + val_footprint ptv v <= b + len) \/
  (?name b len. local_region ce ee.scopes u name b len /\
      b <= w2n sw /\ w2n sw + val_footprint ptv v <= b + len)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vv_at ce cx ty sa sm ee tv vv u` by
    (irule vv_at_alloc_map_frame >> qexistsl [`s`,`sm`] >> simp[] >> metis_tac[]) >>
  irule vv_at_memory_region_prefix >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `vv_at _ _ _ _ _ _ _ _ u` (irule_at Any) >>
  qpat_assum `read_result _ _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand _ u = SOME sw` (irule_at Any) >>
  simp[LESS_EQ_REFL] >> Cases_on `vv` >> fs[vv_operand_def]
QED

(* A non-memory, nonword unwrap emits an ALLOCA. The identity result
   therefore certifies the original VV shape, not the synthetic memory VV. *)
Theorem default_unwrap_identity_shape[local]:
  unwrap_value ce vv sn = (src,sn) /\ fn_has_code sn sn func /\
  vv_holds_mods ce cx ty tv vv ee u /\ ~is_word_type ty ==>
  (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory)
Proof
  Cases_on `vv` >- simp[] >> simp[] >> strip_tac >>
  rename1 `unwrap_value ce (LocatedValue tag p) sn = (src,sn)` >>
  CCONTR_TAC >>
  `p.ptr_location <> LocCalldata /\ tag = ty` by
    (qpat_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[vv_holds_mods_def,vv_holds_def]) >>
  `~is_word_type tag` by simp[] >>
  `?n buf mid. compile_alloc_buffer n sn = (buf,mid) /\
    mid.cs_next_id <= sn.cs_next_id` suffices_by
    (strip_tac >> drule_then strip_assume_tac compile_alloc_buffer_parts >> decide_tac) >>
  Cases_on `p.ptr_location = LocCode`
  >- (
    `?buf mid. compile_alloc_buffer (type_memory_bytes ce tag) sn = (buf,mid) /\
      compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand
        buf.buf_operand ((type_memory_bytes ce tag + 31) DIV 32) 0 mid = ((),sn)` by
      (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
       simp[unwrap_value_def,compile_ensure_in_memory_def,
            comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
       pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
    `ci_mono mid sn` by
      (metis_tac[ci_mono_compile_imm_copy_to_memory,pairTheory.SND]) >>
    qexistsl [`type_memory_bytes ce tag`,`buf`,`mid`] >> fs[ci_mono_def]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` suffices_by
    (disch_tac >> drule_all_then strip_assume_tac storage_unwrap_layout_facts >>
     qexistsl [`type_memory_bytes ce tag`,`buf`,`mid`] >> simp[]) >>
  Cases_on `p.ptr_location` >> fs[]
QED

Theorem default_unwrap_vv_cursor[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv u /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_post_mods H ctx func ce cx e es sa sn s0 ee tv vv u
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  asm_rewrite_tac[vv_post_mods_def] >> conj_tac
  >- (irule vv_at_alloc_mono_frame >> qexistsl [`u`,`sm`] >> simp[]) >>
  strip_tac >> irule vv_own_alloc_mono_frame >> qexistsl [`u`,`sm`] >> simp[]
QED

Theorem ext_kw_default_unwrap_entry_mods:
  compile_expr ce ty e sa = (vv,sm) /\ unwrap_value ce vv sn = (src,sc) /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id < sn.cs_next_id /\
  fn_has_code sn sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sn /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  vv_post_mods (storage_trace_horizon ee.storage_trace) ctx func ce cx
    e es sa sm s0 ee tv vv s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv u /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta u) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv u /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee Ga ta u /\
  (!tag x. vv = StackValue tag x ==> ptr_buf_ok ce e x Ga u) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand Ga u) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?a. read_result cx tv ee = (INL a,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ta.t_mem u.vs_memory mem ==>
          val_in_memory rt a (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 Ga ta /\
  ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!name b len. local_region ce ee.scopes u name b len <=>
                local_region ce ee.scopes s name b len) /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
  not_fresh_at sn q /\ lookup_var q u = SOME dw /\ ptr_covers Ga ta q u n /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n dw,n) /\
  FLOOKUP Ga q = SOME (w2n dw,n) /\ w2n dw + n <= u.vs_alloca_next /\
  (!name b len. local_region ce ee.scopes u name b len ==>
    regions_disjoint (w2n dw) n b len) ==>
  ?z Gf tf sw.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Ga,ta) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post_mods H ctx func ce cx e es sa sc s0 ee v src z /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    ghost_kept_at lo ce ee sn Ga ta u Gf tf /\ wb_frame ce ee ee sn u z /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x u /\
      FLOOKUP Gf x = FLOOKUP Ga x /\ op_taint tf (Var x) = op_taint ta (Var x)) /\
    (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    alloca_history func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
    u.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    z.vs_alloca_next < dimword (:256) /\
    z.vs_labels = u.vs_labels /\ ~z.vs_halted /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    local_ptrs_reserved ce sc /\ not_fresh_at sc q /\ lookup_var q z = SOME dw /\
    ptr_covers Gf tf q z n /\ FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,n) /\
    FLOOKUP Gf q = SOME (w2n dw,n) /\ w2n dw + n <= z.vs_alloca_next /\
    (!name b len. local_region ce ee.scopes z name b len ==>
      regions_disjoint (w2n dw) n b len) /\
    eval_operand src z = SOME sw /\ (!x. src = Var x ==> not_fresh_at sc x) /\
    ptr_mem_ok cx (post_value_type ce e) v src Gf tf z /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size ltv /\
    value_has_type ltv v /\ val_wf ltv v /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory ltv v (w2n sw) mem) /\
    (type_memory_size ltv <> 0 ==>
      (?x. src = Var x /\ ptr_covers Gf tf x z (type_memory_size ltv)) /\
      w2n sw + type_memory_size ltv <= z.vs_alloca_next) /\
    (val_footprint ptv v = 0 \/
      regions_disjoint (w2n dw) n (w2n sw) (val_footprint ptv v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sm.cs_next_id <= sn.cs_next_id` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sn s0 ee tv vv u /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ _ _ _ sm _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- (irule default_unwrap_vv_cursor >> qexists `sm` >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ _ _ _ sm _ _ _ _ u /\ _`
    kall_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`)
    (Q.INST [`s` |-> `u`, `G` |-> `Ga`, `tn` |-> `ta`] ifexp_arm_nonword_unwrap_mods) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`a`,`z`,`Gf`,`tf`,`pt`,`rt`,`sw`]
      (map_every assume_tac o CONJUNCTS))) >>
  `a = v /\ pt = ptv /\ rt = ltv` by fs[] >>
  qpat_x_assum `a = v` SUBST_ALL_TAC >>
  qpat_x_assum `pt = ptv` SUBST_ALL_TAC >>
  qpat_x_assum `rt = ltv` SUBST_ALL_TAC >>
  `sn.cs_next_var <= sc.cs_next_var` by
    (qspecl_then [`ce`,`vv`,`sn`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def])) >>
  `alloca_inv z /\ z.vs_alloca_next < dimword (:256)` by
    (conj_tac >- (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     drule stmt_state_rel_alloca_room >> disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `z.vs_labels = u.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Ga,ta) [] _`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_path_ptr_erase >>
     disch_then (mp_tac o MATCH_MP gas_path_code_labels) >> simp[]) >>
  `not_fresh_at sc q /\ local_ptrs_reserved ce sc` by
    metis_tac[not_fresh_at_mono,local_ptrs_reserved_next_var] >>
  `lookup_var q z = SOME dw /\ FLOOKUP Gf q = SOME (w2n dw,n)` by
    (qpat_assum `!x. not_fresh_at sn x ==> lookup_var x z = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!name b len. local_region ce ee.scopes z name b len ==>
    regions_disjoint (w2n dw) n b len` by
    (rpt strip_tac >> qpat_assum `!name b len. local_region ce ee.scopes u name b len ==> _` irule >>
     qexists `name` >>
     `!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x u` by simp[] >>
     drule_all copy_buffer_local_region_frame >>
     disch_then (qspecl_then [`ee.scopes`,`name`,`b`,`len`] mp_tac) >> simp[]) >>
  `!x. src = Var x ==> not_fresh_at sc x` by suspend "source_var" >>
  `val_footprint ptv v = 0 \/ regions_disjoint (w2n dw) n (w2n sw) (val_footprint ptv v)` by
    suspend "separation" >>
  `s0.vs_alloca_next <= z.vs_alloca_next /\ w2n dw + n <= z.vs_alloca_next` by
    (conj_tac >> irule LESS_EQ_TRANS >> qexists `u.vs_alloca_next` >> asm_rewrite_tac[]) >>
  `ptr_covers Gf tf q z n /\ FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,n)` by simp[] >>
  `ptr_mem_ok cx (post_value_type ce e) v src Gf tf z` by fs[ptr_val_ok_def] >>
  qexistsl [`z`,`Gf`,`tf`,`sw`] >> asm_rewrite_tac[] >> strip_tac >>
  (conj_tac
   >- (`0 < type_memory_size ltv` by simp[GSYM NOT_ZERO_LT_ZERO] >>
       qpat_assum `0 < type_memory_size ltv ==> _` (drule_then strip_assume_tac) >>
       qexists `r` >> asm_rewrite_tac[]) >>
   qpat_assum `type_memory_size ltv = 0 \/ _` mp_tac >> simp[])
QED

Resume ext_kw_default_unwrap_entry_mods[source_var]:
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >>
     drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >>
     disch_then (drule_then assume_tac o cj 1) >>
     irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `(case vv of StackValue _ op => !x. op = Var x ==> not_fresh_at sn x
             | LocatedValue _ p => !x. p.ptr_operand = Var x ==> not_fresh_at sn x)` by
    (Cases_on `vv` >> fs[vv_operand_def]) >>
  rpt strip_tac >> drule_all_then ACCEPT_TAC compiler_unwrap_value_var
QED

Resume ext_kw_default_unwrap_entry_mods[separation]:
  Cases_on `val_footprint ptv v = 0` >- asm_rewrite_tac[] >>
  irule default_unwrap_disjoint >>
  `FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,n)` by simp[] >>
  qpat_assum `FLOOKUP z.vs_allocas _ = SOME _` (irule_at Any) >>
  qexistsl [`ee`,`ce`] >> asm_rewrite_tac[] >>
  qpat_x_assum `(sc = sn /\ _) \/ _` strip_assume_tac
  >- (
    qpat_x_assum `z = u` SUBST_ALL_TAC >>
    qpat_x_assum `sc = sn` SUBST_ALL_TAC >>
    qpat_x_assum `src = vv_operand vv` SUBST_ALL_TAC >>
    `vv_holds_mods ce cx (post_value_type ce e) tv vv ee u` by
      (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ u /\ _`
        (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >>
       first_assum ACCEPT_TAC) >>
    drule_all_then assume_tac default_unwrap_identity_shape >>
    qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s`
      (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
    `0 < val_footprint ptv v` by simp[GSYM NOT_ZERO_LT_ZERO] >>
    drule_all_then strip_assume_tac default_unwrap_identity_region
    >- (disj1_tac >> qexistsl [`aid`,`b`,`len`] >> asm_rewrite_tac[] >>
        strip_tac >> qpat_assum `aid < _` mp_tac >> simp[]) >>
    disj2_tac >> qexistsl [`name`,`b`,`len`] >> asm_rewrite_tac[]) >>
  `ptv = ltv` by fs[] >> qpat_x_assum `ptv = ltv` SUBST_ALL_TAC >>
  drule_then assume_tac exprSimPropsTheory.val_footprint_le >>
  disj1_tac >> qexistsl [`sn.cs_next_id`,`w2n sw`,`type_memory_size ltv`] >>
  simp[] >> strip_tac >> qpat_assum `sm.cs_next_id < _` mp_tac >> simp[]
QED

Finalise ext_kw_default_unwrap_entry_mods
