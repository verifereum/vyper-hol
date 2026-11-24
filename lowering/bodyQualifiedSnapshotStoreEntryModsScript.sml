(* The forced snapshot allocates before unwrapping its open value. *)
Theory bodyQualifiedSnapshotStoreEntryMods
Ancestors
  bodyIfExpAllocMods bodyIfExpArmUnwrapMods bodyCopyReadPhysicalTypeMods bodyFullShadowBodyInv
  exprPtrUnwrapStorageShape bodyFullPostsMods loweringPosts exprLowering
  exprLoweringProps context compileEnv fragExec loweringHalt exprSimUnwrap
  bodyFullAllocaFresh bodyMemoryDefs exprSimAlloc freshWrites
  bodyPtrDefs fragGasOriginPtr vyperStorageFootprint words finite_map arithmetic
  exprSimWordArgs exprSimProps abiCallerAllocation stateRelProj loweringStateRelDefs
  vyperEvalExprPreservesScopesDom vyperState valueTypingMemoryProps valueCopyBytes

Theorem snapshot_retag_nonword[local]:
  compile_expr ce ty e sa = (vv,sm) /\
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  ~is_word_type (post_value_type ce e) /\
  ~is_word_type (lowered_value_type ce e) ==>
  unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) = unwrap_value ce vv
Proof
  Cases_on `vv` >- simp[vv_with_type_def,unwrap_value_def] >>
  rename1 `LocatedValue tag p` >> strip_tac >>
  Cases_on `p.ptr_location = LocMemory`
  >- (`tag = post_value_type ce e \/ is_bytestring_type tag` by
        fs[vv_post_mods_def,vv_holds_mods_def,vv_holds_def] >>
      `~is_word_type tag` by metis_tac[is_bytestring_word_type] >>
      simp[vv_with_type_def,unwrap_value_def]) >>
  drule_all_then assume_tac compile_nonmemory_lowered_value_type >>
  `tag = post_value_type ce e` by
    (Cases_on `p.ptr_location = LocCode` >>
     fs[vv_post_mods_def,vv_holds_mods_def,vv_holds_def]) >>
  simp[vv_with_type_def,post_value_type_lowered]
QED

Theorem snapshot_nonword_code_parts[local]:
  ~is_word_type ty /\
  compile_snapshot_vv ce T (vv_with_type ty vv) sm = (saved,sr) /\
  fn_has_code sm sr func ==>
  ?buf k src su.
    compile_alloc_buffer (type_memory_bytes ce ty) sm = (buf,k) /\
    unwrap_value ce (vv_with_type ty vv) k = (src,su) /\
    compile_store_memory ce src buf.buf_operand ty ty su = ((),sr) /\
    saved = LocatedValue ty (mk_ptr buf.buf_operand LocMemory) /\
    fn_has_code sm k func /\ fn_has_code k su func /\ fn_has_code su sr func /\
    ci_mono sm k /\ ci_mono k su /\ ci_mono su sr
Proof
  strip_tac >>
  `vv_type (vv_with_type ty vv) = ty` by
    (Cases_on `vv` >> simp[vv_type_def,vv_with_type_def]) >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce ty) sm` >>
  rename1 `_ = (buf,k)` >>
  Cases_on `unwrap_value ce (vv_with_type ty vv) k` >> rename1 `_ = (src,su)` >>
  Cases_on `compile_store_memory ce src buf.buf_operand ty ty su` >>
  rename1 `compile_store_memory ce src _ ty ty su = (uu,last)` >> Cases_on `uu` >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def,compile_materialize_vv_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  disch_then (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) >>
  `ci_mono sm k` by
    (qspecl_then [`type_memory_bytes ce ty`,`sm`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono k su` by
    (qspecl_then [`ce`,`vv_with_type ty vv`,`k`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `ci_mono su last` by
    (qspecl_then [`ce`,`src`,`buf.buf_operand`,`ty`,`ty`,`su`] mp_tac
       ci_mono_compile_store_memory >> simp[]) >>
  `cs_extends sm k /\ cs_extends k su /\ cs_extends su last` by fs[ci_mono_def] >>
  `cs_extends k last` by (irule cs_extends_trans >> qexists `su` >> simp[]) >>
  `fn_has_code sm k func /\ fn_has_code k last func` by (irule fn_has_code_split >> simp[]) >>
  `fn_has_code k su func /\ fn_has_code su last func` by (irule fn_has_code_split >> simp[]) >>
  simp[]
QED

val snapshot_base = ``
  expr_body_pre_mods mods ce cx env e es /\
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) < dimword (:256) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv) sm = (saved,sr) /\
  fn_has_code sm sr func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts``;

Theorem qualified_snapshot_store_entry_mods:
  ^snapshot_base ==>
  ?p dw src sw su z Gz tz rt.
    saved = LocatedValue (lowered_value_type ce e) (mk_ptr (Var p) LocMemory) /\
    compile_store_memory ce src (Var p) (lowered_value_type ce e)
      (lowered_value_type ce e) su = ((),sr) /\
    fn_has_code su sr func /\ local_ptrs_reserved ce su /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < su.cs_next_id /\
    su.cs_next_id <= sr.cs_next_id /\ sa.cs_next_var <= su.cs_next_var /\
    su.cs_next_var <= sr.cs_next_var /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    value_has_type rt v /\ val_wf rt v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
    eval_operand src z = SOME sw /\
    (!x. src = Var x ==> not_fresh_at su x) /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n sw) mem) /\
    (0 < type_memory_size rt ==>
      w2n sw + type_memory_size rt <= z.vs_alloca_next /\
      ?x. src = Var x /\ ptr_covers Gz tz x z (type_memory_size rt)) /\
    w2n sw + type_memory_size rt < dimword (:256) /\
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [p]) (fn_insts func) /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size rt) /\
    ~not_fresh_at sa p /\ not_fresh_at su p /\ lookup_var p z = SOME dw /\
    ptr_covers Gz tz p z (type_memory_size rt) /\
    lo <= w2n dw /\ w2n dw + type_memory_size rt < dimword (:256) /\
    w2n dw + type_memory_size rt <= z.vs_alloca_next /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n dw) (type_memory_size rt) b len) /\
    (!name b len. local_region ce ee.scopes z name b len ==>
      regions_disjoint (w2n dw) (type_memory_size rt) b len) /\
    (!name b len. local_region ce es.scopes s0 name b len ==>
      regions_disjoint (w2n dw) (type_memory_size rt) b len) /\
    wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gz tz /\
    return_buf_frame d ce su z /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
    ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\ alloca_history func z /\
    s0.vs_alloca_next <= z.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def] >>
  drule_all copy_read_physical_type_gas_obs_mods >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`pt`,`rt`] (map_every assume_tac o CONJUNCTS)))) >>
  `!v' pt'. read_result cx tv ee = (INL v',ee) /\
             evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt' ==>
             value_has_type pt' v'` by simp[] >>
  drule_all_then (qx_choosel_then [`buf`,`k`,`src`,`su`] strip_assume_tac)
    snapshot_nonword_code_parts >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) = unwrap_value ce vv` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ sm _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     drule_all_then ACCEPT_TAC snapshot_retag_nonword) >>
  drule_all ifexp_arm_result_alloc_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`p`,`dw`,`a`,`Ga`,`ta`,`araw`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "unwrap"
QED

Resume qualified_snapshot_store_entry_mods[unwrap]:
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule_then strip_assume_tac compile_expr_extends >> simp[]) >>
  `sm.cs_next_var <= k.cs_next_var /\ sm.cs_next_id <= k.cs_next_id` by fs[ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `wb_frame ce es ee sa s0 a /\ stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ k _ _ _ _ a /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ sm _ _ _ _ s /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >>
     pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Ga ta` by suspend "alloc_ghost" >>
  `unwrap_value ce vv k = (src,su)` by
    (qpat_assum `unwrap_value ce (vv_with_type _ _) = unwrap_value ce vv` (SUBST1_TAC o SYM) >> simp[]) >>
  `!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op Ga a` by
    (gen_tac >> gen_tac >> disch_tac >>
     qpat_assum `!tag op. _ /\ ~is_word_type _ ==> ptr_buf_ok _ _ _ Ga a` (drule_all_then ACCEPT_TAC)) >>
  drule_at (Pat `unwrap_value _ _ _ = _`)
    (Q.INST [`s` |-> `a`, `G` |-> `Ga`, `tn` |-> `ta`] ifexp_arm_nonword_unwrap_mods) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`v'`,`z`,`Gz`,`tz`,`pt'`,`rt'`,`sw`] (map_every assume_tac o CONJUNCTS))) >>
  `v' = v` by fs[] >> pop_assum SUBST_ALL_TAC >>
  `rt' = rt` by fs[] >> pop_assum SUBST_ALL_TAC >>
  suspend "transport"
QED

Resume qualified_snapshot_store_entry_mods[transport]:
  qpat_x_assum `a = araw with vs_inst_idx := _` kall_tac >>
  `k.cs_next_var <= su.cs_next_var /\ k.cs_next_id <= su.cs_next_id /\
   su.cs_next_var <= sr.cs_next_var /\ su.cs_next_id <= sr.cs_next_id` by fs[ci_mono_def] >>
  `sa.cs_next_var <= su.cs_next_var /\ sm.cs_next_id < su.cs_next_id /\
   s0.vs_alloca_next <= z.vs_alloca_next /\
   w2n dw + type_memory_size rt <= z.vs_alloca_next` by
    (qpat_assum `type_memory_bytes ce _ = type_memory_size rt` (SUBST1_TAC o SYM) >>
     rpt conj_tac
     >- (irule LESS_EQ_TRANS >> qexists `k.cs_next_var` >> simp[] >> decide_tac)
     >- (irule LESS_LESS_EQ_TRANS >> qexists `k.cs_next_id` >> simp[])
     >- (irule LESS_EQ_TRANS >> qexists `a.vs_alloca_next` >> asm_rewrite_tac[] >>
         irule LESS_EQ_TRANS >> qexists `s.vs_alloca_next` >> asm_rewrite_tac[]) >>
     irule LESS_EQ_TRANS >> qexists `a.vs_alloca_next` >> simp[]) >>
  `local_ptrs_reserved ce su` by
    (irule local_ptrs_reserved_next_var >> qexists `k` >> simp[]) >>
  `not_fresh_at su p /\ ~not_fresh_at sa p` by
    (conj_tac >- (irule not_fresh_at_mono >> qexists `k` >> simp[]) >>
     strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then assume_tac) >> fs[]) >>
  `!x. src = Var x ==> not_fresh_at su x` by suspend "source_name" >>
  `lookup_var p z = SOME dw /\ FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size rt) /\
   ptr_covers Gz tz p z (type_memory_size rt)` by
    ((qpat_assum `!x. not_fresh_at k x ==> lookup_var x z = _ /\ _`
       (drule_then strip_assume_tac) >> simp[] >> (metis_tac[]))) >>
  `!name b len. local_region ce ee.scopes z name b len <=> local_region ce ee.scopes a name b len` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     rpt strip_tac >>
     rename1 `lookup_var x z = lookup_var x a` >>
     `not_fresh_at k x` by
       (qpat_x_assum `local_ptrs_reserved ce k` mp_tac >>
        simp[local_ptrs_reserved_def] >> metis_tac[]) >>
     qpat_assum `!x. not_fresh_at k x ==> lookup_var x z = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!name b len. local_region ce es.scopes s0 name b len ==> local_region ce ee.scopes a name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >> qexistsl [`s0`,`sa`,`es.scopes`] >>
     `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x a = SOME w` by
       (rpt strip_tac >> drule_all_then ACCEPT_TAC wb_frame_vars) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame ce es ee sa s0 z /\
   !H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
       storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z` by
    suspend "horizons" >>
  `return_buf_frame d ce su z` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s0`,`sa`] >> simp[] >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC wb_frame_vars) >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  suspend "package"
QED

Resume qualified_snapshot_store_entry_mods[source_name]:
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (gen_tac >> strip_tac >>
     drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `(case vv of StackValue ty op => !x. op = Var x ==> not_fresh_at k x
      | LocatedValue ty lp => !x. lp.ptr_operand = Var x ==> not_fresh_at k x)` by
    (Cases_on `vv` >> simp[vv_operand_def] >> rpt strip_tac >>
     irule not_fresh_at_mono >> qexists `sm` >> fs[vv_operand_def]) >>
  rpt strip_tac >> drule_all_then ACCEPT_TAC exprOperandVarTheory.compiler_unwrap_value_var
QED

Resume qualified_snapshot_store_entry_mods[horizons]:
  conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ su _ _ _ _ z /\ _`
        (qspec_then `storage_trace_horizon ee.storage_trace` (mp_tac o REWRITE_RULE [expr_post_mods_def])) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      strip_tac >> drule_then ACCEPT_TAC expr_post_frame) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ su _ _ _ _ z /\ _`
    (qspec_then `H` (mp_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def])) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume qualified_snapshot_store_entry_mods[package]:
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [p]) (fn_insts func)` by
    (drule_all_then mp_tac buffer_alloc_code >>
     drule_then strip_assume_tac compile_alloc_buffer_parts >> fs[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)` by
    (qx_gen_tac `D` >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK a,Ga,ta)`
       (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     simp_tac std_ss [listTheory.APPEND] >> disch_then irule >>
     qexists `a` >> simp_tac std_ss [] >>
     qpat_assum `!D. gas_origin_ptr_path _ (a,Ga,ta) [] (OK z,Gz,tz)`
       (qspec_then `D` ACCEPT_TAC)) >>
  qpat_assum `buf.buf_operand = Var p` (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_assum `type_memory_bytes ce _ = type_memory_size rt`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  qexistsl [`p`,`dw`,`src`,`sw`,`su`,`z`,`Gz`,`tz`,`rt`] >>
  simp[] >> rpt conj_tac
  >- (strip_tac >> qpat_assum `0 < type_memory_size rt ==> ?r. _`
        (drule_then (qx_choose_then `r` strip_assume_tac)) >>
      qexists `r` >> simp[])
  >- (first_assum ACCEPT_TAC)
  >- (qpat_assum `!n b len. local_region ce ee.scopes a n b len <=> _`
        (fn th => pure_rewrite_tac [GSYM th]) >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!n b len. local_region ce es.scopes s0 n b len ==> _`
        (drule_then assume_tac) >>
      qpat_assum `!n b len. local_region ce ee.scopes a n b len ==> _`
        (drule_then ACCEPT_TAC)) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume qualified_snapshot_store_entry_mods[alloc_ghost]:
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `ta = step_taint _ _ _ _` kall_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ sm _ _ _ _ s /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def,ghost_inv_at_mods_def])) >>
  irule alloc_buffer_ghost_kept_at >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl [`s`,`w2n dw + type_memory_bytes ce (lowered_value_type ce e)`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then assume_tac) >>
      qpat_assum `!x. not_fresh_at sm x ==> _ /\ _` (drule_then strip_assume_tac) >> simp[])
  >- (rpt strip_tac >>
      `local_region ce ee.scopes s name b sz` by
        (irule local_region_frame_fwd >> qexistsl [`s0`,`sa`,`es.scopes`] >> simp[]) >>
      drule_all_then ACCEPT_TAC body_local_region_frontier) >>
  rpt strip_tac >>
  `alloca_inv s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
  irule abi_caller_allocation_end >> simp[] >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[]
QED

Finalise qualified_snapshot_store_entry_mods
