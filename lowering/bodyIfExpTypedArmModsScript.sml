(* Typed widening of the selected ternary arm, at its actual store cursor. *)
Theory bodyIfExpTypedArmMods
Ancestors
  bodyIfExpAllocMods bodyIfExpArmUnwrapMods bodyFullIfExpWidenCall
  typedCopyOriginPtr wideningZeroLayout exprSimIfExpWidenedPosts
  bodyFullPathHistory exprOperandVar exprLowering exprLoweringProps
  compileEnv loweringHalt fragExec loweringPosts vyperTypeSystem
  valueEncoding vyperValue arithmetic context typedMemoryCopy
  exprSimIfExpWidenedArm exprSimAggregateChildren allocaSiteResource
  venomMemDefs venomState finite_map words
  bodyLocalCopyPhysicalRhsMods assignBasePtrBoundary exprSimSend exprSimDefs
  exprSimMemDefs bodyFullPostsMods bodyPtrDefs loweringStateRelDefs
  vyperStorageFootprint vyperContext vyperInterpreter vyperAST vyperState
  stateRelProj valueTypingMemoryProps freshWrites bodyPtrAttributeSource
  placeMemoryTypeInterfaces
Libs
  monadsyntax

Theorem ifexp_typed_arm_layout[local]:
  compile_ifexp_arm ce t sty vv sm = (op,sb) /\
  ~is_word_type t /\ ~same_memory_layout ce sty t /\
  type_widens_to tenv sty t /\ fn_has_code sm sb func ==>
  ?buf k src sc.
    compile_alloc_buffer (type_memory_bytes ce t) sm = (buf,k) /\
    unwrap_value ce vv k = (src,sc) /\
    compile_store_memory_typed ce buf.buf_operand t src sty sc = ((),sb) /\
    op = buf.buf_operand /\ fn_has_code sm k func /\
    fn_has_code k sc func /\ fn_has_code sc sb func /\
    sm.cs_next_var <= k.cs_next_var /\ k.cs_next_var <= sc.cs_next_var /\
    sm.cs_next_id < k.cs_next_id /\ k.cs_next_id <= sc.cs_next_id /\
    sc.cs_next_id <= sb.cs_next_id
Proof
  strip_tac >>
  drule_all_then assume_tac ifexp_widened_call_store_normalize >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce t) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,k)` >>
  Cases_on `unwrap_value ce vv k` >>
  rename1 `unwrap_value ce vv k = (src,sc)` >>
  Cases_on `compile_store_memory_typed ce buf.buf_operand t src sty sc` >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (u,sf)` >>
  Cases_on `u` >>
  `op = buf.buf_operand /\ sb = sf` by
    (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
     simp[compile_ifexp_arm_def,comp_bind_def,comp_ignore_bind_def,comp_return_def]) >>
  qpat_x_assum `sb = sf` (SUBST_ALL_TAC o SYM) >>
  `ci_mono sm k /\ ci_mono k sc /\ ci_mono sc sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_unwrap_value,
      cj 1 ci_mono_typed_memory_family,pairTheory.SND] >>
  `sm.cs_next_id < k.cs_next_id` by
    (drule_then strip_assume_tac compile_alloc_buffer_parts >> simp[]) >>
  qexistsl [`buf`,`k`,`src`,`sc`] >> simp[] >>
  fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]
QED

Theorem ifexp_typed_arm_source_size[local]:
  expr_type e = t /\ post_value_type ce e = lowered_value_type ce e /\
  ~same_memory_layout ce (lowered_value_type ce e) t /\
  type_widens_to tenv (lowered_value_type ce e) t /\
  evaluate_type tenv (lowered_value_type ce e) = SOME rt /\
  evaluate_type tenv t = SOME dt /\ value_has_type rt v ==>
  post_value_type ce e <> expr_type e /\ ~is_bytestring_type t /\
  0 < type_memory_size rt /\ val_footprint rt v = type_memory_size rt
Proof
  strip_tac >>
  `lowered_value_type ce e <> t` by
    (strip_tac >> fs[same_memory_layout_def,punnable_reflexive]) >>
  `~is_bytestring_type t` by metis_tac[post_value_type_bytestring] >>
  `0 < type_memory_size rt` by
    (Cases_on `type_memory_size rt = 0` >> simp[] >>
     drule_all_then assume_tac type_widens_to_zero_layout >> fs[]) >>
  `~is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[type_widens_from_bytestring] >>
  simp[] >> irule evaluated_nonbytes_footprint >> metis_tac[]
QED

Theorem ifexp_typed_arm_window_disjoint[local]:
  alloca_inv s /\ src_id <> dst_id /\
  FLOOKUP s.vs_allocas src_id = SOME (a,cap) /\
  FLOOKUP s.vs_allocas dst_id = SOME (b,n) /\
  0 < m /\ 0 < n /\ a <= w /\ w + m <= a + cap ==>
  w + m <= b \/ b + n <= w
Proof
  strip_tac >> drule_all alloca_site_registered_disjoint >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem ifexp_typed_arm_compiled_shape[local]:
  compile_expr ce ty e sa = (vv,sm) /\
  post_value_type ce e <> expr_type e ==>
  (?p. vv = LocatedValue (lowered_value_type ce e) p /\ p.ptr_location = LocMemory) \/
  vv = StackValue (lowered_value_type ce e) (Lit 0w)
Proof
  strip_tac >>
  `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
    metis_tac[post_value_type_not_int_call] >>
  gvs[compile_expr_call,lowered_value_type_def,Once compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `0 < returns_count` >> gvs[]
  >- (rpt (pairarg_tac >> gvs[]) >> simp[base_ptr_def,mk_ptr_def]) >>
  Cases_on `0 < return_buf_size` >> gvs[base_ptr_def,mk_ptr_def]
QED

Theorem ifexp_typed_identity_read[local]:
  vv_post_mods H ctx func ce cx e es sa k s0 ee tv vv q ==>
  ?v. read_result cx tv ee = (INL v,ee)
Proof
  simp[vv_post_mods_def] >> strip_tac >> Cases_on `vv`
  >- fs[vv_holds_mods_def,vv_holds_def] >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocCode`
  >- fs[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def] >>
  fs[vv_holds_mods_def] >>
  drule_then strip_assume_tac attribute_vv_holds_read_operand >> simp[]
QED

Theorem ifexp_typed_identity_cut[local]:
  ((?p. vv = LocatedValue (lowered_value_type ce e) p /\ p.ptr_location = LocMemory) \/
   vv = StackValue (lowered_value_type ce e) (Lit 0w)) /\
  unwrap_value ce vv k = (src,sc) /\ ~q.vs_halted /\
  post_value_type ce e = lowered_value_type ce e /\
  ~is_word_type (post_value_type ce e) /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post_mods H ctx func ce cx e es sa k s0 ee tv vv q /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv q /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee Ga ta q ==>
  sc = k /\ src = vv_operand vv /\
  expr_post_mods H ctx func ce cx e es sa k s0 ee v src q /\
  ptr_val_ok cx (post_value_type ce e) v src Ga ta q /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
          eval_operand src q = SOME w ==>
     type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= q.vs_alloca_next)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `src = vv_operand vv` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     gvs[unwrap_value_def,comp_return_def,vv_operand_def]) >>
  SUBGOAL_THEN ``(?ty. vv = StackValue ty src) \/
    (?ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory /\
            ~is_word_type ty /\ p.ptr_operand = src)`` assume_tac
  >- (qpat_x_assum `_ \/ _` strip_assume_tac >>
      gvs[unwrap_value_def,comp_return_def]) >>
  drule_all local_copy_rhs_identity_unwrap_mods >>
  disch_then (strip_assume_tac o SPEC_ALL) >> gvs[]
QED

Theorem ifexp_typed_alloca_window[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  post_value_type ce e <> expr_type e /\
  vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\
  eval_operand p.ptr_operand s = SOME w /\ read_result cx tv ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
  val_footprint stv v = type_memory_size stv /\ 0 < type_memory_size stv ==>
  ?id a cap. FLOOKUP s.vs_allocas id = SOME (a,cap) /\
    id < sm.cs_next_id /\ a <= w2n w /\ w2n w + type_memory_size stv <= a + cap
Proof
  Cases_on `vv` >> simp[] >> rpt strip_tac >>
  `vv_own ce cx (post_value_type ce e) sa sm ee tv (LocatedValue tag p) s` by
    fs[vv_post_mods_def] >>
  qpat_x_assum `vv_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_own_def] >>
  disch_then (qx_choose_then `id` (qx_choose_then `a` (qx_choose_then `cap` strip_assume_tac))) >>
  qexistsl [`id`,`a`,`cap`] >> simp[]
QED

Theorem ifexp_typed_arm_store_entry_mods:
  compile_expr ce ty e sa = (vv,sm) /\ local_ptrs_reserved ce sa /\
  unwrap_value ce vv k = (src,sc) /\ sm.cs_next_var <= k.cs_next_var /\
  expr_type e = t /\ post_value_type ce e = lowered_value_type ce e /\
  ~is_word_type (post_value_type ce e) /\
  ~same_memory_layout ce (lowered_value_type ce e) t /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) t /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  evaluate_type (get_tenv cx) t = SOME dtv /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
  storage_trace_domain cx st0 ee.storage_trace /\ ~q.vs_halted /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
    vv_post_mods H ctx func ce cx e es sa k s0 ee tv vv q) /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type stv v /\ value_has_type dtv v) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv q /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee Ga ta q /\
  (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op Ga q) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand Ga q) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> FLOOKUP q.vs_allocas id = SOME entry) /\
  FLOOKUP q.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size dtv) ==>
  ?v xs sw. read_result cx tv ee = (INL v,ee) /\ src = Var xs /\ sc = k /\
    lookup_var xs q = SOME sw /\ not_fresh_at k xs /\
    ptr_covers Ga ta xs q (type_memory_size stv) /\
    (!mem. mem_agree_outside ta.t_mem q.vs_memory mem ==>
           val_in_memory stv v (w2n sw) mem) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n sw + type_memory_size stv <= q.vs_alloca_next /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx e es sa k s0 ee v src q)
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_then (qx_choose_then `v` assume_tac) ifexp_typed_identity_read >>
  `value_has_type stv v /\ value_has_type dtv v` by simp[] >>
  drule_all_then strip_assume_tac ifexp_typed_arm_source_size >>
  drule_all_then assume_tac ifexp_typed_arm_compiled_shape >>
  drule_all_then strip_assume_tac ifexp_typed_identity_cut >>
  `?sw. eval_operand src q = SOME sw` by
    (qhdtm_assum `expr_post_mods`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def,expr_val_rel_def]) >>
     qexists `w` >> simp[]) >>
  `ptr_buf_ok ce e src Ga q` by
    (qpat_assum `_ \/ _` strip_assume_tac >> fs[vv_operand_def]) >>
  `op_taint ta src = {}` by fs[ptr_val_ok_def] >>
  `?xs. src = Var xs /\ ptr_covers Ga ta xs q (type_memory_size stv)` by
    (qpat_x_assum `src = vv_operand vv` kall_tac >>
     irule ptr_buf_ok_read_covers >> simp[] >> qexistsl [`ce`,`e`] >> simp[]) >>
  `lookup_var xs q = SOME sw` by fs[eval_operand_def] >>
  `not_fresh_at sm xs` by
    (`vv_operand vv = Var xs` by metis_tac[] >>
     drule_all (cj 1 compiler_compile_var) >> simp[]) >>
  `not_fresh_at k xs` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post_mods H ctx func ce cx e es sa k s0 ee v src q` by
    (rpt strip_tac >>
     qpat_x_assum `vv_post_mods H0 ctx func ce cx e es sa k s0 ee tv vv q` kall_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
     drule_all_then strip_assume_tac ifexp_typed_identity_cut >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H0 ctx func ce cx ee q` by fs[vv_post_mods_def] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_then assume_tac alloca_room_next_lt >>
  `w2n sw + type_memory_size stv <= q.vs_alloca_next` by
    (qpat_assum `!rt w. _ /\ eval_operand _ _ = SOME w ==> _` drule_all >>
     disch_then strip_assume_tac >> fs[]) >>
  `0 < type_memory_size dtv` by
    (drule_all type_widens_to_zero_memory_size >> decide_tac) >>
  `eval_operand (vv_operand vv) s = SOME sw` by
    (qpat_assum `eval_operand (vv_operand vv) q = _` (SUBST1_TAC o SYM) >>
     qpat_assum `src = vv_operand vv` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `?p. vv = LocatedValue (lowered_value_type ce e) p /\
       p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME sw` by
    (qpat_assum `_ \/ _` strip_assume_tac >> gvs[vv_operand_def]) >>
  `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv` by simp[] >>
  drule_all_then strip_assume_tac ifexp_typed_alloca_window >>
  `FLOOKUP q.vs_allocas id = SOME (a,cap)` by simp[] >>
  `id <> sm.cs_next_id` by decide_tac >>
  drule_all ifexp_typed_arm_window_disjoint >> strip_tac >>
  qexistsl [`v`,`xs`,`sw`] >> simp[value_has_type_memory_wf] >>
  fs[ptr_val_ok_def,ptr_mem_ok_def] >> decide_tac
QED
