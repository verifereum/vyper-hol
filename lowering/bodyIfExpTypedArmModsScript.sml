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
  placeMemoryTypeInterfaces exprSimProps fragGasOriginPtr fragGasOriginPtrLoop
  bodyIfExpTypedImmFrameMods bodyIfExpTypedGhostMods bodyIfExpTypedKeptMods
  bodyIfExpTypedFinishMods exprSimAlloc bodyMemoryDefs venomInst
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

Theorem ifexp_typed_arm_from_read_mods:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_ifexp_arm ce t (lowered_value_type ce e) vv sm = (op,sb) /\
  (e = a \/ e = b) /\ expr_type e = t /\ ~is_word_type t /\
  (is_word_type (post_value_type ce e) ==> is_word_type (expr_type e)) /\
  ~same_memory_layout ce (lowered_value_type ce e) t /\
  post_value_type ce e = lowered_value_type ce e /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) t /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!t' tv. evaluate_type (get_tenv cx) t' = SOME tv ==>
    type_memory_bytes ce t' = type_memory_size tv) /\
  type_memory_size rty < 2 ** 64 /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!id path. raw = PlaceR (MemoryPlace id path) ==>
    same_memory_layout ce (lowered_value_type ce e) t) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~s.vs_halted /\ alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!tag x. vv = StackValue tag x /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e x G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type rty v /\
    !ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv ==>
      value_has_type ptv v) ==>
  ?v f Gf tf.
    read_result cx raw ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK f,Gf,tf) /\
      expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v op f /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf f) /\
    vv_at ce cx t sa sb ee raw (LocatedValue t (mk_ptr op LocMemory)) f /\
    (!id path. raw = PlaceR (MemoryPlace id path) ==>
      vv_place_ptr ce cx ee f raw (LocatedValue t (mk_ptr op LocMemory))) /\
    (!ctv v'. conditional_result cx raw ee = (INL ctv,ee) /\
      ctv = Value v' /\ ~is_word_type t /\ ~is_bytestring_type t ==>
      vv_own ce cx t sa sb ee ctv (LocatedValue t (mk_ptr op LocMemory)) f) /\
    expr_store_bound cx t v op f /\
    f.vs_current_bb = sb.cs_current_bb /\ f.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func f /\ s0.vs_alloca_next <= f.vs_alloca_next /\
    ptr_val_ok cx t v op Gf tf f /\
    (!e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' op Gf f) /\
    (!rt w. evaluate_type (get_tenv cx) t = SOME rt /\ eval_operand op f = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= f.vs_alloca_next) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type (post_value_type ce e)` by
    (qpat_assum `is_word_type (post_value_type ce e) ==> _` mp_tac >> gvs[]) >>
  `type_memory_bytes ce t = type_memory_size rty /\
   type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv` by simp[] >>
  `type_memory_size rty < dimword (:256)` by
    (irule LESS_TRANS >> qexists `2 ** 64` >>
     simp[wordsTheory.dimword_def]) >>
  drule_all_then (qx_choosel_then [`buf`,`k`,`src`,`sc`]
    (map_every assume_tac o CONJUNCTS)) ifexp_typed_arm_layout >>
  `compile_alloc_buffer (type_memory_size rty) sm = (buf,k)` by
    (qpat_assum `type_memory_bytes ce t = _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`tv` |-> `raw`, `n` |-> `type_memory_size rty`]
    ifexp_arm_result_alloc_mods) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> first_x_assum drule >> simp[])) >>
  disch_then (qx_choosel_then [`xd`,`dw`,`q`,`Ga`,`ta`,`reserve`] strip_assume_tac) >>
  suspend "store"
QED

Resume ifexp_typed_arm_from_read_mods[store]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
    vv_post_mods H ctx func ce cx e es sa k s0 ee raw vv q` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ sm _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ k _ _ _ _ q /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!v. read_result cx raw ee = (INL v,ee) ==> value_has_type stv v /\ value_has_type rty v` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!v. read_result cx raw ee = _ ==> _` (drule_then mp_tac) >> simp[]) >>
  drule_all ifexp_typed_arm_store_entry_mods >>
  disch_then (qx_choosel_then [`v`,`xs`,`sw`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `sc = k` SUBST_ALL_TAC >>
  qpat_x_assum `src = Var xs` SUBST_ALL_TAC >>
  `lo <= q.vs_alloca_next` by decide_tac >>
  `compile_store_memory_typed ce (Var xd) t (Var xs) (lowered_value_type ce e) k = ((),sb)` by
    (qpat_assum `buf.buf_operand = Var xd` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  (SUBGOAL_THEN ``type_memory_size stv = 0 \/
    w2n (sw:256 word) + type_memory_size stv <= q.vs_alloca_next`` assume_tac
    >- asm_rewrite_tac[]) >>
  (SUBGOAL_THEN ``type_memory_size rty = 0 \/
    w2n (dw:256 word) + type_memory_size rty <= q.vs_alloca_next`` assume_tac
    >- asm_rewrite_tac[]) >>
  drule_all compile_store_memory_typed_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`f`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "frame"
QED

Resume ifexp_typed_arm_from_read_mods[frame]:
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [xd])
     (fn_insts func)` by
    (qpat_assum `compile_alloc_buffer (type_memory_size rty) sm = _`
       (mp_then Any mp_tac buffer_alloc_code) >>
     disch_then (qspec_then `func` (drule_then mp_tac)) >>
     qpat_assum `compile_alloc_buffer (type_memory_size rty) sm = _`
       (mp_then Any mp_tac compile_alloc_buffer_parts) >>
     disch_then (mp_tac o cj 1) >>
     qpat_assum `buf.buf_operand = Var xd` (fn th =>
       simp[NoAsms,th,operand_11] >> disch_then SUBST1_TAC >> simp[])) >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size rty))] [xd]` >>
  `inst.inst_id = sm.cs_next_id /\ inst.inst_opcode = ALLOCA` by simp[Abbr `inst`,mk_inst_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ sm _ _ _ _ s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ k _ _ _ _ q /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    (qhdtm_assum `vv_post_mods` (ACCEPT_TAC o cj 1 o REWRITE_RULE [vv_post_mods_def])) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee q` by
    (qhdtm_assum `vv_post_mods` (ACCEPT_TAC o cj 1 o REWRITE_RULE [vv_post_mods_def])) >>
  `immutable_frame_mods func ce cx ee q` by
    (qhdtm_assum `vv_post_mods` (ACCEPT_TAC o cj 2 o REWRITE_RULE [vv_post_mods_def])) >>
  `alloca_inv s /\ alloca_inv q /\ local_ptrs_rel func ce ee.scopes q` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s`
       (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ q`
       (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
     asm_rewrite_tac[]) >>
  `alloca_history func f` by
    (qpat_assum `!D. gas_origin_ptr_path _ (q,Ga,ta) [] (OK f,Gf,tf)`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)` assume_tac) >>
     drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  `f.vs_alloca_next = q.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     simp[NoAsms,typed_copy_state_frame_def,venom_state_component_equality]) >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `sa.cs_next_var <= k.cs_next_var /\ sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
   s0.vs_alloca_next <= f.vs_alloca_next` by decide_tac >>
  `FLOOKUP q.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size rty)` by
    (qpat_assum `inst.inst_id = _` (fn th => pure_once_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all_then assume_tac ifexp_typed_immutable_frame_mods >>
  suspend "root_frame"
QED

Resume ifexp_typed_arm_from_read_mods[root_frame]:
  qpat_x_assum `q = reserve with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `ta = step_taint _ _ _ _` kall_tac >>
  rpt (qhdtm_x_assum `vv_post_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vv_post_mods_def])) >>
  `!id b len. local_region ce es.scopes s0 id b len ==>
    local_region ce ee.scopes q id b len` by
    (rpt gen_tac >> disch_tac >> irule local_region_frame_fwd >>
     qexistsl [`s0`,`sa`,`es.scopes`] >> asm_rewrite_tac[]) >>
  `!aid lb len. FLOOKUP s0.vs_allocas aid = SOME (lb,len) /\ aid < sa.cs_next_id ==>
    lb+len <= s.vs_alloca_next /\ regions_disjoint (w2n dw) (type_memory_size rty) lb len` by
    (qx_genl_tac [`aid`,`lb`,`len`] >> strip_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (lb,len)` by simp[] >>
     conj_tac >- (drule_all_then ACCEPT_TAC alloca_site_registered_below) >>
     `aid < sm.cs_next_id` by decide_tac >>
     qpat_assum `!aid b len. aid < sm.cs_next_id /\ _ ==> _` (drule_all_then ACCEPT_TAC)) >>
  `!id lb len. local_region ce es.scopes s0 id lb len ==>
    lb+len <= s.vs_alloca_next /\ regions_disjoint (w2n dw) (type_memory_size rty) lb len` by
    (qx_genl_tac [`id`,`lb`,`len`] >> disch_tac >>
     `local_region ce ee.scopes q id lb len` by simp[] >>
     conj_tac
     >- (`local_region ce ee.scopes s id lb len` by
           (qpat_assum `!id b len. local_region ce ee.scopes q id b len <=> _`
              (qspecl_then [`id`,`lb`,`len`] mp_tac) >> asm_rewrite_tac[]) >>
         drule_all_then ACCEPT_TAC body_local_region_frontier) >>
     qpat_assum `!id b len. local_region ce ee.scopes q id b len ==> _` (drule_then ACCEPT_TAC)) >>
  `!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)` by simp[] >>
  `!x. not_fresh_at sm x ==>
       FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule_all_then assume_tac ifexp_typed_reserve_store_kept >>
  suspend "finish"
QED

Resume ifexp_typed_arm_from_read_mods[finish]:
  `op = Var xd` by (qpat_assum `op = buf.buf_operand` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `op = Var xd` SUBST_ALL_TAC >>
  qpat_x_assum `Var xd = buf.buf_operand` kall_tac >>
  `op_taint ta (Var xd) = {}` by
    (qpat_assum `ptr_covers Ga ta xd q (type_memory_size rty)` mp_tac >> simp[NoAsms,ptr_covers_def]) >>
  `!id lb len. local_region ce ee.scopes q id lb len ==>
     w2n dw + type_memory_size rty <= lb \/ lb+len <= w2n dw` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!id b len. local_region ce ee.scopes q id b len ==> _`
       (drule_then mp_tac) >> simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!aid lb len. FLOOKUP s0.vs_allocas aid = SOME (lb,len) /\ aid < sa.cs_next_id ==>
     w2n dw + type_memory_size rty <= lb \/ lb+len <= w2n dw` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) /\ _ ==> _ /\ _`
       (drule_all_then mp_tac) >> simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  qexistsl [`v`,`f`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- suspend "shape" >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  drule_all ifexp_typed_result_at_site_mods >>
  disch_then (qspec_then `c` (map_every assume_tac o CONJUNCTS)) >>
  conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl [`Ga`,`q`,`ta`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!J. valid_horizon _ _ J _ ==> vv_post_mods J _ _ _ _ _ _ _ k _ _ _ _ q /\
       ghost_inv_at_mods _ _ _ _ _ _ Ga ta q`
    (drule_then strip_assume_tac) >>
  drule_all_then ACCEPT_TAC ifexp_typed_copy_ghost_mods
QED

Resume ifexp_typed_arm_from_read_mods[shape]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  drule_all ifexp_typed_result_at_site_mods >>
  disch_then (qspec_then `c` (map_every assume_tac o CONJUNCTS)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise ifexp_typed_arm_from_read_mods
