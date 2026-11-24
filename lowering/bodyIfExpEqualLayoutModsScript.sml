(* A nonword IfExp arm with equal physical layout needs no store after
   unwrap. Retyping its posts does not change the path or its endpoint. *)
Theory bodyIfExpEqualLayoutMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv exprSimLayoutTransport
  exprSimIfExp exprSimMemDefs exprSimProps bodyPtrDefs bodyDeclMemoryCore
  loweringPosts valueTypingMemoryProps typedMemoryCopy exprLowering
  vyperTypeSystem vyperInterpreter vyperValue vyperState compileEnv
  vyperAST vyperTypeInvariants context bodyIfExpArmUnwrapMods
  vyperStorageFootprint vyperTypeArgFits exprSimMemUnwrap exprPtrUnwrapAllocSemantic
  exprSimOperands exprPtrUnwrapAllocation exprLoweringProps loweringHalt
  loweringStateRelDefs fragExec finite_map words arithmetic
  venomState venomInst

Theorem ifexp_equal_layout_cursor_mods:
  same_memory_layout ce (lowered_value_type ce e) t /\
  compile_ifexp_arm ce t (lowered_value_type ce e) vv sm = (op,sb) ==>
  unwrap_value ce vv sm = (op,sb)
Proof
  strip_tac >> qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
  Cases_on `is_word_type t` >> simp[compile_ifexp_arm_def]
QED

Theorem ifexp_equal_layout_post[local]:
  expr_type e = t /\ (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME sv /\
  evaluate_type (get_tenv cx) t = SOME dv /\ ~is_word_type t /\ value_has_type dv v /\
  (post_value_type ce e = t \/
    same_memory_layout ce (post_value_type ce e) t /\
    arg_type_fits (post_value_type ce e) t) /\
  expr_post_mods H ctx func ce cx e es sa sb u ee v op z ==>
  expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb u ee v op z
Proof
  `post_value_type ce (IfExp t c a b) = t` by simp[post_value_type_def,expr_type_def] >>
  Cases_on `post_value_type ce e = t`
  >- (rw[expr_post_mods_def,expr_post_def,expr_type_def] >> metis_tac[]) >>
  strip_tac >> fs[expr_post_mods_def,expr_post_def] >>
  simp[expr_type_def] >> rpt conj_tac
  >- (irule expr_val_rel_layout_transport >> simp[] >>
      qexistsl [`ce`,`post_value_type ce e`,`sv`] >> simp[])
  >- (irule expr_val_at_layout_transport >> simp[] >>
      qexistsl [`post_value_type ce e`,`sv`] >> simp[]) >>
  metis_tac[]
QED

Theorem ifexp_equal_layout_ptr[local]:
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  ~is_word_type src /\ ~is_word_type dst /\
  val_footprint sv v = val_footprint dv v /\
  val_store_size sv v = val_store_size dv v /\
  (!b mem. val_in_memory sv v b mem ==> val_in_memory dv v b mem) /\
  ptr_val_ok cx src v op G tn z ==> ptr_val_ok cx dst v op G tn z
Proof
  simp[ptr_val_ok_def,ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ifexp_equal_layout_distinct[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  same_memory_layout ce src dst /\ arg_type_fits src dst /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  ~is_word_type dst /\ ~is_bytestring_type src /\ ~is_bytestring_type dst /\
  ptr_val_ok cx src v op G tn z ==> ptr_val_ok cx dst v op G tn z
Proof
  strip_tac >>
  `type_memory_size sv = type_memory_size dv` by
    (fs[same_memory_layout_def] >> metis_tac[]) >>
  irule ifexp_equal_layout_ptr >> simp[] >>
  qexistsl [`src`,`sv`] >> simp[] >> rpt conj_tac
  >- metis_tac[compatible_word_type]
  >- (`!v b mem. val_in_memory sv v b mem <=> val_in_memory dv v b mem` suffices_by simp[] >>
      drule compatible_layout_memory >>
      disch_then (qspecl_then [`src`,`dst`,`sv`,`dv`] mp_tac o cj 1) >>
      fs[same_memory_layout_def])
  >- metis_tac[compatible_footprint] >>
  metis_tac[val_store_size_non_bytestring]
QED

Theorem ifexp_equal_layout_read_value[local]:
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (INL (Value v'),ee) ==> v' = v
Proof
  strip_tac >>
  `bind (conditional_result cx raw) (read_result cx) ee = (INL v',ee)` by
    simp[bind_def,read_result_def,return_def] >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV) conditional_read_cases) >>
  strip_tac >> gvs[]
QED

Theorem ifexp_equal_layout_owned[local]:
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  ~is_word_type src /\ val_wf dv v /\
  val_footprint sv v = val_footprint dv v /\
  expr_val_own ce cx src sa sb ee v op z /\
  read_result cx raw ee = (INL v,ee) ==>
  vv_at ce cx dst sa sb ee raw (LocatedValue dst (mk_ptr op LocMemory)) z /\
  vv_own ce cx dst sa sb ee (Value v) (LocatedValue dst (mk_ptr op LocMemory)) z
Proof
  simp[vv_at_def,vv_own_def,mk_ptr_def,expr_val_own_def,read_result_def,return_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `sv` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ifexp_equal_layout_aggregate_place[local]:
  evaluate_type tenv ty = SOME tv /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\ ty <> NoneT /\
  runtime_place_typed cx st (MemoryPlace id path) tv ==>
  conditional_result cx (PlaceR (MemoryPlace id path)) st =
    (INL (PlaceR (MemoryPlace id path)),st)
Proof
  strip_tac >>
  `place_type_value cx (MemoryPlace id path) st = (INL tv,st)` by
    fs[runtime_place_typed_def] >>
  simp[conditional_result_def,bind_def,return_def] >>
  Cases_on `ty` >>
  gvs[is_word_type_def,is_bytestring_type_def,evaluate_type_def,return_def,AllCaseEqs()] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_word_type_def,is_bytestring_type_def,evaluate_type_def,return_def,AllCaseEqs()] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def,is_bytestring_type_def,evaluate_type_def,return_def,AllCaseEqs()]
QED

Theorem ifexp_identity_nonplace_value[local]:
  vv_at ce cx t sa sm ee raw vv s /\ vv_place_ptr_mods ce cx ee s raw vv /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  ~is_word_type t /\ (!id path. raw <> PlaceR (MemoryPlace id path)) /\
  read_result cx raw ee = (INL v,ee) ==> raw = Value v
Proof
  Cases_on `raw` >> Cases_on `vv` >>
  simp[vv_at_def,vv_location_def,read_result_def,return_def,raise_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >>
  simp[vv_place_ptr_mods_def,vv_place_ptr_def,slot_loc_def,COND_RAND,COND_RATOR] >>
  metis_tac[]
QED

Theorem ifexp_identity_value_owned[local]:
  ~is_word_type t /\ vv_own ce cx t sa sm ee (Value v) vv s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  op = vv_operand vv ==>
  vv_own ce cx t sa sm ee (Value v) (LocatedValue t (mk_ptr op LocMemory)) s
Proof
  Cases_on `vv` >>
  simp[vv_location_def,vv_operand_def,vv_own_def,expr_val_own_def,
       read_result_def,return_def,mk_ptr_def] >> metis_tac[]
QED

Theorem ifexp_none_value_owned[local]:
  eval_operand op z = SOME w ==>
  vv_own ce cx NoneT sa sb ee (Value v) (LocatedValue NoneT (mk_ptr op LocMemory)) z
Proof
  Cases_on `v` >>
  simp[evaluate_type_def,vv_own_def,mk_ptr_def,read_result_def,return_def,
       valueEncodingTheory.type_memory_size_def,val_footprint_def]
QED

Theorem ifexp_equal_layout_capacity[local]:
  same_memory_layout ce (lowered_value_type ce e) t /\
  type_memory_bytes ce t = type_memory_size dv /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  evaluate_type (get_tenv cx) t = SOME dv /\ val_wf dv v /\
  eval_operand op z = SOME w /\ ptr_buf_ok ce e op G z /\
  (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) ==>
  expr_store_bound cx t v op z /\
  (!e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' op G z) /\
  (!rt w. evaluate_type (get_tenv cx) t = SOME rt /\ eval_operand op z = SOME w ==>
    type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next)
Proof
  simp[same_memory_layout_def] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_size rt = type_memory_size dv` by metis_tac[] >>
  conj_tac
  >- (simp[expr_store_bound_def] >> disch_tac >>
      drule_then assume_tac (SPEC_ALL val_store_size_le) >> decide_tac) >>
  rpt strip_tac >> qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  asm_rewrite_tac[ptr_buf_ok_def]
QED

(* The materialized branch exposes its allocation record. Recover the
   corresponding emitted ALLOCA from the compiler, not by replaying the run. *)
Theorem ifexp_unwrap_copy_buffer[local]:
  unwrap_value ce (LocatedValue tag p) sm = (op,sb) /\ fn_has_code sm sb func /\
  ~is_word_type tag /\ p.ptr_location <> LocMemory /\ p.ptr_location <> LocCalldata ==>
  ?n buf mid. compile_alloc_buffer n sm = (buf,mid) /\ fn_has_code sm mid func /\
    mid.cs_next_id <= sb.cs_next_id
Proof
  strip_tac >> Cases_on `p.ptr_location = LocCode`
  >- (`?buf mid. compile_alloc_buffer (type_memory_bytes ce tag) sm = (buf,mid) /\
        compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand
          buf.buf_operand ((type_memory_bytes ce tag + 31) DIV 32) 0 mid = ((),sb)` by
       (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
        simp[unwrap_value_def,compile_ensure_in_memory_def,
             comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
        pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
     `ci_mono sm mid /\ ci_mono mid sb` by
       metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_imm_copy_to_memory,pairTheory.SND] >>
     qexistsl [`type_memory_bytes ce tag`,`buf`,`mid`] >> fs[ci_mono_def] >>
     drule_all fn_has_code_split >> simp[]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` suffices_by
    (disch_tac >> drule_all storage_unwrap_layout_facts >> metis_tac[]) >>
  Cases_on `p.ptr_location` >> fs[]
QED

Theorem ifexp_unwrap_identity_location[local]:
  unwrap_value ce vv sm = (op,sm) /\ fn_has_code sm sm func /\
  (!tag p. vv = LocatedValue tag p ==> ~is_word_type tag /\ p.ptr_location <> LocCalldata) ==>
  vv_location vv = NONE \/ vv_location vv = SOME LocMemory
Proof
  strip_tac >> Cases_on `vv` >> simp[vv_location_def] >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocMemory` >> simp[] >>
  `~is_word_type tag /\ p.ptr_location <> LocCalldata` by gvs[] >>
  drule_all ifexp_unwrap_copy_buffer >> strip_tac >>
  drule_then strip_assume_tac compile_alloc_buffer_parts >> decide_tac
QED

Theorem ifexp_unwrap_alloc_site[local]:
  unwrap_value ce vv sm = (op,sb) /\ sm.cs_next_id < sb.cs_next_id /\
  fn_has_code sm sb func /\ local_ptrs_reserved ce sm /\
  (!tag p. vv = LocatedValue tag p ==> ~is_word_type tag /\ p.ptr_location <> LocCalldata) ==>
  ?n root. MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
    not_local_ptr ce scopes root
Proof
  strip_tac >>
  `?n buf mid. compile_alloc_buffer n sm = (buf,mid) /\ fn_has_code sm mid func` by
    (Cases_on `vv` >- gvs[unwrap_value_def,comp_return_def] >>
     rename1 `unwrap_value ce (LocatedValue tag p) sm = _` >>
     `~is_word_type tag /\ p.ptr_location <> LocCalldata` by metis_tac[] >>
     Cases_on `p.ptr_location = LocMemory` >- gvs[unwrap_value_def,comp_return_def] >>
     drule_all ifexp_unwrap_copy_buffer >> metis_tac[]) >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all emit_inst_fn_member >> simp[] >> strip_tac >>
  qexistsl [`n`,`p`] >> simp[] >> metis_tac[fresh_not_local_ptr]
QED

Theorem ifexp_unwrap_alloc_owned[local]:
  fn_inst_ids_distinct func /\ stmt_state_rel H ctx func ce cx ee z /\
  MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
  not_local_ptr ce ee.scopes root /\
  FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size rt) /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
  evaluate_type (get_tenv cx) t = SOME rt /\ val_wf rt v /\
  eval_operand op z = SOME w ==>
  vv_own ce cx t sa sb ee (Value v) (LocatedValue t (mk_ptr op LocMemory)) z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!name b len. local_region ce ee.scopes z name b len ==>
    regions_disjoint (w2n w) (type_memory_size rt) b len` by
    metis_tac[unwrap_alloc_local_disjoint] >>
  `val_footprint rt v <= type_memory_size rt` by simp[val_footprint_le] >>
  simp[vv_own_def,mk_ptr_def,read_result_def,return_def] >> disj1_tac >>
  qexistsl [`sm.cs_next_id`,`w2n w`,`type_memory_size rt`] >>
  fs[regions_disjoint_def] >> first_assum ACCEPT_TAC
QED

Theorem ifexp_raw_nonword_tags[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
  ~is_word_type (post_value_type ce e) ==>
  !tag p. vv = LocatedValue tag p ==> ~is_word_type tag /\ p.ptr_location <> LocCalldata
Proof
  strip_tac >> rpt gen_tac >> disch_tac >> gvs[vv_post_mods_def,vv_holds_mods_def] >>
  Cases_on `p.ptr_location` >>
  gvs[immutable_holds_mods_def,vv_holds_def] >> metis_tac[valueCopyBytesTheory.is_bytestring_word_type]
QED

Theorem ifexp_arm_equal_layout_from_unwrap_mods:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_ifexp_arm ce t (lowered_value_type ce e) vv sm = (op,sb) /\
  expr_type e = t /\ ~is_word_type t /\ same_memory_layout ce (lowered_value_type ce e) t /\
  (post_value_type ce e = t \/
   post_value_type ce e = lowered_value_type ce e /\
   type_widens_to (get_tenv cx) (lowered_value_type ce e) t) /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  evaluate_type (get_tenv cx) t = SOME dv /\
  (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type dv v) /\
  env.type_defs = get_tenv cx /\ eval_result_typed (env,cx,ee) raw (Type t) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
  (!v. raw = Value v /\ ~is_word_type (post_value_type ce e) /\
        ~is_bytestring_type (post_value_type ce e) ==>
    vv_own ce cx (post_value_type ce e) sa sm ee raw vv s) /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!tag x. vv = StackValue tag x ==> ptr_buf_ok ce e x G s) /\
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
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next ==>
  ?v z Gf tf.
    read_result cx raw ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf) /\
      expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    vv_at ce cx t sa sb ee raw (LocatedValue t (mk_ptr op LocMemory)) z /\
    (!id path. raw = PlaceR (MemoryPlace id path) ==>
      vv_place_ptr ce cx ee z raw (LocatedValue t (mk_ptr op LocMemory))) /\
    (!ctv v. conditional_result cx raw ee = (INL ctv,ee) /\
      ctv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
      vv_own ce cx t sa sb ee ctv (LocatedValue t (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx t v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx t v op Gf tf z /\
    (!e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' op Gf z) /\
    (!rt w. evaluate_type (get_tenv cx) t = SOME rt /\ eval_operand op z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `unwrap_value ce vv sm = (op,sb)` by (drule_all ifexp_equal_layout_cursor_mods >> simp[]) >>
  `~is_word_type (expr_type e)` by simp[] >>
  mp_tac (Q.INST [`k` |-> `sm`, `tv` |-> `raw`] ifexp_arm_nonword_unwrap_mods) >>
  impl_tac >- asm_rewrite_tac[LESS_EQ_REFL] >>
  disch_then (qx_choosel_then [`v`,`z`,`Gf`,`tf`,`pt`,`rt`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `value_has_type dv v` by metis_tac[] >>
  `val_wf dv v` by simp[value_has_type_memory_wf] >>
  `type_memory_bytes ce t = type_memory_size dv` by metis_tac[] >>
  drule_all ifexp_equal_layout_capacity >> strip_tac >>
  `(!id path. raw = PlaceR (MemoryPlace id path) ==>
      vv_place_ptr ce cx ee z raw (LocatedValue t (mk_ptr op LocMemory)))` by
    suspend "place_ptr" >>
  `post_value_type ce e = t \/
   same_memory_layout ce (post_value_type ce e) t /\ arg_type_fits (post_value_type ce e) t`
    suffices_by (disch_tac >> suspend "retype") >>
  fs[type_widens_to_def] >> metis_tac[]
QED

Resume ifexp_arm_equal_layout_from_unwrap_mods[place_ptr]:
  qpat_x_assum `(sb = sm /\ _) \/ _` mp_tac >>
  rpt strip_tac >> gvs[vv_place_ptr_def,mk_ptr_def]
QED

Resume ifexp_arm_equal_layout_from_unwrap_mods[retype]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v op z` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     irule ifexp_equal_layout_post >> asm_rewrite_tac[] >>
     conj_tac >- (qexists `dv` >> asm_rewrite_tac[]) >>
     qexistsl [`e`,`pt`] >> asm_rewrite_tac[]) >>
  qexistsl [`v`,`z`,`Gf`,`tf`] >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  Cases_on `post_value_type ce e = t` >- suspend "same" >>
  suspend "distinct"
QED

Resume ifexp_arm_equal_layout_from_unwrap_mods[same]:
  `ptr_val_ok cx t v op Gf tf z` by fs[] >>
  asm_rewrite_tac[] >> conj_tac
  >- (qpat_assum `(sb = sm /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
      >- (qpat_x_assum `vv_at _ _ _ _ _ _ _ (LocatedValue _ _) _` mp_tac >>
          asm_rewrite_tac[]) >>
      irule ifexp_vv_at_of_val_at >> asm_rewrite_tac[] >> qexists `v` >> asm_rewrite_tac[] >>
      fs[expr_post_mods_def,expr_post_def]) >>
  map_every qx_gen_tac [`ctv`,`v'`] >> strip_tac >>
  qpat_x_assum `ctv = Value v'` SUBST_ALL_TAC >>
  `v' = v` by (drule_all ifexp_equal_layout_read_value >> simp[]) >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  Cases_on `t = NoneT`
  >- (asm_rewrite_tac[] >> irule ifexp_none_value_owned >> qexists `w` >> simp[]) >>
  `!id path. raw <> PlaceR (MemoryPlace id path)` by
    (rpt gen_tac >> disch_tac >>
     `runtime_place_typed cx ee (MemoryPlace id path) dv` by
       (qpat_assum `eval_result_typed _ _ _` mp_tac >>
        qpat_assum `env.type_defs = _` mp_tac >>
        qpat_assum `raw = PlaceR _` mp_tac >>
        qpat_assum `evaluate_type (get_tenv cx) t = SOME dv` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[eval_result_typed_def] >> metis_tac[]) >>
     qpat_x_assum `raw = PlaceR _` SUBST_ALL_TAC >>
     drule_all ifexp_equal_layout_aggregate_place >> simp[]) >>
  `!tag p. vv = LocatedValue tag p ==> ~is_word_type tag /\ p.ptr_location <> LocCalldata` by
    (drule ifexp_raw_nonword_tags >> asm_rewrite_tac[]) >>
  qpat_x_assum `(sb = sm /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
  >- (`vv_location vv = NONE \/ vv_location vv = SOME LocMemory` suffices_by
        (disch_tac >>
         `raw = Value v` by
           (qpat_assum `vv_post_mods (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
              (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
            drule_all ifexp_identity_nonplace_value >> simp[]) >>
         irule ifexp_identity_value_owned >> asm_rewrite_tac[] >>
         qexists `vv` >> asm_rewrite_tac[] >>
         qpat_assum `!v. raw = Value v /\ _ ==> vv_own _ _ _ _ _ _ _ _ _`
           (qspec_then `v` mp_tac) >>
         qpat_assum `raw = Value v` mp_tac >>
         qpat_assum `post_value_type ce e = t` mp_tac >>
         qpat_assum `~is_word_type t` mp_tac >>
         qpat_assum `~is_bytestring_type t` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
      qpat_x_assum `sb = sm` SUBST_ALL_TAC >>
      irule ifexp_unwrap_identity_location >> asm_rewrite_tac[] >>
      qexistsl [`ce`,`func`,`op`,`sm`] >> asm_rewrite_tac[]) >>
  suspend "copied_own"
QED

Resume ifexp_arm_equal_layout_from_unwrap_mods[copied_own]:
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee z` by
    fs[expr_post_mods_def,expr_post_def] >>
  drule_all ifexp_unwrap_alloc_site >>
  disch_then (qspec_then `ee.scopes` strip_assume_tac) >>
  `evaluate_type (get_tenv cx) t = SOME rt` by
    (qpat_assum `post_value_type ce e = t` mp_tac >>
     qpat_assum `post_value_type ce e = lowered_value_type ce e` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  drule_all ifexp_unwrap_alloc_owned >> simp[]
QED

Resume ifexp_arm_equal_layout_from_unwrap_mods[distinct]:
  qpat_x_assum `post_value_type ce e = t \/ same_memory_layout _ _ _ /\ _`
    (DISJ_CASES_THEN strip_assume_tac) >>
  `~is_bytestring_type t` by metis_tac[post_value_type_bytestring] >>
  `~is_bytestring_type (post_value_type ce e)` by
    (qpat_assum `post_value_type ce e = t \/ post_value_type ce e = lowered_value_type ce e /\ _`
       mp_tac >> simp[] >> metis_tac[type_widens_from_bytestring]) >>
  `ptr_val_ok cx t v op Gf tf z` by
    (irule ifexp_equal_layout_distinct >> asm_rewrite_tac[] >> conj_tac
     >- (qexists `dv` >> asm_rewrite_tac[]) >>
     qexistsl [`ce`,`post_value_type ce e`,`pt`] >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  `type_memory_size pt = type_memory_size dv` by
    (qpat_assum `same_memory_layout ce (post_value_type ce e) t` mp_tac >>
     qpat_assum `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==> _`
       (qspecl_then [`post_value_type ce e`,`pt`] mp_tac) >>
     qpat_assum `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt` mp_tac >>
     qpat_assum `type_memory_bytes ce t = type_memory_size dv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[same_memory_layout_def] >> metis_tac[]) >>
  `val_footprint pt v = val_footprint dv v` by
    (drule_all compatible_footprint >> simp[]) >>
  `expr_val_own ce cx (post_value_type ce e) sa sb ee v op z` by
    (qpat_assum `expr_post_mods (storage_trace_horizon _) ctx func ce cx e _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `post_value_type ce e <> t` mp_tac >>
     qpat_assum `expr_type e = t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[expr_post_mods_def,expr_post_def]) >>
  drule_all ifexp_equal_layout_owned >> strip_tac >> asm_rewrite_tac[] >>
  map_every qx_gen_tac [`ctv`,`v'`] >> strip_tac >>
  qpat_x_assum `ctv = Value v'` SUBST_ALL_TAC >>
  drule_all ifexp_equal_layout_read_value >> simp[]
QED

Finalise ifexp_arm_equal_layout_from_unwrap_mods
