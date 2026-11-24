(* The bytestring arm copies the live representation into the IfExp
   result allocation; the allocation's capacity is kept separately. *)
Theory bodyIfExpBytesArmMods
Ancestors
  bodyIfExpAllocMods bodyIfExpArmUnwrapMods bodyLocalBytesCopyPathMods
  bodyFullIfExpWiden bodyPtrMakeArrayCopyStateFrame bodyFullPathHistory
  bodyFullAllocaFresh bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  exprSimIfExpWidenedPosts ghostObservationPtr loweringSlice stateRelProj
  loweringPosts reasonCopySourcePtr exprSimStorageCopy exprSimMemDefs vyperAST
  valueEncoding valueEncodingDefs valueEncodingTyping valueCopyBytes vyperTyping exprSimProps
  bodyPtrDefs typedMemoryCopy loweringStateRelDefs fragExec venomInst finite_map
  fragGasOriginPtr fragGasOriginPtrLoop ptrDiscipline freshWrites exprLoweringProps context venomState words
  loweringHalt exprSimUnwrap compileEnv exprSimAlloc bodyMemoryDefs exprSimIfExp vyperState vyperInterpreter

Theorem bytes_arm_extent[local]:
  is_bytestring_type sty /\ evaluate_type tenv sty = SOME rt /\
  value_has_type rt v ==>
  ?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
         (?str. v = StringV str /\ len = LENGTH str)) /\
    val_store_size rt v = 32 + 32 * word_size len /\ 0 < type_memory_size rt
Proof
  strip_tac >> drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def,val_store_size_def,type_memory_size_def]
QED

Theorem bytes_arm_copy_immutable[local]:
  immutable_frame_mods func ce cx ee s /\ local_ptrs_reserved ce sc /\
  typed_copy_state_frame sc b n s z /\ n <= N /\
  MEM (mk_inst aid ALLOCA [Lit (n2w N)] [p]) (fn_insts func) /\
  FLOOKUP s.vs_allocas aid = SOME (b,N) ==>
  immutable_frame_mods func ce cx ee z
Proof
  strip_tac >>
  `z.vs_data_section = s.vs_data_section /\ z.vs_allocas = s.vs_allocas /\
   z.vs_alloca_next = s.vs_alloca_next` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `!name b sz. local_region ce ee.scopes z name b sz <=>
               local_region ce ee.scopes s name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     fs[typed_copy_state_frame_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def] >> conj_tac
  >- suspend "bytes" >>
  rpt gen_tac >> disch_tac >>
  irule immutable_alloca_sep_fields >> qexistsl [`s`,`ee`] >> simp[] >>
  rpt gen_tac >> disch_tac >> qexists `id` >>
  `!u. local_region (ce with ce_module := src) ee.scopes u id b' sz =
       local_region ce ee.scopes u id b' sz` by simp[local_region_def] >>
  metis_tac[]
QED

Resume bytes_arm_copy_immutable[bytes]:
  rpt gen_tac >> disch_tac >>
  `immutables_rel ce cx.txn.target src ce.ce_is_ctor ee z` suffices_by
    simp[immutables_rel_def] >>
  irule immutables_rel_mem_agree >> qexists `s` >> simp[] >>
  conj_tac >- fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  rpt strip_tac >>
  `immutable_alloca_sep func (ce with ce_module := src) cx ee s` by metis_tac[] >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
    (mp_tac o REWRITE_RULE [immutable_alloca_sep_def]) >>
  simp[] >> strip_tac >> first_x_assum drule_all >> strip_tac >>
  `regions_disjoint off (type_memory_size tv) b N` by
    (qpat_assum `!inst b sz. MEM inst _ /\ _ ==> _` irule >>
     qexists `mk_inst aid ALLOCA [Lit (n2w N)] [p]` >> simp[mk_inst_def]) >>
  fs[regions_disjoint_def, typed_copy_state_frame_def, typed_copy_frame_def] >>
  first_x_assum irule >> decide_tac
QED

Finalise bytes_arm_copy_immutable

Theorem bytes_arm_local_footprint[local]:
  local_ptrs_rel func ce ee.scopes s /\
  lookup_scopes name ee.scopes = SOME entry /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w ==>
  val_wf entry.type entry.value /\ val_footprint entry.type entry.value <= sz /\
  local_region ce ee.scopes s name (w2n w) sz
Proof
  strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  drule_then assume_tac val_footprint_le >>
  simp[local_region_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem bytes_arm_copy_ghost[local]:
  ghost_inv_at_mods D lo d ce cx ee G tn s /\ local_ptrs_reserved ce sc /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  typed_copy_state_frame sc b n s z /\ lo <= b /\
  local_ptrs_rel func ce ee.scopes s /\
  (!id lb k. local_region ce ee.scopes s id lb k ==> lb+k <= b \/ b+n <= lb) /\
  (!x. not_fresh_at sc x ==> FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(b <= i /\ i < b+n) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory ==>
  ghost_inv_at_mods D lo d ce cx ee Gf tf z
Proof
  strip_tac >>
  `!p k. not_fresh_at sc p /\ ptr_covers G tn p s k ==> ptr_covers Gf tf p z k` by
    (rw[ptr_covers_def] >> fs[typed_copy_state_frame_def] >> metis_tac[]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_mods_def] >> strip_tac >>
  `z.vs_call_ctx = s.vs_call_ctx /\ z.vs_accounts = s.vs_accounts /\
   z.vs_transient = s.vs_transient /\ z.vs_immutables = s.vs_immutables /\
   z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  conj_tac >- suspend "locals" >>
  conj_tac >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
    PairCases_on `x` >> gvs[return_buf_ptr_def,typed_copy_state_frame_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[stor_taint_ok_at_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `~(b <= i /\ i < b+n)` by decide_tac >> metis_tac[]) >>
  conj_tac >- (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[allocas_from_def] >> first_assum ACCEPT_TAC
QED

Resume bytes_arm_copy_ghost[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sc p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by (fs[typed_copy_state_frame_def] >> metis_tac[]) >>
  drule_all bytes_arm_local_footprint >> strip_tac >>
  irule robust_val_in_memory_exterior_no_new_taint >> simp[] >>
  qexistsl [`{i | b <= i /\ i < b+n}`,`s.vs_memory`,`z.vs_memory`,`tn.t_mem`,`tf.t_mem`] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
      qpat_assum `!off sz. _ ==> mem_bytes_at _ _ _ = _` irule >> decide_tac) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> qpat_assum `!id lb k. local_region _ _ _ _ _ _ ==> _`
       (drule_then strip_assume_tac) >> decide_tac
QED

Finalise bytes_arm_copy_ghost

Theorem bytes_arm_kept[local]:
  ghost_kept_at lo ce es sa Gi ti u G tn /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!i. ~(b <= i /\ i < b+n) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!old off k. FLOOKUP u.vs_allocas old = SOME (off,k) /\ old < sa.cs_next_id ==>
    off+k <= b \/ b+n <= off) /\
  (!id lb k. local_region ce es.scopes u id lb k ==> lb+k <= b \/ b+n <= lb) ==>
  ghost_kept_at lo ce es sa Gi ti u Gf tf
Proof
  pure_rewrite_tac[ghost_kept_at_def] >> strip_tac >> conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `off+sz <= b \/ b+n <= off` by metis_tac[] >>
      `~(b <= i /\ i < b+n)` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `b'+sz <= b \/ b+n <= b'` by metis_tac[] >>
  `~(b <= i /\ i < b+n)` by decide_tac >> metis_tac[]
QED

(* The raw arm has already been read at sc.  At this cut the destination
   is live, and its allocation record excludes the protected regions. *)
Theorem bytes_arm_store[local]:
  compile_store_memory ce (Var ps) (Var pd) t lt sc = ((),sb) /\
  ~is_word_type t /\ is_bytestring_type t /\ is_bytestring_type lt /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  evaluate_type (get_tenv cx) lt = SOME rt /\
  value_has_type rt v /\ value_has_type tv v /\
  type_memory_bytes ce t = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt v (w2n sw) m) /\
  not_fresh_at sc ps /\ not_fresh_at sc pd /\
  lookup_var ps s = SOME sw /\ lookup_var pd s = SOME dw /\
  ptr_covers G tn ps s (type_memory_size rt) /\
  ptr_covers G tn pd s (type_memory_size tv) /\
  FLOOKUP G pd = SOME (w2n dw,type_memory_size tv) /\
  w2n sw + type_memory_size rt <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,type_memory_size tv) /\
  MEM (mk_inst aid ALLOCA [Lit (n2w (type_memory_size tv))] [pd]) (fn_insts func) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\ sa.cs_next_var <= sc.cs_next_var /\
  lo <= w2n dw /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e es sa sc u ee v (Var ps) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!name b k. local_region ce ee.scopes s name b k ==>
    b+k <= w2n dw \/ w2n dw+type_memory_size tv <= b) /\
  (!old off k. FLOOKUP u.vs_allocas old = SOME (off,k) /\ old < sa.cs_next_id ==>
    off+k <= w2n dw \/ w2n dw+type_memory_size tv <= off) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  ghost_kept_at lo ce es sa Gi ti u G tn /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?z Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb u ee v (Var pd) z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    (!raw. read_result cx raw ee = (INL v,ee) ==>
      vv_own ce cx t sa sb ee raw (LocatedValue t (mk_ptr (Var pd) LocMemory)) z /\
      vv_at ce cx t sa sb ee raw (LocatedValue t (mk_ptr (Var pd) LocMemory)) z) /\
    expr_store_bound cx t v (Var pd) z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ z.vs_alloca_next = s.vs_alloca_next /\
    ptr_val_ok cx t v (Var pd) Gf tf z /\
    (!e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' (Var pd) Gf z) /\
    (!rt w. evaluate_type (get_tenv cx) t = SOME rt /\ eval_operand (Var pd) z = SOME w ==>
      w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo ce es sa Gi ti u Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s` by
    (rpt strip_tac >> first_x_assum drule >> simp[expr_post_mods_def,expr_post_def]) >>
  `alloca_inv s /\ local_ptrs_rel func ce ee.scopes s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _`
      (drule_then (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >> simp[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >> fs[ghost_inv_at_mods_def]) >>
  `w2n dw + type_memory_size tv <= s.vs_alloca_next` by
    (fs[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `val_wf rt v /\ val_wf tv v` by simp[value_has_type_val_wf] >>
  `val_store_size rt v <= type_memory_size rt /\ val_store_size rt v <= type_memory_size tv` by
    (`val_store_size rt v = val_store_size tv v` by
       (irule bytestring_val_store_size_eq >> simp[] >>
        qexistsl [`lt`,`t`,`get_tenv cx`] >> simp[]) >>
     metis_tac[val_store_size_le]) >>
  drule_all (Q.INST [`sty` |-> `lt`] bytes_arm_extent) >>
  disch_then (qx_choose_then `len`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN assume_tac))) >>
  qabbrev_tac `n = val_store_size rt v` >>
  `ptr_covers G tn ps s n /\ ptr_covers G tn pd s n` by
    (conj_tac >- (irule ptr_covers_mono >> qexists `type_memory_size rt` >> simp[]) >>
     irule ptr_covers_mono >> qexists `type_memory_size tv` >> simp[]) >>
  `w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\ n < dimword (:256)` by decide_tac >>
  drule (Q.INST [`tenv` |-> `get_tenv cx`,`dtv` |-> `tv`,`dw` |-> `dw`]
    local_bytes_copy_path_mods) >>
  disch_then (drule_at (Pat `!m. mem_agree_outside _ _ m ==> val_in_memory _ _ _ m`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca _ ==> allocas_below_fmp _`)) >>
  disch_then (drule_at (Pat `n = 32 + 32 * word_size len`)) >>
  disch_then (drule_at (Pat `ptr_covers G tn ps s n`)) >>
  disch_then (drule_at (Pat `fn_has_code sc sb func`)) >>
  disch_then (drule_at (Pat `allocas_from lo s`)) >>
  disch_then (qspecl_then [`tv`,`explicit`,`dw`] mp_tac) >>
  disch_then (qspecl_then [`cx`,`PG`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`z`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "frame"
QED

Resume bytes_arm_store[frame]:
  `z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
   copy_static z = copy_static s` by
    fs[typed_copy_state_frame_def,copy_static_def,venom_state_component_equality] >>
  `lookup_var pd z = SOME dw /\ FLOOKUP Gf pd = SOME (w2n dw,type_memory_size tv) /\
   op_taint tf (Var pd) = {}` by
    ((`op_taint tn (Var pd) = {}` by
       (qpat_assum `ptr_covers G tn pd s (type_memory_size tv)` mp_tac >>
        simp[NoAsms,ptr_covers_def]) >>
     qpat_assum `!x. not_fresh_at sc x ==> _ /\ _` (qspec_then `pd` mp_tac) >>
     asm_rewrite_tac[] >> (metis_tac[NoAsms, ptr_covers_def]))) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by metis_tac[not_fresh_at_mono] >>
  `!off k. off+k <= w2n dw \/ w2n dw+type_memory_size tv <= off ==>
    mem_bytes_at off k z.vs_memory = mem_bytes_at off k s.vs_memory` by
    (rpt strip_tac >> fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
     qpat_assum `!off k. _ ==> mem_bytes_at _ _ z.vs_memory = _` irule >> decide_tac) >>
  `local_ptrs_reserved ce sc` by metis_tac[local_ptrs_reserved_next_var] >>
  `!name b k. local_region ce ee.scopes z name b k <=> local_region ce ee.scopes s name b k` by
    (rpt gen_tac >> irule local_region_lookup_cong >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee z` by
    suspend "state" >>
  `val_footprint tv v <= type_memory_size tv /\ val_store_size tv v <= type_memory_size tv` by
    simp[val_footprint_le,val_store_size_le] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb u ee v (Var pd) z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z` by suspend "posts" >>
  `alloca_history func z` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `ARB` assume_tac) >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  qexistsl [`z`,`Gf`,`tf`] >> simp[] >> suspend "resources"
QED

Resume bytes_arm_store[state]:
  rpt strip_tac >> irule literal_copy_window_stmt_state_rel >>
  qexistsl [`aid`,`w2n dw`,`type_memory_size tv`,`pd`,`sa`,`sc`,`s`] >> simp[] >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def,typed_copy_frame_def]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[regions_disjoint_def] >>
      qpat_assum `!name b k. local_region ce ee.scopes s name b k ==> _`
        (drule_then mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!off k. _ \/ w2n dw + type_memory_size tv <= off ==> _` irule >>
  qpat_x_assum `_ \/ type_memory_size tv + w2n dw <= _` mp_tac >>
  rpt (qpat_x_assum `_` kall_tac) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume bytes_arm_store[posts]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def])) >>
  conj_tac >- suspend "semantic" >>
  irule bytes_arm_copy_ghost >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _` (irule_at Any) >>
  qpat_x_assum `n = 32 + 32 * word_size len` kall_tac >>
  qexistsl [`tn`,`func`,`G`] >> simp[] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `n <= type_memory_size tv` mp_tac >>
  qpat_assum `!name b k. local_region ce ee.scopes s name b k ==> _`
    (drule_then mp_tac) >>
  rpt (qpat_x_assum `_` kall_tac) >> decide_tac
QED

Resume bytes_arm_store[semantic]:
  simp[expr_post_mods_def] >> reverse conj_tac
  >- (irule bytes_arm_copy_immutable >> qpat_assum `typed_copy_state_frame _ _ _ _ _`
        (irule_at Any) >> qexistsl [`pd`,`aid`,`type_memory_size tv`] >> simp[]) >>
  irule allocated_result_expr_post_frame >>
  qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl [`dw`,`mk_inst aid ALLOCA [Lit (n2w (type_memory_size tv))] [pd]`,
    `w2n dw`,`aid`,`type_memory_size tv`] >>
  simp[post_value_type_def,expr_type_def,eval_operand_def,expr_val_rel_def,mk_inst_def] >>
  conj_tac >- (first_assum irule >> simp[mem_agree_outside_def]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!name b k. local_region ce ee.scopes s name b k ==> _`
        (drule_then mp_tac) >>
      rpt (qpat_x_assum `_` kall_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> irule local_region_frame_fwd >>
      qexistsl [`u`,`sa`,`es.scopes`] >> simp[] >> fs[expr_post_def]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!old off k. FLOOKUP u.vs_allocas old = SOME (off,k) /\ _ ==> _`
        (drule_all_then mp_tac) >>
      rpt (qpat_x_assum `_` kall_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!off k. _ \/ w2n dw + type_memory_size tv <= off ==> _` irule >>
  pop_assum mp_tac >> rpt (qpat_x_assum `_` kall_tac) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume bytes_arm_store[resources]:
  conj_tac
  >- (simp[vv_own_def,vv_at_def,mk_ptr_def,eval_operand_def] >> rpt strip_tac >>
      disj1_tac >> qexistsl [`aid`,`w2n dw`,`type_memory_size tv`] >>
      simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  conj_tac >- simp[expr_store_bound_def,eval_operand_def] >>
  conj_tac
  >- (simp[ptr_val_ok_def,ptr_mem_ok_def,eval_operand_def] >> rpt strip_tac >>
      qexistsl [`pd`,`w2n dw`,`type_memory_size tv`] >> simp[]) >>
  conj_tac
  >- (simp[ptr_buf_ok_def,eval_operand_def] >> rpt strip_tac >>
      qexistsl [`pd`,`w2n dw`,`type_memory_size tv`] >> simp[]) >>
  conj_tac >- simp[eval_operand_def] >>
  irule bytes_arm_kept >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_x_assum `n = 32 + 32 * word_size len` kall_tac >>
  qexistsl [`n`,`w2n dw`] >> simp[] >> suspend "kept"
QED

Resume bytes_arm_store[kept]:
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `local_region ce ee.scopes s id lb k` by
        (irule local_region_frame_fwd >> qexistsl [`u`,`sa`,`es.scopes`] >>
         simp[] >> qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods H ctx func ce cx e es sa sc u ee v (Var ps) s /\ _`
           (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def])) >> simp[]) >>
      qpat_assum `!name b k. local_region ce ee.scopes s name b k ==> _`
        (qspec_then `id` (drule_then mp_tac)) >>
      qpat_assum `n <= type_memory_size tv` mp_tac >>
      rpt (qpat_x_assum `_` kall_tac) >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!old off k. FLOOKUP u.vs_allocas old = SOME (off,k) /\ _ ==> _`
    (drule_all_then mp_tac) >>
  qpat_assum `n <= type_memory_size tv` mp_tac >>
  rpt (qpat_x_assum `_` kall_tac) >> decide_tac
QED

Finalise bytes_arm_store

(* Use the actual selected eval, rather than imposing a shape on the raw
   operand. In particular a constructor LocCode can need materialization. *)
Theorem ifexp_bytes_arm_from_read_mods:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_ifexp_arm ce t (lowered_value_type ce e) vv sm = (op,sb) /\
  ~is_word_type t /\ ~same_memory_layout ce (lowered_value_type ce e) t /\
  is_bytestring_type t /\ is_bytestring_type (lowered_value_type ce e) /\
  arg_type_fits (lowered_value_type ce e) t /\
  (e = a \/ e = b) /\ expr_type e = t /\ post_value_type ce e = t /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  type_memory_bytes ce t = type_memory_size tv /\ type_memory_size tv < 2 ** 64 /\
  (!id path. raw = PlaceR (MemoryPlace id path) ==>
     same_memory_layout ce (lowered_value_type ce e) t) /\
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm u ee raw vv z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn z) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv z /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn z /\
  (!tag x. vv = StackValue tag x /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e x G z) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G z) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) z = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type tv v) /\
  ghost_kept_at lo ce es sa Gi ti u G tn /\
  ~z.vs_halted /\ z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func z /\
  u.vs_alloca_next <= z.vs_alloca_next ==>
  ?v z' Gf tf.
    read_result cx raw ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK z',Gf,tf) /\
      expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb u ee v op z' /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z') /\
    vv_at ce cx t sa sb ee raw (LocatedValue t (mk_ptr op LocMemory)) z' /\
    (!id path. raw = PlaceR (MemoryPlace id path) ==>
      vv_place_ptr ce cx ee z' raw (LocatedValue t (mk_ptr op LocMemory))) /\
    (!ctv v'. conditional_result cx raw ee = (INL ctv,ee) /\ ctv = Value v' ==>
      vv_own ce cx t sa sb ee ctv (LocatedValue t (mk_ptr op LocMemory)) z') /\
    expr_store_bound cx t v op z' /\
    z'.vs_current_bb = sb.cs_current_bb /\ z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
    ptr_val_ok cx t v op Gf tf z' /\
    (!e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' op Gf z') /\
    (!rt w. evaluate_type (get_tenv cx) t = SOME rt /\ eval_operand op z' = SOME w ==>
      w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
    ghost_kept_at lo ce es sa Gi ti u Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (CONJUNCT1 compile_expr_grows) >> strip_tac >>
  drule_all ifexp_widen_copy_parts >>
  disch_then (qx_choosel_then [`buf`,`k`,`src`,`sc`] (map_every assume_tac o CONJUNCTS)) >>
  `cs_extends sm k /\ cs_extends k sc` by
    (conj_tac >- (drule compile_alloc_buffer_extends >> simp[]) >>
     drule unwrap_value_extends >> simp[]) >>
  `cs_extends sc sb` by
    (`compile_store_bytestring src buf.buf_operand sc = ((),sb)` by
       (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _`
          (mp_tac o REWRITE_RULE [compile_store_memory_def]) >> simp[]) >>
     drule bytesCopyCodeTheory.compile_store_bytestring_code >>
     simp[cs_extends_def,same_blocks_def,rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sm k func /\ fn_has_code k sc func /\ fn_has_code sc sb func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `type_memory_bytes ce t < dimword (:256)` by
    (simp[] >> irule arithmeticTheory.LESS_TRANS >>
     qexists `2 ** 64` >> simp[wordsTheory.dimword_def]) >>
  suspend "reserve"
QED

Resume ifexp_bytes_arm_from_read_mods[reserve]:
  `!v rt. read_result cx raw ee = (INL v,ee) /\
          evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt ==>
          value_has_type rt v` by simp[] >>
  drule_all ifexp_arm_result_alloc_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`pd`,`dw`,`q`,`Ga`,`ta`,`qa`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "read"
QED

Resume ifexp_bytes_arm_from_read_mods[read]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `ghost_kept_at lo ce es sa Gi ti u Ga ta` by suspend "reserve_kept" >>
  `!aid alloc. FLOOKUP u.vs_allocas aid = SOME alloc ==> FLOOKUP z.vs_allocas aid = SOME alloc` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ _ _ _ sm _ _ _ _ z /\ _`
      (drule_then mp_tac) >>
     simp[NoAsms,vv_post_mods_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee q` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ _ _ _ k _ _ _ _ q /\ _`
       (drule_then mp_tac) >> simp[NoAsms,vv_post_mods_def]) >>
  `sm.cs_next_var <= k.cs_next_var /\ sm.cs_next_id <= k.cs_next_id` by decide_tac >>
  `!tag x. vv = StackValue tag x ==> ptr_buf_ok ce e x Ga q` by simp[] >>
  `~is_word_type (expr_type e)` by simp[] >>
  drule_all ifexp_arm_nonword_unwrap_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`v`,`s`,`Gm`,`tm`,`pt`,`rt`,`sw`]
      (map_every assume_tac o CONJUNCTS))) >>
  `0 < type_memory_size rt` by
    (drule_all (Q.INST [`sty` |-> `lowered_value_type ce e`] bytes_arm_extent) >>
     disch_then (qx_choose_then `len` (map_every assume_tac o CONJUNCTS)) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `0 < type_memory_size rt ==> _` (drule_then (qx_choose_then `ps` strip_assume_tac)) >>
  `k.cs_next_var <= sc.cs_next_var /\ k.cs_next_id <= sc.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`,`vv`,`k`] ci_mono_unwrap_value) >> simp[ci_mono_def]) >>
  `sc.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`,`src`,`buf.buf_operand`,`t`,`lowered_value_type ce e`,`sc`]
      ci_mono_compile_store_memory) >> simp[ci_mono_def]) >>
  suspend "copy"
QED

Resume ifexp_bytes_arm_from_read_mods[reserve_kept]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ e _ _ sm _ _ _ _ z /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def,ghost_inv_at_mods_def])) >>
  irule alloc_buffer_ghost_kept_at >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `ta = step_taint _ _ _ _` kall_tac >>
  qexistsl [`z`,`w2n dw + type_memory_bytes ce t`] >> simp[] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `not_fresh_at sm x` by (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
      qpat_assum `!x. not_fresh_at sm x ==> _ /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (qx_genl_tac [`name`,`lb`,`sz`] >> disch_tac >>
      `local_region ce ee.scopes z name lb sz` by
        (irule local_region_frame_fwd >> qexistsl [`u`,`sa`,`es.scopes`] >> simp[]) >>
      drule_all body_local_region_frontier >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `alloca_inv z` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `FLOOKUP z.vs_allocas aid = SOME (off,sz)` by simp[] >>
  irule abiCallerAllocationTheory.abi_caller_allocation_end >>
  simp[] >> qexistsl [`sz`,`aid`,`off`] >> simp[]
QED

Resume ifexp_bytes_arm_from_read_mods[copy]:
  qpat_assum `src = Var ps` SUBST_ALL_TAC >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))] [pd]) (fn_insts func)` by
    (drule_all buffer_alloc_code >>
     drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `!name lb sz. local_region ce ee.scopes s name lb sz ==>
       lb+sz <= w2n dw \/ w2n dw+type_memory_size tv <= lb` by suspend "copy_locals" >>
  `!old off sz. FLOOKUP u.vs_allocas old = SOME (off,sz) /\ old < sa.cs_next_id ==>
       off+sz <= w2n dw \/ w2n dw+type_memory_size tv <= off` by suspend "copy_allocas" >>
  `(!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sc x) /\
   (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sc x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[] >> decide_tac) >>
  `~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e` by
    (qpat_assum `e = a \/ e = b` mp_tac >> simp[supportedExprTraverseTheory.expr_has_effect_def] >> metis_tac[]) >>
  `not_fresh_at sc pd` by (irule not_fresh_at_mono >> qexists `k` >> simp[]) >>
  `lookup_var ps s = SOME sw /\ lookup_var pd s = SOME dw /\
   FLOOKUP Gm pd = SOME (w2n dw,type_memory_size tv) /\
   ptr_covers Gm tm pd s (type_memory_size tv) /\
   FLOOKUP s.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size tv)` by
    suspend "copy_destination" >>
  `w2n sw + type_memory_size rt <= s.vs_alloca_next` by
    (qpat_x_assum `type_memory_size rt = 0 \/ _` mp_tac >> simp[] >> decide_tac) >>
  `sm.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `compile_store_memory ce (Var ps) (Var pd) t (lowered_value_type ce e) sc = ((),sb)` by
    (qpat_assum `compile_store_memory ce (Var ps) buf.buf_operand _ _ sc = _` mp_tac >>
     qpat_assum `buf.buf_operand = Var pd` (fn th => pure_rewrite_tac[th]) >>
     disch_tac >> first_assum ACCEPT_TAC) >>
  `type_memory_size tv < dimword (:256)` by
    (qpat_assum `type_memory_bytes ce t = type_memory_size tv`
      (fn th => pure_once_rewrite_tac[SYM th]) >> first_assum ACCEPT_TAC) >>
  `value_has_type tv v` by simp[] >>
  drule_at (Pat `compile_store_memory ce (Var ps) (Var pd) t _ sc = _`) bytes_arm_store >>
  disch_then (drule_at (Pat `ptr_covers _ _ pd _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ ps _ _`)) >>
  disch_then (drule_at (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP (_.vs_allocas) _ = SOME (_,type_memory_size _)`)) >>
  disch_then (drule_at (Pat `lookup_var ps _ = SOME _`)) >>
  disch_then (drule_at (Pat `expr_has_effect (IfExp _ _ _ _)`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`sw`,`explicit`,`PG`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`zf`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "finish"
QED

Resume ifexp_bytes_arm_from_read_mods[copy_locals]:
  `!name lb sz. local_region ce ee.scopes s name lb sz <=>
                local_region ce ee.scopes q name lb sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     qpat_assum `local_ptrs_reserved ce k` (mp_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `!x. not_fresh_at k x ==> lookup_var x s = _ /\ _` mp_tac >>
     rpt (qpat_x_assum `_` kall_tac) >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  `local_region ce ee.scopes q name lb sz` by
    (qpat_assum `!name lb sz. local_region ce ee.scopes s name lb sz <=> _`
      (qspecl_then [`name`,`lb`,`sz`] mp_tac) >> simp[]) >>
  qpat_assum `!id b len. local_region ce ee.scopes q id b len ==> _`
    (drule_then mp_tac) >>
  simp[regions_disjoint_def] >> rpt (qpat_x_assum `_` kall_tac) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume ifexp_bytes_arm_from_read_mods[copy_allocas]:
  rpt gen_tac >> strip_tac >>
  `FLOOKUP z.vs_allocas old = SOME (off,sz)` by simp[] >>
  `old < sm.cs_next_id` by decide_tac >>
  qpat_assum `!aid b k. aid < sm.cs_next_id /\ FLOOKUP z.vs_allocas aid = _ ==> _`
    (drule_all_then mp_tac) >>
  simp[regions_disjoint_def] >> rpt (qpat_x_assum `_` kall_tac) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume ifexp_bytes_arm_from_read_mods[copy_destination]:
  qpat_assum `!x. not_fresh_at k x ==> lookup_var x s = _ /\ _`
    (qspec_then `pd` (drule_then strip_assume_tac)) >>
  qpat_assum `!x cap. not_fresh_at k x /\ ptr_covers Ga ta x q cap ==> _`
    (qspecl_then [`pd`,`type_memory_bytes ce t`] (drule_all_then assume_tac)) >>
  qpat_assum `!aid b. FLOOKUP q.vs_allocas aid = SOME b ==> _`
    (qspec_then `sm.cs_next_id` (drule_then assume_tac)) >>
  qpat_assum `eval_operand (Var ps) s = SOME sw`
    (assume_tac o REWRITE_RULE [eval_operand_def]) >>
  qpat_assum `type_memory_bytes ce t = type_memory_size tv` (fn eq =>
    qpat_assum `ptr_covers Gm tm pd s (type_memory_bytes ce t)`
      (assume_tac o REWRITE_RULE [eq])) >>
  simp[]
QED

Resume ifexp_bytes_arm_from_read_mods[finish]:
  `u.vs_alloca_next <= zf.vs_alloca_next` by decide_tac >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK zf,Gf,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl [`Ga`,`q`,`ta`] >> conj_tac >- simp[] >>
     irule gas_origin_ptr_path_trans >>
     qexistsl [`Gm`,`s`,`tm`] >> simp[]) >>
  `op = Var pd` by metis_tac[] >>
  `!id path. raw <> PlaceR (MemoryPlace id path)` by
    (qx_genl_tac [`id`,`path`] >>
     qpat_assum `!id path. raw = PlaceR (MemoryPlace id path) ==> _`
       (qspecl_then [`id`,`path`] mp_tac) >>
     qpat_assum `~same_memory_layout ce (lowered_value_type ce e) t` mp_tac >>
     metis_tac[NoAsms]) >>
  `vv_at ce cx t sa sb ee raw (LocatedValue t (mk_ptr (Var pd) LocMemory)) zf` by
    (qpat_assum `!r. read_result cx r ee = _ ==> vv_own _ _ _ _ _ _ r _ _ /\ _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!ctv v'. conditional_result cx raw ee = (INL ctv,ee) /\ ctv = Value v' ==>
      vv_own ce cx t sa sb ee ctv (LocatedValue t (mk_ptr (Var pd) LocMemory)) zf` by
    suspend "conditional_own" >>
  qexistsl [`v`,`zf`,`Gf`,`tf`] >> simp[]
QED

Resume ifexp_bytes_arm_from_read_mods[conditional_own]:
  qx_genl_tac [`ctv`,`cv`] >> strip_tac >>
  `read_result cx ctv ee = (INL cv,ee)` by simp[read_result_def,return_def] >>
  `(do r <- conditional_result cx raw; read_result cx r od) ee = (INL cv,ee)` by
    simp[bind_def,read_result_def,return_def] >>
  `cv = v` by
    (drule conditional_read_cases >>
     qpat_assum `read_result cx raw ee = (INL v,ee)` (fn th => simp[NoAsms,th])) >>
  qpat_assum `!r. read_result cx r ee = _ ==> vv_own _ _ _ _ _ _ r _ _ /\ _`
    (qspec_then `ctv` mp_tac) >> simp[read_result_def,return_def]
QED

Finalise ifexp_bytes_arm_from_read_mods
