(* Finish the common staged ABI encoder at its actual registered buffer. *)
Theory bodyAbiEncodeFinishMods
Ancestors
  bodyFullAbiEncodeFinish bodyFullAbiEncodeResultResources
  exprSimAbiEncodeBytesOwnership bodyFullPostsMods
  bodyIfExpTypedImmFrameMods bodyIfExpTypedGhostMods bodyPtrMakeArrayCopyStateFrame
  bodyFullUnwrapRun bodyMemoryDefs exprSimHash exprSimStorageCopy exprSimProps
  typedCopyOriginPtrBase typedMemoryCopy exprLoweringProps localPtrsProps stateRelProj allocaSiteResource
  logStoreDataOriginPtr valueEncodingProps valueEncodingDefs valueEncodingProofs abiBuiltinEncodeCode
  loweringPosts loweringStateRelDefs bodyPtrDefs freshWrites context
  venomState venomMemDefs[qualified] vyperAST finite_map pred_set list words arithmetic

Triviality abi_finish_bytes_at:
  typed_copy_state_frame a p 32 s t /\
  tf.t_mem = tn.t_mem DIFF {i | p <= i /\ i < p+32} /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
     mem_word_at p mem = n2w (LENGTH bytes + LENGTH prefix)) /\
  mem_bytes_at (p+32) (LENGTH prefix) s.vs_memory = prefix /\
  mem_bytes_at (p+32+LENGTH prefix) (LENGTH bytes) s.vs_memory = bytes /\
  (!i. p+32 <= i /\ i < p+32+LENGTH prefix+LENGTH bytes ==> i NOTIN tn.t_mem) /\
  mem_agree_outside tf.t_mem t.vs_memory mem ==>
  val_in_memory (BaseTV (BytesT (Dynamic limit))) (BytesV (prefix ++ bytes)) p mem
Proof
  strip_tac >> rpt strip_tac >>
  `!off n. p+32 <= off /\ off+n <= p+32+LENGTH prefix+LENGTH bytes ==>
    mem_bytes_at off n mem = mem_bytes_at off n s.vs_memory` by
    (rpt strip_tac >>
     `mem_bytes_at off n mem = mem_bytes_at off n t.vs_memory` by
       (sym_tac >> irule logStoreDataOriginPtrTheory.mem_agree_outside_window >>
        qexists_tac `tf.t_mem` >> simp[] >> rpt strip_tac >>
        first_x_assum irule >> decide_tac) >>
     fs[typed_copy_state_frame_def, typed_copy_frame_def]) >>
  simp[val_in_memory_def, LENGTH_APPEND] >>
  `LENGTH bytes + LENGTH prefix = LENGTH prefix + LENGTH bytes` by decide_tac >>
  pop_assum SUBST1_TAC >> once_rewrite_tac[mem_bytes_at_split_padded] >>
  asm_rewrite_tac[]
QED

Triviality abi_finish_copy_static:
  typed_copy_state_frame a p n s t ==> copy_static t = copy_static s
Proof
  strip_tac >> fs[typed_copy_state_frame_def] >>
  qpat_assum `_ = s` (mp_tac o AP_TERM ``copy_static``) >> simp[copy_static_def]
QED

Triviality abi_finish_wb_pure:
  typed_copy_state_frame a p cap s t /\ alloca_inv s /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [root]) (fn_insts func) /\
  FLOOKUP s.vs_allocas aid = SOME (p,cap) /\
  cut.cs_next_id <= aid /\ sa.cs_next_id <= cut.cs_next_id /\
  sa.cs_next_var <= cut.cs_next_var /\ cut.cs_next_var <= a.cs_next_var /\
  0 < cap /\ local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!name b n. local_region ce ee.scopes s name b n ==> regions_disjoint p cap b n) /\
  wb_frame ce es ee sa s0 s /\ (~expr_has_effect e ==> pure_frame ce func es sa s0 s) ==>
  wb_frame ce es ee sa s0 t /\ (~expr_has_effect e ==> pure_frame ce func es sa s0 t)
Proof
  strip_tac >> drule_then (strip_assume_tac o MATCH_MP copy_static_fields) abi_finish_copy_static >>
  `!x. not_fresh_at cut x ==> lookup_var x t = lookup_var x s` by
    (fs[typed_copy_state_frame_def] >> metis_tac[not_fresh_at_mono]) >>
  `!off n. off+n <= p \/ p+cap <= off ==>
    mem_bytes_at off n t.vs_memory = mem_bytes_at off n s.vs_memory` by
    (fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (irule wb_frame_allocating_tail >> simp[] >> qexistsl_tac [`s`,`ee.scopes`,`cut`] >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> first_x_assum irule >>
          qpat_assum `!name b n. local_region _ _ _ _ _ _ ==> _` (drule_then mp_tac) >>
          simp[regions_disjoint_def] >> decide_tac) >>
      rpt strip_tac >> rename1 `FLOOKUP s.vs_allocas other = SOME (b,sz)` >>
      Cases_on `sz = 0` >- simp[mem_bytes_at_def] >>
      `venomMemDefs$regions_disjoint (p,cap) (b,sz)` by
        (irule alloca_site_registered_disjoint >> qexistsl_tac [`aid`,`other`] >>
         simp[] >> qexists_tac `s` >> simp[]) >>
      first_x_assum irule >> fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  strip_tac >> irule pure_frame_buffer_tail >>
  qexistsl_tac [`p`,`cap`,`mk_inst aid ALLOCA [Lit (n2w cap)] [root]`,`s`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `n` >>
      irule local_region_frame_fwd >>
      qexistsl_tac [`s0`,`sa`,`es.scopes`] >> fs[wb_frame_def]) >>
  simp[regions_disjoint_def, venomInstTheory.mk_inst_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Triviality abi_finish_registered_frame:
  typed_copy_state_frame a p cap s t /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [root]) (fn_insts func) /\
  FLOOKUP s.vs_allocas aid = SOME (p,cap) /\
  local_ptrs_reserved ce a /\
  (!name b n. local_region ce ee.scopes s name b n ==> regions_disjoint p cap b n) /\
  stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s ==>
  stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t
Proof
  strip_tac >> drule_then assume_tac abi_finish_copy_static >>
  conj_tac
  >- (irule literal_copy_window_stmt_state_rel >>
      qexistsl_tac [`aid`,`p`,`cap`,`root`,`a`,`a`,`s`] >>
      fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
      conj_tac
      >- metis_tac[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  irule ifexp_typed_immutable_frame_mods >>
  qexistsl_tac [`p`,`mk_inst aid ALLOCA [Lit (n2w cap)] [root]`,`a`,`cap`,`s`] >>
  simp[venomInstTheory.mk_inst_def]
QED

Triviality abi_finish_vv_at:
  expr_type e = ann /\ ann = BaseT (BytesT (Dynamic limit)) /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee t /\
  immutable_frame_mods func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
  eval_operand (Var root) t = SOME (n2w p) /\ p < dimword (:256) /\
  LENGTH payload <= limit /\ 32 + LENGTH payload <= cap /\
  val_in_memory (BaseTV (BytesT (Dynamic limit))) (BytesV payload) p t.vs_memory /\
  FLOOKUP t.vs_allocas aid = SOME (p,cap) /\ sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b n. local_region ce ee.scopes t name b n ==> regions_disjoint p cap b n) /\
  wb_frame ce es ee sa s0 t /\ (~expr_has_effect e ==> pure_frame ce func es sa s0 t) ==>
  vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value (BytesV payload))
    (LocatedValue ann (mk_ptr (Var root) LocMemory)) t
Proof
  strip_tac >>
  `vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value (BytesV payload))
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) t` suffices_by simp[] >>
  `vv_post H ctx func ce cx e es sa sb s0 ee (Value (BytesV payload))
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) t` by
    (irule abi_encode_bytes_vv_post >> simp[] >> conj_tac
     >- (qexists_tac `Value (BytesV payload)` >>
         simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
     qexistsl_tac [`aid`,`p`,`cap`] >>
     simp[LESS_MOD] >> fs[regions_disjoint_def] >> rpt strip_tac >>
     first_x_assum drule >> decide_tac) >>
  qhdtm_x_assum `vv_post` (mp_tac o REWRITE_RULE [vv_post_def]) >>
  simp[vv_post_mods_def, vv_holds_mods_def, vv_place_ptr_mods_def, mk_ptr_def] >>
  metis_tac[]
QED

(* The payload is already encoded at the real finish cut.  Only its length
   header is written by this interval; the selector and payload stay in place. *)
Theorem abi_encode_bytes_finish_mods:
  let e = TypeBuiltin (BaseT (BytesT (Dynamic limit))) (AbiEncode ensure mid) target args;
      prefix = abi_encode_method_id_bytes mid;
      payload = prefix ++ bytes;
      vv = LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)
  in
  abi_builtin_encode_finish (Var root) lenop (LENGTH prefix) a = ((),sb) /\
  fn_has_code a sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ alloca_inv s /\ lo <= p /\ s.vs_alloca_next < dimword (:256) /\
  eval_operand (Var root) s = SOME (n2w p) /\ ptr_covers G tn root s cap /\
  eval_operand lenop s = SOME (n2w (LENGTH bytes)) /\ op_taint tn lenop = {} /\
  not_fresh_at a root /\ (!x. lenop = Var x ==> not_fresh_at a x) /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [root]) (fn_insts func) /\
  FLOOKUP s.vs_allocas aid = SOME (p,cap) /\ sa.cs_next_id <= aid /\ aid < a.cs_next_id /\
  not_local_ptr ce ee.scopes root /\ local_ptrs_rel func ce ee.scopes s /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= a.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ wb_frame ce es ee sa s0 s /\
  (~expr_has_effect e ==> pure_frame ce func es sa s0 s) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
     storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  LENGTH payload <= limit /\ 32 + LENGTH payload <= cap /\
  val_store_size (BaseTV (BytesT (Dynamic limit))) (BytesV payload) <= cap /\
  type_memory_bytes ce (lowered_value_type ce e) <= cap /\
  mem_bytes_at (p+32) (LENGTH prefix) s.vs_memory = prefix /\
  mem_bytes_at (p+32+LENGTH prefix) (LENGTH bytes) s.vs_memory = bytes /\
  (!i. p+32 <= i /\ i < p+32+LENGTH prefix+LENGTH bytes ==> i NOTIN tn.t_mem) ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    return_buf_frame d ce sb t /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
       val_in_memory (BaseTV (BytesT (Dynamic limit))) (BytesV payload) p mem) /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee (Value (BytesV payload)) vv t /\
    ptr_vv_ok cx (post_value_type ce e) (Value (BytesV payload)) vv ee Gf tf t /\
    ptr_buf_ok ce e (Var root) Gf t /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value (BytesV payload)) vv t /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf t)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `p+cap <= s.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `32 <= cap /\ p < dimword (:256) /\ p+32 <= s.vs_alloca_next /\
   LENGTH bytes + LENGTH (abi_encode_method_id_bytes mid) < dimword (:256)` by
    (fs[LENGTH_APPEND] >> decide_tac) >>
  `ptr_covers G tn root s 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `cap` >> simp[]) >>
  `lookup_var root s = SOME (n2w p)` by fs[eval_operand_def] >>
  drule_all abi_encode_finish_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `typed_copy_state_frame a p 32 s t` >>
  rename1 `ptr_covers Gf tf root t 32` >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  `a.cs_next_var <= sb.cs_next_var /\ aid < sb.cs_next_id` by
    (drule abi_builtin_encode_finish_shape >> strip_tac >> decide_tac) >>
  `local_ptrs_reserved ce a` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at a x` by metis_tac[not_fresh_at_mono] >>
  `typed_copy_state_frame a p cap s t` by
    (irule typed_copy_state_frame_subinterval >> qexistsl_tac [`p`,`32`] >> simp[]) >>
  `!name b n. local_region ce ee.scopes s name b n ==> regions_disjoint p cap b n` by
    (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`ce`,`func`,`mk_inst aid ALLOCA [Lit (n2w cap)] [root]`,
                   `name`,`root`,`ee.scopes`,`s`] >> simp[venomInstTheory.mk_inst_def]) >>
  simp[] >> suspend "finish_frames"
QED

Resume abi_encode_bytes_finish_mods[finish_frames]:
  `!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s` by simp[] >>
  `ptr_covers Gf tf root t cap` by metis_tac[] >>
  `!i. ~(p <= i /\ i < p+32) ==> (i IN tf.t_mem <=> i IN tn.t_mem)` by simp[] >>
  `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic limit)))
      (BytesV (abi_encode_method_id_bytes mid ++ bytes)) p mem` by
    (rpt strip_tac >> irule abi_finish_bytes_at >>
     qexistsl_tac [`a`,`s`,`t`,`tf`,`tn`] >> simp[]) >>
  `w2n (n2w p : bytes32) = p` by simp[w2n_n2w] >>
  `vv_store_bound cx (BaseT (BytesT (Dynamic limit)))
       (lowered_value_type ce (TypeBuiltin (BaseT (BytesT (Dynamic limit)))
         (AbiEncode ensure mid) target args)) ee
       (Value (BytesV (abi_encode_method_id_bytes mid ++ bytes)))
       (LocatedValue (BaseT (BytesT (Dynamic limit))) (mk_ptr (Var root) LocMemory)) t /\
   ptr_vv_ok cx (BaseT (BytesT (Dynamic limit)))
       (Value (BytesV (abi_encode_method_id_bytes mid ++ bytes)))
       (LocatedValue (BaseT (BytesT (Dynamic limit))) (mk_ptr (Var root) LocMemory)) ee Gf tf t /\
   ptr_buf_ok ce (TypeBuiltin (BaseT (BytesT (Dynamic limit)))
       (AbiEncode ensure mid) target args) (Var root) Gf t` by
    (irule (SIMP_RULE (srw_ss()) [expr_type_def] abi_encode_bytes_full_resources) >>
     qexistsl_tac [`BaseT (BytesT (Dynamic limit))`,`cap`,`n2w p`] >> simp[]) >>
  conj_tac
  >- (drule_then (fn th => simp[th]) typed_copy_state_frame_allocas_below_fmp) >>
  conj_tac
  >- (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`a`] >> simp[]) >>
  conj_tac
  >- (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >>
      simp[DIFF_SUBSET] >> metis_tac[]) >>
  simp[expr_type_def] >> suspend "horizon_posts"
QED

Resume abi_encode_bytes_finish_mods[horizon_posts]:
  qabbrev_tac `encoder = TypeBuiltin (BaseT (BytesT (Dynamic limit))) (AbiEncode ensure mid) target args` >>
  `wb_frame ce es ee sa s0 t /\ (~expr_has_effect encoder ==> pure_frame ce func es sa s0 t)` by
    (irule abi_finish_wb_pure >>
     simp[] >> qexistsl_tac [`a`,`aid`,`cap`,`sa`,`p`,`root`,`s`] >> simp[] >>
     qpat_assum `!name b n. local_region _ _ s _ _ _ ==> _` ACCEPT_TAC) >>
  `!name b n. local_region ce ee.scopes t name b n ==> regions_disjoint p cap b n` by
    (rpt strip_tac >> qpat_assum `!name b n. local_region _ _ s _ _ _ ==> _` irule >>
     qexists_tac `name` >> irule local_region_frame_fwd >>
     qexistsl_tac [`t`,`a`,`ee.scopes`] >> simp[] >>
     rpt strip_tac >> qpat_assum `!x. not_fresh_at a x ==> lookup_var x t = _`
       (drule_then SUBST_ALL_TAC) >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t` by
    (irule abi_finish_registered_frame >>
     qexistsl_tac [`a`,`aid`,`cap`,`p`,`root`,`s`] >> simp[] >>
     qpat_assum `!name b n. local_region _ _ s _ _ _ ==> _` ACCEPT_TAC) >>
  conj_tac
  >- (irule abi_finish_vv_at >> simp[Abbr `encoder`, expr_type_def] >>
      qexistsl_tac [`aid`,`cap`,`p`] >> simp[mem_agree_outside_def] >>
      conj_tac
      >- qpat_assum `!name b n. local_region _ _ t _ _ _ ==> _` ACCEPT_TAC >>
      fs[LENGTH_APPEND] >> decide_tac) >>
  irule ifexp_typed_copy_ghost_mods >>
  qexistsl_tac [`G`,`p`,`func`,`a`,`32`,`s`,`tn`] >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!name b n. local_region _ _ s _ _ _ ==> _` (drule_then mp_tac) >>
  simp[regions_disjoint_def] >> decide_tac
QED

Finalise abi_encode_bytes_finish_mods
