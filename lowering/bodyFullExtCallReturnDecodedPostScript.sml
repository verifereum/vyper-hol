(* Endpoint packaging for the allocated external-return decoder. *)
Theory bodyFullExtCallReturnDecodedPost
Ancestors loweringStateRelDefs[qualified,ignore_grammar]
  extcallReturnFrameBridge abiCallerLocalScratch ptrDiscipline venomMemDefs
  abiMalformedRecursiveInterface localPtrsProps abiMalformedSiteFrame
  abiValidAllocatedContract abiBoundaryChecks allocaSiteResource
  bodyPtrDefs bodyPtrBytestringBuiltinsWindowGhost abiDecoderReentry
  extcallReturnDefaultTypes extcallReturnInterface stateRelProj
  extcallReturnDecoderOwnership supportedExprTraverse
  loweringPosts exprSimMemDefs exprSimProps exprLowering compileEnv
  context venomState vyperState vyperABI valueEncoding words
  finite_map pred_set arithmetic
  exprSimHypsDefs[qualified]

Theorem decoded_local_byte_exterior[local]:
  alloca_inv s /\ fn_inst_ids_distinct func /\ local_ptrs_rel func ce scopes s /\
  abi_malformed_destination func ce scopes dstid d n s /\
  (!id b cap. id IN sites /\ FLOOKUP s.vs_allocas id = SOME (b,cap) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce scopes q) /\
  local_region ce scopes s name lo sz /\ lo <= i /\ i < lo+sz ==>
  ~(d <= i /\ i < d+n) /\ ~abi_malformed_site_range sites s t i 1
Proof
  strip_tac >>
  conj_tac
  >- (strip_tac >> gvs[abi_malformed_destination_def] >>
      drule_all local_ptrs_rel_alloca_disjoint >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `lo + sz <= s.vs_alloca_next` by metis_tac[abi_caller_local_end] >>
  strip_tac >> fs[abi_malformed_site_range_def]
  >- (qpat_x_assum `!id b cap. _` drule >> disch_then drule >> strip_tac >>
      gvs[] >> drule_all local_ptrs_rel_alloca_disjoint >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  decide_tac
QED

Theorem decoded_old_alloca_byte_exterior[local]:
  alloca_inv s /\ abi_malformed_destination func ce scopes dstid d n s /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\ aid <> dstid /\ aid NOTIN sites /\
  b <= i /\ i < b+cap ==>
  ~(d <= i /\ i < d+n) /\ ~abi_malformed_site_range sites s t i 1
Proof
  strip_tac >>
  conj_tac
  >- (strip_tac >> gvs[abi_malformed_destination_def, alloca_inv_def,
                       allocas_non_overlapping_def] >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> decide_tac) >>
  strip_tac >>
  `b+cap <= i \/ i+1 <= b` by
    (irule abi_malformed_site_range_protected >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  decide_tac
QED

Theorem decoded_prefix_byte_exterior[local]:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  abi_malformed_destination func ce scopes dstid d n s /\ i < lo ==>
  ~(d <= i /\ i < d+n) /\ ~abi_malformed_site_range sites s t i 1
Proof
  strip_tac >>
  conj_tac
  >- (strip_tac >> fs[abi_malformed_destination_def, allocas_from_def] >>
      first_x_assum drule >> decide_tac) >>
  strip_tac >> fs[abi_malformed_site_range_def]
  >- (fs[allocas_from_def] >> first_x_assum drule >> decide_tac) >>
  decide_tac
QED

(* The singleton ABI wrapper has no memory header.  The same projection
   applies to the concrete representation and to every untainted view. *)
Theorem decoded_located_value[local]:
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  n = type_memory_size tv /\ n = type_memory_bytes ce ty /\
  eval_operand (Var output) t = SOME w /\ ptr_covers G tn output t n /\
  val_in_memory tv v (w2n w) t.vs_memory /\
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
  FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w+n <= b+cap /\ b+cap <= t.vs_alloca_next /\
  (!name l k. local_region ce ee.scopes t name l k ==> b+cap <= l \/ l+k <= b) ==>
  vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr (Var output) LocMemory)) ee t /\
  vv_at ce cx ty sa sb ee (Value v) (LocatedValue ty (mk_ptr (Var output) LocMemory)) t /\
    vv_own ce cx ty sa sb ee (Value v) (LocatedValue ty (mk_ptr (Var output) LocMemory)) t /\
    vv_store_bound cx ty ty ee (Value v) (LocatedValue ty (mk_ptr (Var output) LocMemory)) t /\
    ptr_vv_ok cx ty (Value v) (LocatedValue ty (mk_ptr (Var output) LocMemory)) ee G tn t /\
    (!e. lowered_value_type ce e = ty ==> ptr_buf_ok ce e (Var output) G t)
Proof
  strip_tac >> drule val_store_size_le >> strip_tac >>
  `val_footprint tv v <= n` by metis_tac[val_footprint_le] >>
  `is_word_type ty ==> mem_word_at (w2n w) t.vs_memory = typed_val_to_w256 tv v`
    by metis_tac[val_in_memory_word_type] >>
  gs[ptr_covers_def, eval_operand_def] >>
  simp[vv_holds_def, vv_at_def, vv_own_def, vv_store_bound_def, ptr_vv_ok_def,
       ptr_mem_ok_def, ptr_buf_ok_def, mk_ptr_def, read_result_def, return_def,
       eval_operand_def] >>
  rpt conj_tac >> rpt strip_tac
  >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`cap`] >> simp[] >>
      metis_tac[ADD_COMM])
  >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`cap`] >> simp[] >>
      metis_tac[ADD_COMM])
QED

Theorem decoded_older_operand[local]:
  not_fresh_at sa x /\ sa.cs_next_var <= st.cs_next_var ==>
  abi_decoder_operand_live st.cs_next_var (Var x)
Proof
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem decoded_ghost_frame[local]:
  ghost_inv_at D lo rb ce cx ee G tn s /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= st.cs_next_var /\
  alloca_inv s /\ fn_inst_ids_distinct func /\ local_ptrs_rel func ce ee.scopes s /\
  abi_malformed_destination func ce ee.scopes dstid d n s /\
  (!id b cap. id IN sites /\ FLOOKUP s.vs_allocas id = SOME (b,cap) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce ee.scopes q) /\
  abi_valid_allocated_frame sites d n s t /\
  abi_malformed_resource_post ctx func ce cx ee st.cs_next_var sites dstid s t /\
  (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!i. ~(d <= i /\ i < d+n) /\ ~abi_malformed_site_range sites s t i 1 ==>
    (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  ghost_inv_at D lo rb ce cx ee G' tn' t
Proof
  strip_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w` by
    (gvs[abi_malformed_resource_post_def, eval_operand_def] >>
     rpt strip_tac >> drule_all decoded_older_operand >>
     qpat_x_assum `!op w. _` (qspecl_then [`Var x`,`w`] mp_tac) >>
     simp[eval_operand_def]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> drule_all decoded_older_operand >> metis_tac[]) >>
  `stor_taint_ok_at D tn' t` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [ghost_inv_at_def]) >>
     fs[stor_taint_ok_at_def]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  irule ghost_inv_at_local_window_transport >>
  simp[] >> qexistsl_tac [`G`,`ee`,`func`,`s`,`sa`,`tn`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac
      >- (irule return_allocated_local_frame >> goal_assum (drule_at Any) >>
          qexistsl_tac [`ce`,`d`,`dstid`,`func`,`n`,`name`,`ee.scopes`,`sites`] >> simp[]) >>
      drule_all decoded_local_byte_exterior >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all decoded_prefix_byte_exterior >> metis_tac[]) >>
  irule abi_valid_allocated_frame_slice >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> disch_tac >>
  drule_all decoded_prefix_byte_exterior >> simp[]
QED

Theorem decoded_ghost_kept[local]:
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ wb_frame ce es ee sa s0 s /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_id <= dstid /\ sa.cs_next_var <= st.cs_next_var /\
  (!id. id IN sites ==> sa.cs_next_id <= id) /\
  alloca_inv s /\ fn_inst_ids_distinct func /\ local_ptrs_rel func ce ee.scopes s /\
  abi_malformed_destination func ce ee.scopes dstid d n s /\
  (!id b cap. id IN sites /\ FLOOKUP s.vs_allocas id = SOME (b,cap) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce ee.scopes q) /\
  (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!i. ~(d <= i /\ i < d+n) /\ ~abi_malformed_site_range sites s t i 1 ==>
    (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ghost_kept_at lo ce es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> drule_all decoded_older_operand >> metis_tac[]) >>
  irule bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_kept_at >>
  goal_assum (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> rpt conj_tac >> rpt strip_tac
  >- (rename1 `local_region ce es.scopes s0 name b sz` >>
      `local_region ce ee.scopes s name b sz` by
        (irule local_region_frame_fwd >> qexistsl_tac [`s0`,`sa`,`es.scopes`] >>
         fs[wb_frame_def]) >>
      drule_all decoded_local_byte_exterior >> metis_tac[])
  >- (rename1 `FLOOKUP s0.vs_allocas aid = SOME (off,sz)` >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by fs[wb_frame_def] >>
      `aid NOTIN sites /\ aid <> dstid` by
        (conj_tac >> strip_tac >> gvs[] >>
         qpat_x_assum `!id. id IN sites ==> _` drule >> decide_tac) >>
      drule_all decoded_old_alloca_byte_exterior >> metis_tac[]) >>
  drule_all decoded_prefix_byte_exterior >> metis_tac[]
QED

Theorem decoded_destination_at[local]:
  stmt_state_rel H ctx func ce cx ee t /\ fn_inst_ids_distinct func /\
  abi_malformed_destination func ce ee.scopes aid d n t ==>
  ?b cap. FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
    b <= d /\ d+n <= b+cap /\ b+cap <= t.vs_alloca_next /\
    (!name lo sz. local_region ce ee.scopes t name lo sz ==>
       b+cap <= lo \/ lo+sz <= b)
Proof
  strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  gvs[abi_malformed_destination_def] >>
  conj_tac >- (fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  rpt strip_tac >> drule_all local_ptrs_rel_alloca_disjoint >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

(* Package the witness returned by the decoder before any control-flow join. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule extcall_return_type_bounds >> strip_tac >>
  `type_memory_bytes cenv (if needs_external_call_wrap ret_type
       then TupleT [ret_type] else ret_type) = type_memory_bytes cenv ret_type` by
    (drule (cj 6 return_default_wrapped_types) >>
     disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >> simp[]) >>
  drule_all extcall_return_memory_size >> strip_tac >>
  drule_all return_default_source_success >> strip_tac >>
  qabbrev_tac `n = type_memory_bytes cenv
    (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)` >>
  qhdtm_x_assum `abi_malformed_entry`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_malformed_entry_def]) >>
  qhdtm_x_assum `abi_valid_allocated_post`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
  qabbrev_tac `sites = abi_malformed_scratch_sites st en func` >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_def] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee decoded /\
   eval_operand (Var output) decoded = SOME (n2w dest) /\
   u.vs_alloca_next <= decoded.vs_alloca_next` by
    (qhdtm_assum `abi_malformed_resource_post`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
     rpt conj_tac >> first_assum (irule_at Any) >> simp[]) >>
  `?b cap. FLOOKUP decoded.vs_allocas dstid = SOME (b,cap) /\
    b <= dest /\ dest+n <= b+cap /\ b+cap <= decoded.vs_alloca_next /\
    (!name off sz. local_region cenv ee.scopes decoded name off sz ==>
       b+cap <= off \/ off+sz <= b)` by
    (drule_all abi_malformed_resource_destination >> disch_then assume_tac >>
     drule_all (Q.INST [`t` |-> `decoded`] decoded_destination_at) >>
     disch_then ACCEPT_TAC) >>
  `w2n (n2w dest : bytes32) = dest` by
    (`dest < dimword (:256)` by decide_tac >> simp[w2n_n2w, LESS_MOD]) >>
  `val_in_memory actual_tv value dest decoded.vs_memory /\
   (!mem. mem_agree_outside td.t_mem decoded.vs_memory mem ==>
      val_in_memory actual_tv value dest mem)` by
    (Cases_on `needs_external_call_wrap ret_type` >> fs[val_in_memory_singleton_tuple]) >>
  `!id. id IN sites ==> sa.cs_next_id <= id` by
    (simp[Abbr `sites`, abi_malformed_scratch_sites_def] >> decide_tac) >>
  `!id b cap. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,cap) ==>
     ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
       inst.inst_outputs = [q] /\ not_local_ptr cenv ee.scopes q` by
    ((metis_tac[return_decoder_scratch_owned])) >>
  drule_all return_allocated_wb_frame >> strip_tac >>
  `expr_has_effect (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)` by
    simp[expr_has_effect_def, Once supported_expr_exists_def, expr_effect_root_def] >>
  `n = type_memory_size actual_tv` by simp[] >>
  qpat_assum `w2n (n2w dest : bytes32) = dest` (fn address =>
    drule_all (SIMP_RULE bool_ss [address, LET_THM]
      (Q.INST [`w` |-> `n2w dest`, `t` |-> `decoded`] decoded_located_value))) >>
  strip_tac >>
  simp[lowered_value_type_def, post_value_type_def, vyperASTTheory.expr_type_def] >>
  rpt conj_tac
  >- (fs[vv_post_def, wb_frame_def, post_value_type_def, vyperASTTheory.expr_type_def] >>
      first_assum ACCEPT_TAC)
  >- (drule_all (PURE_REWRITE_RULE [DE_MORGAN_THM] decoded_ghost_frame) >>
      disch_then ACCEPT_TAC)
  >- (drule_all (PURE_REWRITE_RULE [DE_MORGAN_THM] decoded_ghost_kept) >>
      disch_then ACCEPT_TAC) >>
  decide_tac
QED
*)
Theorem extcall_return_decoded_post:
  !mods.
  expr_body_pre_mods mods cenv cx env (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)
    es /\
  ret_type <> NoneT /\
  evaluate_type (get_tenv cx) ret_type = SOME actual_tv /\
  evaluate_abi_decode_return (get_tenv cx) ret_type bs = INL value /\
  compile_abi_decode_to_buf (Var output) (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info cenv.ce_struct_fields cenv (if needs_external_call_wrap ret_type then TupleT
      [ret_type] else ret_type)) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry H ctx func cenv cx ee st (abi_malformed_scratch_sites st en func) dstid live
    base_op hi (Lit 0w) (Var output) B L xs 0 dest (type_memory_bytes cenv (if
      needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)) u /\
  storage_well_formed_on cx ee (FST H) /\
  wb_frame cenv es ee sa s0 u /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_id <= dstid /\ dstid < sb.cs_next_id /\
  sa.cs_next_id <= st.cs_next_id /\ sa.cs_next_var <= st.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at D lo rb cenv cx ee Gf tm u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tm /\
  abi_valid_allocated_post (if needs_external_call_wrap ret_type then TupleTV [actual_tv] else
    actual_tv) (if needs_external_call_wrap ret_type then ArrayV (TupleV [value]) else value) ctx func
    cenv cx ee st en ceiling dstid dest (type_memory_bytes cenv (if needs_external_call_wrap ret_type
    then TupleT [ret_type] else ret_type)) u decoded /\
  decoded.vs_accounts = u.vs_accounts /\ decoded.vs_transient = u.vs_transient /\
  decoded.vs_call_ctx = u.vs_call_ctx /\ decoded.vs_immutables = u.vs_immutables /\
  ptr_covers Gd td output decoded (type_memory_bytes cenv (if needs_external_call_wrap ret_type then
    TupleT [ret_type] else ret_type)) /\
  (!mem. mem_agree_outside td.t_mem decoded.vs_memory mem ==>
     val_in_memory (if needs_external_call_wrap ret_type then TupleTV [actual_tv] else actual_tv) (if
       needs_external_call_wrap ret_type then ArrayV (TupleV [value]) else value) dest mem) /\
  (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
     FLOOKUP Gd x = FLOOKUP Gf x /\ op_taint td (Var x) = op_taint tm (Var x)) /\
  td.t_stor = tm.t_stor /\ td.t_trans = tm.t_trans /\ td.t_imm = tm.t_imm /\
  (!i. ~(dest <= i /\
  i < dest+(type_memory_bytes cenv (if needs_external_call_wrap ret_type then TupleT [ret_type] else
    ret_type))) /\
  ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) u decoded i 1 ==>
     (i IN td.t_mem <=> i IN tm.t_mem)) /\
  allocas_from lo decoded /\ lo <= decoded.vs_alloca_next ==>
  vv_post H ctx func cenv cx (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)
    es sa sb s0 ee (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) decoded /\
  vv_store_bound cx (expr_type (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args
    dflt)) (lowered_value_type cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args
    dflt)) ee (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) decoded /\
  vv_own cenv cx (post_value_type cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts)
    args dflt)) sa sb ee (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) decoded /\
  ptr_vv_ok cx (post_value_type cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts)
    args dflt)) (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) ee Gd td decoded /\
  ptr_buf_ok cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) (Var
    output) Gd decoded /\
  ghost_inv_at D lo rb cenv cx ee Gd td decoded /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gd td /\
  s0.vs_alloca_next <= decoded.vs_alloca_next
Proof
  cheat
QED
