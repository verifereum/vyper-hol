(* Linked postcondition on the actual successful external-return decoder cut. *)
Theory bodyExtReturnDecodedPostMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrBytestringBuiltinsWindowGhost
  extcallReturnFrameBridge extcallReturnDecoderOwnership extcallReturnDefaultTypes
  abiValidAllocatedContract abiMalformedRecursiveInterface abiMalformedSiteFrame
  abiCallerLocalScratch abiDecoderReentry localPtrsProps abiBoundaryChecks supportedExprTraverse
  bodyInvSplit loweringSlice freshWrites
  fragGasOriginPtr fragGasOrigin fragGasPathFrameMem fragExec venomExecProofs venomInstProps
  venomExecSemantics venomInst
  bodyFullUnwrapSlotPost stateRelProj exprSimProps loweringPosts
  bodyPtrDefs ptrDiscipline valueEncoding exprLoweringProps compileEnv exprSimMemDefs
  loweringStateRelDefs context venomState venomMemDefs vyperState vyperABI vyperAST
  finite_map pred_set list words arithmetic

Theorem return_term_data_section[local]:
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK t ==>
  t.vs_data_section = s.vs_data_section
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> simp[Once step_inst_def] >>
  qpat_assum `inst.inst_opcode = _` (fn eq =>
    PURE_ONCE_REWRITE_TAC
      [tryfind (fn th => MATCH_MP th eq) (CONJUNCTS step_inst_base_opcode_eqs)]) >>
  simp[AllCaseEqs(), jump_to_def] >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem return_origin_data_section[local]:
  !mem explicit ctx func s marks r. gas_origin_path mem explicit ctx func s marks r ==>
  !t. r = OK t ==> t.vs_data_section = s.vs_data_section
Proof
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac >> rpt strip_tac >>
  gvs[exit_result_def] >>
  rename1 `gas_origin_edge _ _ _ _ s _ (OK mid)` >>
  `mid.vs_data_section = s.vs_data_section` suffices_by simp[] >>
  qhdtm_x_assum `gas_origin_edge` mp_tac >>
  simp[gas_origin_edge_def, exit_result_def] >> strip_tac >> gvs[jump_to_def]
  >- (drule_all step_preserves_data_section >> simp[])
  >- (drule_then SUBST1_TAC eval_phis_only_updates_vs_vars >>
      drule_all return_term_data_section >> simp[]) >>
  qpat_x_assum `OK _ = step_inst _ _ _ _` (ASSUME_TAC o SYM) >>
  fs[exit_result_def]
QED

Theorem return_decode_path_frame[local]:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gf,tm) [] (OK z,Gd,td) ==>
  z.vs_data_section = u.vs_data_section /\ LENGTH u.vs_memory <= LENGTH z.vs_memory
Proof
  strip_tac >> drule_then strip_assume_tac gas_origin_ptr_path_projections >>
  conj_tac >- (drule return_origin_data_section >> simp[]) >>
  drule_then strip_assume_tac gas_origin_path_erase >>
  fs[fragGasModeTheory.gas_marked_path_def] >>
  drule gas_path_mem_memory_length >> simp[]
QED

Theorem return_decoded_location[local]:
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
  rpt conj_tac >> rpt strip_tac >>
  disj1_tac >> qexistsl_tac [`aid`,`b`,`cap`] >> simp[] >> metis_tac[ADD_COMM]
QED

Theorem return_decoded_destination[local]:
  stmt_state_rel H ctx func ce cx ee t /\ fn_inst_ids_distinct func /\
  abi_malformed_destination func ce ee.scopes aid d n t ==>
  ?b cap. FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
    b <= d /\ d+n <= b+cap /\ b+cap <= t.vs_alloca_next /\
    (!name lo sz. local_region ce ee.scopes t name lo sz ==> b+cap <= lo \/ lo+sz <= b)
Proof
  strip_tac >> drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  gvs[abi_malformed_destination_def] >>
  conj_tac >- (fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  rpt strip_tac >> drule_all local_ptrs_rel_alloca_disjoint >> simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

(* A decoder destination and its scratch sites are exterior to the
   immutable prefix and to caller-owned regions. *)
Theorem return_decode_prefix_exterior[local]:
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  abi_malformed_destination func ce scopes dstid d n u /\ i < lo ==>
  ~(d <= i /\ i < d+n) /\ ~abi_malformed_site_range sites u t i 1
Proof
  strip_tac >> conj_tac
  >- (strip_tac >> fs[abi_malformed_destination_def, allocas_from_def] >>
      first_x_assum drule >> decide_tac) >>
  strip_tac >> fs[abi_malformed_site_range_def]
  >- (fs[allocas_from_def] >> first_x_assum drule >> decide_tac) >>
  decide_tac
QED

Theorem return_decode_local_exterior[local]:
  alloca_inv u /\ fn_inst_ids_distinct func /\ local_ptrs_rel func ce scopes u /\
  abi_malformed_destination func ce scopes dstid d n u /\
  (!id b cap. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,cap) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce scopes q) /\
  local_region ce scopes u name lo sz /\ lo <= i /\ i < lo+sz ==>
  ~(d <= i /\ i < d+n) /\ ~abi_malformed_site_range sites u t i 1
Proof
  strip_tac >> conj_tac
  >- (strip_tac >> gvs[abi_malformed_destination_def] >>
      drule_all local_ptrs_rel_alloca_disjoint >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `lo + sz <= u.vs_alloca_next` by metis_tac[abi_caller_local_end] >>
  strip_tac >> fs[abi_malformed_site_range_def]
  >- (qpat_x_assum `!id b cap. _` drule >> disch_then drule >> strip_tac >>
      gvs[] >> drule_all local_ptrs_rel_alloca_disjoint >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  decide_tac
QED

Theorem return_decode_old_exterior[local]:
  alloca_inv u /\ abi_malformed_destination func ce scopes dstid d n u /\
  FLOOKUP u.vs_allocas aid = SOME (b,cap) /\ aid <> dstid /\ aid NOTIN sites /\
  b <= i /\ i < b+cap ==>
  ~(d <= i /\ i < d+n) /\ ~abi_malformed_site_range sites u t i 1
Proof
  strip_tac >> conj_tac
  >- (strip_tac >> gvs[abi_malformed_destination_def, alloca_inv_def,
                       allocas_non_overlapping_def] >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> decide_tac) >>
  strip_tac >>
  `b+cap <= i \/ i+1 <= b` by
    (irule abi_malformed_site_range_protected >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  decide_tac
QED

Theorem return_destination_module[local]:
  abi_malformed_destination func (ce with ce_module := src) scopes aid d n u <=>
  abi_malformed_destination func ce scopes aid d n u
Proof
  simp[abi_malformed_destination_def, not_local_ptr_def]
QED

Theorem return_local_region_module[local]:
  local_region (ce with ce_module := src) scopes s name b sz <=>
  local_region ce scopes s name b sz
Proof
  simp[local_region_def]
QED

Theorem return_decode_immutable_frame[local]:
  immutable_frame_mods func ce cx ee u /\
  abi_malformed_destination func ce ee.scopes dstid d n u /\
  (!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
    ?inst. MEM inst (fn_insts func) /\ inst.inst_id = id /\ inst.inst_opcode = ALLOCA) /\
  abi_valid_allocated_frame sites d n u t /\
  t.vs_data_section = u.vs_data_section /\ LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  u.vs_alloca_next <= t.vs_alloca_next /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    FLOOKUP u.vs_allocas aid = SOME (b,sz) \/ u.vs_alloca_next <= b) /\
  (!name b sz. local_region ce ee.scopes t name b sz ==> local_region ce ee.scopes u name b sz) ==>
  immutable_frame_mods func ce cx ee t
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >> irule immutables_rel_mem_agree >>
      qexists_tac `u` >> simp[] >> rpt strip_tac >>
      irule (Q.INST [`ce` |-> `ce with ce_module := src`] return_allocated_immutable_frame) >>
      simp[return_destination_module] >>
      goal_assum (drule_at (Pat `abi_malformed_destination _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `abi_valid_allocated_frame _ _ _ _ _`)) >>
      simp[] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> irule immutable_alloca_sep_frame >>
  qexistsl_tac [`u`,`ee`] >> simp[] >> rpt strip_tac >> disj1_tac >>
  qexists_tac `id` >> fs[return_local_region_module]
QED

Theorem return_decode_ghost_frame[local]:
  ghost_inv_at_mods D lo rb ce cx ee G tm u /\
  local_ptrs_rel func ce ee.scopes u /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x w. not_fresh_at sa x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gd x = FLOOKUP G x /\ op_taint td (Var x) = op_taint tm (Var x)) /\
  (!name b len. local_region ce ee.scopes u name b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len u.vs_memory /\
     (!i. b <= i /\ i < b+len /\ i IN td.t_mem ==> i IN tm.t_mem)) /\
  stor_taint_ok_at D td t /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo u.vs_memory /\
  (!i. i < lo /\ i IN td.t_mem ==> i IN tm.t_mem) /\
  allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  ghost_inv_at_mods D lo rb ce cx ee Gd td t
Proof
  strip_tac >>
  `ghost_inv_at D 0 rb ce cx ee G tm u` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 rb ce cx ee Gd td t` by
    (irule ghost_inv_at_local_window_transport >>
     simp[allocas_from_def] >> qexistsl_tac [`G`,`ee`,`func`,`u`,`sa`,`tm`] >>
     `mem_bytes_at 0 0 t.vs_memory = mem_bytes_at 0 0 u.vs_memory` by
       simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  fs[local_ptrs_reserved_def] >> rpt strip_tac >> metis_tac[]
QED

(* The value, writeback and linked frame are all on the same decoded state. *)
Theorem extcall_decoded_post_mods:
  ann = ret_type /\ ret_type <> NoneT /\
  evaluate_type (get_tenv cx) ret_type = SOME actual_tv /\
  evaluate_abi_decode_return (get_tenv cx) ret_type bs = INL value /\
  rt = (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
  tv = (if needs_external_call_wrap ret_type then TupleTV [actual_tv] else actual_tv) /\
  n = type_memory_bytes cenv rt /\ n = type_memory_bytes cenv ret_type /\
  n = type_memory_size actual_tv /\
  compile_abi_decode_to_buf (Var output) (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry H ctx func cenv cx ee st (abi_malformed_scratch_sites st en func)
    dstid live base_op hi (Lit 0w) (Var output) B L xs 0 dest n u /\
  storage_well_formed_on cx ee (FST H) /\
  immutable_frame_mods func cenv cx ee u /\
  wb_frame cenv es ee sa s0 u /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_id <= dstid /\ dstid < sb.cs_next_id /\
  sa.cs_next_id <= st.cs_next_id /\ sa.cs_next_var <= st.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at_mods D lo rb cenv cx ee Gf tm u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tm /\
  abi_valid_allocated_post tv
    (if needs_external_call_wrap ret_type then ArrayV (TupleV [value]) else value)
    ctx func cenv cx ee st en ceiling dstid dest n u decoded /\
  decoded.vs_accounts = u.vs_accounts /\ decoded.vs_transient = u.vs_transient /\
  decoded.vs_call_ctx = u.vs_call_ctx /\ decoded.vs_immutables = u.vs_immutables /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gf,tm) [] (OK decoded,Gd,td) /\
  ptr_covers Gd td output decoded n /\
  (!mem. mem_agree_outside td.t_mem decoded.vs_memory mem ==>
     val_in_memory tv
       (if needs_external_call_wrap ret_type then ArrayV (TupleV [value]) else value) dest mem) /\
  (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
     FLOOKUP Gd x = FLOOKUP Gf x /\ op_taint td (Var x) = op_taint tm (Var x)) /\
  td.t_stor = tm.t_stor /\ td.t_trans = tm.t_trans /\ td.t_imm = tm.t_imm /\
  (!i. ~(dest <= i /\ i < dest+n) /\
       ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) u decoded i 1 ==>
       (i IN td.t_mem <=> i IN tm.t_mem)) /\
  allocas_from lo decoded /\ lo <= decoded.vs_alloca_next ==>
  vv_post_mods H ctx func cenv cx (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)
    es sa sb s0 ee (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) decoded /\
  vv_store_bound cx (expr_type (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt))
    (lowered_value_type cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt))
    ee (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) decoded /\
  vv_own cenv cx (post_value_type cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt))
    sa sb ee (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) decoded /\
  ptr_vv_ok cx (post_value_type cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt))
    (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) ee Gd td decoded /\
  ptr_buf_ok cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) (Var output) Gd decoded /\
  ghost_inv_at_mods D lo rb cenv cx ee Gd td decoded /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gd td /\
  s0.vs_alloca_next <= decoded.vs_alloca_next
Proof
  strip_tac >>
  drule return_default_source_success >> disch_then drule >> strip_tac >>
  drule_then strip_assume_tac return_decode_path_frame >>
  qhdtm_assum `abi_malformed_entry`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  qhdtm_assum `abi_valid_allocated_post`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
  qabbrev_tac `sites = abi_malformed_scratch_sites st en func` >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `stmt_state_rel H ctx func cenv cx ee decoded /\
   eval_operand (Var output) decoded = SOME (n2w dest) /\
   u.vs_alloca_next <= decoded.vs_alloca_next` by
    (qhdtm_assum `abi_malformed_resource_post`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
     rpt conj_tac >> first_assum (irule_at Any) >> fs[]) >>
  `?b cap. FLOOKUP decoded.vs_allocas dstid = SOME (b,cap) /\
    b <= dest /\ dest+n <= b+cap /\ b+cap <= decoded.vs_alloca_next /\
    (!name off sz. local_region cenv ee.scopes decoded name off sz ==>
       b+cap <= off \/ off+sz <= b)` by
    (drule_all_then assume_tac abi_malformed_resource_destination >>
     drule_at_then (Pat `abi_malformed_destination _ _ _ _ _ _ decoded`)
       (drule_all_then ACCEPT_TAC) return_decoded_destination) >>
  `w2n (n2w dest : bytes32) = dest` by
    (`dest < dimword (:256)` by decide_tac >> simp[w2n_n2w, LESS_MOD]) >>
  `val_in_memory actual_tv value dest decoded.vs_memory /\
   (!mem. mem_agree_outside td.t_mem decoded.vs_memory mem ==>
      val_in_memory actual_tv value dest mem)` by
    (Cases_on `needs_external_call_wrap ret_type` >> gvs[val_in_memory_singleton_tuple]) >>
  `!id. id IN sites ==> sa.cs_next_id <= id` by
    (simp[Abbr `sites`, abi_malformed_scratch_sites_def] >> decide_tac) >>
  `!id b cap. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,cap) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\ not_local_ptr cenv ee.scopes q` by
    (rpt strip_tac >> irule return_decoder_scratch_owned >>
     simp[] >> goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
     fs[Abbr `sites`]) >>
  `!id b cap. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,cap) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr cenv ee.scopes q` by metis_tac[] >>
  drule_all_then assume_tac return_allocated_wb_frame >>
  `expr_has_effect (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)` by
    simp[expr_has_effect_def, Once supported_expr_exists_def, expr_effect_root_def] >>
  qpat_assum `w2n (n2w dest : bytes32) = dest` (fn address =>
    drule_at (Pat `eval_operand (Var _) decoded = _`)
      (SIMP_RULE bool_ss [address] (Q.INST [`w` |-> `n2w dest`] return_decoded_location))) >>
  disch_then (drule_all_then strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> abi_decoder_operand_live st.cs_next_var (Var x)` by
    (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x u = SOME w ==> lookup_var x decoded = SOME w` by
    (qhdtm_assum `abi_malformed_resource_post`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
     rpt strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var x)` by metis_tac[] >>
     qpat_assum `!op w. abi_decoder_operand_live _ op /\ _ ==> _`
       (qspecl_then [`Var x`,`w`] (mp_tac o PURE_REWRITE_RULE [eval_operand_def])) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `!name b sz. local_region cenv ee.scopes decoded name b sz ==>
     local_region cenv ee.scopes u name b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists `func` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`sa`,`ee.scopes`,`decoded`] >> simp[]) >>
  `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
    ?inst. MEM inst (fn_insts func) /\ inst.inst_id = id /\ inst.inst_opcode = ALLOCA` by
    (rpt strip_tac >> qpat_assum `!id b cap. _ ==> ?inst q. _ /\ _ /\ inst.inst_opcode = ALLOCA /\ _`
       (drule_all_then strip_assume_tac) >> qexists `inst` >> simp[]) >>
  `immutable_frame_mods func cenv cx ee decoded` by
    (irule return_decode_immutable_frame >>
     goal_assum (drule_at (Pat `abi_malformed_destination _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `abi_valid_allocated_frame _ _ _ _ _`)) >> simp[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gd x = FLOOKUP Gf x /\ op_taint td (Var x) = op_taint tm (Var x)` by
    (rpt strip_tac >> first_assum (qspec_then `x` mp_tac) >> simp[]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `!i. i < lo ==> ~(dest <= i /\ i < dest+n) /\ ~abi_malformed_site_range sites u decoded i 1` by
    (gen_tac >> disch_tac >> irule return_decode_prefix_exterior >>
     conj_tac >- (qexists `lo` >> simp[]) >>
     qexistsl_tac [`cenv`,`dstid`,`func`,`ee.scopes`] >> simp[]) >>
  `!i. i < lo /\ i IN td.t_mem ==> i IN tm.t_mem` by
    (rpt strip_tac >> qpat_assum `!i. _ /\ _ ==> (i IN td.t_mem <=> _)`
       (qspec_then `i` mp_tac) >> fs[]) >>
  `!name b sz i. local_region cenv ee.scopes u name b sz /\ b <= i /\ i < b+sz ==>
       ~(dest <= i /\ i < dest+n) /\ ~abi_malformed_site_range sites u decoded i 1` by
    (map_every qx_gen_tac [`lname`,`locoff`,`locsz`,`i`] >> strip_tac >>
     irule return_decode_local_exterior >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cenv`,`dstid`,`func`,`locoff`,`lname`,`ee.scopes`,`locsz`] >> simp[]) >>
  `!name q k. local_region cenv ee.scopes u name q k ==>
    mem_bytes_at q k decoded.vs_memory = mem_bytes_at q k u.vs_memory /\
    (!i. q <= i /\ i < q+k /\ i IN td.t_mem ==> i IN tm.t_mem)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (irule abi_valid_allocated_frame_slice >>
         goal_assum (drule_at (Pat `abi_valid_allocated_frame _ _ _ _ _`)) >>
         rpt strip_tac >> metis_tac[]) >>
     rpt strip_tac >> metis_tac[]) >>
  `mem_bytes_at 0 lo decoded.vs_memory = mem_bytes_at 0 lo u.vs_memory` by
    (irule abi_valid_allocated_frame_slice >>
     goal_assum (drule_at (Pat `abi_valid_allocated_frame _ _ _ _ _`)) >>
     simp[] >> rpt strip_tac >> metis_tac[]) >>
  `stor_taint_ok_at D td decoded` by fs[ghost_inv_at_mods_def, stor_taint_ok_at_def] >>
  `ghost_inv_at_mods D lo rb cenv cx ee Gd td decoded` by
    (drule_then irule return_decode_ghost_frame >>
     simp[] >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE (qexists `sa` >> simp[]) ORELSE
      (qexists `func` >> first_assum ACCEPT_TAC))) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gd td` by
    (irule unwrap_slot_copy_ghost_kept_at >>
     goal_assum (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> rpt conj_tac >> rpt strip_tac
     >- (rename1 `local_region _ _ s0 lname locoff locsz` >>
         `local_region cenv ee.scopes u lname locoff locsz` by
           (irule local_region_frame_fwd >> qexistsl_tac [`s0`,`sa`,`es.scopes`] >>
            fs[wb_frame_def]) >>
         qpat_assum `!name q k. local_region _ _ u name q k ==> _`
           (drule_then strip_assume_tac) >> first_assum irule >> simp[]) >>
     rename1 `FLOOKUP _ aid = SOME (off,sz)` >>
     `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by fs[wb_frame_def] >>
     `aid NOTIN sites /\ aid <> dstid` by
       (conj_tac >> strip_tac >> gvs[] >>
        qpat_assum `!id. id IN sites ==> _` drule >> decide_tac) >>
     `~(dest <= i /\ i < dest+n) /\ ~abi_malformed_site_range sites u decoded i 1` by
       (irule return_decode_old_exterior >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`aid`,`off`,`sz`,`cenv`,`dstid`,`func`,`ee.scopes`] >> simp[]) >>
     qpat_assum `!i. _ /\ _ ==> (i IN td.t_mem <=> _)` (qspec_then `i` mp_tac) >> fs[]) >>
  `s0.vs_alloca_next <= decoded.vs_alloca_next` by decide_tac >>
  gs[vv_post_mods_def, post_value_type_def, exprLoweringTheory.lowered_value_type_def,
     vyperASTTheory.expr_type_def, vv_holds_mods_def, vv_place_ptr_mods_def, mk_ptr_def,
     wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
