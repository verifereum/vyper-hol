(* A forced bytes/string read followed by the direct live-extent store. *)
Theory bodyAnnBytesInstalledMods
Ancestors
  bodyAnnCopyInstallMods bodyLocalBytesCopyPathMods bodyMemoryDefs
  bodyBinopFragMemory stmtReasonLitFragMemory typedCopyOriginPtrBase
  stmtLowering bytesCopyCode stmtSimDeclSource valueTypingMemoryProps
  exprLoweringProps compileEnv venomInst venomState rich_list context
  typedMemoryCopy bodyFullShadowBodyInv vyperStorageFootprint stmtSimDefs
  valueCopyBytes bodyPtrDefs exprSimMemDefs words loweringPosts ptrDiscipline

Theorem ann_bytes_store_history[local]:
  compile_store_bytestring src dst b = ((),sf) /\ fn_has_code b sf func /\
  alloca_history func s /\ s.vs_current_bb = b.cs_current_bb /\
  t.vs_current_bb = sf.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts /\
  t.vs_inst_idx = LENGTH sf.cs_current_insts /\ t.vs_allocas = s.vs_allocas ==>
  ~block_is_terminated sf /\ alloca_history func t /\ b.cs_next_var <= sf.cs_next_var
Proof
  strip_tac >> drule bytesCopyCodeTheory.compile_store_bytestring_code >> strip_tac >>
  `sf.cs_current_bb = b.cs_current_bb` by fs[same_blocks_def] >>
  conj_tac
  >- (`LAST sf.cs_current_insts = LAST (emitted_insts b sf)` by
        simp[LAST_APPEND_NOT_NIL,bytes_copy_insts_def] >>
      `sf.cs_current_insts <> []` by simp[bytes_copy_insts_def] >>
      rewrite_tac[block_is_terminated_def] >> Cases_on `sf.cs_current_insts` >>
      simp[bytes_copy_insts_def,mk_inst_def,is_terminator_def]) >>
  reverse conj_tac >- simp[] >>
  drule_all fn_has_code_code >> strip_tac >>
  fs[IS_PREFIX_APPEND] >>
  `alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts b sf))` by
    (irule alloca_history_no_alloca_slice >> simp[bytes_copy_insts_def,mk_inst_def]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts b sf) = t.vs_inst_idx` by simp[] >>
  fs[venom_state_component_equality]
QED

Theorem ann_copy_bytes_installed_mods:
  compile_assign_value ce (Var p) LocMemory (Var xs) F loc typ sty sz' b = ((),sf) /\
  is_bytestring_type typ /\ loc <> SOME LocMemory /\ is_bytestring_type sty /\
  fn_has_code b sf func /\ fn_inst_ids_distinct func /\
  evaluate_type (get_tenv cx) sty = SOME rt /\ evaluate_type (get_tenv cx) typ = SOME dtv /\
  value_has_type rt v /\ value_has_type dtv v /\ type_memory_size dtv <= sz /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/ (?str. v = StringV str /\ len = LENGTH str)) /\
  val_store_size rt v = 32 + 32 * word_size len /\ val_store_size rt v <= sz /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt v (w2n sw) m) /\
  not_fresh_at b xs /\ not_fresh_at b p /\
  lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
  ptr_covers G tn xs s (val_store_size rt v) /\ ptr_covers G tn p s (val_store_size rt v) /\
  w2n sw + val_store_size rt v <= s.vs_alloca_next /\
  w2n dw + sz <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  return_buf_frame d ce b s /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
  ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
            ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
  FLOOKUP old.ce_vars id = NONE /\
  not_local_ptr ce mid.scopes p /\ local_ptrs_reserved ce b /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n dw,sz) /\ ptr_covers G tn p s sz /\
  (!q cap. ce.ce_return_buf = SOME (PtrVar (Var q) cap) ==> not_fresh_at b q) /\
  (!q cap. ce.ce_return_pc = SOME (PtrVar (Var q) cap) ==> not_fresh_at b q) /\
  (!q. not_fresh_at sa q ==> not_fresh_at b q) /\
  alloca_frame old es sa s0 ce mid s /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!aid off cap i. FLOOKUP s0.vs_allocas aid = SOME (off,cap) /\ aid < sa.cs_next_id /\
     (!name a k. local_region old es.scopes s0 name a k ==> off+cap <= a \/ a+k <= off) /\
     off <= i /\ i < off+cap /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  (!q z. not_fresh_at sa q /\ lookup_var q s0 = SOME z ==> lookup_var q s = SOME z) /\
  (!q. not_fresh_at sa q ==>
       FLOOKUP G q = FLOOKUP G0 q /\ op_taint tn (Var q) = op_taint tn0 (Var q)) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  return_buf_sep d old es s0 /\ local_ptrs_reserved old sa /\
  (?J:(bool # 256 word # type_value) list # num list. stmt_state_rel J ctx func old cx es s0) /\
  MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  new_variable id dtv v mid = (INL (),out) /\ mid.gas_obs = [] /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func ce cx mid s /\ storage_well_formed_on cx mid (FST H) /\
     immutable_frame_mods func ce cx mid s /\ ghost_inv_at_mods (DF H) lo d ce cx mid G tn s) ==>
  ?t Gf tf.
    (!tail. new_variable id dtv v (mid with gas_obs := tail) =
       (INL (),out with gas_obs := tail)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H. valid_horizon cx st0 H out.storage_trace ==>
      (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw+cap) t) ==>
      stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
      cenv_top_ext old ce (out with gas_obs := []).scopes /\
      stmt_state_rel H ctx func ce cx (out with gas_obs := []) t /\
      immutable_frame_mods func ce cx (out with gas_obs := []) t /\
      storage_well_formed_on cx (out with gas_obs := []) (FST H) /\
      return_buf_frame d ce sf t /\ alloca_history func t /\
      return_buf_sep d ce (out with gas_obs := []) t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx (out with gas_obs := []) Gf tf t /\
      (!q z. not_fresh_at sa q /\ lookup_var q s0 = SOME z ==> lookup_var q t = SOME z) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
      (!q. not_fresh_at sa q ==>
        FLOOKUP Gf q = FLOOKUP G0 q /\ op_taint tf (Var q) = op_taint tn0 (Var q)) /\
      alloca_frame old es sa s0 ce (out with gas_obs := []) t /\
      (!aid off cap i. FLOOKUP s0.vs_allocas aid = SOME (off,cap) /\ aid < sa.cs_next_id /\
        (!name a k. local_region old es.scopes s0 name a k ==> off+cap <= a \/ a+k <= off) /\
        off <= i /\ i < off+cap /\ i IN tf.t_mem ==> i IN tn0.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type typ` by simp[is_bytestring_word_type] >>
  `compile_store_memory ce (Var xs) (Var p) typ sty b = ((),sf)` by
    fs[compile_assign_value_def] >>
  `compile_store_bytestring (Var xs) (Var p) b = ((),sf)` by
    (qpat_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     pure_rewrite_tac[compile_store_memory_def] >> simp[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by suspend "resources" >>
  `w2n dw + val_store_size rt v <= s.vs_alloca_next /\ val_store_size rt v < dimword (:256)` by
    decide_tac >>
  drule_all (Q.INST [`n` |-> `val_store_size rt v`, `len` |-> `len`,
                    `lo` |-> `lo`, `ctx` |-> `ctx`] local_bytes_copy_path_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac)) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    fs[typed_copy_state_frame_def,venom_state_component_equality] >>
  drule_all ann_bytes_store_history >> strip_tac >>
  `return_buf_frame d ce sf t` by suspend "return_buf" >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >- (drule new_variable_success_gas_obs >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "install"
QED

Resume ann_copy_bytes_installed_mods[resources]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >>
  simp[ghost_inv_at_mods_def]
QED

Resume ann_copy_bytes_installed_mods[return_buf]:
  irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`b`] >>
  simp[] >> rpt strip_tac >> first_assum drule >> simp[]
QED

Resume ann_copy_bytes_installed_mods[install]:
  `out.storage_trace = mid.storage_trace /\ out with gas_obs := [] = out` by
    (`stmt_res_ok lctx (FST (new_variable id dtv v mid))` by simp[stmt_res_ok_def] >>
     drule_then strip_assume_tac new_variable_admissible_success >>
     gvs[vyperStateTheory.evaluation_state_component_equality]) >>
  qpat_assum `out with gas_obs := [] = out` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `out.storage_trace = mid.storage_trace` (fn th => pure_rewrite_tac[th]) >>
  gen_tac >> ntac 2 disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `val_wf dtv v` by simp[value_has_type_memory_wf] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw+cap) s` by
    (qpat_assum `!bw cap. _ ==> allocas_from _ t` mp_tac >>
     pure_rewrite_tac[allocas_from_def] >>
     qpat_assum `t.vs_allocas = s.vs_allocas` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  `!q. not_fresh_at b q ==> FLOOKUP Gf q = FLOOKUP G q /\
       op_taint tf (Var q) = op_taint tn (Var q)` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at b x ==> lookup_var x t = _ /\ _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  irule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``] ann_copy_install_post_mods) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `typed_copy_state_frame b _ _ s t` (irule_at Any) >>
  qpat_assum `new_variable id dtv v mid = _` (irule_at Any) >>
  qpat_assum `ghost_inv_at_mods (DF H) lo d ce cx mid G tn s` (irule_at Any) >>
  qpat_assum `FLOOKUP ce.ce_vars id = SOME _` (irule_at Any) >>
  qpat_assum `MEM (mk_inst _ ALLOCA _ _) (fn_insts func)` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms,mk_inst_def] >> simp[]
QED

Finalise ann_copy_bytes_installed_mods
