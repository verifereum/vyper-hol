(* The read-only length/data preparation after the reached Extract32 source. *)
Theory bodyExtractPrepareMods
Ancestors
  bodyFullPostsMods bodyForRangeScalarFrameMods
  bodyFullBuiltinSliceDynamicCapture bodyPtrSignedConvertSourceCompile
  extract32PrepareFrame typeBuiltinPrereqs rawCallBufferPtr bodyFullUnwrapRun
  valueEncodingProps ghostPcTransportPtr vyperStorageFootprint
  venomState exprSimMemDefs bodyPtrDefs compileEnv ptrDiscipline finite_map

Theorem extract32_prepare_allocas_room[local]:
  allocas_below_fmp (s with <|vs_vars := vs; vs_inst_idx := k|>) =
  allocas_below_fmp s
Proof
  simp[allocas_below_fmp_def]
QED

Theorem extract32_prepared_posts_mods[local]:
  expr_post_mods H ctx func cenv cx src es sa sm s0 ee (BytesV bs) (Var sv) s /\
  expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) s /\
  ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G tn s /\
  ptr_buf_ok cenv src (Var sv) G s /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  not_fresh_at sm sv /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
  tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
  tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm ==>
  expr_post_mods H ctx func cenv cx src es sa sn s0 ee (BytesV bs) (Var sv) u /\
  expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) u /\
  ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G2 tn2 u /\
  ptr_buf_ok cenv src (Var sv) G2 u /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  simp[expr_post_mods_def] >> strip_tac >>
  `eval_operand (Var sv) u = eval_operand (Var sv) s /\
   FLOOKUP G2 sv = FLOOKUP G sv /\
   op_taint tn2 (Var sv) = op_taint tn (Var sv)` by
    (first_x_assum drule >> simp[eval_operand_def]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_allocas = s.vs_allocas /\ u.vs_data_section = s.vs_data_section /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- (conj_tac
      >- (irule extract32_prepare_post_readonly >> conj_tac >- (qexists_tac `m` >> simp[]) >>
          qexistsl_tac [`s`,`sm`] >> simp[]) >>
      irule immutable_frame_mods_exterior_frame >>
      qexistsl_tac [`ee`,`s`,`sm`] >> simp[]) >>
  conj_tac >- fs[expr_store_bound_def] >>
  conj_tac >- fs[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def] >>
  conj_tac >- fs[ptr_buf_ok_def] >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >>
      qexistsl_tac [`G`,`ee`,`s`,`sm`,`tn`] >> simp[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >> simp[] >>
  rpt strip_tac >>
  `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >> simp[]
QED

Theorem extract32_prepare_mods:
  compile_bytestring_src (Var sv) sm = ((lenop,dataop),sn) /\
  not_fresh_at sm sv /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func cenv cx src es sa sm s0 ee (BytesV bs) (Var sv) s /\
    expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) s /\
    ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G tn s /\
    ptr_buf_ok cenv src (Var sv) G s /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  ?p u G2 tn2 len data.
    lenop = Var len /\ dataop = Var data /\
    not_fresh_at sn sv /\ not_fresh_at sn len /\ not_fresh_at sn data /\
    op_taint tn2 (Var len) = {} /\ op_prov G2 (Var len) = NONE /\
    u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    tn2.t_mem = tn.t_mem /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    eval_operand (Var sv) u = SOME (n2w p) /\
    eval_operand lenop u = SOME (n2w (LENGTH bs)) /\
    eval_operand dataop u = SOME (n2w (p+32)) /\
    mem_word_at p u.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (p+32) (LENGTH bs) u.vs_memory = bs /\
    p+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
    p+32+LENGTH bs <= u.vs_alloca_next /\
    (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers G2 tn2 data u n) /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func u /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,G2,tn2) /\
      expr_post_mods H ctx func cenv cx src es sa sn s0 ee (BytesV bs) (Var sv) u /\
      expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) u /\
      ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G2 tn2 u /\
      ptr_buf_ok cenv src (Var sv) G2 u /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_all extract32_source_post_alloca_bound >>
  disch_then (qx_choose_then `bp0` strip_assume_tac) >>
  `ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G tn s /\
   op_taint tn (Var sv) = {}` by fs[ptr_val_ok_def, is_word_type_def] >>
  drule_all ptr_mem_ok_dynamic_bytes_site >> strip_tac >>
  drule_all ptr_mem_ok_dynamic_bytes_clean >> strip_tac >>
  `w2n (n2w bp0 : bytes32) = bp0` by simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `lookup_var sv s = SOME (n2w bp0)` by fs[eval_operand_def] >>
  `ptr_covers G tn sv s (32+LENGTH bs)` by
    (fs[ptr_covers_def] >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `mload bp0 s = n2w (LENGTH bs)` by fs[mem_word_at_eq_mload] >>
  `!i. bp0 <= i /\ i < bp0+32+LENGTH bs ==> i NOTIN tn.t_mem` by
    (gen_tac >> strip_tac >> Cases_on `i < bp0+32`
     >- (qpat_assum `!j. w2n _ <= j /\ j < w2n _ + 32 ==> _`
           (qspec_then `i` mp_tac) >> simp[]) >>
     qpat_assum `!j. w2n _ + 32 <= j /\ _ ==> _`
       (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  `32 <= 32 + LENGTH bs /\ bp0+32 <= s.vs_alloca_next` by decide_tac >>
  qpat_assum `w2n (n2w bp0 : bytes32) = bp0`
    (fn th => drule_all (REWRITE_RULE [th]
      (Q.INST [`capacity` |-> `32+LENGTH bs`, `p` |-> `n2w bp0`]
       slice_dynamic_capture_full_run))) >>
  suspend "landing"
QED

Resume extract32_prepare_mods[landing]:
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `raw` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  drule_all extract32_prepare_site >> strip_tac >>
  drule_all compile_bytestring_src_shape_fresh >> strip_tac >>
  qabbrev_tac `u = raw with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  `alloca_history func u` by
    (qunabbrev_tac `u` >> irule emitted_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`emitted_insts sm sn`,`s`,`sm`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  `u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>` by
    (simp[Abbr `u`] >>
     qpat_assum `raw = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x. not_fresh_at sm x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
    op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `u`, lookup_var_def] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x raw = _ /\ _`
       (mp_tac o REWRITE_RULE [lookup_var_def]) >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_halted = s.vs_halted /\
   u.vs_current_bb = s.vs_current_bb /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >> simp[extract32_prepare_allocas_room]) >>
  `eval_operand (Var sv) u = SOME (n2w bp0)` by simp[eval_operand_def] >>
  `u.vs_inst_idx = LENGTH sn.cs_current_insts /\
   eval_operand lenop u = SOME (n2w (LENGTH bs)) /\
   eval_operand dataop u = SOME (n2w (bp0+32))` by
    simp[Abbr `u`, wordsTheory.word_add_n2w] >>
  `!n. n <= LENGTH bs ==> ptr_covers G2 tn2 dp u n` by
    (gen_tac >> strip_tac >>
     qpat_assum `!n. 32+n <= _ ==> ?dp. _` (qspec_then `n` mp_tac) >>
     qpat_assum `dataop = Var dp` (fn th => pure_rewrite_tac[th]) >>
     simp[Abbr `u`]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post_mods H ctx func cenv cx src es sa sn s0 ee (BytesV bs) (Var sv) u /\
     expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) u /\
     ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G2 tn2 u /\
     ptr_buf_ok cenv src (Var sv) G2 u /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 u /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     irule extract32_prepared_posts_mods >> conj_tac >- (qexists_tac `m` >> simp[]) >>
     qexistsl_tac [`G`,`s`,`sm`,`tn`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `len = lp /\ data = dp` by
    (conj_tac
     >- (qpat_x_assum `lenop = Var len` mp_tac >> simp[]) >>
     qpat_x_assum `dataop = Var data` mp_tac >> simp[]) >>
  `op_taint tn2 (Var lp) = {} /\ op_prov G2 (Var lp) = NONE` by
    (qpat_assum `lenop = Var lp` (fn th => pure_rewrite_tac[GSYM th]) >> simp[]) >>
  qexistsl_tac [`bp0`,`u`,`G2`,`tn2`,`lp`,`dp`] >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ u /\ _`
    (qspec_then `H` mp_tac) >> simp[]
QED

Finalise extract32_prepare_mods
