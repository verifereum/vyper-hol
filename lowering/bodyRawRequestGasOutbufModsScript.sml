(* Physical preparation for both raw-call input routes. *)
Theory bodyRawRequestGasOutbufMods
Ancestors
  bodyExtRequestOptionalGasMods bodyFullAllocaFresh bodyECAddAllocFrameMods
  bodyFullRawCallOutbufAdd rawCallOutbufCompile bodyFullPostsMods
  bodyForRangeScalarFrameMods bodyPtrSignedConvertSourceFrame bodyFullUnwrapRun
  exprSimCopy fragExec venomInst loweringHalt exprSimAccounts
  exprOperandVar wordArgsPtr arithmetic compileEnv typedMemoryCopy
  gasShadowState gasShadowUnit gasExplicitSites vyperValue vyperState
  bodyFullHashKeccakFixed[qualified,ignore_grammar] stateRelProj
  immutableRegionLoadPtr exprSimWordArgs bodyFullGhostFrame bodyPtrDefs
  bodyMemoryDefs fragGasOriginPtr fragExecMem emitHelperProps
  exprLoweringProps loweringStateRelDefs vyperStorageFootprint
  bodyFullShadowBodyInv ptrDiscipline venomExecSemantics venomState finite_map words list

val raw_entry = ``\(H : (bool # bytes32 # type_value) list # num list).
  stmt_state_rel H ctx func ce cx ee s /\
  immutable_frame_mods func ce cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at_mods (DF H) lo d ce cx ee G tn s``;

val old_regs = ``\sa s (G : string |-> num # num) tn t J tf.
  !x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP J x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)``;

val out_separated = ``\b n t.
  (!name base sz. local_region ce ee.scopes t name base sz ==>
                 regions_disjoint b n base sz) /\
  (ce.ce_is_ctor ==> !src tops name tv v off.
    ALOOKUP ce.ce_modules src = SOME tops /\
    FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
              | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint b n off (type_memory_size tv))``;

Theorem raw_alloc_cut_mods[local]:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\ n < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> (^raw_entry) H) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q b t J tf.
    buf.buf_operand = Var q /\ not_fresh_at sb q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,J,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee J tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    eval_operand (Var q) t = SOME (n2w b) /\ FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,n) /\
    op_prov J (Var q) = SOME (b,n) /\ op_taint tf (Var q) = {} /\
    b+n < dimword (:256) /\ b+n <= t.vs_alloca_next /\ (^out_separated) b n t /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP t.vs_allocas aid = SOME entry) /\
    t.vs_memory = s.vs_memory /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_labels = s.vs_labels /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. i IN tf.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+n)) /\
    (^old_regs) sa s G tn t J tf
Proof
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_all (INST_TYPE [``:β`` |-> ``:256``]
    alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `lookup_var q t = SOME w` >>
  `~t.vs_halted /\ t.vs_memory = s.vs_memory /\ t.vs_gas_readings = s.vs_gas_readings /\
   t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_labels = s.vs_labels` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s`
       mp_tac >> simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    immutable_frame_mods func ce cx ee t /\ ghost_inv_at_mods (DF H) lo d ce cx ee G' tn' t /\
    (ce.ce_is_ctor ==> !src tops name tv v off.
       ALOOKUP ce.ce_modules src = SOME tops /\
       FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
                | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
       regions_disjoint (w2n w) n off (type_memory_size tv))` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     drule_all_then strip_assume_tac ecadd_alloc_frame_mods >> simp[] >>
     disch_tac >> rpt gen_tac >> strip_tac >>
     qpat_assum `!src tops. ALOOKUP _ src = SOME tops /\ _ ==> _`
       (drule_all_then strip_assume_tac) >> first_assum drule_all >> simp[]) >>
  `op_taint tn' (Var q) = {}` by fs[ptr_covers_def] >>
  qexistsl_tac [`q`,`w2n w`,`t`,`G'`,`tn'`] >>
  qpat_x_assum `t = r with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `G' = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `tn' = step_taint _ _ _ _` kall_tac >>
  simp[eval_operand_def,op_prov_def] >>
  conj_tac
  >- (qx_gen_tac `hz` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> immutable_frame_mods _ _ _ _ t /\ _`
        (drule_then strip_assume_tac) >> simp[] >>
      qpat_assum `!h. stmt_state_rel h _ _ _ _ _ _ ==> stmt_state_rel h _ _ _ _ _ _`
        (fn rule => simp[rule])) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> immutable_frame_mods _ _ _ _ t /\ _`
    (drule_then strip_assume_tac) >> conj_tac >> FIRST_ASSUM ACCEPT_TAC
QED

Theorem raw_add_cut_mods[local]:
  emit_op ADD [ov;Lit 32w] sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> (^raw_entry) H) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ eval_operand ov s = SOME w /\
  op_prov G ov = SOME (b,n) /\ op_taint tn ov = {} /\
  (!x. ov = Var x ==> not_fresh_at sa x) ==>
  ?t J tf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,J,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee J tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    eval_operand ov t = SOME w /\ eval_operand op t = SOME (w+32w) /\
    op_prov J ov = SOME (b,n) /\ op_prov J op = SOME (b,n) /\
    op_taint tf ov = {} /\ op_taint tf op = {} /\
    (!x. ov = Var x \/ op = Var x ==> not_fresh_at sb x) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_labels = s.vs_labels /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (^old_regs) sa s G tn t J tf
Proof
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all_then strip_assume_tac emit_add_runtime_frame >>
  qpat_x_assum `copy_runtime_frame _ _ _ _` (strip_assume_tac o REWRITE_RULE [copy_runtime_frame_def]) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ _ = OK u` >>
  qabbrev_tac `t = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `t = u with vs_inst_idx := LENGTH sb.cs_current_insts` by simp[Abbr `t`] >>
  drule_all raw_call_outbuf_add_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ _ (OK t,_,_)` >>
  `alloca_inv s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_history func t` by
    (simp_tac std_ss [Abbr `t`] >> irule emitted_alloca_history >>
     conj_tac >- simp[] >> qexistsl_tac [`emitted_insts sa sb`,`s`,`sa`] >>
     fs[same_blocks_def,mk_inst_def,is_terminator_def]) >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s`
       (fn th => pure_once_rewrite_tac [GSYM th]) >> simp[NoAsms]) >>
  pop_assum (mk_asm "readonly") >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = s.vs_memory /\ t.vs_gas_readings = s.vs_gas_readings /\
   t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_labels = s.vs_labels /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
   t.vs_data_section = s.vs_data_section` by
    (asm "readonly" (fn th => pure_once_rewrite_tac [th]) >> simp[NoAsms]) >>
  qpat_x_assum `t = u with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s` kall_tac >>
  qexistsl_tac [`t`,`G1`,`tn1`] >>
  rpt (FIRST_ASSUM ACCEPT_TAC ORELSE conj_tac) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule stmt_state_rel_readonly_vars_pc >> qexistsl_tac [`s`,`sa`] >>
      simp[] >> asm "readonly" mp_tac >> simp[]) >>
  conj_tac
  >- (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`ee`,`s`,`sa`] >>
      simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`G`,`ee`,`s`,`sa`,`tn`] >> simp[]
QED

Theorem raw_append_silent[local]:
  gas_origin_ptr_path P x marks (OK u,J,tf) /\
  gas_origin_ptr_path P (u,J,tf) [] (OK v,J2,tg) ==>
  gas_origin_ptr_path P x marks (OK v,J2,tg)
Proof
  strip_tac >>
  qpat_assum `gas_origin_ptr_path _ _ marks _`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`u`,`J`,`tf`,`[]`] mp_tac) >> simp[]
QED

Theorem raw_outbuf_cut_mods[local]:
  compile_raw_call_outbuf M sa = ((ov,op),sb) /\
  n = (if M = 0 then 0 else ((M+31) DIV 32)*32+32) /\ n < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> (^raw_entry) H) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?b t J tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,J,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee J tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    eval_operand ov t = SOME (n2w b) /\
    eval_operand op t = SOME (n2w (if M = 0 then b else b+32)) /\
    (M = 0 ==> ov = op) /\ (!x. ov = Var x \/ op = Var x ==> not_fresh_at sb x) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,n) /\
    op_prov J ov = SOME (b,n) /\ op_prov J op = SOME (b,n) /\
    op_taint tf ov = {} /\ op_taint tf op = {} /\
    b+n < dimword (:256) /\ b+n <= t.vs_alloca_next /\ (^out_separated) b n t /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    t.vs_memory = s.vs_memory /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_labels = s.vs_labels /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. i IN tf.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+n)) /\
    (^old_regs) sa s G tn t J tf
Proof
  BETA_TAC >> strip_tac >> drule_then strip_assume_tac calldata_outbuf_compile >>
  Cases_on `M = 0`
  >- (gvs[] >> `0 < dimword (:256)` by simp[] >>
      drule_all (BETA_RULE raw_alloc_cut_mods) >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      qexistsl_tac [`b`,`t`,`J`,`tf`] >> simp[] >> conj_tac
      >- (gen_tac >> disch_tac >>
          qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
            (drule_then strip_assume_tac) >> simp[]) >>
      conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  fs[] >> qpat_x_assum `n = _` SUBST_ALL_TAC >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (conj_tac >- (drule compile_alloc_buffer_extends >> simp[]) >>
     drule emit_op_extends_next_var >> simp[]) >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule_then strip_assume_tac compile_alloc_buffer_emission >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  drule_all (BETA_RULE raw_alloc_cut_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  suspend "add"
QED

Resume raw_outbuf_cut_mods[add]:
  gvs[] >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[] >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[] >>
  `!x. Var q = Var x ==> not_fresh_at sm x` by simp[] >>
  drule_all (BETA_RULE raw_add_cut_mods) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t',J',tf')` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _` (qspec_then `D` assume_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (t,J,tf) [] _`
       (qspecl_then [`D`,`explicit`] assume_tac) >>
     drule_all raw_append_silent >> simp[]) >>
  `allocas_from lo t'` by
    (qpat_assum `t'.vs_allocas = t.vs_allocas` (fn th => simp[allocas_from_def,th]) >>
     fs[allocas_from_def] >> FIRST_ASSUM ACCEPT_TAC) >>
  `!x. not_fresh_at sm x ==> lookup_var x t' = lookup_var x t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t' = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!name base sz. local_region ce ee.scopes t' name base sz <=>
                  local_region ce ee.scopes t name base sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `sm` >> simp[]) >>
  qexistsl_tac [`b`,`t'`,`J'`,`tf'`] >> simp[GSYM word_add_n2w] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t' /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (qpat_assum `!x. Var q = Var x \/ op = Var x ==> _` mp_tac >> simp[NoAsms]) >>
  conj_tac >> FIRST_ASSUM ACCEPT_TAC
QED

Finalise raw_outbuf_cut_mods

Theorem raw_gas_operand_ready[local]:
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
  (!x. go = SOME (Var x) ==> not_fresh_at s5 x) ==>
  !x. gas = Var x ==> not_fresh_at s6 x
Proof
  Cases_on `go` >> simp[]
  >- (strip_tac >> drule typed_copy_emit_op_fresh >> simp[]) >>
  strip_tac >> gvs[]
QED

Theorem raw_gas_read_frame[local]:
  eval_operand gas s = SOME w /\ op_taint tn gas = {} /\
  t.vs_labels = s.vs_labels /\ (!x. gas = Var x ==> not_fresh_at sa x) /\
  (^old_regs) sa s G tn t J tf ==>
  eval_operand gas t = SOME w /\ op_taint tf gas = {}
Proof
  BETA_TAC >> strip_tac >> Cases_on `gas` >> gvs[eval_operand_def,op_taint_def]
QED

Theorem raw_request_gas_outbuf_mods:
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
  (case go of SOME g => (g,h5) | NONE => emit_op GAS [] h5) = (gas,h6) /\
  gas_shadow_state s5 h5 /\ gas_shadow_context ctx shctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shfunc /\
  MEM func ctx.ctx_functions /\ MEM shfunc shctx.ctx_functions /\
  fn_has_code s5 s6 func /\ fn_has_code h5 h6 shfunc /\ ci_mono s5 s6 /\
  compile_raw_call_outbuf M s6 = ((ov,op),sout) /\ fn_has_code s6 sout func /\
  n = (if M = 0 then 0 else ((M+31) DIV 32)*32+32) /\ n < dimword (:256) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce s5 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> (^raw_entry) H) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = s5.cs_current_bb /\
  s.vs_inst_idx = LENGTH s5.cs_current_insts /\
  (case source_gas of NONE => go = NONE
   | SOME gv => ?opr w. go = SOME opr /\ eval_operand opr s = SOME w /\
       dest_NumV gv = SOME (w2n w) /\ op_taint tn opr = {}) /\
  (!x. go = SOME (Var x) ==> not_fresh_at s5 x) /\
  sa.cs_next_var <= s5.cs_next_var /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  return_buf_frame d ce s5 s /\ wb_frame ce es ee sa s0 s /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
     off + sz <= s.vs_alloca_next) /\
  (!name base sz. local_region ce es.scopes s0 name base sz ==> base + sz <= s.vs_alloca_next) ==>
  ?gw t J tf b.
    (IS_NONE go ==> gas_prefix 1 s.vs_gas_readings = [gw]) /\
    t.vs_gas_readings = DROP (if IS_NONE go then 1 else 0) s.vs_gas_readings /\
    eval_operand gas t = SOME gw /\ op_taint tf gas = {} /\
    (!k. OPTION_BIND source_gas dest_NumV = SOME k ==> k = w2n gw) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (s,G,tn) (if IS_NONE go then [F] else []) (OK t,J,tf) /\
      stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee J tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sout.cs_current_bb /\
    t.vs_inst_idx = LENGTH sout.cs_current_insts /\ alloca_history func t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    eval_operand ov t = SOME (n2w b) /\
    eval_operand op t = SOME (n2w (if M = 0 then b else b+32)) /\
    (M = 0 ==> ov = op) /\ (!x. ov = Var x \/ op = Var x ==> not_fresh_at sout x) /\
    FLOOKUP t.vs_allocas s6.cs_next_id = SOME (b,n) /\
    op_prov J ov = SOME (b,n) /\ op_prov J op = SOME (b,n) /\
    op_taint tf ov = {} /\ op_taint tf op = {} /\
    b+n < dimword (:256) /\ b+n <= t.vs_alloca_next /\ (^out_separated) b n t /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    t.vs_memory = s.vs_memory /\ t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. i IN tf.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+n)) /\
    (^old_regs) s5 s G tn t J tf /\
    return_buf_frame d ce s5 t /\ wb_frame ce es ee sa s0 t /\
    ghost_kept_at lo ce es sa G0 tn0 s0 J tf
Proof
  BETA_TAC >> strip_tac >>
  `s5.cs_next_var <= s6.cs_next_var` by fs[ci_mono_def] >>
  `!x. not_fresh_at s5 x ==> not_fresh_at s6 x` by metis_tac[compiler_ci_mono_not_fresh] >>
  `local_ptrs_reserved ce s6` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s6 x` by
    metis_tac[] >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s6 x` by
    metis_tac[] >>
  `!x. gas = Var x ==> not_fresh_at s6 x` by
    (qpat_assum `_ = (gas,s6)` (mp_then Any mp_tac raw_gas_operand_ready) >>
     simp[]) >>
  drule_all ext_request_optional_gas_mods >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "gas_exit"
QED

Resume raw_request_gas_outbuf_mods[gas_exit]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee zg /\ immutable_frame_mods func ce cx ee zg /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gg tng zg` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  drule_all (BETA_RULE raw_outbuf_cut_mods) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`] strip_assume_tac) >>
  `!x. not_fresh_at s5 x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP J x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at s6 x` by simp[] >>
     qpat_assum `!x. not_fresh_at s5 x ==> lookup_var x _ = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at s6 x ==> lookup_var x _ = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `eval_operand gas t = SOME gw /\ op_taint tf gas = {}` by
    (drule_all (BETA_RULE raw_gas_read_frame) >> simp[]) >>
  `s.vs_alloca_next <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next` by
    (conj_tac >> decide_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (rewrite_tac[GSYM storage_trace_domain_def] >> FIRST_ASSUM ACCEPT_TAC) >>
  `lo <= s.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `ghost_inv_at_mods _ lo _ _ _ _ G tn s`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `lo <= t.vs_alloca_next` by decide_tac >>
  `REPLICATE n' F = if IS_NONE go then [F] else []` by (Cases_on `IS_NONE go` >> simp[] >> EVAL_TAC) >>
  `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e` by
    (qpat_assum `zg.vs_allocas = s.vs_allocas` (fn eq =>
       qpat_assum `!aid e. FLOOKUP zg.vs_allocas aid = SOME e ==> _`
         (ACCEPT_TAC o REWRITE_RULE[eq]))) >>
  qexistsl_tac [`gw`,`t`,`J`,`tf`,`b`] >>
  rpt (FIRST_ASSUM ACCEPT_TAC ORELSE conj_tac) >>
  TRY (asm_rewrite_tac [] >> NO_TAC)
  >- (gen_tac >> disch_tac >>
   qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
     (drule_then strip_assume_tac) >>
   qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
     (drule_then strip_assume_tac) >>
   qpat_assum `!D. gas_origin_ptr_path _ (zg,Gg,tng) [] _`
     (qspec_then `DF H` assume_tac) >>
   conj_tac
   >- (drule_all raw_append_silent >> asm_rewrite_tac[]) >>
   rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)
  >- (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`s5`] >>
      asm_rewrite_tac[] >> simp[NoAsms] >> rpt strip_tac >>
      qpat_assum `!x. not_fresh_at s5 x ==> lookup_var x t = _ /\ _`
        (drule_then strip_assume_tac) >> asm_rewrite_tac[])
  >- (irule wb_frame_readonly_tail >> qexistsl_tac [`s6`,`zg`] >>
      `sa.cs_next_var <= s6.cs_next_var` by decide_tac >>
      asm_rewrite_tac[] >> simp[NoAsms] >> rpt strip_tac >>
      qpat_assum `!x. not_fresh_at s6 x ==> lookup_var x t = _ /\ _`
        (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  irule alloc_buffer_ghost_kept_at >> qexistsl_tac [`G`,`b+n`,`s`,`tn`] >>
  asm_rewrite_tac[] >> simp[NoAsms] >> gen_tac >> disch_tac >>
  `not_fresh_at s5 x` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `sa` >> asm_rewrite_tac[]) >>
  qpat_assum `!x. not_fresh_at s5 x ==> lookup_var x t = _ /\ _`
    (drule_then strip_assume_tac) >> asm_rewrite_tac[]
QED

Finalise raw_request_gas_outbuf_mods
