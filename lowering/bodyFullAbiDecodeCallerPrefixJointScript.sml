Theory bodyFullAbiDecodeCallerPrefixJoint
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeLeafCases
  bodyFullAbiDecodeFiniteObserved assignTuplePtrCopyLen abiDecodePtrRead
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiBuiltinLengthGuard
  abiDecodePtrMemberFrame assignTuplePtrLoadStep instSeqPtrLo
  bodyPtrIfExpBytesCounted bodyPtrIfExpBytesFrame loweringHalt
  abiDecoderReentry stateRelProj
  fragGasOriginPtrLoop fragGasSeqPtr bodyFullUnwrapRun
  emitHelperProps exprLoweringProps loweringStateRelDefs
  exprSimAccounts bodyPtrDefs assignTuplePtrLocalBytesCopy
  stateFrame allocaHistory fragExecMem instMemFrontier
  bodyBinopFragMemory stmtReasonLitFragMemory decoderGhostFramePtr
  compileEnv emitHelper freshWrites ptrDiscipline
  venomExecSemantics venomInst venomState words arithmetic finite_map list rich_list
  bodyFullAbiDecodeRelativeLoadExact[qualified]

val caller_setup_pre = ``\data min_size max_size outsz st ready ops s G tn b data_var d.
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved ce st /\ origin.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ (?H. V H) /\
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name a sz. local_region ce es0.scopes s0 name a sz ==>
    a+sz <= s.vs_alloca_next) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  data = Var data_var /\ eval_operand data s = SOME (n2w b) /\
  op_taint tn data = {} /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_decode_ptr_window G tn s data_var (n2w b) (32+LENGTH input_bytes) /\
  mload b s = n2w (LENGTH input_bytes) /\
  mem_bytes_at (b+32) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  b+32+LENGTH input_bytes <= s.vs_alloca_next /\
  b+32+LENGTH input_bytes < dimword (:256) /\
  min_size <= max_size /\ max_size < dimword (:256) /\
  outsz < dimword (:256) /\ d+outsz < dimword (:256) /\
  (b+32+LENGTH input_bytes <= d \/ d+outsz <= b+32) /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
     SOME (d,outsz))``;

Theorem abi_decode_caller_prefix_joint:
  (^caller_setup_pre) data min_size max_size outsz st ready ops s G tn b data_var d /\
  emit_op MLOAD [data] st = (len,sa) /\
  emit_op ADD [data; Lit 32w] sa = (src,sb) ==>
  ?u Gp tnp.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK u,Gp,tnp)) /\
    (!obs. fn_has_code st sb obs ==> gas_path ctx obs s 0 (OK u)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (?input. src = Var input /\
      abi_decode_ptr_window Gp tnp u input (n2w (b+32)) (LENGTH input_bytes)) /\
    eval_operand len u = SOME (n2w (LENGTH input_bytes)) /\
    op_prov Gp len = NONE /\ op_taint tnp len = {} /\ op_taint tnp src = {} /\
    abi_decoder_operand_live sb.cs_next_var len /\
    abi_decoder_operand_live sb.cs_next_var src /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tnp.t_mem = tn.t_mem /\ tnp.t_stor = tn.t_stor /\
    tnp.t_trans = tn.t_trans /\ tnp.t_imm = tn.t_imm /\ alloca_history fn u /\
    (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)) /\
    (!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\
      ghost_inv_at (DF H) lo delta ce cx es Gp tnp u /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 Gp tnp)
Proof
  BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?H. V H` strip_assume_tac >>
  qpat_x_assum `(_ <= d \/ _)` kall_tac >>
  qpat_x_assum `(FLOOKUP _ _ = NONE /\ _ \/ _)` kall_tac >>
  `cs_extends st sa /\ cs_extends sa sb /\
   st.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `?lv. len = Var lv` by metis_tac[emitted_insts_emit_op] >>
  `b < dimword (:256)` by decide_tac >>
  `ptr_covers G tn data_var s 32 /\ lookup_var data_var s = SOME (n2w b) /\
   (!i. w2n (n2w b:256 word) <= i /\ i < w2n (n2w b:256 word)+32 ==>
      i NOTIN tn.t_mem)` by
    (gvs[abi_decode_ptr_window_def, ptr_covers_def] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  qpat_x_assum `data = Var data_var` SUBST_ALL_TAC >>
  qpat_x_assum `len = Var lv` SUBST_ALL_TAC >>
  drule_all (Q.SPECL [`ARB`, `ctx`, `fn`, `PG`] emit_mload_clean_seq_ptr) >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st sa) s = OK raw_load` >>
  rename1 `inst_seq_ptr ARB 0 ctx fn PG G tn (emitted_insts st sa) s Gl tnl` >>
  `not_fresh_at st data_var` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  qabbrev_tac `mid = raw_load with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  `~mid.vs_halted /\ mid.vs_current_bb = st.cs_current_bb /\
   mid.vs_inst_idx = LENGTH sa.cs_current_insts /\
   mid.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `(raw_load with vs_vars := _) = s` mp_tac >>
     simp[Abbr `mid`, venom_state_component_equality]) >>
  `abi_decode_ptr_window Gl tnl mid data_var (n2w b) (32+LENGTH input_bytes)` by
    (irule abi_decode_ptr_window_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >>
     `lookup_var data_var mid = lookup_var data_var raw_load` by
       (simp[Abbr `mid`, lookup_var_def] >> (metis_tac[Abbr `mid`, lookup_var_def, abi_decode_ptr_window_frame])) >> simp[]) >>
  `sa.cs_current_bb = st.cs_current_bb` by
    (fs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
       comp_ignore_bind_def, comp_return_def, emit_def] >> (gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def])) >>
  `cs_extends sb ready` by
    (drule abi_builtin_decode_setup_trace >> strip_tac >>
     qpat_x_assum `abi_builtin_decode_header _ _ _ _ = _` mp_tac >>
     simp[abi_builtin_decode_header_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, LET_THM] >>
     pairarg_tac >> simp[] >>
     rename1 `abi_builtin_length_guard (Var lv) min_size max_size sb = _` >>
     strip_tac >> gvs[] >>
     drule abi_builtin_length_guard_shape >> strip_tac >>
     irule cs_extends_trans >>
     first_assum (irule_at Any o MATCH_MP compile_alloc_buffer_extends) >>
     simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code st sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `fn_has_code sa sb fn` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `compile_abi_dec_addr (Var data_var) (Lit 32w) sa = (src,sb)` by
    simp[abiEncoderTheory.compile_abi_dec_addr_def] >>
  `eval_operand (Lit 32w) mid = SOME (n2w 32) /\
   op_taint tnl (Lit 32w) = {} /\ 32 <= 32+LENGTH input_bytes /\
   w2n (n2w b:256 word) + (32+LENGTH input_bytes) < dimword (:256)` by
    (simp[eval_operand_def, op_taint_def] >>
     `b MOD dimword (:256) = b` by simp[LESS_MOD] >> decide_tac) >>
  drule abi_decode_ptr_address >>
  disch_then (qspecl_then
    [`tnl`, `mid`, `32`, `32+LENGTH input_bytes`, `fn`, `ctx`, `n2w b`,
     `PG`, `Gl`, `ARB`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) mid = OK (t with vs_inst_idx := mid.vs_inst_idx)` >>
  rename1 `inst_seq_ptr ARB 0 ctx fn PG Gl tnl (emitted_insts sa sb) mid Gp tnp` >>
  `sa.cs_current_insts = st.cs_current_insts ++ emitted_insts st sa /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st sa) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_assum `emit_op MLOAD _ st = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     qpat_assum `emit_op ADD _ sa = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `(mid with vs_inst_idx := s.vs_inst_idx) = raw_load` by
    (qpat_assum `(raw_load with vs_vars := _) = s`
       (mp_tac o AP_TERM ``venom_state_vs_inst_idx``) >>
     simp[Abbr `mid`] >> disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `run_inst_seq (emitted_insts st sa) s = OK (mid with vs_inst_idx := s.vs_inst_idx)`
    by simp[] >>
  drule_all emitted_insts_join_normalized_ptr >> strip_tac >>
  `sb.cs_current_bb = st.cs_current_bb` by
    (qpat_assum `emit_op ADD _ sa = _`
       (strip_assume_tac o MATCH_MP loweringShapeRulesTheory.emit_op_facts) >>
     simp[]) >>
  qabbrev_tac `il = mk_inst st.cs_next_id MLOAD [Var data_var]
    [STRING #"%" (toString st.cs_next_var)]` >>
  qabbrev_tac `ia = mk_inst sa.cs_next_id ADD [Var data_var; Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  `emitted_insts st sa = [il] /\ emitted_insts sa sb = [ia]` by
    (qpat_assum `emit_op MLOAD _ st = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     qpat_assum `emit_op ADD _ sa = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     simp[Abbr `il`, Abbr `ia`]) >>
  `emitted_insts st sb = [il;ia]` by metis_tac[emitted_insts_append, APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> GAS) (emitted_insts st sb)` by
    simp[Abbr `il`, Abbr `ia`, mk_inst_def, is_terminator_def] >>
  `step_inst_base il s = OK raw_load` by
    (qpat_assum `run_inst_seq (emitted_insts st sa) s = OK raw_load` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()] >> gvs[run_inst_seq_def, AllCaseEqs()]) >>
  `step_prov PG G il raw_load = Gl /\ step_taint il s raw_load tn = tnl` by
    (qpat_assum `inst_seq_ptr ARB 0 ctx fn PG G tn (emitted_insts st sa) _ _ _` mp_tac >>
     qpat_assum `emitted_insts st sa = [il]`
       (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `step_inst_base il s = OK raw_load`
       (fn th => simp[NoAsms, inst_seq_ptr_def, th])) >>
  qexistsl_tac [`t`, `Gp`, `tnp`] >>
  conj_tac >- suspend "origin" >>
  conj_tac >- suspend "observer" >>
  suspend "frame"
QED

Resume abi_decode_caller_prefix_joint[origin]:
  qx_gen_tac `horizon` >> strip_tac >>
  `allocas_from lo s` by
    (qpat_assum `!H. V H ==> _` (qspec_then `horizon` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> fs[ghost_inv_at_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st sb) s` by
    (`run_inst_seq_mem_ok [il] s` by
       (simp[run_inst_seq_mem_ok_last, Abbr `il`, below_frontier_MLOAD,
             LESS_MOD, memSafeRunTheory.inst_dload_in_section_other, mk_inst_def] >>
        decide_tac) >>
     `!v. run_inst_seq_mem_ok [ia] v` by
       (simp[run_inst_seq_mem_ok_last, Abbr `ia`, mk_inst_def,
             memSafeRunTheory.inst_dload_in_section_other, below_frontier_no_ranges]) >>
     `emitted_insts st sb = [il] ++ [ia]` by simp[] >>
     pure_once_asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  `mid.vs_allocas = s.vs_allocas` by
    (qpat_assum `(raw_load with vs_vars := _) = s`
       (mp_tac o AP_TERM ``venom_state_vs_allocas``) >> simp[Abbr `mid`]) >>
  `allocas_from lo mid` by
    (qpat_assum `allocas_from lo s` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     qpat_assum `mid.vs_allocas = s.vs_allocas`
       (fn th => rewrite_tac[allocas_from_def, th])) >>
  `mid = raw_load with vs_inst_idx := SUC s.vs_inst_idx` by
    simp[Abbr `mid`, ADD1] >>
  `ptr_inst_ok (DF horizon) lo 0 ctx fn G tn il s` by
    (simp[Abbr `il`] >> irule exprPtrCtorImmStoreTheory.ptr_inst_ok_mload_lo >> simp[]) >>
  `op_taint tnl (Var data_var) = {}` by metis_tac[] >>
  `ptr_inst_ok (DF horizon) lo 0 ctx fn Gl tnl ia mid` by
    (simp[Abbr `ia`, NoAsms] >> irule bodyPtrEnvBuiltinsEdgesTheory.ptr_inst_ok_scalar_builtin_at >>
     simp[IgnAsm `mid = _ with vs_inst_idx := _`, DISJ_IMP_THM, FORALL_AND_THM]) >>
  `inst_seq_ptr (DF horizon) lo ctx fn PG G tn (emitted_insts st sb) s Gp tnp` by
    (qpat_x_assum `inst_seq_ptr ARB 0 ctx fn PG G tn (emitted_insts st sb) _ _ _` mp_tac >>
     qpat_x_assum `ptr_inst_ok (DF horizon) lo 0 ctx fn Gl tnl ia mid` mp_tac >>
     simp[inst_seq_ptr_def]) >>
  `OK t = OK ((t with vs_inst_idx := s.vs_inst_idx)
      with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `t.vs_inst_idx = LENGTH sb.cs_current_insts`
       (fn th => simp[GSYM th, NoAsms])) >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  irule emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`emitted_insts st sb`, `st`] >>
  simp[Abbr `il`, Abbr `ia`, mk_inst_def, is_terminator_def]
QED

Resume abi_decode_caller_prefix_joint[observer]:
  qx_gen_tac `obs` >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb obs.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (qpat_x_assum `fn_has_code st sb obs` mp_tac >>
     simp[fragExecTheory.fn_has_code_def]) >>
  `isPREFIX (emitted_insts st sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
     qpat_assum `sb.cs_current_insts = st.cs_current_insts ++ emitted_insts st sb`
       (fn th => rewrite_tac[th, IS_PREFIX_APPEND]) >>
     disch_then (qx_choose_then `rest` (fn th =>
       qexists_tac `rest` >> once_rewrite_tac[th])) >>
     qpat_assum `s.vs_inst_idx = LENGTH st.cs_current_insts`
       (fn th => pure_rewrite_tac[th]) >>
     pure_once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     rewrite_tac[DROP_LENGTH_APPEND]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st sb)) = 0` by
    simp[Abbr `il`, Abbr `ia`, mk_inst_def] >>
  `s.vs_inst_idx + LENGTH (emitted_insts st sb) = t.vs_inst_idx` by simp[] >>
  `((t with vs_inst_idx := s.vs_inst_idx) with
      vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st sb)) = t` by
    (qpat_assum `s.vs_inst_idx + LENGTH (emitted_insts st sb) = t.vs_inst_idx`
       (fn th => simp[th, NoAsms])) >>
  qpat_assum `run_inst_seq (emitted_insts st sb) s = OK (t with vs_inst_idx := _)`
    (mp_then (Pat `run_inst_seq _ _ = OK _`) mp_tac fragGasSeqTheory.tuple_run_inst_seq_gas_path) >>
  disch_then (qspecl_then [`ctx`, `obs`, `bb`] mp_tac) >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  simp[Abbr `il`, Abbr `ia`, mk_inst_def, is_terminator_def]
QED

Resume abi_decode_caller_prefix_joint[frame]:
  `tnl.t_imm = tn.t_imm` by
    (qpat_assum `step_taint il s raw_load tn = tnl`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     simp[step_taint_nonmemory_frame, Abbr `il`, mk_inst_def]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_assum `(raw_load with vs_vars := _) = s` mp_tac >>
     simp[Abbr `mid`, venom_state_component_equality]) >>
  `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx)` by
    (qpat_assum `state_frame t = state_frame (mid with vs_inst_idx := _)`
       (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `(raw_load with vs_vars := _) = s`
       (mp_tac o AP_TERM ``\z:venom_state. state_frame (z with vs_inst_idx := t.vs_inst_idx)``) >>
     simp[Abbr `mid`, state_frame_def, venom_state_component_equality, NoAsms]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `state_frame t = state_frame (s with vs_inst_idx := _)`
       (mp_tac o AP_TERM ``venom_state_vs_alloca_next``) >> simp[state_frame_def, NoAsms]) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)` by
    ((qx_gen_tac `x` >> strip_tac >>
     `not_fresh_at sa x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` strip_assume_tac) >>
     simp[Abbr `mid`, lookup_var_def] >>
     qpat_assum `!p. not_fresh_at st p ==> lookup_var p raw_load = _`
       (qspec_then `x` mp_tac) >> simp[lookup_var_def] >> (metis_tac[freshWritesTheory.not_fresh_at_mono, Abbr `mid`, lookup_var_def]))) >>
  `?bb rest. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts st sb ++ rest` by
    (drule_all (Q.SPECL [`st`, `sb`, `fn`, `emitted_insts st sb`] fn_has_code_code) >>
     simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts st sb) = t.vs_inst_idx` by simp[] >>
  `alloca_history fn t` by
    (mp_tac (Q.SPECL [`fn`, `s`, `t`, `bb`, `emitted_insts st sb`, `rest`]
       alloca_history_no_alloca_slice) >>
     (impl_tac >- simp[Abbr `il`, Abbr `ia`, mk_inst_def]) >>
     qpat_assum `s.vs_inst_idx + LENGTH (emitted_insts st sb) = t.vs_inst_idx`
       (fn th => simp[th, NoAsms])) >>
  `abi_decoder_operand_live sa.cs_next_var (Var lv)` by
    metis_tac[abi_decoder_operand_live_emit] >>
  `not_fresh_at sa lv` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `lv` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `n2w b + 32w = (n2w (b+32):256 word)` by simp[word_add_n2w] >>
  `op_taint tnp src = {}` by fs[abi_decode_ptr_window_def, ptr_covers_def] >>
  `lookup_var lv mid = lookup_var lv raw_load` by
    simp[Abbr `mid`, lookup_var_def, NoAsms] >>
  `abi_decoder_operand_live sb.cs_next_var (Var lv) /\
   abi_decoder_operand_live sb.cs_next_var src` by
    metis_tac[abi_decoder_operand_live_emit, abi_decoder_operand_live_mono] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
     ghost_inv_at (DF H) lo delta ce cx es Gp tnp t /\
     ghost_kept_at lo ce es0 origin G0 tn0 s0 Gp tnp` by
    (ho_match_mp_tac (bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_scalar_joint_frame_lower |>
       Q.INST [`sa` |-> `st`, `s` |-> `s`, `G` |-> `G`, `tn` |-> `tn`]) >>
     pure_asm_rewrite_tac[] >> simp[NoAsms]) >>
  fs[eval_operand_def, op_prov_def, LESS_MOD] >>
  qx_gen_tac `horizon` >> strip_tac >>
  qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\ _`
    (qspec_then `horizon` mp_tac) >> simp[]
QED

Finalise abi_decode_caller_prefix_joint
