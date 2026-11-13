(* Framed actual singleton allocation/address prefix, before decoder execution. *)
Theory entryRegistrationSingletonFrame
Ancestors
  entryRegistrationPrefixFrame entryRegistrationAddressFrame calldataRegistrationExec
  actualRegistrationCode calldataRegistration moduleLowering abiDecoderCounters loweringHalt abiDecoderAppend entryDecoderStateFrame
  abiDecoderReentryAddress abiDecoderReentry fragExec compileEnv emitHelper
  exprLoweringProps venomState venomExecSemantics finite_map words list arithmetic
  abiAllocationHistory calldataRegistration

(* The calldata pointer guard (LT; ISZERO; ASSERT) passes when the pointer is
   not below 4, defining only its two fresh test variables. *)
Theorem registration_ptr_guard_pass_run[local]:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) st = ((),last) /\
  eval_operand src s = SOME w /\ ~(w <+ 4w) ==>
  run_inst_seq (emitted_insts st last) s =
    OK (update_var (STRING #"%" (toString (st.cs_next_var + 1))) 1w
      (update_var (STRING #"%" (toString st.cs_next_var)) 0w s))
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_arg_ptr_guard _ _ _ _ = _` mp_tac >>
  simp[compile_abi_arg_ptr_guard_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `emit_op LT [src; Lit 4w] st = (below,c1)` >>
  rename1 `emit_op ISZERO [below] c1 = (ok,c2)` >>
  qpat_assum `emit_op LT _ _ = _`
    (strip_assume_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >>
  `step_inst_base (mk_inst st.cs_next_id LT [src; Lit 4w]
     [STRING #"%" (toString st.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString st.cs_next_var))
     (bool_to_word (w2n w < w2n (4w:bytes32))) s)` by
    (irule emitHelperPropsTheory.step_LT >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst c1.cs_next_id ISZERO [below]
     [STRING #"%" (toString c1.cs_next_var)])
     (update_var (STRING #"%" (toString st.cs_next_var))
       (bool_to_word (w2n w < w2n (4w:bytes32))) s) =
   OK (update_var (STRING #"%" (toString c1.cs_next_var))
     (bool_to_word (bool_to_word (w2n w < w2n (4w:bytes32)) = 0w))
     (update_var (STRING #"%" (toString st.cs_next_var))
       (bool_to_word (w2n w < w2n (4w:bytes32))) s))` by
    (irule emitHelperPropsTheory.step_ISZERO >>
     simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var]) >>
  drule_all calldataWordLiveTheory.calldata_two_tests_repeat >> strip_tac >>
  gvs[WORD_LO, bool_to_word_def]
QED

(* A passing guard step, framed like the pure address operations. *)
Theorem registration_ptr_guard_frame[local]:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) st = ((),last) /\
  eval_operand src s = SOME w /\ ~(w <+ 4w) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  fresh_vars_wrt limit_st s /\ last.cs_next_var <= limit_st.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    entry_decoder_obs s t /\ alloca_history fn t /\ fresh_vars_wrt limit_st t /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule calldataRegistrationExecTheory.registration_ptr_guard_code >> strip_tac >>
  drule_all registration_ptr_guard_pass_run >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK u` >>
  `run_inst_seq_mem_ok (emitted_insts st last) s` by
    (irule fragExecMemTheory.run_inst_seq_mem_ok_every >>
     qpat_x_assum `EVERY _ (emitted_insts st last)` mp_tac >>
     match_mp_tac EVERY_MONOTONIC >> BETA_TAC >> rpt strip_tac
     >- (irule instMemFrontierTheory.below_frontier_no_ranges >> fs[]) >>
     simp[memSafeRunTheory.inst_dload_in_section_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st last)` by
    (qpat_x_assum `EVERY _ (emitted_insts st last)` mp_tac >>
     match_mp_tac EVERY_MONOTONIC >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st last)` by
    (qpat_assum `EVERY _ (emitted_insts st last)` mp_tac >>
     match_mp_tac EVERY_MONOTONIC >> simp[]) >>
  `inst_extends st last` by
    (simp[emitHelperPropsTheory.inst_extends_def, emitted_insts_def] >>
     fs[rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all entryDecoderHistoryFrameTheory.entry_straight_line_alloca_history >>
  strip_tac >>
  `st.cs_next_var < limit_st.cs_next_var /\
   st.cs_next_var + 1 < limit_st.cs_next_var` by decide_tac >>
  `fresh_vars_wrt limit_st u` by
    (simp[Abbr `u`] >>
     irule abiDecoderLoopRegistersTheory.abi_decoder_generated_update_fresh >>
     simp[] >>
     irule abiDecoderLoopRegistersTheory.abi_decoder_generated_update_fresh >>
     simp[]) >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`P` |-> `\s:venom_state. T`]
      successfulSequenceEndpointTheory.successful_sequence_endpoint)) >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  suspend "package"
QED

Resume registration_ptr_guard_frame[package]:
  qexists_tac `u with vs_inst_idx := LENGTH last.cs_current_insts` >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op (u with vs_inst_idx := LENGTH last.cs_current_insts) =
     eval_operand op s` by
    (rpt strip_tac >>
     simp[Abbr `u`, instIdxIndepTheory.eval_op_inst_idx,
       calldataRegistrationExecTheory.registration_guard_state_live]) >>
  `(u with vs_inst_idx := LENGTH last.cs_current_insts).vs_memory = s.vs_memory /\
   (u with vs_inst_idx := LENGTH last.cs_current_insts).vs_allocas = s.vs_allocas /\
   (u with vs_inst_idx := LENGTH last.cs_current_insts).vs_alloca_next =
     s.vs_alloca_next /\
   (u with vs_inst_idx := LENGTH last.cs_current_insts).vs_call_ctx =
     s.vs_call_ctx /\
   (u with vs_inst_idx := LENGTH last.cs_current_insts).vs_data_section =
     s.vs_data_section /\
   entry_decoder_obs s (u with vs_inst_idx := LENGTH last.cs_current_insts) /\
   fresh_vars_wrt limit_st (u with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (qpat_x_assum `fresh_vars_wrt limit_st u` mp_tac >>
     simp[Abbr `u`, update_var_def, entry_decoder_obs_def,
       loweringStateRelDefsTheory.fresh_vars_wrt_def]) >>
  `alloca_inv (u with vs_inst_idx := LENGTH last.cs_current_insts) /\
   alloca_frontier_inv ctx fn site
     (u with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (qpat_x_assum `alloca_inv s` mp_tac >>
     qpat_x_assum `alloca_frontier_inv _ _ _ s` mp_tac >>
     simp[Abbr `u`, update_var_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       allocaFrontierBoundTheory.alloca_frontier_inv_def,
       allocaBudgetPropsTheory.remaining_alloca_budget_def]) >>
  simp[]
QED

Finalise registration_ptr_guard_frame

(* The address prelude with its passing pointer guard. *)
Theorem entry_registration_guarded_address_frame[local]:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] st = (head,after_head) /\
  (if dyn then
    ?offset after_load after_src.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,after_src) /\
      compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) after_src = ((),first)
   else src = head /\ first = after_head) /\
  (dyn ==> ~(n2w 4 + abi_decode_load CALLDATALOAD
     (n2w 4 + n2w (off-4):bytes32) s <+ 4w)) /\
  fn_has_code st first fn /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\
  fresh_vars_wrt limit_st s /\ first.cs_next_var <= limit_st.cs_next_var ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = first.cs_current_bb /\
    t.vs_inst_idx = LENGTH first.cs_current_insts /\
    eval_operand src t = SOME
      (if dyn then n2w 4 + abi_decode_load CALLDATALOAD
         (n2w 4 + n2w (off-4):bytes32) s else n2w 4 + n2w (off-4)) /\
    abi_decoder_operand_live first.cs_next_var src /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    entry_decoder_obs s t /\ alloca_history fn t /\ fresh_vars_wrt limit_st t /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `if dyn then _ else _` (strip_assume_tac o
    MATCH_MP calldataRegistrationExecTheory.registration_address_mid) >>
  drule_all calldataRegistrationExecTheory.registration_address_prelude_mid_bounds >>
  strip_tac >>
  `cs_extends mid first /\ mid.cs_next_var <= first.cs_next_var` by
    (Cases_on `dyn` >> gvs[cs_extends_refl] >>
     drule calldataRegistrationExecTheory.registration_ptr_guard_code >>
     strip_tac >>
     drule calldataRegistrationExecTheory.registration_ptr_guard_extends >>
     simp[]) >>
  `fn_has_code st mid fn /\ fn_has_code mid first fn` by
    metis_tac[fn_has_code_split] >>
  `mid.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all entry_registration_address_frame >> strip_tac >>
  reverse (Cases_on `dyn`) >> gvs[] >- (qexists_tac `t` >> simp[]) >>
  suspend "guard"
QED

Resume entry_registration_guarded_address_frame[guard]:
  drule_all registration_ptr_guard_frame >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >>
  `abi_decoder_operand_live first.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >>
     qexists_tac `mid.cs_next_var` >> simp[]) >>
  `eval_operand src gs = eval_operand src t` by
    (qpat_x_assum `!op. abi_decoder_operand_live mid.cs_next_var op ==> _`
       irule >> first_assum ACCEPT_TAC) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op gs = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live mid.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >>
     metis_tac[]) >>
  `entry_decoder_obs s gs` by metis_tac[entry_decoder_obs_trans] >>
  simp[] >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn gs = r /\ _ ==> _` mp_tac >>
  qpat_x_assum `!fuel. (!err. run_from fuel ctx fn t <> Error err) ==> _`
    mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
QED

Finalise entry_registration_guarded_address_frame

Theorem entry_registration_singleton_prefix_frame:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st =
    (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME n /\
  (prim ==> ?c. info = DecPrimWord c) /\
  (dyn /\ ~prim ==> ~(n2w 4 + abi_decode_load CALLDATALOAD
     (n2w 4 + n2w (off-4):bytes32) initial <+ 4w)) /\
  fn_has_code st final fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct fn /\ alloca_history fn initial /\
  fresh_vars_wrt limit_st initial /\ final.cs_next_var <= limit_st.cs_next_var ==>
  ?dst src first ready p.
    FLOOKUP cef.ce_vars name = SOME (PtrVar dst n) /\
    (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
      ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
      ins.inst_id = st.cs_next_id) /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) info first =
      ((),final) /\ fn_has_code first final fn /\
    st.cs_next_id < first.cs_next_id /\
    st.cs_next_var <= first.cs_next_var /\
    ~ready.vs_halted /\ ready.vs_current_bb = first.cs_current_bb /\
    ready.vs_inst_idx = LENGTH first.cs_current_insts /\
    eval_operand src ready = SOME
      (if dyn /\ ~prim then n2w 4 + abi_decode_load CALLDATALOAD
         (n2w 4 + n2w (off-4):bytes32) initial
       else n2w 4 + n2w (off-4)) /\
    eval_operand dst ready = SOME (n2w p) /\
    abi_decoder_operand_live first.cs_next_var src /\
    abi_decoder_operand_live first.cs_next_var dst /\
    FLOOKUP ready.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\
    alloca_inv ready /\ alloca_frontier_inv ctx fn site ready /\
    initial.vs_alloca_next <= ready.vs_alloca_next /\
    ready.vs_memory = initial.vs_memory /\
    ready.vs_call_ctx = initial.vs_call_ctx /\
    ready.vs_data_section = initial.vs_data_section /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op ready = eval_operand op initial) /\
    (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
      FLOOKUP ready.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP ready.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!fuel r. run_from fuel ctx fn ready = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn ready ==> mem_safe_run fuel' ctx fn initial)) /\
    entry_decoder_obs initial ready /\ alloca_history fn ready /\
    (abi_alloca_history (fn_insts fn) initial ==> abi_alloca_history (fn_insts fn) ready) /\
    fresh_vars_wrt limit_st ready /\
    ((!fuel. mem_safe_run fuel ctx fn ready) ==>
      !fuel. mem_safe_run fuel ctx fn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all register_singleton_allocated_boundary >> strip_tac >>
  `FLOOKUP cef.ce_vars name = SOME (PtrVar buf.buf_operand n)` by
    simp[FLOOKUP_UPDATE] >>
  `var_location_decode_operand (PtrVar buf.buf_operand n) =
    SOME buf.buf_operand` by simp[var_location_decode_operand_def] >>
  drule_all registration_decoder_prelude >> strip_tac >>
  `cs_extends st allocated /\ cs_extends allocated final` by
    metis_tac[compile_alloc_buffer_extends, decode_args_suffix_extends] >>
  `fn_has_code st allocated fn /\ fn_has_code allocated final fn` by
    metis_tac[fn_has_code_split] >>
  `cs_extends allocated first /\ allocated.cs_next_id < first.cs_next_id /\
    allocated.cs_next_var <= first.cs_next_var` by
    (drule_all registration_address_prelude_bounds >> simp[]) >>
  `cs_extends first final` by
    metis_tac[cs_appends_abi_decode_mutual, cs_appends_def] >>
  `fn_has_code allocated first fn /\ fn_has_code first final fn` by
    metis_tac[fn_has_code_split] >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\
   first.cs_next_var <= limit_st.cs_next_var` by
    (drule abi_decoder_variable_counter >> strip_tac >> decide_tac) >>
  drule_all entry_registration_alloc_buffer_frame >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!entry. FLOOKUP initial.vs_allocas _ = SOME entry ==> _` kall_tac >>
  qpat_x_assum `alloca_inv initial` kall_tac >>
  qpat_x_assum `alloca_frontier_inv _ _ _ initial` kall_tac >>
  `dyn /\ ~prim ==> ~(n2w 4 + abi_decode_load CALLDATALOAD
     (n2w 4 + n2w (off-4):bytes32) v <+ 4w)` by
    (qpat_x_assum `v.vs_call_ctx = _` mp_tac >>
     qpat_x_assum `dyn /\ ~prim ==> _` mp_tac >>
     simp[abiDecoderContractTheory.abi_decode_load_def,
       abiDecoderContractTheory.abi_decode_source_def]) >>
  drule_all entry_registration_guarded_address_frame >> strip_tac >>
  `?vname ins. buf.buf_operand = Var vname /\ MEM ins (fn_insts fn) /\
    ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
    ins.inst_id = st.cs_next_id` by
    (drule_all actualAllocExecTheory.actual_alloc_buffer_site >>
     strip_tac >> qexistsl [`STRING #"%" (toString st.cs_next_var)`,
       `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
         [STRING #"%" (toString st.cs_next_var)]`] >>
     simp[venomInstTheory.mk_inst_def]) >>
  `abi_alloca_history (fn_insts fn) initial ==>
    abi_alloca_history (fn_insts fn) t` by
    (strip_tac >> irule abi_alloca_history_frame >> qexists_tac `v` >> simp[]) >>
  qexistsl [`buf.buf_operand`,`src`,`first`,`t`,`p`] >>
  simp[abiDecoderContractTheory.abi_decode_load_def,
    abiDecoderContractTheory.abi_decode_source_def, SF SFY_ss] >>
  suspend "package"
QED

Resume entry_registration_singleton_prefix_frame[package]:
  conj_tac
  >- (qpat_x_assum `abi_decoder_operand_live allocated.cs_next_var _` mp_tac >>
      qpat_x_assum `allocated.cs_next_var <= first.cs_next_var` mp_tac >>
      qpat_x_assum `buf.buf_operand = _` SUBST_ALL_TAC >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono]) >>
  conj_tac
  >- (qpat_x_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _` mp_tac >>
      qpat_x_assum `!op. abi_decoder_operand_live allocated.cs_next_var op ==> _` mp_tac >>
      qpat_x_assum `allocated.cs_next_var = _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      metis_tac[abi_decoder_operand_live_mono, LESS_EQ_ADD]) >>
  conj_tac
  >- (qpat_x_assum `!fuel r. run_from fuel ctx fn t = r /\ _ ==> _` mp_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx fn v = r /\ _ ==> _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  metis_tac[entry_decoder_obs_trans]
QED

Finalise entry_registration_singleton_prefix_frame

val () =
  let val th = entry_registration_singleton_prefix_frame
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "ENTRY_REGISTRATION_SINGLETON_FRAME_AUDIT OK\n"
     else raise Fail "registration singleton frame inherited admission"
  end;
