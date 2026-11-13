(* Framed actual singleton allocation/address prefix, before decoder execution. *)
Theory entryRegistrationSingletonFrame
Ancestors
  entryRegistrationPrefixFrame entryRegistrationAddressFrame calldataRegistrationExec
  actualRegistrationCode calldataRegistration moduleLowering abiDecoderCounters loweringHalt abiDecoderAppend entryDecoderStateFrame
  abiDecoderReentryAddress abiDecoderReentry fragExec compileEnv emitHelper
  exprLoweringProps venomState venomExecSemantics finite_map words list arithmetic
  abiAllocationHistory calldataRegistration

Theorem entry_registration_singleton_prefix_frame:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st =
    (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME n /\
  (prim ==> ?c. info = DecPrimWord c) /\
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
  drule_all entry_registration_address_frame >> strip_tac >>
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
