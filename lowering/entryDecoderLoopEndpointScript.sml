(* Named terminal endpoints for entry decoder loops. *)
Theory entryDecoderLoopEndpoint
Ancestors
  entryDecoderJointLoop entryDecoderLoopStep entryDecoderStateFrame
  entryDecoderHistoryFrame abiDecoderArrayInit abiDecoderArrayLoopInit
  abiDecoderDynarrayPrefix abiDecoderArrayHeader abiDecoderIndexInit
  emitHelperProps rich_list abiDecoderGuards abiDecoderReentry abiEncoder
  compileEnv emitHelper venomInst context abiDecoderGuard abiDecoderVarSequence
  abiDecoderDynarrayBound calldataValidInitHeader finite_map venomWf
  ctorAbiActualArrayRun
  calldataOwnedLoopClosure calldataDynOwned decoderPrefixEdges
  abiDecoderLoopRegisters abiDecoderDynamic abiDecoderContract
  abiDecoderExecution abiDecoderArrayBackedge
  abiDecoderFrame exprLoweringProps allocaHistory
  venomState venomExecSemantics words list arithmetic

Theorem entry_terminal_header_endpoint:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  abi_decoder_operand_live next src /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcword /\
  mload (w2n p) s = n2w (LENGTH vs) /\
  abi_decode_load CALLDATALOAD srcword s = n2w (LENGTH vs) /\
  LENGTH vs < dimword (:256) /\ w2n p+32 <= s.vs_alloca_next /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  LENGTH vs <= maxn /\ EVERY (val_wf tv) vs /\
  mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
  (!k. k < LENGTH vs ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) s.vs_memory) /\
  next+4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  alloca_history fn s /\
  t = jump_to exit_lbl
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) (LENGTH vs) (LENGTH vs) s) ==>
  ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
  val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
  fresh_vars_wrt limit_st t /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s) /\
  (!op. abi_decoder_operand_live next op ==> eval_operand op t = eval_operand op s) /\
  (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
  ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
  entry_decoder_obs s t /\ alloca_history fn t
Proof
  strip_tac >>
  `src <> Var (STRING #"%" (toString next))` by
    (drule abi_decoder_live_excludes_output >> simp[]) >>
  `STRING #"%" (toString (next:num)) <> STRING #"%" (toString (next+1))` by simp[] >>
  `LENGTH vs = LENGTH vs` by simp[] >>
  drule_all calldata_terminal_header_array >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  drule_all abi_decoder_header_registers >>
  disch_then (qspecl_then [`LENGTH vs`,`LENGTH vs`] strip_assume_tac) >>
  `entry_decoder_obs s t` by
    (qpat_assum `t = _` (fn th => pure_rewrite_tac[th]) >>
     simp[entry_decoder_obs_def, abi_decode_header_state_def, jump_to_def, update_var_def]) >>
  `alloca_history fn t` by
    (qpat_assum `t = _` (fn th => pure_rewrite_tac[th]) >>
     irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `s` >>
     simp[abi_decode_header_state_def, jump_to_def, update_var_def]) >>
  `~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0` by
    (qpat_assum `t = _` (fn th => pure_rewrite_tac[th]) >>
     simp[abi_decode_header_state_def, jump_to_def, update_var_def]) >>
  `fresh_vars_wrt limit_st t` by
    (qpat_assum `t = _` (fn th => pure_rewrite_tac[th]) >>
     simp_tac bool_ss [abi_decoder_fresh_jump] >> first_assum ACCEPT_TAC) >>
  `!op. abi_decoder_operand_live next op ==> eval_operand op t = eval_operand op s` by
    (qpat_assum `t = _` (fn th => pure_rewrite_tac[th]) >>
     simp_tac bool_ss [abi_decoder_operand_jump] >> first_assum ACCEPT_TAC) >>
  `(!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s` by
    (ho_match_mp_tac (GEN_ALL calldata_header_all_fuel_pullback) >>
     goal_assum (drule_at (Pos hd)) >>
     qexistsl_tac [`srcword`,`p`,`exit_bb`,`LENGTH vs`,`LENGTH vs`] >>
     simp_tac bool_ss [LESS_EQ_REFL, prim_recTheory.LESS_REFL] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then () else raise Fail "entry loop endpoint inherited admission"
    end) [entry_terminal_header_endpoint];

(* Frame the very sequence witness supplied by calldata_valid_init_header.
   The cursor update is used only for the history proof, not for execution. *)
Theorem entry_initializer_sequence_frame:
  fn_inst_ids_distinct fn /\ alloca_history fn initial /\ alloca_inv initial /\
  fn_has_code st loop_st fn /\
  loop_st.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts loop_st.cs_current_insts /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st loop_st) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st loop_st) /\
  run_inst_seq (emitted_insts st loop_st) initial = OK t ==>
  entry_decoder_obs initial (jump_to hdr t) /\
  alloca_history fn (jump_to hdr t)
Proof
  strip_tac >>
  drule_all entry_decoder_sequence_obs >> strip_tac >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  conj_tac >- simp[] >>
  irule alloca_history_jump >> simp[jump_to_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH loop_st.cs_current_insts` >>
  simp[jump_to_def]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_initializer_sequence_frame)
  in if null axioms andalso null (Thm.hyp entry_initializer_sequence_frame) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry initializer frame inherited admission"
  end;

Theorem entry_array_initializer_reentry_code:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    (setup,loop_st) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st loop_st)
Proof
  simp[abi_decode_array_loop_init_def, abi_decode_dynarray_prefix_def,
       abi_decode_count_guard_def, abi_decode_array_header_def,
       abi_decode_dynarray_end_guard_def, abi_decode_dynarray_end_def,
       abi_decode_le_guard_def, abi_decode_index_init_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def]
QED

Theorem entry_array_initializer_frame:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    (setup,loop_st) /\
  fn_inst_ids_distinct fn /\ alloca_history fn initial /\ alloca_inv initial /\
  fn_has_code st loop_st fn /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq (emitted_insts st loop_st) initial = OK t ==>
  entry_decoder_obs initial (jump_to hdr t) /\
  alloca_history fn (jump_to hdr t)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule entry_array_initializer_reentry_code >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st loop_st)` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all entry_initializer_sequence_frame >> simp[]
QED

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then () else raise Fail "entry array initializer inherited admission"
    end) [entry_array_initializer_reentry_code, entry_array_initializer_frame];

(* The source-valid initializer's original resource witness, now framed. *)
Theorem entry_valid_initializer_header:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  fn_inst_ids_distinct fn /\ alloca_history fn initial /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
     p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  abi_decode_load CALLDATALOAD srcword initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ LENGTH vs < dimword (:256) /\
  st.cs_next_id <= header_st.cs_next_id /\ header_st.cs_next_id < end_st.cs_next_id /\
  EntryLoopOwn fn st.cs_next_id end_st.cs_next_id initial /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  fresh_vars_wrt limit_st initial /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  loop_st.cs_blocks = st.cs_blocks /\ loop_st.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts loop_st.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (emitted_insts st loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st = ((hdr,body_lbl,exit_lbl),prefix_st) /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st prefix_st fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. run_inst_seq (emitted_insts st loop_st) initial = OK t /\
    run_inst_seq_mem_ok (emitted_insts st loop_st) initial /\
    EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
      src srcword dst ip d p header_st.cs_next_id oid base_addr cap sb bs b cap
      initial 0 (jump_to hdr t) [(p,32)] /\
    EntryLoopSafe ctx fn initial (jump_to hdr t) /\
    EntryLoopPull ctx fn initial (jump_to hdr t) /\
    entry_decoder_obs initial (jump_to hdr t) /\ alloca_history fn (jump_to hdr t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ctor_actual_function_ids >> disch_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM, GSYM EntryLoopOwn_def,
      GSYM EntryLoopHeader_def]
    (INST_TYPE [alpha |-> ``:value``] calldata_valid_init_header)) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  drule_all entry_array_initializer_frame >>
  disch_then (qspec_then `hdr` strip_assume_tac) >>
  qexists_tac `t` >>
  asm_rewrite_tac[EntryLoopSafe_def, EntryLoopPull_def, EntryLoopInv_def,
    prim_recTheory.NOT_LESS_0] >>
  conj_tac
  >- (asm_rewrite_tac[EntryLoopHeader_def] >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_valid_initializer_header)
  in if null axioms andalso null (Thm.hyp entry_valid_initializer_header) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry valid initializer inherited admission"
  end;
