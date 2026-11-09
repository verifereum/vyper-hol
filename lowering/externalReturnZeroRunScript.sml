Theory externalReturnZeroRun
Ancestors
  externalReturnZeroWindow abiEncoderWindowRun abiEncoderWindowLeaves
  abiEncoderWindow abiEncoderInput contractABI valueEncoding valueEncodingDefs
  abiEncoderLeaves abiEncoderRegisteredEffect abiEncoderExtendSim
  abiEncoderPrimitiveEffect
  emitHelperProps exprLoweringProps compileEnv venomState venomExecSemantics
  venomInst words list finite_map pred_set

Theorem zero_window_copy_run:
  compile_abi_encode_to_buf dst src (AbiCopy 0) st = (out,st') /\
  abi_encoder_admissible (AbiCopy 0) /\
  abi_encoder_window_input (AbiCopy 0) at av sb 0 initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_inv initial /\ alloca_room ctx func initial /\
  d + LENGTH (enc at av) <= initial.vs_alloca_next /\
  (!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st st' /\
    FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_registered_effect (frag_ids st st')
      [(d,LENGTH (enc at av))] initial actual /\
    alloca_inv actual /\ alloca_room ctx func actual /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
           lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >>
  `enc at av = []` by fs[abi_encoder_window_copy_iff, mem_bytes_at_def] >>
  drule abi_encode_copy_code >> strip_tac >>
  `d < dimword (:256)` by
    (drule alloca_room_next_lt >> simp[] >> decide_tac) >>
  `eval_operand src initial = SOME (n2w (sb MOD dimword (:256)))` by simp[] >>
  `eval_operand (Lit 0w) initial = SOME (n2w 0)` by simp[eval_operand_def] >>
  `run_inst_seq (emitted_insts st st') initial =
     OK (mcopy d (sb MOD dimword (:256)) 0 initial) /\
   inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
   st'.cs_current_bb = st.cs_current_bb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by
    (irule window_emit_copy_run >> simp[] >> metis_tac[]) >>
  `abi_encoder_extend_sim ctx func initial
    ((mcopy d (sb MOD dimword (:256)) 0 initial)
       with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >>
     (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `(mcopy d (sb MOD dimword (:256)) 0 initial)
    with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, mem_bytes_at_def, abi_encoder_extend_sim_sim] >>
  conj_tac
  >- (irule abi_encoder_registered_effect_trans >>
      qexists_tac `mcopy d (sb MOD dimword (:256)) 0 initial` >>
      simp[abi_encoder_registered_output_copy, abi_encoder_registered_inst_idx]) >>
  metis_tac[window_copy_state_resources]
QED
