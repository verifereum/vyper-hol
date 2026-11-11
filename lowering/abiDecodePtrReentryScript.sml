(* Successful straight-line pointer replay from an extended runtime state. *)
Theory abiDecodePtrReentry
Ancestors
  abiDecodePtrReentryStep abiDecodePtrReentryGhost abiDecodePtrReentryObservations
  abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend
  abiEncoderVarTransport fragGasSeqPtr fragExec venomExecSemantics
  bodyPtrDefs compileEnv exprLoweringProps instIdxIndep venomState venomInst list

Theorem abi_decode_ptr_sequence_reentry:
  !insts extras s t u G tn G' tn'.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) insts /\
  abi_decoder_vars_extend extras s t /\ run_inst_seq insts s = OK u /\
  inst_seq_ptr D lo ctx fn PG G tn insts s G' tn' ==>
  inst_seq_ptr D lo ctx fn PG G tn insts t G' tn'
Proof
  Induct >- simp[inst_seq_ptr_def] >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp_tac bool_ss [EVERY_DEF, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst s` >> gvs[] >>
  rename1 `step_inst_base inst s = OK mid` >>
  `abi_decoder_inputs_defined inst s` by
    metis_tac[abi_decoder_step_inputs_defined] >>
  drule_all abi_decoder_step_vars_extend >> strip_tac >>
  rename1 `step_inst_base inst t = OK actual` >>
  fs[inst_seq_ptr_def] >>
  `ptr_inst_ok D lo 0 ctx fn G tn inst t` by
    metis_tac[abi_decode_ptr_reentry_inst] >> simp[] >>
  `step_prov PG G inst mid = step_prov PG G inst actual` by
    metis_tac[abi_decode_ptr_reentry_prov] >>
  `step_taint inst s mid tn = step_taint inst t actual tn` by
    metis_tac[abi_decode_ptr_reentry_taint] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[abi_decode_ptr_reentry_frame] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) insts` by
    fs[EVERY_MEM] >>
  `run_inst_seq insts (mid with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `abi_decoder_vars_extend extras
    (mid with vs_inst_idx := SUC s.vs_inst_idx)
    (actual with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[abi_encoder_vars_extend_idx] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem abi_decode_ptr_sequence_extend:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) insts /\
  abi_decoder_vars_extend extras s t /\ run_inst_seq insts s = OK u /\
  inst_seq_ptr D lo ctx fn PG G tn insts s G' tn' ==>
  ?v. run_inst_seq insts t = OK v /\ abi_decoder_vars_extend extras u v /\
    inst_seq_ptr D lo ctx fn PG G tn insts t G' tn'
Proof
  strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) insts` by
    fs[EVERY_MEM] >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[abi_decode_ptr_sequence_reentry]
QED

(* Internal freshness and ghost facts are obtained by pruning, not demanded
   of the actual entry state. The raw and checked runs share an endpoint. *)
Theorem abi_decode_ptr_pruned_entry:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) insts /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv st /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p) /\
  run_inst_seq insts (abi_decoder_prune_vars st.cs_next_var s) = OK u /\
  inst_seq_ptr D lo ctx fn PG G tn insts
    (abi_decoder_prune_vars st.cs_next_var s) G' tn' ==>
  fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s) /\
  ghost_inv d cenv cx es G tn (abi_decoder_prune_vars st.cs_next_var s) /\
  ?v. run_inst_seq insts s = OK v /\
    abi_decoder_vars_extend s.vs_vars u v /\
    inst_seq_ptr D lo ctx fn PG G tn insts s G' tn'
Proof
  strip_tac >> simp[abi_decoder_prune_fresh] >>
  conj_tac >- metis_tac[abi_decode_ptr_prune_ghost_reserved] >>
  irule abi_decode_ptr_sequence_extend >> simp[] >>
  qexists_tac `abi_decoder_prune_vars st.cs_next_var s` >>
  simp[abi_decoder_prune_extension] >> metis_tac[]
QED
