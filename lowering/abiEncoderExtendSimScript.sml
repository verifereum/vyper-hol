(* Extension-stable continuation simulation, proved from concrete execution. *)
Theory abiEncoderExtendSim
Ancestors
  abiEncoderVarTransport abiEncoderSequence abiDecoderLoop abiDecoderVarSequence
  abiDecoderReentry exprLoweringProps venomExecSemantics list

Definition abi_encoder_extend_sim_def:
  abi_encoder_extend_sim ctx fn s u <=>
    abi_decode_sim ctx fn s u /\
    (!extras t. abi_decoder_vars_extend extras s t ==>
      ?v. abi_decoder_vars_extend extras u v /\ abi_decode_sim ctx fn t v)
End

Theorem abi_encoder_extend_sim_sim:
  abi_encoder_extend_sim ctx fn s u ==> abi_decode_sim ctx fn s u
Proof
  simp[abi_encoder_extend_sim_def]
QED

Theorem abi_encoder_extend_sim_refl:
  abi_encoder_extend_sim ctx fn s s
Proof
  simp[abi_encoder_extend_sim_def, abi_decode_sim_refl] >>
  rpt strip_tac >> qexists_tac `t` >> simp[abi_decode_sim_refl]
QED

Theorem abi_encoder_extend_sim_trans:
  abi_encoder_extend_sim ctx fn s t /\ abi_encoder_extend_sim ctx fn t u ==>
  abi_encoder_extend_sim ctx fn s u
Proof
  rw[abi_encoder_extend_sim_def]
  >- metis_tac[abi_decode_sim_trans] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem abi_encoder_sequence_extend:
  !insts extras s t u.
  EVERY (\i. i.inst_opcode <> INVOKE) insts /\
  abi_decoder_vars_extend extras s t /\ run_inst_seq insts s = OK u ==>
  ?v. run_inst_seq insts t = OK v /\ abi_decoder_vars_extend extras u v
Proof
  Induct >- (simp[run_inst_seq_def] >> metis_tac[]) >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp_tac bool_ss [EVERY_DEF, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst s` >> gvs[] >>
  drule_all abi_encoder_step_extend >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `abi_decoder_vars_extend extras u reached` >>
  qexists_tac `reached` >> simp[run_inst_seq_def]
QED

Theorem abi_encoder_run_sequence_extend_sim:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  fn_has_code st st' func /\ run_inst_seq (emitted_insts st st') initial = OK encoded /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial
    (encoded with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_extend_sim_def] >> conj_tac
  >- (drule_all abi_encoder_run_sequence_reach >> simp[]) >>
  rpt strip_tac >>
  drule abi_encoder_vars_extend_control >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  drule_all abi_encoder_sequence_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend extras encoded extended` >>
  qexists_tac `extended with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  conj_tac
  >- (irule abi_encoder_vars_extend_idx >> simp[]) >>
  mp_tac (Q.INST [`initial` |-> `t`, `encoded` |-> `extended`]
    abi_encoder_run_sequence_reach) >>
  (impl_tac >- gvs[]) >> simp[]
QED
