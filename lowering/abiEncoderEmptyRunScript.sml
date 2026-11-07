(* Public execution adapter for the zero-output part of the encoder. *)
Theory abiEncoderEmptyRun
Ancestors
  abiEncoderEmptyCode abiEncoderExtendSim abiEncoderVarRestore
  abiDecoderReentry abiDecoderVarExtend abiEncoderSequence abiEncoderRegisteredEffect
  exprLoweringProps emitHelperProps compileEnv venomState venomExecSemantics
  valueEncoding list finite_map pred_set

Theorem abi_encoder_empty_unpruned:
  abi_encoder_empty ei /\
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  eval_operand dst initial = SOME d /\ eval_operand src initial = SOME b /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var src ==>
  ?encoded.
    run_inst_seq (emitted_insts st st') initial = OK encoded /\
    out = Lit 0w /\ abi_encoder_empty_effect initial encoded /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op encoded = SOME w) /\
    inst_extends st st' /\ same_blocks st st' /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st')
Proof
  strip_tac >>
  `eval_operand dst (abi_decoder_prune_vars st.cs_next_var initial) = SOME d /\
   eval_operand src (abi_decoder_prune_vars st.cs_next_var initial) = SOME b` by
    metis_tac[abi_decoder_prune_eval] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)` by
    simp[abi_decoder_prune_fresh] >>
  drule_all (cj 1 abi_encoder_empty_execution) >> strip_tac >>
  rename1 `abi_encoder_empty_seq st st' _ small` >>
  fs[abi_encoder_empty_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  `abi_decoder_vars_extend initial.vs_vars
    (abi_decoder_prune_vars st.cs_next_var initial) initial` by
    simp[abi_decoder_prune_extension] >>
  drule_all abi_encoder_sequence_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars small encoded` >>
  qexists_tac `encoded` >> simp[] >> conj_tac
  >- (drule abi_decoder_vars_extend_restore >>
      gvs[abi_encoder_empty_effect_def, abi_decoder_prune_vars_def] >>
      simp[venom_state_component_equality] >> strip_tac >>
      gvs[venom_state_component_equality]) >>
  rpt strip_tac >>
  `eval_operand op (abi_decoder_prune_vars st.cs_next_var initial) = SOME w` by
    metis_tac[abi_decoder_prune_eval] >>
  `eval_operand op small = SOME w` by metis_tac[] >>
  drule_all abi_decoder_vars_extend_eval >> simp[]
QED

Theorem abi_encoder_empty_effect_resources:
  abi_encoder_empty_effect s t ==>
  (alloca_inv s ==> alloca_inv (t with vs_inst_idx := ix)) /\
  (alloca_room ctx func s ==> alloca_room ctx func (t with vs_inst_idx := ix)) /\
  abi_encoder_registered_effect ids outs s (t with vs_inst_idx := ix)
Proof
  simp_tac bool_ss [abi_encoder_empty_effect_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  simp[venomMemDefsTheory.alloca_inv_def,
    venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def,
    alloca_room_def, pending_alloca_size_def, abi_encoder_registered_effect_def]
QED

Theorem compile_abi_encode_to_buf_empty_window_run:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
  LENGTH (enc at av) = 0 /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st st' func /\
  alloca_inv initial /\ alloca_room ctx func initial /\
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
  `abi_encoder_empty ei` by metis_tac[abi_encoder_window_empty] >>
  `abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var src` by
    (Cases_on `dst` >> Cases_on `src` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >> metis_tac[]) >>
  drule_all abi_encoder_empty_unpruned >> strip_tac >>
  gvs[same_blocks_def] >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qexists_tac `actual` >>
  gvs[] >>
  `~encoded.vs_halted` by
    (fs[abi_encoder_empty_effect_def, venom_state_component_equality]) >>
  simp[eval_operand_def, mem_bytes_at_def] >>
  reverse (rpt conj_tac)
  >- (rpt strip_tac >>
      `abi_decoder_operand_live st.cs_next_var (Var x)` by
        simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          GSYM not_fresh_at_def] >>
      qpat_x_assum `!op w. _` (qspecl_then [`Var x`, `w`] mp_tac) >>
      simp[eval_operand_def, lookup_var_def]) >>
  metis_tac[abi_encoder_empty_effect_resources]
QED
