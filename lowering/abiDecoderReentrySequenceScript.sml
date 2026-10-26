(* Lift existing fresh-state sequence proofs to repeated execution. The public
   postcondition protects live operands and freshness at the enclosing bound. *)
Theory abiDecoderReentrySequence
Ancestors
  abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend abiDecoderTypedContract
  abiDecoderFrame abiDecoderContract emitHelperProps exprLoweringProps
  compileEnv valueEncoding venomState venomExecProps arithmetic finite_map

Theorem abi_decoder_post_vars_extend:
  abi_decoder_post tv v st' d sz b cap (abi_decoder_prune_vars next initial) clean /\
  abi_decoder_vars_extend initial.vs_vars clean actual /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w) /\
  abi_decode_footprint_frame [(d,sz);(b,cap)] initial actual
Proof
  strip_tac >>
  qpat_assum `abi_decoder_post _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_post_def]) >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `fresh_vars_wrt limit_st clean` by
    (mp_tac (Q.SPECL [`st'`, `limit_st`, `clean`] fresh_vars_wrt_mono) >> simp[GREATER_EQ]) >>
  `!n. limit_st.cs_next_var <= n ==> STRING #"%" (toString n) NOTIN FDOM initial.vs_vars`
    by fs[fresh_vars_wrt_def, GREATER_EQ] >>
  `fresh_vars_wrt limit_st actual` by
    (drule_all abi_decoder_vars_extend_fresh >> simp[]) >>
  `abi_decode_footprint_frame [(d,sz);(b,cap)] initial actual` by
    fs[abi_decode_footprint_frame_def, abi_decoder_prune_vars_def] >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `eval_operand op (abi_decoder_prune_vars next initial) = SOME w` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `eval_operand op clean = SOME w` by metis_tac[] >>
  drule_all abi_decoder_vars_extend_eval >> simp[]
QED

Theorem abi_decoder_sequence_halted:
  run_inst_seq insts s = OK t ==> t.vs_halted = s.vs_halted
Proof
  strip_tac >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_halted` run_inst_seq_preserves_field)) >>
  qexists_tac `insts` >> simp[] >> rpt strip_tac >>
  drule_all step_inst_base_OK_preserves_halted >> simp[]
QED

Theorem abi_decoder_reentry_frame:
  abi_decode_frame d sz (abi_decoder_prune_vars next initial) clean /\
  abi_decoder_vars_extend initial.vs_vars clean actual ==>
  abi_decode_frame d sz initial actual
Proof
  strip_tac >> drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  fs[abi_decode_frame_def, abi_decoder_prune_vars_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_sequence_reentry:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) insts /\
  run_inst_seq insts (abi_decoder_prune_vars next initial) = OK clean /\
  abi_decoder_post tv v st' d sz b cap (abi_decoder_prune_vars next initial) clean /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq insts initial = OK actual /\
    abi_decoder_vars_extend initial.vs_vars clean actual /\
    val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    abi_decode_footprint_frame [(d,sz);(b,cap)] initial actual /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >>
  `abi_decoder_vars_extend initial.vs_vars (abi_decoder_prune_vars next initial) initial`
    by irule abi_decoder_prune_extension >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_post_vars_extend >> strip_tac >>
  `actual.vs_halted = initial.vs_halted` by
    (drule_all abi_decoder_sequence_halted >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_REENTRY_SEQUENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder re-entry sequence not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderReentrySequence");
