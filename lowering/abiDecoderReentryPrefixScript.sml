(* Successful address/guard prefixes can be re-entered without requiring all
   their old output variables to be absent from the enclosing loop state. *)
Theory abiDecoderReentryPrefix
Ancestors
  abiDecoderReentry abiDecoderReentrySequence abiDecoderVarSequence abiDecoderVarExtend
  emitHelperProps exprLoweringProps compileEnv venomState arithmetic finite_map

Theorem abi_decoder_prefix_vars_extend:
  abi_decoder_vars_extend initial.vs_vars clean actual /\
  fresh_vars_wrt st' clean /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\
  (!op w. eval_operand op (abi_decoder_prune_vars next initial) = SOME w ==>
    eval_operand op clean = SOME w) ==>
  fresh_vars_wrt limit_st actual /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w)
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st clean` by
    (mp_tac (Q.SPECL [`st'`, `limit_st`, `clean`] fresh_vars_wrt_mono) >> simp[GREATER_EQ]) >>
  `!n. limit_st.cs_next_var <= n ==> STRING #"%" (toString n) NOTIN FDOM initial.vs_vars`
    by fs[fresh_vars_wrt_def, GREATER_EQ] >>
  `fresh_vars_wrt limit_st actual` by
    (drule_all abi_decoder_vars_extend_fresh >> simp[]) >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `eval_operand op (abi_decoder_prune_vars next initial) = SOME w` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `eval_operand op clean = SOME w` by metis_tac[] >>
  drule_all abi_decoder_vars_extend_eval >> simp[]
QED

Theorem abi_decoder_sequence_reentry_prefix:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) insts /\
  run_inst_seq insts (abi_decoder_prune_vars next initial) = OK clean /\
  fresh_vars_wrt st' clean /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\
  (!op w. eval_operand op (abi_decoder_prune_vars next initial) = SOME w ==>
    eval_operand op clean = SOME w) ==>
  ?actual. run_inst_seq insts initial = OK actual /\
    abi_decoder_vars_extend initial.vs_vars clean actual /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >>
  `abi_decoder_vars_extend initial.vs_vars (abi_decoder_prune_vars next initial) initial`
    by irule abi_decoder_prune_extension >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_prefix_vars_extend >> strip_tac >>
  `actual.vs_halted = initial.vs_halted` by
    (drule_all abi_decoder_sequence_halted >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
