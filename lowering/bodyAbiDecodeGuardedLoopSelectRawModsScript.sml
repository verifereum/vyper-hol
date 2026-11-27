Theory bodyAbiDecodeGuardedLoopSelectRawMods
Ancestors
  fragExec[qualified,ignore_grammar] exprSimWordBuiltins[qualified,ignore_grammar]
  bodyFullAbiDecodeMemberPrefix abiDecodePtrHead abiDecodePtrBytesMember
  bodyPtrBopScalarOutcome abiDecoderGuard abiDecoderReentry
  abiDecoderArrayInitReentry abiDecoderRange emitHelperProps exprLoweringProps
  compileEnv emitHelper venomInst venomExecSemantics venomState
  words arithmetic list rich_list finite_map loweringStateRelDefs abiEncoder

(* The selector can run on a state with old temporaries. It only needs
   freshness relative to the two operands of its footprint test. *)
Theorem live_operand_update[local]:
  abi_decoder_operand_live sa.cs_next_var op /\ sa.cs_next_var <= n ==>
  eval_operand op (update_var (STRING #"%" (toString n)) w s) = eval_operand op s
Proof
  strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
  qexists_tac `sa` >> simp[] >>
  rpt strip_tac >> gvs[abi_decoder_operand_live_def,
    abi_decoder_older_vars_def, not_fresh_at_def]
QED

Theorem selector_range_raw[local]:
  emit_op ADD [src;Lit (n2w asz)] sa = (e,sm) /\
  compile_abi_decode_range_check src e hi sm = ((),sb) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var hi /\ eval_operand src s = SOME p /\
  eval_operand hi s = SOME hw /\ asz < dimword(:256) ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       w2n p + asz <= w2n hw)
Proof
  simp[compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `!n w u. sa.cs_next_var <= n ==>
    eval_operand src (update_var (STRING #"%" (toString n)) w u) =
      eval_operand src u` by (rpt strip_tac >> irule live_operand_update >> qexists_tac `sa` >> simp[]) >>
  `!n w u. sa.cs_next_var <= n ==>
    eval_operand hi (update_var (STRING #"%" (toString n)) w u) =
      eval_operand hi u` by (rpt strip_tac >> irule live_operand_update >> qexists_tac `sa` >> simp[]) >>
  `!x y w u. eval_operand (Var x) (update_var y w u) =
     if x = y then SOME w else eval_operand (Var x) u` by
    simp[eval_operand_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE, EQ_SYM_EQ] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  Cases_on `w2n p <= w2n (p+n2w asz) /\ w2n (p+n2w asz) <= w2n hw`
  >- suspend "accept" >>
  suspend "reject"
QED

Resume selector_range_raw[accept]:
  pop_assum strip_assume_tac >> disj2_tac >>
  simp[Once run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure2_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure2_def, eval_operand_update_var, bool_to_word_def] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure1_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure2_def, ASCIInumbersTheory.toString_inj, bool_to_word_def] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure1_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure2_def, ASCIInumbersTheory.toString_inj] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       eval_operand_update_var, WORD_AND_IDEM] >>
  simp[run_inst_seq_def] >>
  `w2n p + asz < dimword(:256)` by
    (spose_not_then assume_tac >>
     `dimword(:256) <= w2n p + w2n (n2w asz : bytes32)` by simp[] >>
     drule arithmeticPropsTheory.w2n_add_overflow >> simp[] >> decide_tac) >>
  gvs[w2n_add_2]
QED

Resume selector_range_raw[reject]:
  disj1_tac >>
  simp[Once run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure2_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure2_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure1_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure2_def, ASCIInumbersTheory.toString_inj] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure1_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_opcode,
       exec_pure2_def, ASCIInumbersTheory.toString_inj] >>
  Cases_on `w2n (p+n2w asz) < w2n p` >>
  Cases_on `w2n (p+n2w asz) > w2n hw` >>
  gvs[bool_to_word_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ st` >>
  `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var+5)))) st = SOME 0w` by
    simp[Abbr `st`, eval_operand_update_var] >>
  mp_tac (Q.SPECL [`Var (STRING #"%" (toString (sa.cs_next_var+5)))`,
    `sa.cs_next_id+6`, `st`] step_ASSERT_revert) >>
  simp[Once run_inst_seq_def, mk_inst_def]
QED

Finalise selector_range_raw

Theorem scalar_run_live_operand[local]:
  bop_scalar_seq (abi_decoder_older_vars next) A code B /\
  run_inst_seq code s = OK t /\ abi_decoder_operand_live next op ==>
  eval_operand op t = eval_operand op s
Proof
  strip_tac >> drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `t = _ with vs_vars := _` (once_rewrite_tac o single) >> simp[]) >>
  Cases_on `op` >> gvs[abi_decoder_operand_live_def, eval_operand_def, lookup_var_def]
QED

Theorem selector_lower_guard_live[local]:
  emit_op ADD [data;loadval] s2 = (child_src,s3) /\
  abi_decode_ge_guard child_src data s3 = ((),s4) /\
  abi_decoder_operand_live s2.cs_next_var hi ==>
  abi_decoder_operand_live s4.cs_next_var child_src /\
  abi_decoder_operand_live s4.cs_next_var hi
Proof
  simp[abi_decode_ge_guard_def,emit_op_def,emit_void_def,
       fresh_var_def,fresh_id_def,emit_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def] >> rpt strip_tac >> gvs[]
  >- (irule abi_decoder_generated_var_live >> simp[]) >>
  irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]
QED

val selector_suffix_raw =
  let val tm = ``
    emit_op ADD [data;loadval] s2 = (child_src,s3) /\
    abi_decode_ge_guard child_src data s3 = ((),s4) /\
    emit_op ADD [child_src;Lit (n2w asz)] s4 = (e,s5) /\
    compile_abi_decode_range_check child_src e hi s5 = ((),sb) /\
    emitted_insts s2 sb = emitted_insts s2 s4 ++ emitted_insts s4 sb /\
    eval_operand data t = SOME dw /\ eval_operand loadval t = SOME lw /\
    eval_operand hi t = SOME (n2w h) /\
    abi_decoder_operand_live s2.cs_next_var data /\
    abi_decoder_operand_live s2.cs_next_var loadval /\
    abi_decoder_operand_live s2.cs_next_var hi /\
    asz < dimword(:256) /\ h < dimword(:256) ==>
    (?v. run_inst_seq (emitted_insts s2 sb) t = Abort Revert_abort v) \/
    (?v q. run_inst_seq (emitted_insts s2 sb) t = OK v /\
      eval_operand child_src v = SOME (n2w q) /\ q < dimword(:256) /\
      w2n dw <= q /\ q+asz <= h)``
  in list_mk_forall (free_vars tm, tm) end;

Theorem abi_decode_loop_select_suffix_raw:
  ^selector_suffix_raw
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_decode_member_actual_run >> strip_tac
  >- (disj1_tac >> simp[run_inst_seq_append_err]) >>
  rename1 `run_inst_seq (emitted_insts s2 s4) t = OK mid` >>
  `?C. bop_scalar_seq (abi_decoder_older_vars s2.cs_next_var)
    {data;loadval;hi;Lit (n2w asz)} (emitted_insts s2 s4) C /\ child_src IN C` by
    (irule abi_decode_position_suffix_scalar >>
     conj_tac >- simp[abi_decoder_older_vars_def,not_fresh_at_def] >>
     qexistsl_tac [`Lit 1w`,`s3`,`loadval`,`data`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  `eval_operand hi mid = SOME (n2w h)` by
    (qpat_assum `abi_decoder_operand_live _ hi`
       (mp_then Any mp_tac scalar_run_live_operand) >>
     disch_then drule >> disch_then drule >> simp[]) >>
  drule_all selector_lower_guard_live >> strip_tac >>
  drule_all selector_range_raw >> strip_tac
  >- (disj1_tac >> qexists_tac `t'` >>
      qpat_assum `run_inst_seq (emitted_insts s2 s4) t = OK mid`
        (mp_then Any (qspec_then `emitted_insts s4 sb` assume_tac) run_inst_seq_append) >>
      simp[]) >>
  `?E. bop_scalar_seq (abi_decoder_older_vars s4.cs_next_var)
    {child_src;hi;Lit (n2w asz)} (emitted_insts s4 sb) E /\
    {child_src;hi;Lit (n2w asz)} SUBSET E /\ e IN E` by
    (irule abi_decode_add_range_scalar >>
     simp[abi_decoder_older_vars_def,not_fresh_at_def] >>
     qexistsl_tac [`hi`,`Lit (n2w asz)`,`s5`,`child_src`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  `eval_operand child_src t' = eval_operand child_src mid` by
    (irule scalar_run_live_operand >> rpt (goal_assum (drule_at Any))) >>
  disj2_tac >> qexistsl_tac [`t'`,`w2n (dw + lw)`] >>
  simp[] >> conj_tac >- metis_tac[run_inst_seq_append] >> gvs[]
QED
