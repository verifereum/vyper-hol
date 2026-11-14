(* Concrete nested INVOKE closure, consuming the actual returned callee run. *)
Theory lowerDloadReturnInvoke
Ancestors
  lowerDloadReturnInvokePush lowerDloadReturnInvokePop lowerDloadReturnAlignment
  lowerDloadEnvelopeControl lowerDloadSafetyLocations lowerDloadReturnInterior
  lowerDloadSafetyKernel lowerDloadSafetyRelation
  lowerDloadSafetyRunInduction venomExecSemantics venomInst list
Libs
  lowerDloadReturnPackageLib

Theorem ld_return_invoke_S_core[local]:
  ti.inst_opcode = INVOKE /\ decode_invoke ti = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\ setup_callee calleeT argsT t = SOME ct /\
  run_blocks fuel ctx calleeT ct = IntRet rt u /\
  ^ld_probe_R (\lo C C' vs0 Sigma names fn fn'.
      ^ld_covered_ambient_static lo C C' vs0 Sigma names fn fn' /\ Q vs0) ^ld_probe_point ^ld_probe_terminal
    fuel ctx calleeT ct (IntRet rt u) /\
  bind_outputs ti.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state t u)) = SOME q ==>
  ^ld_probe_S (\lo C C' vs0 Sigma names fn fn'.
      ^ld_covered_ambient_static lo C C' vs0 Sigma names fn fn' /\ Q vs0) ^ld_probe_point ^ld_probe_terminal
    fuel ctx ti t (OK q)
Proof
  qabbrev_tac `Ambient = (\lo C C' vs0 Sigma names fn fn'.
      ^ld_covered_ambient_static lo C C' vs0 Sigma names fn fn' /\ Q vs0)` >>
  qabbrev_tac `Point = ^ld_probe_point` >>
  qabbrev_tac `Terminal = ^ld_probe_terminal` >>
  strip_tac >> simp[NoAsms] >> rpt gen_tac >> strip_tac >>
  simp[is_terminator_def] >> gen_tac >> disch_tac >>
  qunabbrev_tac `Ambient` >> qunabbrev_tac `Point` >>
  `^ld_covered_ambient_static lo C ctx vs0 Sigma names fn fn'` by
    (CONV_TAC (DEPTH_CONV BETA_CONV) >>
     first_assum (ACCEPT_TAC o CONJUNCT1 o BETA_RULE)) >>
  `Q vs0` by (first_assum (ACCEPT_TAC o CONJUNCT2 o BETA_RULE)) >>
  drule_all ld_point_alignment_static >> strip_tac >>
  `ti = EL h X` by metis_tac[optionTheory.SOME_11] >>
  `o1_ctx_shape C` by fs[] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (Cases_on `inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES`
     >- (`~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
           fs[is_terminator_def] >>
         drule_all ld_envelope_nonterminal >> simp[EVERY_EL] >>
         disch_then (qspec_then `h` mp_tac) >> gvs[]) >> fs[]) >>
  `X = [inst]` by (drule_all ld_envelope_ordinary >> simp[]) >>
  `h = 0` by fs[] >>
  `ti = inst /\ t0 = t` by fs[ld_prefix_zero] >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t0 = t` SUBST_ALL_TAC >>
  Cases_on `frames` >- fs[ld_sync_def] >>
  rename1 `ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::tail) N` >>
  drule_all ld_invoke_guarded_push_static >> strip_tac >>
  qabbrev_tac `Ambient = (\lo C C' vs0 Sigma names fn fn'.
      ^ld_covered_ambient_static lo C C' vs0 Sigma names fn fn' /\ Q vs0)` >>
  qabbrev_tac `Point = ^ld_probe_point` >>
  qabbrev_tac `Entry = ^ld_probe_entry` >>
  qpat_x_assum `_ Ambient Point Terminal fuel ctx calleeT ct (IntRet rt u)` mp_tac >>
  simp[NoAsms] >> disch_tac >>
  first_x_assum (drule_at (Pat `Entry _ _ _ _`)) >>
  (impl_tac >-
    (qunabbrev_tac `Ambient` >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
     conj_tac >- first_assum (ACCEPT_TAC o BETA_RULE) >>
     first_assum ACCEPT_TAC)) >> disch_tac >>
  qunabbrev_tac `Ambient` >> qunabbrev_tac `Point` >>
  qunabbrev_tac `Terminal` >>
  `^ld_probe_guard ctx j bb (q with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qpat_assum `(?u. run_block_non_phis j ctx bb _ = OK u) \/ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  qpat_x_assum `X = [inst]` SUBST_ALL_TAC >>
  qpat_x_assum `fn' = ld_image (HD (f::tail))` (assume_tac o SRULE []) >>
  qpat_x_assum `ld_envelope (HD (f::tail)).lf_supply fn s s.vs_inst_idx X p`
    (assume_tac o SRULE []) >>
  drule_all ld_invoke_guarded_pop_static >> simp[NoAsms]
QED


Theorem ld_return_invoke_S_static:
  ti.inst_opcode = INVOKE /\ decode_invoke ti = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\ setup_callee calleeT argsT t = SOME ct /\
  run_blocks fuel ctx calleeT ct = IntRet rt u /\
  ^ld_probe_R ^ld_covered_ambient_static ^ld_probe_point ^ld_probe_terminal
    fuel ctx calleeT ct (IntRet rt u) /\
  bind_outputs ti.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state t u)) = SOME q ==>
  ^ld_probe_S ^ld_covered_ambient_static ^ld_probe_point ^ld_probe_terminal
    fuel ctx ti t (OK q)
Proof
  mp_tac (Q.INST [`Q` |-> `\vs0. T`] ld_return_invoke_S_core) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rewrite_tac [AND_CLAUSES]
QED

Theorem ld_return_invoke_S:
  ti.inst_opcode = INVOKE /\ decode_invoke ti = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\ setup_callee calleeT argsT t = SOME ct /\
  run_blocks fuel ctx calleeT ct = IntRet rt u /\
  ^ld_probe_R ^ld_covered_ambient ^ld_probe_point ^ld_probe_terminal
    fuel ctx calleeT ct (IntRet rt u) /\
  bind_outputs ti.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state t u)) = SOME q ==>
  ^ld_probe_S ^ld_covered_ambient ^ld_probe_point ^ld_probe_terminal
    fuel ctx ti t (OK q)
Proof
  `(\lo C C' vs0 Sigma names fn fn'.
      ^ld_covered_ambient_static lo C C' vs0 Sigma names fn fn' /\
      o1_run_state_ok vs0) = ^ld_covered_ambient` by
    (simp[FUN_EQ_THM, o1PassContractTheory.o1_run_state_ok_def, SF CONJ_ss] >>
     rpt gen_tac >> eq_tac >> strip_tac >> asm_rewrite_tac []) >>
  mp_tac (Q.INST [`Q` |-> `o1_run_state_ok`] ld_return_invoke_S_core) >>
  asm_rewrite_tac []
QED

val _ = if null (hyp ld_return_invoke_S_static) andalso
           null (hyp ld_return_invoke_S) then ()
        else raise Fail "ld_return_invoke_S has kernel hypotheses";
