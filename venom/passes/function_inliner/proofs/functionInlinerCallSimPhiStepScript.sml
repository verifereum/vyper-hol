(*
 * Function Inliner — PHI-label substitution and prev_bb independence
 *
 * Proves that PHI instructions with substituted labels produce equivalent
 * results, and that non-PHI instructions are independent of prev_bb.
 * Key result: run_block_phi_subst_result_equiv.
 *)

Theory functionInlinerCallSimPhiStep
Ancestors
  functionInlinerPrevBBMap functionInlinerCallSimHelpers
  functionInlinerInline functionInlinerDefs functionInlinerSim
  functionInlinerFresh functionInlinerCloneSim functionInlinerStepClone
  functionInlinerCalleeSim functionInlinerCloneNp functionInlinerCloneExec
  functionInlinerBlockSplit
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  execEquivProps cfgTransform cfgTransformProps venomExecProps

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory

open functionInlinerPrevBBMapTheory functionInlinerCallSimHelpersTheory
     functionInlinerDefsTheory functionInlinerInlineTheory
     functionInlinerCloneSimTheory functionInlinerSimTheory
     functionInlinerStepCloneTheory functionInlinerFreshTheory
     functionInlinerRenumberTheory functionInlinerCalleeSimTheory
     functionInlinerCloneNpTheory
     functionInlinerCloneExecTheory functionInlinerBlockSplitTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     execEquivPropsTheory cfgTransformTheory cfgTransformPropsTheory
     venomExecPropsTheory venomInstPropsTheory


(* prev_bb helpers for INVOKE case *)
Triviality eval_operands_prev_bb[local]:
  !ops s p. eval_operands ops (s with vs_prev_bb := p) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def] >>
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Triviality setup_callee_prev_bb[local]:
  !callee_fn args s p. setup_callee callee_fn args (s with vs_prev_bb := p) =
    setup_callee callee_fn args s
Proof
  simp[setup_callee_def]
QED

Triviality merge_callee_state_prev_bb[local]:
  !caller callee p. merge_callee_state (caller with vs_prev_bb := p) callee =
    (merge_callee_state caller callee) with vs_prev_bb := p
Proof
  simp[merge_callee_state_def]
QED

Triviality foldl_update_var_prev_bb[local]:
  !pairs (s:venom_state) p.
    FOLDL (\s' (out,v). update_var out v s') (s with vs_prev_bb := p) pairs =
    (FOLDL (\s' (out,v). update_var out v s') s pairs) with vs_prev_bb := p
Proof
  Induct >- simp[] >>
  Cases >> rw[] >>
  `update_var q r (s with vs_prev_bb := p) = (update_var q r s) with vs_prev_bb := p` by
    simp[update_var_def] >>
  simp[]
QED

Triviality bind_outputs_prev_bb[local]:
  !outs vals s p. bind_outputs outs vals (s with vs_prev_bb := p) =
    OPTION_MAP (\st. st with vs_prev_bb := p) (bind_outputs outs vals s)
Proof
  simp[bind_outputs_def] >> rpt gen_tac >>
  Cases_on `LENGTH outs = LENGTH vals` >> simp[foldl_update_var_prev_bb]
QED

Triviality step_inst_invoke_prev_bb[local]:
  !fuel ctx inst (s:venom_state) p.
    inst.inst_opcode = INVOKE ==>
    step_inst fuel ctx inst (s with vs_prev_bb := p) =
    case step_inst fuel ctx inst s of
      OK r => OK (r with vs_prev_bb := p)
    | x => x
Proof
  rw[step_inst_def] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `SOME decoded` >> PairCases_on `decoded` >> simp[] >>
  Cases_on `lookup_function decoded0 ctx.ctx_functions` >> simp[] >>
  rename1 `SOME callee_fn` >>
  simp[eval_operands_prev_bb, setup_callee_prev_bb] >>
  Cases_on `eval_operands decoded1 s` >> simp[] >>
  rename1 `SOME args` >>
  Cases_on `setup_callee callee_fn args s` >> simp[] >>
  rename1 `SOME callee_s` >>
  Cases_on `run_function fuel ctx callee_fn callee_s` >> simp[] >>
  simp[merge_callee_state_prev_bb, bind_outputs_def] >>
  Cases_on `LENGTH inst.inst_outputs = LENGTH l` >> simp[] >>
  simp[foldl_update_var_prev_bb, venom_state_component_equality]
QED

(* ================================================================
   Section 4: Block-level PHI-label substitution equivalence
   ================================================================ *)

(* Proxy-state lemma: given execution_equiv (which allows different prev_bb),
   we can form a proxy state sbp that is state_equiv with sa (matching prev_bb)
   and recovers sb when prev_bb is restored. This bridges the gap between
   execution_equiv (no prev_bb) and state_equiv (requires prev_bb match). *)
Triviality execution_equiv_proxy_state:
  !vars sa sb.
    execution_equiv vars sa sb /\
    sa.vs_current_bb = sb.vs_current_bb /\
    sa.vs_inst_idx = sb.vs_inst_idx ==>
    ?sbp. state_equiv vars sa sbp /\
          sbp with vs_prev_bb := sb.vs_prev_bb = sb
Proof
  rpt strip_tac >>
  qexists_tac `sb with vs_prev_bb := sa.vs_prev_bb` >>
  gvs[state_equiv_def, execution_equiv_def, lookup_var_def,
      venom_state_component_equality]
QED

(* Helper: for non-PHI instructions, step_inst on execution_equiv states
   (with same current_bb/inst_idx but possibly different prev_bb)
   gives execution_equiv results.
   Split into two parts: same-shape guarantee and OK-case properties.
   INVOKE is included (same ctx). *)

(* Part 1: Same-shape — if one side returns OK, so does the other.
   Also covers all other constructor pairs. *)
(* exec_result_constructor: classify exec_result by its constructor.
   Used to state "same constructor" without a 25-arm case expression. *)
Definition exec_result_tag_def:
  exec_result_tag (OK _) = (0:num) /\
  exec_result_tag (Halt _) = 1 /\
  exec_result_tag (Abort _ _) = 2 /\
  exec_result_tag (IntRet _ _) = 3 /\
  exec_result_tag (Error _) = 4
End

(* prev_bb commutation preserves the result constructor tag.
   For ANY non-PHI instruction, changing prev_bb doesn't change the constructor. *)
Triviality step_inst_prev_bb_same_tag:
  !fuel ctx inst s p.
    inst.inst_opcode <> PHI ==>
    exec_result_tag (step_inst fuel ctx inst (s with vs_prev_bb := p)) =
    exec_result_tag (step_inst fuel ctx inst s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `p`]
      step_inst_invoke_prev_bb) >>
    ASM_REWRITE_TAC[] >> DISCH_TAC >>
    Cases_on `step_inst fuel ctx inst s` >>
    gvs[exec_result_tag_def]
  ) >>
  `step_inst fuel ctx inst (s with vs_prev_bb := p) =
   step_inst_base inst (s with vs_prev_bb := p)` by
    simp[step_inst_non_invoke] >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    simp[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
            inst.inst_opcode = DJMP` >- (
    `step_inst_base inst (s with vs_prev_bb := p) = step_inst_base inst s` by
      metis_tac[step_inst_base_prev_bb_jmp] >>
    gvs[]
  ) >>
  mp_tac (Q.SPECL [`inst`, `s`, `p`] step_inst_base_prev_bb_map) >>
  impl_tac >- gvs[] >> DISCH_TAC >>
  Cases_on `step_inst_base inst s` >>
  gvs[exec_result_map_state_def, exec_result_tag_def]
QED

(* Same-constructor helper: step_inst on execution_equiv states always
   produces results with the same constructor (OK/Halt/Abort/IntRet/Error). *)
Theorem step_inst_non_phi_same_tag:
  !fuel ctx inst vars sa sb.
    execution_equiv vars sa sb /\
    sa.vs_current_bb = sb.vs_current_bb /\
    sa.vs_inst_idx = sb.vs_inst_idx /\
    inst.inst_opcode <> PHI /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    exec_result_tag (step_inst fuel ctx inst sa) =
    exec_result_tag (step_inst fuel ctx inst sb)
Proof
  rpt strip_tac >>
  drule_all execution_equiv_proxy_state >> strip_tac >>
  `result_equiv vars (step_inst fuel ctx inst sa)
                     (step_inst fuel ctx inst sbp)` by
    metis_tac[step_inst_same_ctx_result_equiv] >>
  `exec_result_tag (step_inst fuel ctx inst sa) =
   exec_result_tag (step_inst fuel ctx inst sbp)` by (
    Cases_on `step_inst fuel ctx inst sa` >>
    Cases_on `step_inst fuel ctx inst sbp` >>
    gvs[result_equiv_def, exec_result_tag_def]
  ) >>
  `exec_result_tag (step_inst fuel ctx inst sbp) =
   exec_result_tag (step_inst fuel ctx inst sb)` by (
    `sb = sbp with vs_prev_bb := sb.vs_prev_bb` by gvs[] >>
    pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
    simp[step_inst_prev_bb_same_tag]
  ) >>
  simp[]
QED

(* Record identity update: s with prev_bb := s.prev_bb = s *)
Triviality venom_state_prev_bb_id[simp]:
  !s. s with vs_prev_bb := s.vs_prev_bb = (s:venom_state)
Proof
  simp[venom_state_component_equality]
QED

(* step_inst_base preserves prev_bb for non-PHI/INVOKE/JMP/JNZ/DJMP *)
Triviality step_inst_base_preserves_prev_bb:
  !inst (s:venom_state) v.
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\
    step_inst_base inst s = OK v ==>
    v.vs_prev_bb = s.vs_prev_bb
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`inst`, `s`, `s.vs_prev_bb`] step_inst_base_prev_bb_map) >>
  simp[exec_result_map_state_def, venom_state_component_equality]
QED

(* If step_inst_base returns OK and isn't JMP/JNZ/DJMP, then not a terminator.
   All other terminators (RET/RETURN/REVERT/STOP/SINK/INVALID/SELFDESTRUCT)
   return non-OK results. *)
Triviality step_inst_base_ok_not_terminator:
  !inst (s:venom_state) v.
    step_inst_base inst s = OK v /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP ==>
    ~is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  (* 7 remaining: RET, RETURN, REVERT, STOP, SINK, INVALID, SELFDESTRUCT *)
  gvs[step_inst_base_def, halt_state_def, revert_state_def,
      set_returndata_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* ================================================================
   Block-level prev_bb irrelevance for no-PHI blocks (OK case)
   ================================================================ *)

(* Step-level helper: for non-PHI OK-terminator instructions,
   the result is completely prev_bb independent (must be JMP/JNZ/DJMP). *)
Theorem step_inst_ok_term_prev_bb_same:
  !fuel ctx inst s s' p.
    inst.inst_opcode <> PHI /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    step_inst fuel ctx inst (s with vs_prev_bb := p) = OK s'
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (
    Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  fs[step_inst_non_invoke] >>
  `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
   inst.inst_opcode = DJMP` by (
    CCONTR_TAC >> fs[] >>
    imp_res_tac step_inst_base_ok_not_terminator >> fs[]) >>
  metis_tac[step_inst_base_prev_bb_jmp]
QED

(* Step-level helper: for non-PHI OK-non-terminator instructions,
   prev_bb maps through — the result is OK with prev_bb adjusted. *)
Theorem step_inst_ok_nonterm_prev_bb_map:
  !fuel ctx inst s s' p.
    inst.inst_opcode <> PHI /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    ?q. step_inst fuel ctx inst (s with vs_prev_bb := p) =
        OK (s' with vs_prev_bb := q)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `p`]
      step_inst_invoke_prev_bb) >>
    ASM_REWRITE_TAC[] >> simp[] >> metis_tac[]
  ) >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    metis_tac[step_inst_non_invoke] >>
  `inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
   inst.inst_opcode <> DJMP` by (
    Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  mp_tac (Q.SPECL [`inst`, `s`, `p`] step_inst_base_prev_bb_map) >>
  (impl_tac >- fs[]) >> strip_tac >>
  gvs[step_inst_non_invoke, exec_result_map_state_def] >>
  qexists_tac `p` >> simp[]
QED

(* Helper: for non-PHI, prev_bb change preserves result_equiv for non-OK results.
   INVOKE: non-OK results identical. JMP/JNZ/DJMP: results identical.
   Other: prev_bb maps through states, but execution_equiv absorbs prev_bb updates.
   Moved here (before run_block_no_phi_prev_bb_lift) so the lift proof can use it. *)
Triviality step_inst_prev_bb_result_equiv_non_ok:
  !fuel ctx inst vars (s:venom_state) p.
    inst.inst_opcode <> PHI /\
    (~?r. step_inst fuel ctx inst s = OK r) ==>
    result_equiv vars (step_inst fuel ctx inst s)
                      (step_inst fuel ctx inst (s with vs_prev_bb := p))
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `p`]
      step_inst_invoke_prev_bb) >>
    ASM_REWRITE_TAC[] >> DISCH_TAC >>
    Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
    simp[result_equiv_refl]
  ) >>
  gvs[step_inst_non_invoke] >>
  (Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
            inst.inst_opcode = DJMP` >- (
    `step_inst_base inst (s with vs_prev_bb := p) = step_inst_base inst s` by
      metis_tac[step_inst_base_prev_bb_jmp] >>
    simp[result_equiv_refl]
  )) >>
  mp_tac (Q.SPECL [`inst`, `s`, `p`] step_inst_base_prev_bb_map) >>
  (impl_tac >- gvs[]) >> DISCH_TAC >>
  Cases_on `step_inst_base inst s` >>
  gvs[exec_result_map_state_def, result_equiv_def,
      execution_equiv_def, lookup_var_def]
QED

(* shared_globals_np is trivially reflexive up to prev_bb.
   Placed here so run_block_no_phi_prev_bb_lift can use it as [simp]. *)
Triviality shared_globals_np_prev_bb[simp]:
  !s p. shared_globals_np s (s with vs_prev_bb := p)
Proof
  simp[shared_globals_np_def]
QED

Triviality shared_globals_np_refl[simp]:
  !s. shared_globals_np s s
Proof
  simp[shared_globals_np_def]
QED

(* Unified prev_bb independence for no-PHI blocks.
   Subsumes both tag-preservation and OK-equality:
   - OK: results are identical (s1 = s2)
   - Halt/Abort/IntRet: shared_globals_np on payloads
   - Error: trivially true
   Why: non-PHI instructions don't read prev_bb. Along any execution path,
   intermediate states differ only in prev_bb, so terminal results are
   identical (for OK) or differ only in prev_bb (for non-OK). *)
Theorem run_block_no_phi_prev_bb_lift:
  !fuel ctx bb s p.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    bb_well_formed bb ==>
    lift_result (\s1 s2. s1 = s2) shared_globals_np
      (run_block fuel ctx bb s)
      (run_block fuel ctx bb (s with vs_prev_bb := p))
Proof
  gen_tac >> gen_tac >> gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [run_block_def]))) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >>
  simp[lift_result_def] >>
  rename1 `SOME inst` >>
  `inst.inst_opcode <> PHI` by (
    qpat_x_assum `EVERY _ _` mp_tac >>
    qpat_x_assum `get_instruction _ _ = _` mp_tac >>
    rw[get_instruction_def, AllCaseEqs()] >> fs[EVERY_EL]
  ) >>
  Cases_on `step_inst fuel ctx inst s`
  >- ((* step_inst = OK *)
    rename1 `step_inst _ _ _ s = OK s_step` >>
    Cases_on `is_terminator inst.inst_opcode`
    >- ((* Terminator + OK: result identical *)
      imp_res_tac step_inst_ok_term_prev_bb_same >>
      first_x_assum (qspec_then `p` assume_tac) >> simp[lift_result_def] >>
      Cases_on `s_step.vs_halted` >> simp[lift_result_def])
    >- ((* Not terminator: recurse with IH *)
      imp_res_tac step_inst_ok_nonterm_prev_bb_map >>
      qpat_x_assum `!p. ?q. _` (qspec_then `p` strip_assume_tac) >>
      simp[] >>
      qpat_x_assum `!m. m < v ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
      impl_tac >- (fs[get_instruction_def, AllCaseEqs()] >> simp[]) >>
      disch_then (qspecl_then [`bb`,
        `s_step with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[] >> disch_then (qspec_then `q` mp_tac) >> simp[]))
  >> ((* step_inst = non-OK (Halt/Abort/IntRet/Error) *)
    `~(?r. step_inst fuel ctx inst s = OK r)` by
      (strip_tac >> gvs[]) >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `{}`, `s`, `p`]
      step_inst_prev_bb_result_equiv_non_ok) >>
    simp[] >> strip_tac >>
    qpat_x_assum `result_equiv _ _ _` mp_tac >>
    simp[result_equiv_is_lift_result] >>
    Cases_on `step_inst fuel ctx inst (s with vs_prev_bb := p)` >>
    simp[lift_result_def, execution_equiv_def, shared_globals_np_def])
QED

(* Corollary: OK result is identical (derived from lift) *)
Theorem run_block_no_phi_prev_bb_ok:
  !fuel ctx bb s s_ok p.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    bb_well_formed bb /\
    run_block fuel ctx bb s = OK s_ok ==>
    run_block fuel ctx bb (s with vs_prev_bb := p) = OK s_ok
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `p`]
    run_block_no_phi_prev_bb_lift) >>
  simp[] >>
  Cases_on `run_block fuel ctx bb (s with vs_prev_bb := p)` >>
  simp[lift_result_def]
QED

(* Lift to run_function: if the entry block has no PHI and run_block
   returns OK, then run_function with adjusted prev_bb equals
   run_function with original prev_bb. *)
Theorem run_function_no_phi_entry_prev_bb:
  !fuel ctx fn s p bb s_ok.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    bb_well_formed bb /\
    run_block fuel ctx bb s = OK s_ok ==>
    run_function (SUC fuel) ctx fn (s with vs_prev_bb := p) =
    run_function (SUC fuel) ctx fn s
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  imp_res_tac run_block_no_phi_prev_bb_ok >>
  first_x_assum (qspec_then `p` assume_tac) >>
  simp[] >>
  Cases_on `s_ok.vs_halted` >> simp[]
QED

(* execution_equiv ignores vs_prev_bb, vs_current_bb, vs_inst_idx.
   Changing any of these on either side preserves execution_equiv. *)
Triviality execution_equiv_update_prev_bb[simp]:
  !vars s1 s2 p.
    execution_equiv vars s1 (s2 with vs_prev_bb := p) <=>
    execution_equiv vars s1 s2
Proof
  simp[execution_equiv_def, lookup_var_def]
QED

Triviality execution_equiv_update_prev_bb_l[simp]:
  !vars s1 s2 p.
    execution_equiv vars (s1 with vs_prev_bb := p) s2 <=>
    execution_equiv vars s1 s2
Proof
  simp[execution_equiv_def, lookup_var_def]
QED

Theorem execution_equiv_update_inst_idx:
  !vars s1 s2 i j.
    execution_equiv vars (s1 with vs_inst_idx := i)
                         (s2 with vs_inst_idx := j) <=>
    execution_equiv vars s1 s2
Proof
  simp[execution_equiv_def, lookup_var_def]
QED

Triviality execution_equiv_update_current_bb:
  !vars s1 s2 b1 b2.
    execution_equiv vars (s1 with vs_current_bb := b1)
                         (s2 with vs_current_bb := b2) <=>
    execution_equiv vars s1 s2
Proof
  simp[execution_equiv_def, lookup_var_def]
QED

(* Direct prev_bb preservation for non-terminator step_inst.
   Derived from commutation lemmas: s with prev_bb := s.prev_bb = s,
   so commutation gives step(s) = step(s) with prev_bb adjustment = identity. *)
Triviality step_inst_non_term_preserves_prev_bb:
  !fuel ctx inst s r.
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK r ==>
    r.vs_prev_bb = s.vs_prev_bb
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- (
    (* INVOKE: step_inst_invoke_prev_bb gives
       step(s with prev_bb := p) = case step(s) of OK r => OK (r with prev_bb := p)
       Specializing p = s.vs_prev_bb: step(s) = case step(s) of OK r => OK (r with prev_bb := s.prev_bb)
       Since step(s) = OK r: OK r = OK (r with prev_bb := s.prev_bb) *)
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `s.vs_prev_bb`]
      step_inst_invoke_prev_bb) >>
    ASM_REWRITE_TAC[] >> simp[] >>
    gvs[venom_state_component_equality]
  ) >>
  (* Non-INVOKE: step_inst = step_inst_base *)
  gvs[step_inst_non_invoke] >>
  (Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
            inst.inst_opcode = DJMP` >-
    gvs[is_terminator_def]) >>
  Cases_on `inst.inst_opcode = PHI` >- (
    (* PHI: update_var only touches vs_vars *)
    gvs[step_inst_base_def] >>
    BasicProvers.EVERY_CASE_TAC >> gvs[update_var_def]
  ) >>
  (* Other non-PHI/non-INVOKE/non-JMP: step_inst_base_prev_bb_map *)
  mp_tac (Q.SPECL [`inst`, `s`, `s.vs_prev_bb`] step_inst_base_prev_bb_map) >>
  (impl_tac >- gvs[]) >>
  simp[] >> gvs[exec_result_map_state_def, venom_state_component_equality]
QED

(* Part 2a: OK-case — when both return OK, results have execution_equiv +
   field equalities + prev_bb properties.
   Terminators synchronize prev_bb; non-terminators preserve input prev_bb. *)
Theorem step_inst_non_phi_exec_equiv:
  !fuel ctx inst vars sa sb ra rb.
    execution_equiv vars sa sb /\
    sa.vs_current_bb = sb.vs_current_bb /\
    sa.vs_inst_idx = sb.vs_inst_idx /\
    inst.inst_opcode <> PHI /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    step_inst fuel ctx inst sa = OK ra /\
    step_inst fuel ctx inst sb = OK rb ==>
    execution_equiv vars ra rb /\
    ra.vs_current_bb = rb.vs_current_bb /\
    ra.vs_inst_idx = rb.vs_inst_idx /\
    (is_terminator inst.inst_opcode ==> ra.vs_prev_bb = rb.vs_prev_bb) /\
    (~is_terminator inst.inst_opcode ==>
       ra.vs_prev_bb = sa.vs_prev_bb /\ rb.vs_prev_bb = sb.vs_prev_bb) /\
    (ra.vs_halted <=> rb.vs_halted)
Proof
  rpt gen_tac >> strip_tac >>
  `?sbp. state_equiv vars sa sbp /\
         sbp with vs_prev_bb := sb.vs_prev_bb = sb` by
    metis_tac[execution_equiv_proxy_state] >>
  `result_equiv vars (step_inst fuel ctx inst sa)
                     (step_inst fuel ctx inst sbp)` by
    metis_tac[step_inst_same_ctx_result_equiv] >>
  Cases_on `inst.inst_opcode = INVOKE` >- (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `sbp`, `sb.vs_prev_bb`]
      step_inst_invoke_prev_bb) >>
    ASM_REWRITE_TAC[] >> DISCH_TAC >>
    Cases_on `step_inst fuel ctx inst sbp` >>
    gvs[result_equiv_def, state_equiv_def, is_terminator_def] >>
    imp_res_tac step_inst_non_term_preserves_prev_bb >>
    gvs[is_terminator_def, execution_equiv_def]
  ) >>
  gvs[step_inst_non_invoke] >>
  (Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
            inst.inst_opcode = DJMP` >- (
    `step_inst_base inst sbp = OK rb` by
      metis_tac[step_inst_base_prev_bb_jmp] >>
    gvs[result_equiv_def, state_equiv_def, is_terminator_def,
        execution_equiv_def]
  )) >>
  mp_tac (Q.SPECL [`inst`, `sbp`, `sb.vs_prev_bb`]
    step_inst_base_prev_bb_map) >>
  (impl_tac >- gvs[]) >>
  DISCH_TAC >>
  Cases_on `step_inst_base inst sbp` >>
  gvs[result_equiv_def, exec_result_map_state_def, state_equiv_def] >>
  imp_res_tac step_inst_base_preserves_prev_bb >>
  imp_res_tac step_inst_base_ok_not_terminator >>
  gvs[execution_equiv_def]
QED

(* Part 2b: Non-OK cases — when a non-PHI instruction returns Halt/Abort/IntRet/Error,
   execution_equiv states produce result_equiv (since execution_equiv ignores prev_bb,
   Halt/Abort/IntRet all use execution_equiv, and Error is trivially true).
   Proof: proxy → result_equiv(step sa, step sbp) → bridge(step sbp, step sb) → transitivity *)
Theorem step_inst_non_phi_result_equiv_non_ok:
  !fuel ctx inst vars sa sb.
    execution_equiv vars sa sb /\
    sa.vs_current_bb = sb.vs_current_bb /\
    sa.vs_inst_idx = sb.vs_inst_idx /\
    inst.inst_opcode <> PHI /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    ((?x. step_inst fuel ctx inst sa = Halt x) \/
     (?a x. step_inst fuel ctx inst sa = Abort a x) \/
     (?ws x. step_inst fuel ctx inst sa = IntRet ws x) \/
     (?e. step_inst fuel ctx inst sa = Error e)) ==>
    result_equiv vars (step_inst fuel ctx inst sa)
                      (step_inst fuel ctx inst sb)
Proof
  rpt gen_tac >> strip_tac >>
  (* Proxy: sbp is state_equiv to sa, recovers sb when prev_bb restored *)
  drule_all execution_equiv_proxy_state >> strip_tac >>
  `result_equiv vars (step_inst fuel ctx inst sa)
                     (step_inst fuel ctx inst sbp)` by
    metis_tac[step_inst_same_ctx_result_equiv] >>
  (* step sbp is non-OK (same constructor as step sa, via result_equiv) *)
  `~(?r. step_inst fuel ctx inst sbp = OK r)` by (
    strip_tac >>
    Cases_on `step_inst fuel ctx inst sa` >>
    gvs[result_equiv_def]
  ) >>
  (* Bridge: step sbp → step sb via prev_bb commutation *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `vars`, `sbp`, `sb.vs_prev_bb`]
    step_inst_prev_bb_result_equiv_non_ok) >>
  (impl_tac >- gvs[]) >>
  `(sbp with vs_prev_bb := sb.vs_prev_bb) = sb` by gvs[] >>
  gvs[] >>
  strip_tac >>
  metis_tac[result_equiv_trans]
QED

(* Clean characterization of step_inst for PHI.
   Avoids expanding step_inst_base_def in every PHI proof. *)
Triviality step_phi_result:
  !fuel ctx inst s.
    inst.inst_opcode = PHI ==>
    step_inst fuel ctx inst s =
    case inst.inst_outputs of
      [out] =>
        (case s.vs_prev_bb of
           NONE => Error "phi at entry block"
         | SOME prev =>
           case resolve_phi prev inst.inst_operands of
             NONE => Error "phi: no matching predecessor"
           | SOME val_op =>
             case eval_operand val_op s of
               NONE => Error "phi: undefined operand"
             | SOME v => OK (update_var out v s))
    | _ => Error "phi requires single output"
Proof
  rpt strip_tac >>
  simp[step_inst_non_invoke] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >> simp[]
QED

Theorem step_phi_ok_or_error:
  !fuel ctx inst s.
    inst.inst_opcode = PHI ==>
    (?v. step_inst fuel ctx inst s = OK v) \/
    (?e. step_inst fuel ctx inst s = Error e)
Proof
  rpt strip_tac >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  pop_assum (mp_tac o GSYM) >>
  simp[step_phi_result] >>
  rpt (CHANGED_TAC (simp[AllCaseEqs(), exec_result_distinct]))
QED

(* Core: PHI with known resolve_phi relationship *)
Triviality step_phi_subst_core:
  !fuel ctx vars inst old_lbl new_lbl prev_a prev_b sa sb.
    inst.inst_opcode = PHI /\
    execution_equiv vars sa sb /\
    sa.vs_current_bb = sb.vs_current_bb /\
    sa.vs_inst_idx = sb.vs_inst_idx /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    ~MEM (Label new_lbl) inst.inst_operands /\
    sa.vs_prev_bb = SOME prev_a /\
    sb.vs_prev_bb = SOME prev_b /\
    FDOM sa.vs_labels = {} /\
    resolve_phi prev_b
      (MAP (subst_label_op old_lbl new_lbl) inst.inst_operands) =
    OPTION_MAP (subst_label_op old_lbl new_lbl)
      (resolve_phi prev_a inst.inst_operands) ==>
    let inst' = subst_label_inst old_lbl new_lbl inst in
    let ra = step_inst fuel ctx inst sa in
    let rb = step_inst fuel ctx inst' sb in
    (exec_result_tag ra = exec_result_tag rb) /\
    (!va vb. ra = OK va /\ rb = OK vb ==>
             execution_equiv vars va vb /\
             va.vs_current_bb = vb.vs_current_bb /\
             va.vs_inst_idx = vb.vs_inst_idx /\
             va.vs_prev_bb = sa.vs_prev_bb /\
             vb.vs_prev_bb = sb.vs_prev_bb /\
             (va.vs_halted <=> vb.vs_halted))
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_phi_result, subst_label_inst_def] >>
  Cases_on `inst.inst_outputs` >> simp[exec_result_tag_def] >>
  Cases_on `t` >> simp[exec_result_tag_def] >>
  Cases_on `resolve_phi prev_a inst.inst_operands` >>
  gvs[exec_result_tag_def] >>
  rename1 `resolve_phi _ _ = SOME val_op` >>
  Cases_on `val_op` >>
  gvs[subst_label_op_def, eval_operand_def, exec_result_tag_def] >| [
    (* Lit: update_var h c on both sides *)
    simp[update_var_def] >> fs[execution_equiv_def, lookup_var_def, FLOOKUP_UPDATE],
    (* Var: establish lookup equality, case split, then update_var *)
    `s NOTIN vars` by (imp_res_tac resolve_phi_MEM >> metis_tac[]) >>
    `lookup_var s sa = lookup_var s sb` by fs[execution_equiv_def] >>
    simp[] >> Cases_on `lookup_var s sb` >>
    simp[exec_result_tag_def, update_var_def] >>
    fs[execution_equiv_def, lookup_var_def, FLOOKUP_UPDATE],
    (* Label: vs_labels empty on both sides, so both FLOOKUP = NONE *)
    `sa.vs_labels = sb.vs_labels` by (
      qpat_x_assum `execution_equiv _ _ _` mp_tac >>
      simp[execution_equiv_def]) >>
    `FDOM sb.vs_labels = {}` by metis_tac[] >>
    `!k. FLOOKUP sa.vs_labels k = NONE` by
      (fs[FLOOKUP_DEF] >> metis_tac[pred_setTheory.NOT_IN_EMPTY]) >>
    `!k. FLOOKUP sb.vs_labels k = NONE` by
      (fs[FLOOKUP_DEF] >> metis_tac[pred_setTheory.NOT_IN_EMPTY]) >>
    IF_CASES_TAC >> simp[eval_operand_def, exec_result_tag_def]
  ]
QED

(* Step-level: PHI with label-substituted operands *)
Theorem step_phi_subst_equiv:
  !fuel ctx vars inst old_lbl new_lbl sa sb.
    inst.inst_opcode = PHI /\
    execution_equiv vars sa sb /\
    sa.vs_current_bb = sb.vs_current_bb /\
    sa.vs_inst_idx = sb.vs_inst_idx /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    ~MEM (Label new_lbl) inst.inst_operands /\
    FDOM sa.vs_labels = {} /\
    ((sa.vs_prev_bb = sb.vs_prev_bb /\
      sa.vs_prev_bb <> SOME old_lbl /\ sa.vs_prev_bb <> SOME new_lbl) \/
     (sa.vs_prev_bb = SOME old_lbl /\ sb.vs_prev_bb = SOME new_lbl)) ==>
    let inst' = subst_label_inst old_lbl new_lbl inst in
    let ra = step_inst fuel ctx inst sa in
    let rb = step_inst fuel ctx inst' sb in
    (exec_result_tag ra = exec_result_tag rb) /\
    (!va vb. ra = OK va /\ rb = OK vb ==>
             execution_equiv vars va vb /\
             va.vs_current_bb = vb.vs_current_bb /\
             va.vs_inst_idx = vb.vs_inst_idx /\
             va.vs_prev_bb = sa.vs_prev_bb /\
             vb.vs_prev_bb = sb.vs_prev_bb /\
             (va.vs_halted <=> vb.vs_halted))
Proof
  rpt gen_tac >> strip_tac >> fs[] >| [
    (* Case 1: same prev_bb, not old or new *)
    Cases_on `sb.vs_prev_bb` >> gvs[] >| [
      (* NONE: both Error, vacuously true *)
      simp[step_phi_result, subst_label_inst_def, exec_result_tag_def,
           AllCaseEqs()],
      (* SOME: use step_phi_subst_core + resolve_phi_subst_other *)
      irule (SIMP_RULE (srw_ss()) [LET_THM] step_phi_subst_core) >> simp[] >>
      irule resolve_phi_subst_other >> gvs[]
    ],
    (* Case 2: old -> new *)
    irule (SIMP_RULE (srw_ss()) [LET_THM] step_phi_subst_core) >> simp[] >>
    irule resolve_phi_subst_label >> simp[]
  ]
QED

(* Unified step-level helper: for any instruction (PHI or not),
   if step_inst on s1 returns OK, then the appropriately-transformed
   instruction (identity for non-PHI, subst_label for PHI) on
   execution_equiv s2 also returns OK with equiv result.
   Eliminates the PHI/non-PHI dispatch duplication in callers. *)
Theorem step_phi_subst_or_same_step_equiv:
  !fuel ctx vars inst old_lbl new_lbl s1 s2 s1'.
    step_inst fuel ctx inst s1 = OK s1' /\
    execution_equiv vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    FDOM s1.vs_labels = {} /\
    ((s1.vs_prev_bb = s2.vs_prev_bb /\
      s1.vs_prev_bb <> SOME old_lbl /\ s1.vs_prev_bb <> SOME new_lbl) \/
     (s1.vs_prev_bb = SOME old_lbl /\ s2.vs_prev_bb = SOME new_lbl)) /\
    ~is_terminator inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    ~MEM (Label new_lbl) inst.inst_operands ==>
    let inst' = if inst.inst_opcode <> PHI then inst
                else subst_label_inst old_lbl new_lbl inst in
    ?s2'. step_inst fuel ctx inst' s2 = OK s2' /\
          execution_equiv vars s1' s2' /\
          s1'.vs_current_bb = s2'.vs_current_bb /\
          s1'.vs_inst_idx = s2'.vs_inst_idx /\
          ((s1'.vs_prev_bb = s2'.vs_prev_bb /\
            s1'.vs_prev_bb <> SOME old_lbl /\
            s1'.vs_prev_bb <> SOME new_lbl) \/
           (s1'.vs_prev_bb = SOME old_lbl /\
            s2'.vs_prev_bb = SOME new_lbl))
Proof
  rpt gen_tac
  \\ DISCH_THEN (fn th => map_every ASSUME_TAC (CONJUNCTS th))
  \\ simp[LET_THM]
  \\ Cases_on `inst.inst_opcode = PHI`
  >- suspend "phi_case"
  >> suspend "nonphi_case"
QED

Resume step_phi_subst_or_same_step_equiv[phi_case]:
  simp[]
  \\ mp_tac (SIMP_RULE (srw_ss()) [LET_THM] step_phi_subst_equiv)
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `vars`, `inst`,
      `old_lbl`, `new_lbl`, `s1`, `s2`] mp_tac)
  \\ (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >> TRY (qpat_x_assum `(_ /\ _) \/ _` ACCEPT_TAC) >> simp[]))
  \\ strip_tac
  (* Extract OK from tag match *)
  \\ (SUBGOAL_THEN ``?s2v. step_inst fuel ctx
         (subst_label_inst old_lbl new_lbl inst) s2 = OK s2v``
    STRIP_ASSUME_TAC
    >- (Cases_on `step_inst fuel ctx (subst_label_inst old_lbl new_lbl inst) s2`
        >> qpat_x_assum `exec_result_tag _ = _` mp_tac
        >> simp[exec_result_tag_def]))
  \\ res_tac
  \\ qpat_x_assum `step_inst _ _ (subst_label_inst _ _ _) _ = OK _` (fn eq =>
       EXISTS_TAC (rand (rhs (concl eq))) >> ASSUME_TAC eq)
  \\ simp[]
QED

Resume step_phi_subst_or_same_step_equiv[nonphi_case]:
  simp[]
  \\ mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `vars`, `s1`, `s2`]
      step_inst_non_phi_same_tag)
  \\ (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]))
  \\ strip_tac
  (* Extract OK from tag equality *)
  \\ qpat_x_assum `exec_result_tag (step_inst _ _ inst s1) = _` mp_tac
  \\ qpat_x_assum `step_inst _ _ inst s1 = OK s1'` (fn eq =>
       REWRITE_TAC[eq] >> ASSUME_TAC eq)
  \\ simp[exec_result_tag_def]
  \\ Cases_on `step_inst fuel ctx inst s2`
  \\ simp[exec_result_tag_def]
  \\ strip_tac
  (* Now: step_inst fuel ctx inst s2 = OK v, goal is equiv properties *)
  \\ imp_res_tac step_inst_non_phi_exec_equiv
  \\ simp[]
QED

Finalise step_phi_subst_or_same_step_equiv;

(* ================================================================
   Corollaries of run_block_no_phi_prev_bb_lift
   ================================================================ *)

(* Tag corollary: result constructor is preserved *)
Theorem run_block_no_phi_prev_bb_tag:
  !fuel ctx bb s p.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    bb_well_formed bb ==>
    exec_result_tag (run_block fuel ctx bb (s with vs_prev_bb := p)) =
    exec_result_tag (run_block fuel ctx bb s)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `p`]
    run_block_no_phi_prev_bb_lift) >>
  simp[] >>
  Cases_on `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel ctx bb (s with vs_prev_bb := p)` >>
  simp[lift_result_def, exec_result_tag_def]
QED

(* General prev_bb independence for run_function: lift_result version.
   OK results are identical; non-OK results satisfy shared_globals_np. *)
Triviality lift_result_refl:
  (!x. R x x) /\ (!x. G x x) ==> lift_result R G r r
Proof
  Cases_on `r` >> simp[lift_result_def]
QED

(* Weak version: OK relation is trivial *)
Theorem run_function_no_phi_entry_prev_bb_general:
  !fuel ctx fn s p bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    bb_well_formed bb ==>
    lift_result (\_ _. T) shared_globals_np
      (run_function (SUC fuel) ctx fn s)
      (run_function (SUC fuel) ctx fn (s with vs_prev_bb := p))
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `p`]
    run_block_no_phi_prev_bb_lift) >>
  simp[] >> strip_tac >>
  Cases_on `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel ctx bb (s with vs_prev_bb := p)` >>
  gvs[lift_result_def] >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def] >>
  irule lift_result_refl >> simp[shared_globals_np_def]
QED

(* Strong version: OK results are equal.
   If the entry block has no PHI, prev_bb only affects non-OK result states
   (where it's invisible to shared_globals_np). For OK, jump_to overwrites
   prev_bb, so the continuation states are identical. *)
Theorem run_function_no_phi_entry_prev_bb_eq:
  !fuel ctx fn s p bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    bb_well_formed bb ==>
    lift_result (=) shared_globals_np
      (run_function (SUC fuel) ctx fn s)
      (run_function (SUC fuel) ctx fn (s with vs_prev_bb := p))
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `p`]
    run_block_no_phi_prev_bb_lift) >>
  simp[] >> strip_tac >>
  Cases_on `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel ctx bb (s with vs_prev_bb := p)` >>
  gvs[lift_result_def] >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def] >>
  irule lift_result_refl >> simp[shared_globals_np_def]
QED

val _ = export_theory();
