(* Local semantic boundaries for assert-combiner emissions. *)
Theory acMergeStepProofs
Ancestors
  acChainProofs acAbortRelProofs acBaseProofs
  execEquivParamProps stateEquiv stateEquivProps passSimulationDefs
  venomExecSemantics venomExecProofs venomState venomInst
  finite_map list pred_set words analysisSimDefs

(* This covers every untouched opcode, including GAS and INVOKE.  Outputs
   need not be disjoint: writing the same value preserves the relation. *)
Theorem ac_unchanged_step:
  !X fuel ctx inst s t.
    state_equiv X s t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN X) ==>
    lift_result (state_equiv X) (execution_equiv UNIV) ac_abort_equiv
      (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)
Proof
  rpt strip_tac >>
  `lift_result (state_equiv X) (execution_equiv X) (execution_equiv X)
     (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)` by
    (irule step_inst_preserves_R >>
     simp[state_equiv_execution_equiv_valid_state_rel] >>
     gvs[state_equiv_def, execution_equiv_def] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s` >>
  Cases_on `step_inst fuel ctx inst t` >>
  gvs[lift_result_def] >>
  metis_tac[execution_equiv_weaken_UNIV, execution_equiv_ac_abort_equiv]
QED

(* The emitted prefix is total when its two inputs evaluate.  Even if a
   generated name already has a binding, that binding is overwritten. *)
Theorem ac_or_iszero_prefix:
  !fuel ctx s p q a b oi ov zi zv.
    eval_operand p s = SOME a /\ eval_operand q s = SOME b ==>
    run_insts fuel ctx
      [instruction oi OR [p;q] [ov];
       instruction zi ISZERO [Var ov] [zv]] s =
    OK (update_var zv (bool_to_word (a = 0w /\ b = 0w))
          (update_var ov (word_or a b) s))
Proof
  rpt strip_tac >>
  simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
       exec_pure2_def, exec_pure1_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, word_or_eq_0w]
QED

(* The final ASSERT tests the accumulated predicate. *)
Theorem ac_or_iszero_assert:
  !fuel ctx s p q a b oi ov zi zv ai outs.
    eval_operand p s = SOME a /\ eval_operand q s = SOME b ==>
    run_insts fuel ctx
      [instruction oi OR [p;q] [ov];
       instruction zi ISZERO [Var ov] [zv];
       instruction ai ASSERT [Var zv] outs] s =
    if a = 0w /\ b = 0w then
      OK (update_var zv (bool_to_word (a = 0w /\ b = 0w))
            (update_var ov (word_or a b) s))
    else
      Abort Revert_abort
        (revert_state (set_returndata []
          (update_var zv (bool_to_word (a = 0w /\ b = 0w))
            (update_var ov (word_or a b) s))))
Proof
  rpt strip_tac >>
  qpat_assum `eval_operand p s = SOME a`
    (mp_then (Pos hd) mp_tac ac_or_iszero_prefix) >>
  disch_then drule >> disch_then assume_tac >>
  pure_rewrite_tac[run_insts_three] >>
  asm_simp_tac bool_ss [] >>
  simp[run_insts_def, step_inst_non_invoke, step_inst_base_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
  Cases_on `a = 0w /\ b = 0w` >> simp[bool_to_word_def]
QED

(* A middle member of a chain records its OR but does not assert yet. *)
Theorem ac_or_iszero_nop:
  !fuel ctx s p q a b oi ov zi zv ai.
    eval_operand p s = SOME a /\ eval_operand q s = SOME b ==>
    run_insts fuel ctx
      [instruction oi OR [p;q] [ov];
       instruction zi ISZERO [Var ov] [zv];
       instruction ai NOP [] []] s =
    OK (update_var zv (bool_to_word (a = 0w /\ b = 0w))
          (update_var ov (word_or a b) s))
Proof
  rpt strip_tac >> irule run_insts_two_snoc_nop >>
  simp[ac_or_iszero_prefix]
QED

(* Equal-predicate emissions retain the original assertion, whose condition
   is justified by a DFG certificate, rather than an invented OR. *)
Theorem ac_assert_predicate:
  !fuel ctx inst s c a.
    inst.inst_opcode = ASSERT /\ inst.inst_operands = [c] /\
    eval_operand c s = SOME (bool_to_word (a = 0w)) ==>
    step_inst fuel ctx inst s =
      if a = 0w then OK s
      else Abort Revert_abort (revert_state (set_returndata [] s))
Proof
  rpt strip_tac >> Cases_on `a = 0w` >>
  gvs[bool_to_word_def] >>
  simp[step_inst_non_invoke, step_inst_base_def]
QED

(* Fresh output names may already be present in the runtime map. *)
Theorem ac_or_iszero_frame:
  !X s t ov zv a b.
    state_equiv X s t /\ ov IN X /\ zv IN X ==>
    state_equiv X s
      (update_var zv (bool_to_word (a = 0w /\ b = 0w))
        (update_var ov (word_or a b) t))
Proof
  simp[state_equiv_def, execution_equiv_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ac_or_iszero_abort_frame:
  !s t ov zv a b.
    ac_abort_equiv s t ==>
    ac_abort_equiv (revert_state (set_returndata [] s))
      (revert_state (set_returndata []
        (update_var zv (bool_to_word (a = 0w /\ b = 0w))
          (update_var ov (word_or a b) t))))
Proof
  rpt strip_tac >> irule ac_abort_equiv_revert_returndata >> simp[]
QED

(* The OR output, not the ISZERO output, is carried into the next merge.
   Distinctness is needed here even though prefix evaluation needs none. *)
Theorem ac_or_iszero_chain_value:
  !fuel ctx s t p q a b oi ov zi zv.
    eval_operand p s = SOME a /\ eval_operand q s = SOME b /\
    ov <> zv /\
    run_insts fuel ctx
      [instruction oi OR [p;q] [ov];
       instruction zi ISZERO [Var ov] [zv]] s = OK t ==>
    lookup_var ov t = SOME (word_or a b) /\
    lookup_var zv t = SOME (bool_to_word (a = 0w /\ b = 0w))
Proof
  rpt strip_tac >>
  `t = update_var zv (bool_to_word (a = 0w /\ b = 0w))
         (update_var ov (word_or a b) s)` by
    metis_tac[ac_or_iszero_prefix, venomExecSemanticsTheory.exec_result_11] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
