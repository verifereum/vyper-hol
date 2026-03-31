(*
 * Assert Combiner — Base Proofs
 *
 * Contains opcode-enumeration proofs that are slow to compile (~50s).
 * Separated to benefit from build caching.
 *)

Theory acBaseProofs
Ancestors
  assertCombinerDefs venomInstProps venomExecProofs venomExecSemantics venomWf
  venomState
Libs
  pred_setTheory listTheory

val safe_between_simp = [ac_is_safe_between_def,
    venomInstTheory.is_effect_free_op_def,
    venomInstTheory.is_terminator_def, ac_is_volatile_def,
    venomEffectsTheory.write_effects_def, venomEffectsTheory.read_effects_def,
    venomEffectsTheory.empty_effects_def, venomEffectsTheory.all_effects_def,
    pred_setTheory.NOT_INSERT_EMPTY];

Theorem ac_safe_between_effect_free:
  !inst. ac_is_safe_between inst ==> is_effect_free_op inst.inst_opcode
Proof
  Cases_on `inst` >> rename1 `instruction _ opc _ _` >>
  Cases_on `opc` >> simp safe_between_simp
QED

(* ASSIGN semantics — targeted lemma to avoid unfolding step_inst_base_def *)
Theorem step_assign_value:
  !s src out id v.
    eval_operand src s = SOME v ==>
    step_inst_base <| inst_id := id; inst_opcode := ASSIGN;
      inst_operands := [src]; inst_outputs := [out] |> s =
    OK (update_var out v s)
Proof
  rw[step_inst_base_def, exec_pure1_def, update_var_def]
QED

(* safe_between + inst_wf + operands evaluate ==> step_inst = OK *)
Theorem safe_between_wf_step_ok:
  !inst (s:venom_state) fuel ctx.
    ac_is_safe_between inst /\ inst_wf inst /\
    (!op. MEM op inst.inst_operands ==> IS_SOME (eval_operand op s)) ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rpt strip_tac >>
  Cases_on `inst` >> rename1 `instruction iid opc ops outs` >>
  fs[ac_is_safe_between_def] >>
  `opc <> INVOKE` by
    (strip_tac >> gvs[ac_is_volatile_def,
       venomEffectsTheory.write_effects_def,
       venomEffectsTheory.all_effects_def,
       venomEffectsTheory.empty_effects_def,
       pred_setTheory.NOT_INSERT_EMPTY]) >>
  fs[step_inst_non_invoke] >>
  Cases_on `opc` >> gvs safe_between_simp >>
  gvs[inst_wf_def, LENGTH_EQ_NUM,
      step_inst_base_def, exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >>
  metis_tac[optionTheory.IS_SOME_DEF, optionTheory.NOT_SOME_NONE]
QED

(* IS_SOME(lookup_var) monotone through safe_between steps.
   Proof: NOP/ASSERT don't change state; other safe_between opcodes write
   via update_var (FUPDATE), which preserves existing bindings.
   Non-output vars preserved by step_preserves_non_output_vars. *)
Theorem safe_between_step_is_some_mono:
  !inst (s:venom_state) fuel ctx s' v.
    ac_is_safe_between inst /\ inst_wf inst /\
    (!op. MEM op inst.inst_operands ==> IS_SOME (eval_operand op s)) /\
    step_inst fuel ctx inst s = OK s' /\
    IS_SOME (lookup_var v s) ==>
    IS_SOME (lookup_var v s')
Proof
  rpt strip_tac >>
  Cases_on `MEM v inst.inst_outputs`
  >- (
    Cases_on `inst` >> rename1 `instruction iid opc ops outs` >>
    fs[ac_is_safe_between_def] >>
    Cases_on `opc = NOP` >- gvs[step_inst_non_invoke, step_inst_base_def] >>
    Cases_on `opc = ASSERT` >- (
      gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute,
          step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]) >>
    Cases_on `opc = ASSERT_UNREACHABLE` >- (
      gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute,
          step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]) >>
    `opc <> INVOKE` by
      (strip_tac >> gvs[ac_is_volatile_def,
         venomEffectsTheory.write_effects_def,
         venomEffectsTheory.all_effects_def,
         venomEffectsTheory.empty_effects_def,
         pred_setTheory.NOT_INSERT_EMPTY]) >>
    fs[step_inst_non_invoke] >>
    Cases_on `opc` >> gvs safe_between_simp >>
    gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute,
        step_inst_base_def, exec_pure1_def, exec_pure2_def, exec_pure3_def,
        exec_read0_def, exec_read1_def, AllCaseEqs(),
        update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE])
  >- (
    `~is_terminator inst.inst_opcode` by fs[ac_is_safe_between_def] >>
    `lookup_var v s' = lookup_var v s` by
      metis_tac[step_preserves_non_output_vars] >>
    fs[])
QED
