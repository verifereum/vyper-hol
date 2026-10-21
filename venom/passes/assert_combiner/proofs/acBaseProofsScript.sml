(*
 * Assert Combiner — Base Proofs
 *
 * Opcode classification and basic safe-instruction semantics.
 *)

Theory acBaseProofs
Ancestors
  assertCombinerDefs venomInstProps venomExecProofs venomExecSemantics venomWf
  venomState
Libs
  pred_setTheory listTheory

(* Cache only constructor-level classification facts, not the large definitions
   in each branch's simpset. Effects are needed only for the four survivors. *)
val safe_between_class_ss = let
  val classify = SIMP_CONV (srw_ss())
    [venomInstTheory.is_effect_free_op_def,
     venomInstTheory.is_terminator_def, ac_is_volatile_def]
  val facts = List.concat (map (fn opc =>
    map (fn pred => classify (mk_comb (pred, opc)))
      [``is_effect_free_op``, ``is_terminator``, ``ac_is_volatile``])
    (TypeBase.constructors_of ``:opcode``))
in
  srw_ss() ++ simpLib.rewrites facts
end;

Theorem ac_safe_between_effect_free:
  !inst. ac_is_safe_between inst ==> is_effect_free_op inst.inst_opcode
Proof
  Cases_on `inst` >> rename1 `instruction _ opc _ _` >>
  Cases_on `opc` >>
  simp_tac safe_between_class_ss [] >>
  simp_tac safe_between_class_ss [ac_is_safe_between_def] >>
  simp[venomEffectsTheory.write_effects_def,
       venomEffectsTheory.empty_effects_def,
       venomEffectsTheory.all_effects_def]
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
  `is_effect_free_op inst.inst_opcode` by
    metis_tac[ac_safe_between_effect_free] >>
  `inst.inst_opcode <> INVOKE` by (
    strip_tac >> gvs[ac_is_safe_between_def,
      venomEffectsTheory.write_effects_def,
      venomEffectsTheory.all_effects_def,
      venomEffectsTheory.empty_effects_def,
      pred_setTheory.NOT_INSERT_EMPTY]) >>
  `inst.inst_opcode <> PHI /\ inst.inst_opcode <> PARAM /\
   inst.inst_opcode <> FMP_PARAM` by
    gvs[ac_is_safe_between_def, venomInstTheory.is_effect_free_op_def] >>
  `?s'. step_inst_base inst s = OK s'` by (
    irule effect_free_step_inst_base_ok >> gvs[] >>
    metis_tac[optionTheory.IS_SOME_DEF, optionTheory.NOT_SOME_NONE]) >>
  qexists_tac `s'` >>
  gvs[step_inst_non_invoke]
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
  `inst.inst_opcode <> PHI` by gvs[ac_is_safe_between_def] >>
  metis_tac[step_inst_lookup_mono]
QED
