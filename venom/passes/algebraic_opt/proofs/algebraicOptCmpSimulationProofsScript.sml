Theory algebraicOptCmpSimulationProofs
Ancestors
  algebraicOptCmpLocalProofs stateFrame venomState venomExecSemantics

Definition ao_cmp_state_rel_def:
  ao_cmp_state_rel ignored flipped s t <=>
    execution_frame s = execution_frame t /\
    !v. v NOTIN ignored ==>
      if v IN flipped then
        (lookup_var v s = NONE /\ lookup_var v t = NONE) \/
        (?b. lookup_var v s = SOME (bool_to_word b) /\
             lookup_var v t = SOME (bool_to_word (~b)))
      else lookup_var v s = lookup_var v t
End

Theorem ao_cmp_state_rel_initial:
  !ignored flipped s.
    (!v. v IN flipped /\ v NOTIN ignored ==> lookup_var v s = NONE) ==>
    ao_cmp_state_rel ignored flipped s s
Proof
  rpt strip_tac >> simp[ao_cmp_state_rel_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem ao_cmp_state_rel_write:
  !ignored flipped s t out a b.
    ao_cmp_state_rel ignored flipped s t /\
    (if out IN flipped then
       ?p. a = bool_to_word p /\ b = bool_to_word (~p)
     else a = b) ==>
    ao_cmp_state_rel ignored flipped (update_var out a s) (update_var out b t)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ao_cmp_state_rel _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ao_cmp_state_rel_def]) >>
  pure_rewrite_tac[ao_cmp_state_rel_def] >>
  conj_tac >- asm_rewrite_tac[frame_update_var] >>
  rpt strip_tac >> Cases_on `v = out`
  >- (gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[lookup_var_def]
QED

Theorem ao_cmp_state_rel_operand:
  !ignored flipped s t op.
    ao_cmp_state_rel ignored flipped s t /\
    (!v. op = Var v ==> v NOTIN ignored /\ v NOTIN flipped) ==>
    eval_operand op s = eval_operand op t
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def, ao_cmp_state_rel_def] >> metis_tac[]
QED

Theorem ao_cmp_state_rel_assign_probe:
  !fuel ctx inst op out ignored flipped s t x.
    ao_cmp_state_rel ignored flipped s t /\
    inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
    inst.inst_outputs = [out] /\ out NOTIN flipped /\
    (!v. op = Var v ==> v NOTIN ignored /\ v NOTIN flipped) /\
    eval_operand op s = SOME x ==>
    ?s1 t1. step_inst fuel ctx inst s = OK s1 /\
      step_inst fuel ctx inst t = OK t1 /\
      ao_cmp_state_rel ignored flipped s1 t1
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand op s = eval_operand op t` by
    (irule ao_cmp_state_rel_operand >> metis_tac[]) >>
  qexistsl_tac [`update_var out x s`, `update_var out x t`] >>
  reverse (rpt conj_tac)
  >- (irule ao_cmp_state_rel_write >> simp[]) >>
  simp[step_inst_non_invoke] >> asm_rewrite_tac[step_inst_base_def] >>
  pure_rewrite_tac[venomInstTheory.opcode_case_def] >> gvs[]
QED

Theorem ao_cmp_state_rel_ignored_write:
  !ignored flipped s t out x.
    ao_cmp_state_rel ignored flipped s t /\ out IN ignored ==>
    ao_cmp_state_rel ignored flipped s (update_var out x t)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ao_cmp_state_rel _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ao_cmp_state_rel_def]) >>
  pure_rewrite_tac[ao_cmp_state_rel_def] >>
  conj_tac >- asm_rewrite_tac[frame_update_var] >>
  rpt strip_tac >> `v <> out` by metis_tac[] >>
  simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[lookup_var_def]
QED

(* Runtime-interface checkpoint (not a block simulation theorem).
 *
 * Sets: flipped contains exactly outputs of selected comparator producers;
 * ignored contains comparator-postpass allocated variables, not all main-pass
 * allocated variables.  The scan must show selected producers retain original
 * outputs: main rewrites insert NOT/XOR/ISZERO, never a new comparator.  Thus
 * original output absence initializes flipped; arbitrary main-pass fresh values
 * need not be absent and are compared exactly between mid and postpass at entry.
 * This provenance/initialization bridge is still a static obligation.
 *
 * Remaining branch ledger:
 * - Producer: singleton-read certificates exclude every flipped variable from
 *   comparator operands; supply coverage excludes ignored operands.  Apply
 *   ao_cmp_producer_refresh and ao_cmp_state_rel_write on every visit.  No
 *   first-visit assumption is needed.  Output uniqueness excludes other writes.
 * - Removed ISZERO: paired NONE makes the source error; paired complement uses
 *   ao_cmp_iszero_compensation.  Its output is not flipped, by distinct outputs
 *   and the fact that a flipped writer is a comparator, not ISZERO.
 * - Inserted ASSERT: a paired NONE source errors.  Otherwise use
 *   ao_cmp_assert_compensation; target temporary writes preserve the relation
 *   by ao_cmp_state_rel_ignored_write.  Successful and abort frames match,
 *   using equal original frames and shared revert/set_returndata operations.
 * - Untouched instruction: singleton reads rule out flipped operands, and
 *   unique writers rule out flipped outputs.  Need a general masked-variable
 *   step congruence interface; assign_probe checks only one representative.
 * - Atomic PHIs: all incoming operands are unflipped (singleton consumer is
 *   ISZERO or ASSERT); all PHI outputs are unflipped (unique comparator writer).
 *   Evaluate the whole batch in pre-states before writing outputs.  Also carry
 *   equal current/previous block labels separately from execution_frame.
 * - Terminators: no flipped operand; exact arguments give equal successors,
 *   return values, abort tags and frame.  Control/index correspondence is a
 *   separate block-boundary invariant; inserted instructions shift indices.
 * - INVOKE: no flipped argument or output.  Equal args/frame make setup_callee
 *   states equal (setup clears vs_vars), hence identical callee runs at equal
 *   fuel.  Merge retains caller vars; bind_outputs writes only unflipped vars.
 *   Prove the corresponding merge/bind relation boundary, including returns,
 *   aborts and errors, before lifting through exec_block.
 *
 * Main simulation must provide the actual mid structural package and original
 * output provenance, not wf_ssa mid or absence of all mid outputs.  Static
 * scan coherence must supply disjoint flipped/ignored sets, no other writer,
 * unmodified-operand restrictions and correct action lookup precedence.
 * Equal-block-fuel induction and terminal execution_equiv remain unproved.
 *)
