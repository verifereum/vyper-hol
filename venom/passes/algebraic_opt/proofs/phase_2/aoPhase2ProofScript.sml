(* Phase 2: Iszero Chain Analysis Soundness
 *
 * Proves that at function entry (all outputs undefined), the chain
 * invariants hold vacuously:
 *   - ao_targets_wf targets (structural, from targets_wf theorem)
 *   - ao_iszero_chain_inv targets s (chain vars undefined → premise false)
 *   - ao_chains_defined_at targets s (same argument)
 *
 * TOP-LEVEL: ao_phase2_correct
 *)

Theory aoPhase2Proof
Ancestors
  algebraicOptDefs aoTargetProps aoPhase1Proof aoResolveObligation
  venomExecSemantics venomState venomInst venomWf
Libs
  pairLib BasicProvers

val _ = delsimps ["ao_iszero_chain_inv_def",
                  "ao_chains_defined_at_def",
                  "ao_chains_defined_def"]

Theorem ao_phase2_correct:
  !fn fn0 targets s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    FDOM s.vs_vars = {} ==>
    ao_targets_wf targets /\
    ao_iszero_chain_inv targets s /\
    ao_chains_defined_at targets s
Proof
  rpt gen_tac >> strip_tac >>
  `!x. lookup_var x s = NONE` by
    fs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
  qpat_x_assum `fn0 = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `targets = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  rpt conj_tac
  >- metis_tac[ao_compute_fn_iszero_targets_wf, markerTheory.Abbrev_def]
  >- (simp[ao_iszero_chain_inv_def] >> rpt strip_tac >>
      `ALOOKUP (ao_compute_fn_iszero_targets fn0) v = SOME chain` by
        fs[Abbr `targets`] >>
      drule ao_fn_targets_chain_tail_var >> strip_tac >>
      `?w. EL (k + 1) chain = Var w` by
        (first_x_assum (qspec_then `k + 1` mp_tac) >> simp[]) >>
      qpat_x_assum `eval_operand (EL (k + 1) chain) s = SOME _` mp_tac >>
      gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_DEF])
  >- (simp[ao_chains_defined_at_def] >> rpt strip_tac >>
      qpat_x_assum `eval_operand (Var v) s = SOME _` mp_tac >>
      simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_DEF])
QED

