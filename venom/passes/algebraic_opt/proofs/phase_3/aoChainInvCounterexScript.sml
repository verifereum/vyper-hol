(* COUNTEREXAMPLE: ao_iszero_chain_inv is NOT step-preserved across a
 * loop re-entry, because the chain ROOT can be a loop-varying variable.
 *
 * ao_compute_iszero_step builds, for an instruction `c1 = ISZERO a`, the
 * chain [Var "a"; Var "c1"] whose ROOT (EL 0) is the operand `Var "a"`.
 * Nothing constrains `a` to be an ISZERO output: in a loop it can be
 * redefined by e.g. an ADD on every iteration.
 *
 * We exhibit a consistent state s0 (a = 5, c1 = iszero(5) = 0) at which
 * ao_iszero_chain_inv holds, and show that after redefining the root
 * (a := 0) — exactly what executing the producer of `a` does via
 * update_var on the next iteration — the invariant is FALSE (it would
 * demand c1 = iszero(0) = 1, but c1 is still the stale 0 until its own
 * ISZERO re-executes).
 *
 * This is the mid-block "staleness window" on loop re-entry.
 *)
Theory aoChainInvCounterex
Ancestors
  algebraicOptDefs aoResolveObligation
  venomState venomInst venomExecSemantics
  alist finite_map
Libs
  wordsLib BasicProvers

(* The concrete ISZERO instruction `c1 = ISZERO a`. *)
Definition cex_iszero_def:
  cex_iszero =
    <| inst_id := 0; inst_opcode := ISZERO;
       inst_operands := [Var "a"]; inst_outputs := ["c1"] |>
End

(* The chain built by the real construction function has root Var "a". *)
Theorem cex_targets_eq:
  ao_compute_iszero_targets [cex_iszero] = [("c1", [Var "a"; Var "c1"])]
Proof
  EVAL_TAC
QED

(* (1) At the consistent entry state, the chain invariant HOLDS. *)
Theorem cex_chain_inv_holds:
  !s0.
    FLOOKUP s0.vs_vars "a" = SOME 5w /\
    FLOOKUP s0.vs_vars "c1" = SOME 0w ==>
    ao_iszero_chain_inv (ao_compute_iszero_targets [cex_iszero]) s0
Proof
  rw[cex_targets_eq, ao_iszero_chain_inv_def] >>
  gvs[ALOOKUP_def, AllCaseEqs()] >>
  `k = 0` by DECIDE_TAC >> gvs[] >>
  gvs[eval_operand_def, lookup_var_def, bool_to_word_def] >>
  EVAL_TAC
QED

(* (2) After redefining the chain ROOT (a := 0), the invariant is FALSE. *)
Theorem cex_chain_inv_broken:
  !s0.
    FLOOKUP s0.vs_vars "a" = SOME 5w /\
    FLOOKUP s0.vs_vars "c1" = SOME 0w ==>
    ~ao_iszero_chain_inv (ao_compute_iszero_targets [cex_iszero])
        (update_var "a" 0w s0)
Proof
  rpt strip_tac >>
  qpat_x_assum `ao_iszero_chain_inv _ _`
    (assume_tac o SIMP_RULE std_ss [cex_targets_eq, ao_iszero_chain_inv_def]) >>
  `ALOOKUP [("c1", [Var "a"; Var "c1"])] "c1" = SOME [Var "a"; Var "c1"]`
    by simp[ALOOKUP_def] >>
  `(0w:bytes32) = bool_to_word (0w = 0w)` by
    (qpat_x_assum `!v chain. _` drule >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then (qspecl_then [`0w`, `0w`] mp_tac) >>
     simp[eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> gvs[]) >>
  gvs[bool_to_word_def]
QED

(* Together: ao_iszero_chain_inv held at s0 but is broken by one update,
   so it is not preserved by execution on a loop re-entry. *)
Theorem cex_chain_inv_not_preserved:
  ?(targets:(string # operand list) list) s0 s1.
    s1 = update_var "a" 0w s0 /\
    ao_iszero_chain_inv targets s0 /\
    ~ao_iszero_chain_inv targets s1
Proof
  qexists_tac `ao_compute_iszero_targets [cex_iszero]` >>
  qexists_tac
    `(ARB : venom_state) with
       vs_vars := FEMPTY |+ ("a", 5w) |+ ("c1", 0w)` >>
  qmatch_goalsub_abbrev_tac `update_var _ _ s0` >>
  `FLOOKUP s0.vs_vars "a" = SOME 5w /\
   FLOOKUP s0.vs_vars "c1" = SOME 0w` by
    simp[Abbr `s0`, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[cex_chain_inv_holds, cex_chain_inv_broken]
QED

val _ = export_theory();
