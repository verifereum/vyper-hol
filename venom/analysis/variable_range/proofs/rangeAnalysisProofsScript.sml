(*
 * Range Analysis — Proofs
 *
 * Internal proof machinery for range analysis soundness.
 * Consumer-facing theorems are in variableRangeAnalysisPropsScript.sml.
 *)

Theory rangeAnalysisProofs
Ancestors
  rangeAnalysisDefs rangeEvalDefs rangeEvalProofs valueRangeDefs valueRangeProofs
  venomExecSemantics venomState venomInst venomInstProps venomWf dfAnalyzeWidenDefs
  dfAnalyzeWidenProofs dfAnalyzeWidenProps cfgAnalysisProps

(* ===== rs_write helper ===== *)

(* Key helper: rs_write preserves in_range_state when the new range
   covers the variable's concrete value. Used by most transfer proofs. *)
Theorem rs_write_preserves_in_range_state[local]:
  ∀rs env v new_r.
    in_range_state rs env ∧
    (∀w. FLOOKUP env v = SOME w ⇒ in_range new_r w) ⇒
    in_range_state (rs_write rs v new_r) env
Proof
  rw[in_range_state_def, rs_write_def] >>
  fs[finite_mapTheory.DOMSUB_FLOOKUP_THM,
     finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `v' = v` >> fs[] >> res_tac
QED

(* If in_range_state holds and we look up a variable, its range contains
   the concrete value. Bridges rs_lookup and in_range_state. *)
Theorem rs_lookup_in_range[local]:
  ∀rs env v w.
    in_range_state rs env ∧ FLOOKUP env v = SOME w ⇒
    in_range (rs_lookup rs v) w
Proof
  rw[in_range_state_def, rs_lookup_def] >>
  Cases_on `FLOOKUP rs v` >> simp[in_range_top] >> res_tac
QED

(* ===== Lattice ===== *)

Theorem range_join_two_sound:
  ∀s1 s2 env.
    in_range_state s1 env ∧ in_range_state s2 env ⇒
    in_range_state (range_join_two s1 s2) env
Proof
  rw[in_range_state_def, range_join_two_def] >>
  rpt strip_tac >>
  `FINITE (FDOM s1 ∩ FDOM s2)` by
    simp[pred_setTheory.FINITE_INTER, finite_mapTheory.FDOM_FINITE] >>
  fs[finite_mapTheory.FLOOKUP_FUN_FMAP] >>
  Cases_on `v ∈ FDOM s1 ∩ FDOM s2` >> fs[] >>
  fs[pred_setTheory.IN_INTER] >>
  `∃r1. FLOOKUP s1 v = SOME r1` by
    fs[finite_mapTheory.FLOOKUP_DEF] >>
  `∃r2. FLOOKUP s2 v = SOME r2` by
    fs[finite_mapTheory.FLOOKUP_DEF] >>
  gvs[rs_lookup_def] >>
  irule in_range_union_l >> res_tac
QED

Theorem range_widen_states_sound:
  ∀old_st new_st env.
    in_range_state new_st env ⇒
    in_range_state (range_widen_states old_st new_st) env
Proof
  rw[in_range_state_def, range_widen_states_def] >>
  rpt strip_tac >>
  `FINITE (FDOM new_st)` by simp[finite_mapTheory.FDOM_FINITE] >>
  fs[finite_mapTheory.FLOOKUP_FUN_FMAP] >>
  Cases_on `v ∈ FDOM new_st` >> fs[] >>
  `∃r2. FLOOKUP new_st v = SOME r2` by fs[finite_mapTheory.FLOOKUP_DEF] >>
  irule in_range_monotone >>
  qexists_tac `r2` >> conj_tac
  >- (res_tac >> simp[rs_lookup_def])
  >> gvs[rs_lookup_def, vr_widen_upper_new]
QED

(* ===== Branch refinement ===== *)

Theorem range_apply_iszero_sound:
  ∀target is_true rs env.
    in_range_state rs env ∧
    (∀w. FLOOKUP env target = SOME w ⇒
         (is_true ⇒ w = 0w) ∧ (¬is_true ⇒ w ≠ 0w)) ⇒
    in_range_state (range_apply_iszero target is_true rs) env
Proof
  rpt strip_tac >>
  simp[range_apply_iszero_def] >>
  Cases_on `is_true` >> simp[]
  >- ((* is_true: write vr_constant 0 *)
      irule rs_write_preserves_in_range_state >> simp[] >>
      rpt strip_tac >> res_tac >> fs[] >>
      simp[in_range_constant, integer_wordTheory.word_0_w2i])
  >> (* ¬is_true *)
  Cases_on `rs_lookup rs target` >> simp[LET_THM]
  >> rpt IF_CASES_TAC >> gvs[]
  >> irule rs_write_preserves_in_range_state >> simp[]
  >> rpt strip_tac
  >> `in_range (rs_lookup rs target) w` by
       (mp_tac (Q.SPECL [`rs`, `env`, `target`, `w`] rs_lookup_in_range) >>
        simp[])
  >> `w2i w ≠ 0` by (res_tac >> gvs[integer_wordTheory.w2i_eq_0])
  >> gvs[in_range_def]
  >- (irule in_range_clamp_intro >> gvs[in_range_def] >>
      intLib.ARITH_TAC)
  >> irule in_range_intersect_intro >> simp[in_range_def]
  >> mp_tac (Q.SPEC `w` (INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_le))
  >> simp[INT256_MAX_def] >> intLib.ARITH_TAC
QED

Theorem range_apply_eq_sound:
  ∀lhs rhs is_true rs env.
    in_range_state rs env ∧
    (is_true ⇒
      (∀v. (lhs = Var v ∨ rhs = Var v) ⇒ ∃w. FLOOKUP env v = SOME w) ∧
      (∀v w. (lhs = Var v ∧ rhs = Lit w ∨
              rhs = Var v ∧ lhs = Lit w) ⇒
             ∀w'. FLOOKUP env v = SOME w' ⇒ w' = w) ∧
      (∀v1 v2 w1 w2.
        lhs = Var v1 ∧ rhs = Var v2 ∧
        FLOOKUP env v1 = SOME w1 ∧ FLOOKUP env v2 = SOME w2 ⇒
        w1 = w2)) ⇒
    in_range_state (range_apply_eq lhs rhs is_true rs) env
Proof
  rpt strip_tac >> simp[range_apply_eq_def] >>
  Cases_on `is_true` >> simp[] >> fs[] >>
  Cases_on `lhs` >> Cases_on `rhs` >> simp[] >>
  TRY (irule rs_write_preserves_in_range_state >> simp[] >>
       rpt strip_tac >> res_tac >> fs[in_range_constant] >> NO_TAC) >>
  (* Var-Var: both have values in env, and they're equal *)
  `∃ws. FLOOKUP env s = SOME ws` by
    (first_x_assum (qspec_then `s` mp_tac) >> simp[]) >>
  `∃ws'. FLOOKUP env s' = SOME ws'` by
    (first_x_assum (qspec_then `s'` mp_tac) >> simp[]) >>
  `ws = ws'` by
    (first_x_assum (qspecl_then [`s`, `s'`, `ws`, `ws'`] mp_tac) >> simp[]) >>
  gvs[] >>
  `in_range (rs_lookup rs s) ws` by
    (mp_tac (Q.SPECL [`rs`, `env`, `s`, `ws`] rs_lookup_in_range) >> simp[]) >>
  `in_range (rs_lookup rs s') ws` by
    (mp_tac (Q.SPECL [`rs`, `env`, `s'`, `ws`] rs_lookup_in_range) >> simp[]) >>
  `in_range (vr_intersect (rs_lookup rs s) (rs_lookup rs s')) ws` by
    (irule in_range_intersect_intro >> simp[]) >>
  irule rs_write_preserves_in_range_state >> simp[] >>
  irule rs_write_preserves_in_range_state >> simp[]
QED

(* Helper: rs_write with vr_clamp is sound when bounds hold *)
Theorem rs_write_clamp_sound[local]:
  ∀rs env var lo hi.
    in_range_state rs env ∧
    (∀w. FLOOKUP env var = SOME w ⇒ lo ≤ w2i w ∧ w2i w ≤ hi) ⇒
    in_range_state
      (rs_write rs var (vr_clamp (rs_lookup rs var) (SOME lo) (SOME hi))) env
Proof
  rpt strip_tac >>
  irule rs_write_preserves_in_range_state >> simp[] >>
  rpt strip_tac >> irule in_range_clamp_intro >> simp[] >>
  mp_tac (Q.SPECL [`rs`, `env`, `var`, `w`] rs_lookup_in_range) >>
  simp[]
QED

(* Unified bridge: when 0 < w2i c (positive signed constant),
   unsigned w2n ordering implies signed w2i ordering in all directions. *)
Theorem w2i_unsigned_bridge[local]:
  ∀(c : 256 word) (w : 256 word).
    0 < w2i c ⇒
    (w2n w ≤ w2n c ⇒ 0 ≤ w2i w ∧ w2i w ≤ w2i c) ∧
    (w2n w < w2n c ⇒ 0 ≤ w2i w ∧ w2i w < w2i c) ∧
    (w2n c ≤ w2n w ∧ 0 ≤ w2i w ⇒ w2i c ≤ w2i w) ∧
    (w2n c < w2n w ∧ 0 ≤ w2i w ⇒ w2i c < w2i w)
Proof
  rpt strip_tac >> (
    `w2n c < INT_MIN(:256)` by (
      CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS] >>
      `w2i c = &(w2n c) - &dimword(:256)` by
        simp[integer_wordTheory.w2i_eq_w2n] >>
      `w2n c < dimword(:256)` by simp[wordsTheory.w2n_lt] >>
      `dimword(:256) = 2 * INT_MIN(:256)` by
        simp[wordsTheory.dimword_def, wordsTheory.INT_MIN_def,
             fcpLib.INDEX_CONV ``dimindex(:256)``] >>
      qabbrev_tac `nn = w2n c` >>
      qabbrev_tac `dd = dimword(:256)` >>
      qabbrev_tac `hh = INT_MIN(:256)` >>
      intLib.ARITH_TAC)) >>
  TRY (`w2n w < INT_MIN(:256)` by intLib.ARITH_TAC >>
       `w2i w = &(w2n w)` by simp[integer_wordTheory.w2i_eq_w2n] >>
       `w2i c = &(w2n c)` by simp[integer_wordTheory.w2i_eq_w2n] >>
       intLib.ARITH_TAC) >>
  `w2n w < INT_MIN(:256)` by (
    CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS] >>
    `w2i w = &(w2n w) - &dimword(:256)` by
      simp[integer_wordTheory.w2i_eq_w2n] >>
    `w2n w < dimword(:256)` by simp[wordsTheory.w2n_lt] >>
    `dimword(:256) = 2 * INT_MIN(:256)` by
      simp[wordsTheory.dimword_def, wordsTheory.INT_MIN_def,
           fcpLib.INDEX_CONV ``dimindex(:256)``] >>
    qabbrev_tac `nn = w2n w` >>
    qabbrev_tac `dd = dimword(:256)` >>
    qabbrev_tac `hh = INT_MIN(:256)` >>
    intLib.ARITH_TAC) >>
  `w2i w = &(w2n w)` by simp[integer_wordTheory.w2i_eq_w2n] >>
  `w2i c = &(w2n c)` by simp[integer_wordTheory.w2i_eq_w2n] >>
  intLib.ARITH_TAC
QED

Theorem range_apply_compare_sound:
  ∀op lhs rhs is_true rs env.
    in_range_state rs env ∧
    (op = LT ∨ op = GT ∨ op = SLT ∨ op = SGT) ∧
    (∀v w w'.
      lhs = Var v ∧ rhs = Lit w ∧ FLOOKUP env v = SOME w' ⇒
      (is_true ⇔
        if op = LT then w2n w' < w2n w
        else if op = GT then w2n w' > w2n w
        else if op = SLT then w2i w' < w2i w
        else w2i w' > w2i w)) ∧
    (∀v w w'.
      lhs = Lit w ∧ rhs = Var v ∧ FLOOKUP env v = SOME w' ⇒
      (is_true ⇔
        if op = LT then w2n w < w2n w'
        else if op = GT then w2n w > w2n w'
        else if op = SLT then w2i w < w2i w'
        else w2i w > w2i w')) ⇒
    in_range_state (range_apply_compare op lhs rhs is_true rs) env
Proof
  rpt strip_tac >>
  simp[range_apply_compare_def, LET_THM] >>
  Cases_on `lhs` >> Cases_on `rhs` >> simp[] >>
  gvs[] >>
  rpt IF_CASES_TAC >> simp[] >>
  simp[range_narrow_var_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  irule rs_write_clamp_sound >> simp[] >>
  rpt strip_tac >> res_tac >> gvs[] >>
  (* Layer 1: INT256_MIN/MAX bounds from w2i_ge/w2i_le *)
  TRY (mp_tac (INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_le
               |> Q.SPEC `w`) >> simp[INT256_MAX_def] >> NO_TAC) >>
  TRY (mp_tac (INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_ge
               |> Q.SPEC `w`) >> simp[INT256_MIN_def] >> NO_TAC) >>
  (* Layer 2: Signed comparison cases *)
  TRY intLib.ARITH_TAC >>
  (* Layer 3: Bridge via w2i_unsigned_bridge *)
  `0 < w2i c` by intLib.ARITH_TAC >>
  mp_tac (Q.SPECL [`c`, `w`] w2i_unsigned_bridge) >> simp[] >> strip_tac >>
  (* Layer 3a: strict forward (w2n w < w2n c) *)
  TRY (`w2n w < w2n c` by fs[arithmeticTheory.GREATER_DEF] >>
       res_tac >> intLib.ARITH_TAC) >>
  (* Layer 3b: non-strict forward (w2n w ≤ w2n c from negated strict) *)
  TRY (`w2n w ≤ w2n c` by
         fs[arithmeticTheory.NOT_LESS, arithmeticTheory.NOT_GREATER,
            arithmeticTheory.GREATER_DEF] >>
       res_tac >> intLib.ARITH_TAC) >>
  (* Layer 3c: reverse direction — need 0 ≤ w2i w from vr_lo *)
  `in_range (rs_lookup rs s) w` by
    (mp_tac (Q.SPECL [`rs`, `env`, `s`, `w`] rs_lookup_in_range) >> simp[]) >>
  `0 ≤ w2i w` by
    (Cases_on `rs_lookup rs s` >>
     gvs[vr_is_top_def, vr_lo_def, in_range_def] >> intLib.ARITH_TAC) >>
  TRY (`w2n c < w2n w` by fs[arithmeticTheory.GREATER_DEF] >>
       res_tac >> intLib.ARITH_TAC) >>
  `w2n c ≤ w2n w` by
    fs[arithmeticTheory.NOT_LESS, arithmeticTheory.NOT_GREATER,
       arithmeticTheory.GREATER_DEF] >>
  res_tac
QED

(* ===== Edge transfer ===== *)

(* PHI renaming is sound when the concrete values of PHI outputs match
   the ranges of the predecessor operands. This holds when execution
   came from pred: PHI assigns out := v, so env(out) = env(v) ∈ range(v). *)
Theorem range_phi_edge_rename_sound:
  ∀bbs pred succ rs env.
    in_range_state rs env ∧
    (∀bb inst out v.
      lookup_block succ bbs = SOME bb ∧
      MEM inst bb.bb_instructions ∧
      inst.inst_opcode = PHI ∧
      inst.inst_outputs = [out] ∧
      ALOOKUP (phi_pairs inst.inst_operands) pred = SOME v ⇒
        ∀w. FLOOKUP env out = SOME w ⇒ in_range (rs_lookup rs v) w) ⇒
    in_range_state (range_phi_edge_rename bbs pred succ rs) env
Proof
  rpt strip_tac >>
  simp[range_phi_edge_rename_def] >>
  CASE_TAC >> simp[] >>
  qsuff_tac `∀instrs st.
     in_range_state st env ∧
     (∀inst. MEM inst instrs ⇒ MEM inst x.bb_instructions) ⇒
     in_range_state (FOLDL (λst inst.
       if inst.inst_opcode ≠ PHI then st
       else case inst.inst_outputs of
         [] => st | [out] =>
           (case ALOOKUP (phi_pairs inst.inst_operands) pred of
              NONE => st | SOME v => rs_write st out (rs_lookup rs v))
         | _ => st) st instrs) env`
  >- (disch_then (qspecl_then [`x.bb_instructions`, `rs`] mp_tac) >>
      simp[]) >>
  Induct >> simp[] >>
  rpt strip_tac >>
  first_x_assum irule >> conj_tac >- simp[] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  CASE_TAC >> simp[] >> CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  irule rs_write_preserves_in_range_state >> simp[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`x`, `h`, `h'`, `x'`] mp_tac) >>
  simp[]
QED

(* ===== Transfer function soundness ===== *)

(* in_range_state is preserved when the environment only changes at
   variables not tracked by rs (or tracked with compatible ranges). *)
Theorem in_range_state_env_equiv[local]:
  ∀rs env env'.
    in_range_state rs env ∧
    (∀v. v ∈ FDOM rs ⇒ FLOOKUP env' v = FLOOKUP env v) ⇒
    in_range_state rs env'
Proof
  rw[in_range_state_def] >>
  `v ∈ FDOM rs` by fs[finite_mapTheory.FLOOKUP_DEF] >>
  `FLOOKUP env' v = FLOOKUP env v` by res_tac >>
  gvs[] >> res_tac
QED

(* For eval_range returning VR_Top: trivially sound for any word value *)
Theorem eval_range_top_sound[local]:
  ∀w. in_range VR_Top w
Proof
  simp[in_range_top]
QED

(* rs_write is sound when env changes: non-output vars preserved,
   output variable gets a value in the new range. *)
Theorem rs_write_transfer_sound[local]:
  ∀rs env env' out new_r.
    in_range_state rs env ∧
    (∀v. v ∈ FDOM rs ∧ v ≠ out ⇒ FLOOKUP env' v = FLOOKUP env v) ∧
    (∀w. FLOOKUP env' out = SOME w ⇒ in_range new_r w) ⇒
    in_range_state (rs_write rs out new_r) env'
Proof
  rw[in_range_state_def, rs_write_def] >>
  rpt strip_tac >>
  Cases_on `vr_is_top new_r` >> fs[]
  >- (fs[finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
      Cases_on `v = out` >> gvs[] >>
      `v ∈ FDOM rs` by fs[finite_mapTheory.FLOOKUP_DEF] >>
      `FLOOKUP env' v = FLOOKUP env v` by res_tac >>
      fs[in_range_state_def] >> res_tac)
  >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `v = out` >> gvs[]
  >> `v ∈ FDOM rs` by fs[finite_mapTheory.FLOOKUP_DEF] >>
  `FLOOKUP env' v = FLOOKUP env v` by res_tac >>
  fs[in_range_state_def] >> res_tac
QED

(* Helper: if rs unchanged and output vars still have sound ranges, in_range_state preserved *)
Triviality in_range_state_identity[local]:
  ∀rs env env' (outs : string list).
    in_range_state rs env ∧
    (∀v. ¬MEM v outs ⇒ FLOOKUP env' v = FLOOKUP env v) ∧
    (∀out. MEM out outs ∧ out ∈ FDOM rs ⇒
      ∀w. FLOOKUP env' out = SOME w ⇒ in_range (rs ' out) w) ⇒
    in_range_state rs env'
Proof
  simp[in_range_state_def]
  \\ rpt strip_tac
  \\ Cases_on `MEM v outs`
  >- (
    `v ∈ FDOM rs` by metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]
    \\ `FLOOKUP env' v = SOME w` by simp[]
    \\ `in_range (rs ' v) w` by metis_tac[]
    \\ `rs ' v = r` by metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.SOME_11]
    \\ fs[]
  )
  \\ `FLOOKUP env' v = FLOOKUP env v` by metis_tac[]
  \\ `FLOOKUP env v = SOME w` by fs[]
  \\ metis_tac[]
QED

(* PHI [out]: DOMSUB removes out, remaining vars preserved *)
Triviality rei_sound_phi_single[local]:
  ∀dfg inst rs env env' out.
    in_range_state rs env ∧
    inst.inst_opcode = PHI ∧ inst.inst_outputs = [out] ∧
    (∀v. v ≠ out ⇒ FLOOKUP env' v = FLOOKUP env v) ⇒
    in_range_state (range_evaluate_inst dfg inst rs) env'
Proof
  rpt strip_tac
  >> simp[range_evaluate_inst_def, in_range_state_def,
          finite_mapTheory.DOMSUB_FLOOKUP_THM]
  >> rpt strip_tac
  >> `FLOOKUP env' v = FLOOKUP env v` by (first_x_assum irule >> fs[])
  >> fs[in_range_state_def] >> res_tac
QED

(* non-PHI [out]: rs_write with eval_range *)
Triviality rei_sound_eval_single[local]:
  ∀dfg inst rs env env' out.
    in_range_state rs env ∧
    inst.inst_opcode ≠ PHI ∧ inst.inst_outputs = [out] ∧
    (∀v. v ≠ out ⇒ FLOOKUP env' v = FLOOKUP env v) ∧
    (∀w. FLOOKUP env' out = SOME w ⇒
      in_range (eval_range inst.inst_opcode
                 (MAP (operand_range rs) inst.inst_operands)
                 (MAP operand_lit inst.inst_operands)) w) ⇒
    in_range_state (range_evaluate_inst dfg inst rs) env'
Proof
  rpt strip_tac
  >> simp[range_evaluate_inst_def]
  >> match_mp_tac rs_write_transfer_sound
  >> qexists_tac `env` >> simp[]
  >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Triviality in_range_state_fempty_early[local]:
  ∀env. in_range_state FEMPTY env
Proof
  simp[in_range_state_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

(* Identity cases: empty/multi outputs, PHI or not *)
Triviality rei_sound_identity[local]:
  ∀dfg inst rs env env'.
    in_range_state rs env ∧
    (inst.inst_outputs = [] ∨ (∃a b c. inst.inst_outputs = a::b::c)) ∧
    (∀v. ¬MEM v inst.inst_outputs ⇒ FLOOKUP env' v = FLOOKUP env v) ⇒
    in_range_state (range_evaluate_inst dfg inst rs) env'
Proof
  rpt gen_tac >> strip_tac >> fs[]
  (* [] case *)
  >- (Cases_on `inst.inst_opcode = PHI`
      (* PHI with [] outputs: case [] => FEMPTY *)
      >- (simp[range_evaluate_inst_def] >> irule in_range_state_fempty_early)
      (* non-PHI with [] outputs: rs *)
      >> simp[range_evaluate_inst_def] >>
         match_mp_tac in_range_state_identity >>
         qexistsl_tac [`env`, `[] : string list`] >> simp[])
  (* a::b::c case: both PHI and non-PHI multi-output return FEMPTY *)
  >> (Cases_on `inst.inst_opcode = PHI`
      >> simp[range_evaluate_inst_def]
      >> irule in_range_state_fempty_early)
QED

(* Combined: range_evaluate_inst preserves in_range_state *)
Theorem range_evaluate_inst_sound[local]:
  ∀dfg inst rs env env'.
    in_range_state rs env ∧
    (∀v. ¬MEM v inst.inst_outputs ⇒ FLOOKUP env' v = FLOOKUP env v) ∧
    (∀out. inst.inst_opcode ≠ PHI ∧ inst.inst_outputs = [out] ⇒
      ∀w. FLOOKUP env' out = SOME w ⇒
        in_range (eval_range inst.inst_opcode
                   (MAP (operand_range rs) inst.inst_operands)
                   (MAP operand_lit inst.inst_operands)) w) ⇒
    in_range_state (range_evaluate_inst dfg inst rs) env'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs`
  >- (match_mp_tac rei_sound_identity >> qexists_tac `env` >> fs[])
  >> Cases_on `t`
  >- (Cases_on `inst.inst_opcode = PHI`
      >- (match_mp_tac rei_sound_phi_single >>
          qexistsl_tac [`env`, `h`] >> fs[])
      >> match_mp_tac rei_sound_eval_single >>
      qexistsl_tac [`env`, `h`] >> fs[] >>
      rpt strip_tac >> first_x_assum (qspec_then `h` mp_tac) >> simp[])
  >> match_mp_tac rei_sound_identity >> qexists_tac `env` >> fs[]
QED

(* ===== Lattice properties for convergence ===== *)

(* vr_union is absorptive: join(join(a,b),b) = join(a,b) *)
Triviality vr_union_absorb:
  ∀a b. vr_union (vr_union a b) b = vr_union a b
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[vr_union_def, integerTheory.INT_MIN, integerTheory.INT_MAX] >>
  intLib.ARITH_TAC
QED

(* vr_widen is absorptive *)
Triviality vr_widen_absorb:
  ∀a b. vr_widen (vr_widen a b) b = vr_widen a b
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[vr_widen_def, integerTheory.int_gt] >>
  rpt COND_CASES_TAC >> gvs[vr_widen_def, integerTheory.int_gt]
QED

(* vr_widen is idempotent *)
Triviality vr_widen_idem:
  ∀a. vr_widen a a = a
Proof
  Cases_on `a` >> simp[vr_widen_def, integerTheory.int_gt]
QED

(* range_normalize is idempotent *)
Triviality range_normalize_idem:
  ∀rs. range_normalize (range_normalize rs) = range_normalize rs
Proof
  simp[range_normalize_def] >>
  simp[finite_mapTheory.DRESTRICT_DRESTRICT] >>
  gen_tac >> AP_TERM_TAC >>
  simp[pred_setTheory.EXTENSION, pred_setTheory.IN_INTER,
       pred_setTheory.GSPECIFICATION,
       finite_mapTheory.FDOM_DRESTRICT] >>
  simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  gen_tac >> eq_tac >> rpt strip_tac >> gvs[]
QED

(* FDOM of range_normalize ⊆ FDOM of input *)
Triviality range_normalize_fdom:
  ∀rs. FDOM (range_normalize rs) ⊆ FDOM rs
Proof
  simp[range_normalize_def, finite_mapTheory.FDOM_DRESTRICT,
       pred_setTheory.SUBSET_INTER]
QED

(* FDOM of range_join_two is intersection *)
Triviality range_join_two_fdom:
  ∀s1 s2. FDOM (range_join_two s1 s2) = FDOM s1 ∩ FDOM s2
Proof
  simp[range_join_two_def, finite_mapTheory.FDOM_FMAP,
       finite_mapTheory.FDOM_FINITE, pred_setTheory.FINITE_INTER]
QED

(* vr_union is idempotent *)
Triviality vr_union_idem:
  ∀a. vr_union a a = a
Proof
  Cases_on `a` >>
  simp[vr_union_def, integerTheory.INT_MIN, integerTheory.INT_MAX]
QED

(* Helper: join_two f g = f when f's domain ⊆ g's domain and
   vr_union(f(k), g(k)) = f(k) for all k ∈ FDOM f *)
Triviality range_join_two_absorb:
  ∀f g.
    FDOM f ⊆ FDOM g ∧
    (∀k. k ∈ FDOM f ⇒ vr_union (f ' k) (rs_lookup g k) = f ' k) ⇒
    range_join_two f g = f
Proof
  rpt strip_tac >>
  simp[range_join_two_def] >>
  `FDOM f ∩ FDOM g = FDOM f` by
    metis_tac[pred_setTheory.SUBSET_INTER_ABSORPTION] >>
  pop_assum SUBST_ALL_TAC >>
  simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_FUN_FMAP,
       finite_mapTheory.FDOM_FINITE] >>
  rpt strip_tac >> Cases_on `x ∈ FDOM f` >> simp[finite_mapTheory.FLOOKUP_DEF] >>
  `x ∈ FDOM g` by metis_tac[pred_setTheory.SUBSET_DEF] >>
  simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF] >>
  res_tac >> gvs[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF]
QED

(* Helper: normalize preserves values of surviving entries *)
Triviality range_normalize_value:
  ∀rs k. k ∈ FDOM (range_normalize rs) ⇒
    (range_normalize rs) ' k = rs ' k
Proof
  simp[range_normalize_def, finite_mapTheory.FDOM_DRESTRICT,
       pred_setTheory.IN_INTER, pred_setTheory.GSPECIFICATION,
       finite_mapTheory.DRESTRICT_DEF]
QED

(* Helper: normalize(join_two(normalize A, B)) = normalize A
   when FDOM(normalize A) ⊆ FDOM B and vr_union absorbs *)
Triviality normalize_join_stable:
  ∀A B.
    FDOM (range_normalize A) ⊆ FDOM B ∧
    (∀k. k ∈ FDOM (range_normalize A) ⇒
      vr_union (A ' k) (rs_lookup B k) = A ' k) ⇒
    range_normalize (range_join_two (range_normalize A) B) =
    range_normalize A
Proof
  rpt strip_tac >>
  `range_join_two (range_normalize A) B = range_normalize A` by
    (irule range_join_two_absorb >> simp[] >>
     rpt strip_tac >>
     `(range_normalize A) ' k = A ' k` by
       (irule range_normalize_value >> simp[]) >>
     simp[]) >>
  simp[range_normalize_idem]
QED

(* Instantiation helper for normalize_join_stable with idem *)
Triviality normalize_join_self:
  ∀x. range_normalize (range_join_two (range_normalize x) x) =
      range_normalize x
Proof
  gen_tac >> irule normalize_join_stable >> simp[range_normalize_fdom] >>
  rpt strip_tac >>
  `(range_normalize x) ' k = x ' k` by
    (irule range_normalize_value >> simp[]) >>
  `k ∈ FDOM x` by
    metis_tac[range_normalize_fdom, pred_setTheory.SUBSET_DEF] >>
  simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF, vr_union_idem]
QED

(* range_join_opt absorption *)
Triviality range_join_opt_absorb:
  ∀a b. range_join_opt (range_join_opt a b) b = range_join_opt a b
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[range_join_opt_def, range_normalize_idem] >>
  irule normalize_join_stable >>
  (* Both goals (SOME/NONE and SOME/SOME) need FDOM subset + absorption.
     After irule, we have a conjunction: values absorb ∧ FDOM subset *)
  TRY (
    (* SOME/NONE case: A = x, B = x *)
    simp[range_normalize_fdom] >>
    rpt strip_tac >>
    `(range_normalize x) ' k = x ' k` by
      (irule range_normalize_value >> simp[]) >>
    `k ∈ FDOM x` by
      metis_tac[range_normalize_fdom, pred_setTheory.SUBSET_DEF] >>
    simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF, vr_union_idem] >>
    NO_TAC) >>
  (* SOME/SOME case: A = join_two x x', B = x' *)
  conj_tac
  >- (rpt strip_tac >>
      `(range_normalize (range_join_two x x')) ' k =
       (range_join_two x x') ' k` by
        (irule range_normalize_value >> simp[]) >>
      `k ∈ FDOM (range_join_two x x')` by
        metis_tac[range_normalize_fdom, pred_setTheory.SUBSET_DEF] >>
      fs[range_join_two_fdom, pred_setTheory.IN_INTER] >>
      `FINITE (FDOM x ∩ FDOM x')` by
        simp[pred_setTheory.FINITE_INTER, finite_mapTheory.FDOM_FINITE] >>
      fs[range_join_two_def, finite_mapTheory.FUN_FMAP_DEF,
         pred_setTheory.IN_INTER] >>
      simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF, vr_union_absorb])
  >> irule pred_setTheory.SUBSET_TRANS >>
  qexists_tac `FDOM (range_join_two x x')` >>
  simp[range_normalize_fdom, range_join_two_fdom,
       pred_setTheory.INTER_SUBSET]
QED

(* range_widen_states is idempotent: widen(x, x) = x *)
Triviality range_widen_states_idem:
  ∀x. range_widen_states x x = x
Proof
  gen_tac >> simp[range_widen_states_def] >>
  `FINITE (FDOM x)` by simp[finite_mapTheory.FDOM_FINITE] >>
  simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_FUN_FMAP] >>
  rpt strip_tac >> Cases_on `x' ∈ FDOM x` >>
  simp[finite_mapTheory.FLOOKUP_DEF] >>
  simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF,
       vr_widen_def] >>
  Cases_on `x ' x'` >> simp[vr_widen_def, integerTheory.int_gt]
QED

(* vr_widen VR_Top x = VR_Top *)
Triviality vr_widen_top_l:
  ∀x. vr_widen VR_Top x = VR_Top
Proof
  Cases_on `x` >> simp[vr_widen_def]
QED

(* Helper: rs_lookup through FUN_FMAP of vr_widen *)
Triviality rs_lookup_fun_fmap_widen:
  FINITE (FDOM b0) ∧ x ∈ FDOM b0 ⇒
  rs_lookup (FUN_FMAP (λv. vr_widen (rs_lookup n0 v) (rs_lookup b0 v))
     (FDOM b0)) x = vr_widen (rs_lookup n0 x) (rs_lookup b0 x)
Proof
  simp[rs_lookup_def, finite_mapTheory.FLOOKUP_FUN_FMAP]
QED

(* Core helper: normalize(widen_states(n, b)) = n when n's entries absorb
   under vr_widen and are not Top. *)
Triviality normalize_widen_stable:
  ∀n0 b0.
    FINITE (FDOM b0) ∧ FDOM n0 ⊆ FDOM b0 ∧
    (∀k. k ∈ FDOM n0 ⇒ vr_widen (n0 ' k) (rs_lookup b0 k) = n0 ' k) ∧
    (∀k. k ∈ FDOM n0 ⇒ ¬vr_is_top (n0 ' k)) ⇒
    range_normalize (range_widen_states n0 b0) = n0
Proof
  rpt strip_tac >>
  simp[range_normalize_def, range_widen_states_def,
       finite_mapTheory.fmap_eq_flookup,
       finite_mapTheory.FLOOKUP_DRESTRICT,
       finite_mapTheory.FLOOKUP_FUN_FMAP,
       finite_mapTheory.FDOM_FMAP] >>
  rpt strip_tac >>
  Cases_on `x ∈ FDOM b0` >> simp[rs_lookup_fun_fmap_widen] >>
  Cases_on `x ∈ FDOM n0`
  >- (res_tac >>
      sg `rs_lookup n0 x = n0 ' x`
      >- simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF] >>
      sg `rs_lookup b0 x = b0 ' x`
      >- (simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF] >>
          fs[pred_setTheory.SUBSET_DEF]) >>
      fs[finite_mapTheory.FLOOKUP_DEF])
  >- simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF,
          vr_widen_top_l, vr_is_top_def]
  >- (fs[pred_setTheory.SUBSET_DEF] >> res_tac)
  >- simp[finite_mapTheory.FLOOKUP_DEF]
QED

(* normalize(widen_states(normalize(widen_states(a,b)), b)) =
   normalize(widen_states(a,b)) — absorption via normalize_widen_stable *)
(* Helper: normalize entries are never vr_is_top *)
Triviality normalize_not_top:
  ∀rs k. k ∈ FDOM (range_normalize rs) ⇒
    ¬vr_is_top ((range_normalize rs) ' k)
Proof
  simp[range_normalize_def, finite_mapTheory.FDOM_DRESTRICT,
       finite_mapTheory.DRESTRICT_DEF,
       pred_setTheory.IN_INTER, pred_setTheory.GSPECIFICATION] >>
  rpt strip_tac >> rfs[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF]
QED

(* Helper: FDOM(normalize(widen_states a b)) ⊆ FDOM b *)
Triviality normalize_widen_fdom_sub:
  ∀a b. FDOM (range_normalize (range_widen_states a b)) ⊆ FDOM b
Proof
  rpt gen_tac >>
  irule pred_setTheory.SUBSET_TRANS >>
  qexists_tac `FDOM (range_widen_states a b)` >>
  simp[range_normalize_fdom, range_widen_states_def,
       finite_mapTheory.FDOM_FMAP]
QED

(* Helper: normalize value lookup for widen_states *)
Triviality normalize_widen_states_value:
  ∀a b k. k ∈ FDOM (range_normalize (range_widen_states a b)) ⇒
    (range_normalize (range_widen_states a b)) ' k =
    vr_widen (rs_lookup a k) (rs_lookup b k)
Proof
  rpt strip_tac >>
  sg `(range_normalize (range_widen_states a b)) ' k =
      (range_widen_states a b) ' k`
  >- (irule range_normalize_value >> simp[]) >>
  sg `k ∈ FDOM (range_widen_states a b)`
  >- (mp_tac range_normalize_fdom >>
      simp[pred_setTheory.SUBSET_DEF]) >>
  fs[range_widen_states_def, finite_mapTheory.FUN_FMAP_DEF]
QED

(* normalize(widen_states(normalize(widen_states(a,b)), b)) =
   normalize(widen_states(a,b)) — absorption via normalize_widen_stable *)
Triviality normalize_widen_absorb:
  ∀a b.
    range_normalize (range_widen_states (range_normalize (range_widen_states a b)) b) =
    range_normalize (range_widen_states a b)
Proof
  rpt gen_tac >>
  irule normalize_widen_stable >>
  simp[finite_mapTheory.FDOM_FINITE, normalize_widen_fdom_sub] >>
  conj_tac >- metis_tac[normalize_not_top] >>
  rpt strip_tac >> fs[normalize_widen_states_value, vr_widen_absorb]
QED

(* normalize(widen_states(normalize x, x)) = normalize x — self via stable *)
Triviality normalize_widen_self:
  ∀x. range_normalize (range_widen_states (range_normalize x) x) =
      range_normalize x
Proof
  gen_tac >>
  irule normalize_widen_stable >>
  simp[finite_mapTheory.FDOM_FINITE, range_normalize_fdom] >>
  conj_tac >- metis_tac[normalize_not_top] >>
  rpt strip_tac >>
  sg `(range_normalize x) ' k = x ' k`
  >- (irule range_normalize_value >> simp[]) >>
  sg `k ∈ FDOM x`
  >- (mp_tac range_normalize_fdom >>
      simp[pred_setTheory.SUBSET_DEF]) >>
  simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF, vr_widen_idem]
QED

(* range_widen_opt idempotent — with the equality guard, trivially true *)
Triviality range_widen_opt_idem:
  ∀a. range_widen_opt a a = a
Proof
  Cases_on `a` >> simp[range_widen_opt_def]
QED

(* range_widen_opt absorption *)
Triviality range_widen_opt_absorb:
  ∀a b. range_widen_opt (range_widen_opt a b) b = range_widen_opt a b
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[range_widen_opt_def] >>
  rpt (COND_CASES_TAC >> simp[range_widen_opt_def])
QED

(* ===== Fixpoint ===== *)

(* Entry identity when entry is FEMPTY: widen_opt always returns FEMPTY *)
Triviality widen_states_fempty_all_top:
  ∀x v. v ∈ FDOM x ⇒
    (range_widen_states FEMPTY x) ' v = VR_Top
Proof
  rpt strip_tac >>
  simp[range_widen_states_def, finite_mapTheory.FUN_FMAP_DEF] >>
  simp[rs_lookup_def, finite_mapTheory.FLOOKUP_EMPTY, vr_widen_def] >>
  CASE_TAC >> simp[vr_widen_def] >> CASE_TAC >> simp[]
QED

Triviality normalize_all_top_fempty:
  ∀fm. (∀v. v ∈ FDOM fm ⇒ fm ' v = VR_Top) ⇒
    range_normalize fm = FEMPTY
Proof
  rpt strip_tac >>
  simp[range_normalize_def, finite_mapTheory.fmap_eq_flookup,
       finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_EMPTY] >>
  rpt strip_tac >>
  Cases_on `x ∈ FDOM fm` >> simp[] >>
  res_tac >> simp[vr_is_top_def, rs_lookup_def, finite_mapTheory.FLOOKUP_DEF]
QED

Triviality widen_opt_fempty_stable:
  ∀x. range_widen_opt (SOME FEMPTY) x = SOME FEMPTY
Proof
  Cases_on `x` >> simp[range_widen_opt_def]
QED

(* Widen dichotomy: result is either SOME FEMPTY or identity *)
Triviality widen_opt_dichotomy[local]:
  ∀a b. range_widen_opt a b = SOME FEMPTY ∨ range_widen_opt a b = a
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[range_widen_opt_def] >>
  rpt (COND_CASES_TAC >> simp[])
QED

(* Edge symmetry holds unconditionally for cfg_analyze.
   build_succs only maps block labels, build_preds inverts exactly. *)
Triviality cfg_edge_symmetry_always:
  ∀fn a b.
    MEM b (cfg_succs_of (cfg_analyze fn) a) ⇔
    MEM a (cfg_preds_of (cfg_analyze fn) b)
Proof
  rpt strip_tac >>
  simp[cfgHelpersTheory.cfg_analyze_succs,
       cfgHelpersTheory.cfg_analyze_preds,
       cfgHelpersTheory.mem_build_preds] >>
  eq_tac >> rpt strip_tac >> gvs[]
  >- (`MEM a (MAP (λbb. bb.bb_label) fn.fn_blocks)` by
        (CCONTR_TAC >>
         imp_res_tac cfgHelpersTheory.cfg_succs_of_not_in_labels >> fs[]) >>
      fs[listTheory.MEM_MAP] >> metis_tac[])
QED

(* Helper: dfs_post labels are in dfs_pre *)
Triviality cfg_dfs_post_mem_pre_local:
  ∀fn lbl.
    MEM lbl (cfg_analyze fn).cfg_dfs_post ⇒
    MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  rw[cfgHelpersTheory.cfg_analyze_dfs_post,
     cfgHelpersTheory.cfg_analyze_dfs_pre] >>
  Cases_on `entry_block fn` >> fs[] >>
  metis_tac[cfgHelpersTheory.dfs_post_walk_sound_thm,
            cfgHelpersTheory.dfs_pre_walk_complete]
QED

Triviality cfg_succs_closure[local]:
  ∀fn lbl.
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ⇒
    EVERY (λs. MEM s (cfg_analyze fn).cfg_dfs_pre)
      (cfg_succs_of (cfg_analyze fn) lbl)
Proof
  rw[listTheory.EVERY_MEM, cfgHelpersTheory.cfg_analyze_dfs_pre,
     cfgDefsTheory.cfg_succs_of_def] >>
  Cases_on `entry_block fn` >> fs[] >> rpt strip_tac >>
  `(cfg_analyze fn).cfg_succs = build_succs fn.fn_blocks` by
    (simp[cfgDefsTheory.cfg_analyze_def] >>
     Cases_on `entry_block fn` >> simp[] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[]) >>
  fs[] >>
  `MEM s (FST (dfs_pre_walk (build_succs fn.fn_blocks) [] x.bb_label))` by
    metis_tac[cfgHelpersTheory.dfs_pre_walk_closure |> CONJUNCT1] >>
  mp_tac (Q.SPECL [`build_succs fn.fn_blocks`, `[] : string list`,
                    `x.bb_label`]
    (CONJUNCT1 (INST_TYPE [alpha |-> ``:string``]
      cfgHelpersTheory.dfs_pre_walk_visited_eq))) >>
  simp[pred_setTheory.UNION_EMPTY, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

(* === Fixpoint infrastructure ===
   Named invariant P for the by_visits convergence proof.
   Extracted as a Definition to avoid lambda/beta issues in batch mode. *)
Definition range_fold_result_def:
  range_fold_result fn st lbl =
    df_fold_block Forward
      (range_transfer_opt (dfg_build_function fn, fn.fn_blocks))
      lbl
      (case lookup_block lbl fn.fn_blocks of
         NONE => [] | SOME bb => bb.bb_instructions)
      (df_widen_entry NONE st lbl)
End

Triviality submap_funion_disjoint[local]:
  ∀a b c. DISJOINT (FDOM a) (FDOM b) ∧ a ⊑ c ⇒ a ⊑ b ⊌ c
Proof
  rw[finite_mapTheory.SUBMAP_DEF, finite_mapTheory.FLOOKUP_FUNION,
     finite_mapTheory.FDOM_FUNION] >>
  rpt strip_tac >> res_tac >> fs[] >>
  fs[pred_setTheory.IN_DISJOINT] >>
  `x NOTIN FDOM b` by metis_tac[] >>
  simp[finite_mapTheory.FUNION_DEF]
QED

Definition range_fixpoint_P_def:
  range_fixpoint_P fn st ⇔
    ∀lbl.
      (df_widen_visits st lbl > 0 ⇒
        FLOOKUP st.dws_boundary lbl =
          SOME (df_widen_boundary NONE st lbl) ∧
        FLOOKUP st.dws_entry lbl =
          SOME (df_widen_entry NONE st lbl) ∧
        range_join_opt (df_widen_boundary NONE st lbl)
          (FST (range_fold_result fn st lbl)) =
          df_widen_boundary NONE st lbl ∧
        SND (range_fold_result fn st lbl) SUBMAP st.dws_inst) ∧
      (df_widen_visits st lbl > WIDEN_THRESHOLD ⇒
        df_widen_entry NONE st lbl = SOME FEMPTY)
End

(* --- P_preserved decomposed into helpers to avoid huge unfolded goals --- *)

(* Helper: identity-widen case → 3-field record equals st *)
Triviality range_process_identity[local]:
  ∀fn lbl st final_val inst_map.
    range_fixpoint_P fn st ⇒
    df_widen_visits st lbl > 0 ⇒
    df_fold_block Forward (range_transfer_opt (dfg_build_function fn, fn.fn_blocks))
      lbl (case lookup_block lbl fn.fn_blocks of NONE => [] | SOME bb => bb.bb_instructions)
      (df_widen_entry NONE st lbl) = (final_val, inst_map) ⇒
    st with <|dws_boundary := st.dws_boundary |+ (lbl,
                range_join_opt (df_widen_boundary NONE st lbl) final_val);
              dws_entry := st.dws_entry |+ (lbl, df_widen_entry NONE st lbl);
              dws_inst := inst_map ⊌ st.dws_inst|> = st
Proof
  rpt strip_tac >>
  fs[range_fixpoint_P_def, range_fold_result_def] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >> strip_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_widen_state_component_equality] >>
  rpt conj_tac >>
  TRY (irule finite_mapTheory.FUPDATE_ELIM >>
       fs[df_widen_boundary_def, df_widen_entry_def,
          finite_mapTheory.FLOOKUP_DEF] >> NO_TAC) >>
  fs[finite_mapTheory.SUBMAP_FUNION_ABSORPTION]
QED

(* P at lbl when visits > WT: widen either gives SOME FEMPTY or
   returns identity (old_entry), in which case process = st. *)
Triviality range_P_entry_fempty[local]:
  ∀fn lbl st entry joined final_val inst_map.
    range_fixpoint_P fn st ⇒
    df_widen_visits st lbl >= WIDEN_THRESHOLD ⇒
    entry = range_widen_opt (df_widen_entry NONE st lbl) joined ⇒
    df_fold_block Forward (range_transfer_opt (dfg_build_function fn, fn.fn_blocks))
      lbl (case lookup_block lbl fn.fn_blocks of NONE => [] | SOME bb => bb.bb_instructions)
      entry = (final_val, inst_map) ⇒
    st with <|dws_boundary := st.dws_boundary |+ (lbl,
                range_join_opt (df_widen_boundary NONE st lbl) final_val);
              dws_entry := st.dws_entry |+ (lbl, entry);
              dws_inst := inst_map ⊌ st.dws_inst|> ≠ st ⇒
    entry = SOME FEMPTY
Proof
  rpt strip_tac >>
  `df_widen_visits st lbl > 0` by (
    `WIDEN_THRESHOLD > 0` by simp[WIDEN_THRESHOLD_def] >> DECIDE_TAC) >>
  `range_widen_opt (df_widen_entry NONE st lbl) joined = SOME FEMPTY ∨
   range_widen_opt (df_widen_entry NONE st lbl) joined =
     df_widen_entry NONE st lbl` by
    simp[widen_opt_dichotomy] >>
  fs[] >>
  (* Identity case: entry = old_entry → record = st → contradiction *)
  qpat_x_assum `entry = _` (SUBST_ALL_TAC) >>
  `F` suffices_by simp[] >>
  qpat_x_assum `_ ≠ st` mp_tac >>
  mp_tac range_process_identity >>
  disch_then (qspecl_then [`fn`, `lbl`, `st`, `final_val`, `inst_map`] mp_tac) >>
  simp[]
QED

(* P is preserved by processing any block *)
Triviality range_fixpoint_P_preserved[local]:
  ∀fn lbl st.
    range_fixpoint_P fn st ⇒
    range_fixpoint_P fn
      (df_process_block_widen Forward NONE range_join_opt range_widen_opt
         WIDEN_THRESHOLD range_transfer_opt range_edge_transfer_opt
         (dfg_build_function fn, fn.fn_blocks)
         (OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [dfAnalyzeWidenDefsTheory.df_process_block_widen_def,
                   LET_THM,
                   dfAnalyzeDefsTheory.direction_case_def] >>
  pairarg_tac >> simp_tac std_ss [] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  IF_CASES_TAC >- simp[] >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `st.dws_entry |+ (lbl, entry_val)` >>
  simp[range_fixpoint_P_def, range_fold_result_def,
       df_widen_visits_def, df_widen_entry_def, df_widen_boundary_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >>
  qpat_x_assum `range_fixpoint_P _ _`
    (fn th => assume_tac th >>
      assume_tac (SIMP_RULE std_ss
        [range_fixpoint_P_def, range_fold_result_def] th)) >>
  reverse (Cases_on `lbl' = lbl`)
  (* -- lbl' ≠ lbl -- *)
  >- (
    simp[] >>
    first_x_assum (qspec_then `lbl'` mp_tac) >> strip_tac >>
    conj_tac
    >- (strip_tac >>
        `df_widen_visits st lbl' > 0` by fs[df_widen_visits_def] >>
        res_tac >> fs[] >>
        irule submap_funion_disjoint >> simp[] >>
        metis_tac[dfAnalyzeWidenProofsTheory.fold_inst_disjoint,
                  pairTheory.PAIR])
    >> (strip_tac >>
        `df_widen_visits st lbl' > WIDEN_THRESHOLD` by
          fs[df_widen_visits_def] >>
        res_tac >> fs[df_widen_entry_def]))
  >> (* -- lbl' = lbl -- *)
  pop_assum SUBST_ALL_TAC >> simp[] >>
  conj_tac
  >- (strip_tac >> simp[] >>
      simp[range_join_opt_absorb, finite_mapTheory.SUBMAP_FUNION_ID])
  >> strip_tac >>
  Cases_on `FLOOKUP st.dws_visits lbl`
  >- fs[WIDEN_THRESHOLD_def]
  >> `df_widen_visits st lbl >= WIDEN_THRESHOLD` by
    fs[df_widen_visits_def, WIDEN_THRESHOLD_def] >>
  `df_widen_visits st lbl > WIDEN_THRESHOLD \/
   df_widen_visits st lbl = WIDEN_THRESHOLD` by DECIDE_TAC
  >- ((* visits > WT: old entry FEMPTY, widen of FEMPTY = FEMPTY *)
    first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >> strip_tac >>
    qunabbrev_tac `entry_val` >> simp[widen_opt_fempty_stable])
  >> (* visits = WT: threshold crossing, use dichotomy *)
  qunabbrev_tac `entry_val` >> simp[] >>
  qmatch_goalsub_abbrev_tac `range_widen_opt _ joined` >>
  DISJ_CASES_TAC (Q.SPECL [`df_widen_entry NONE st lbl`, `joined`]
    (INST_TYPE [alpha |-> ``:string``, beta |-> ``:value_range``]
      widen_opt_dichotomy))
  >- first_x_assum ACCEPT_TAC
  >> (* Identity case: entry = old_entry → process = st → contradiction *)
  `F` suffices_by simp[] >>
  `df_widen_visits st lbl > 0` by
    (fs[dfAnalyzeWidenDefsTheory.df_widen_visits_def,
        WIDEN_THRESHOLD_def] >> DECIDE_TAC) >>
  qpat_x_assum `_ <> st` mp_tac >>
  mp_tac range_process_identity >>
  disch_then (qspecl_then [`fn`, `lbl`, `st`, `final_val`, `inst_map`]
    mp_tac) >>
  simp[] >>
  qpat_x_assum `df_fold_block _ _ _ _ _ = _` mp_tac >> simp[]
QED

(* P holds for the initial state *)
Triviality range_fixpoint_P_initial[local]:
  ∀fn.
    case OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
      NONE =>
        range_fixpoint_P fn
          (init_df_widen_state NONE (MAP (λbb. bb.bb_label) fn.fn_blocks))
    | SOME (lbl, v) =>
        range_fixpoint_P fn
          (init_df_widen_state NONE (MAP (λbb. bb.bb_label) fn.fn_blocks)
           with dws_boundary :=
             (init_df_widen_state NONE
                (MAP (λbb. bb.bb_label) fn.fn_blocks)).dws_boundary |+ (lbl, v))
Proof
  rpt gen_tac >>
  Cases_on `fn_entry_label fn` >>
  simp[range_fixpoint_P_def, init_df_widen_state_def, df_widen_visits_def,
       finite_mapTheory.FLOOKUP_EMPTY, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* P ∧ visits ≥ K ⇒ process is identity *)
Triviality range_fixpoint_P_stabilization[local]:
  ∀fn lbl st.
    range_fixpoint_P fn st ∧
    df_widen_visits st lbl ≥ WIDEN_THRESHOLD + 1 ⇒
    df_process_block_widen Forward NONE range_join_opt range_widen_opt
      WIDEN_THRESHOLD range_transfer_opt range_edge_transfer_opt
      (dfg_build_function fn, fn.fn_blocks)
      (OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st = st
Proof
  rpt gen_tac >> strip_tac >>
  `df_widen_visits st lbl > WIDEN_THRESHOLD` by DECIDE_TAC >>
  `df_widen_visits st lbl > 0` by DECIDE_TAC >>
  (* Unfold process_block_widen *)
  simp_tac std_ss [dfAnalyzeWidenDefsTheory.df_process_block_widen_def,
    LET_THM, dfAnalyzeDefsTheory.direction_case_def] >>
  pairarg_tac >> simp_tac std_ss [] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  (* Show computed entry = SOME FEMPTY via P *)
  `df_widen_entry NONE st lbl = SOME FEMPTY` by
    (fs[range_fixpoint_P_def] >> res_tac) >>
  `df_widen_visits st lbl >= WIDEN_THRESHOLD` by DECIDE_TAC >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `range_widen_opt (SOME FEMPTY) joined_val` >>
  `range_widen_opt (SOME FEMPTY) joined_val = SOME FEMPTY` by
    (Cases_on `joined_val` >> simp[range_widen_opt_def]) >>
  simp[] >>
  (* 3-field record = st follows from range_process_identity *)
  mp_tac range_process_identity >>
  disch_then (qspecl_then [`fn`, `lbl`, `st`, `final_val`, `inst_map`] mp_tac) >>
  simp[] >>
  rpt strip_tac >> gvs[]
QED

(* The range analysis computes a fixpoint.
   Uses by_visits with K = WIDEN_THRESHOLD + 1 and range_fixpoint_P. *)
Theorem range_fixpoint[local]:
  ∀fn.
    let cfg = cfg_analyze fn in
    let ra = range_analyze fn in
    let process = df_process_block_widen Forward NONE
          range_join_opt range_widen_opt WIDEN_THRESHOLD
          range_transfer_opt range_edge_transfer_opt
          (dfg_build_function fn, fn.fn_blocks)
          (OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
          cfg fn.fn_blocks in
    is_fixpoint process cfg.cfg_dfs_pre ra
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM, range_analyze_def] >>
  irule (SIMP_RULE std_ss [LET_THM] df_analyze_widen_fixpoint_by_visits) >>
  rpt conj_tac
  >- simp[range_join_opt_absorb]
  >- simp[range_widen_opt_absorb]
  >- simp[range_widen_opt_idem]
  >- simp[cfg_edge_symmetry_always]
  >- simp[cfg_succs_closure]
  (* K and P *)
  >> qexistsl_tac [`WIDEN_THRESHOLD + 1`, `range_fixpoint_P fn`] >>
  simp[range_fixpoint_P_preserved, range_fixpoint_P_stabilization] >>
  mp_tac (Q.SPEC `fn` range_fixpoint_P_initial) >>
  Cases_on `OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)` >>
  simp[]
QED

(* ===== in_range_state monotonicity ===== *)

Triviality in_range_state_weaken:
  ∀rs1 rs2 env.
    in_range_state rs1 env ∧ FDOM rs2 ⊆ FDOM rs1 ∧
    (∀v. v ∈ FDOM rs2 ⇒ FLOOKUP rs2 v = FLOOKUP rs1 v) ⇒
    in_range_state rs2 env
Proof
  rw[in_range_state_def] >>
  `v ∈ FDOM rs2` by fs[finite_mapTheory.FLOOKUP_DEF] >>
  `v ∈ FDOM rs1` by fs[pred_setTheory.SUBSET_DEF] >>
  `FLOOKUP rs2 v = FLOOKUP rs1 v` by res_tac >>
  gvs[] >> res_tac
QED

(* join_two is sound from right argument alone *)
Triviality range_join_two_sound_r[local]:
  ∀s1 s2 env.
    in_range_state s2 env ⇒
    in_range_state (range_join_two s1 s2) env
Proof
  rw[in_range_state_def, range_join_two_def] >>
  `FINITE (FDOM s1 ∩ FDOM s2)` by
    simp[pred_setTheory.FINITE_INTER, finite_mapTheory.FDOM_FINITE] >>
  fs[finite_mapTheory.FLOOKUP_FUN_FMAP] >>
  (* Goal: in_range (vr_union (rs_lookup s1 v) (rs_lookup s2 v)) w *)
  `∃r2. FLOOKUP s2 v = SOME r2 ∧ in_range r2 w` by
    (fs[finite_mapTheory.FLOOKUP_DEF] >> res_tac >> metis_tac[]) >>
  `rs_lookup s2 v = r2` by
    simp[rs_lookup_def, finite_mapTheory.FLOOKUP_DEF] >>
  gvs[] >> irule in_range_union_r >> simp[]
QED

(* normalize preserves soundness *)
Triviality range_normalize_sound[local]:
  ∀rs env.
    in_range_state rs env ⇒
    in_range_state (range_normalize rs) env
Proof
  rw[in_range_state_def, range_normalize_def,
     finite_mapTheory.FLOOKUP_DRESTRICT] >>
  res_tac
QED

(* Boundary absorption: if join(a, SOME x) = a and x is sound,
   then range_unwrap a is sound. Used for exit_state soundness. *)
Triviality range_join_absorb_sound[local]:
  ∀a x env.
    range_join_opt a (SOME x) = a ∧ in_range_state x env ⇒
    in_range_state (range_unwrap a) env
Proof
  Cases_on `a` >> simp[range_join_opt_def, range_unwrap_def] >>
  rpt strip_tac >>
  (* SOME case: normalize(join_two x' x) = x', in_range_state x env *)
  (* Chain: x sound → join_two x' x sound → normalize sound = x' sound *)
  `in_range_state (range_join_two x x') env` by
    metis_tac[range_join_two_sound_r] >>
  `in_range_state (range_normalize (range_join_two x x')) env` by
    metis_tac[range_normalize_sound] >>
  gvs[]
QED

(*
 * COUNTEREXAMPLE (range_analyze_block_sound without vs_inst_idx = 0):
 *
 * The original statement is universally quantified over s without
 * constraining s.vs_inst_idx.  It is FALSE when vs_inst_idx > 0:
 *
 *   Block bb = [x := Lit 1w, JMP lbl], entry block with no predecessors.
 *   Analysis: entry_state = FEMPTY, exit_state = {x : VR_Range 1 1}.
 *   State s with vs_inst_idx = 1, vs_vars = {x : 3w}.
 *     • in_range_state FEMPTY {x:3w} = T  (FEMPTY has no constraints)
 *     • exec_block skips instruction 0, executes JMP → OK s'
 *     • s'.vs_vars = {x:3w} (JMP preserves vars)
 *     • in_range_state {x:[1,1]} {x:3w} = F  (3 ∉ [1,1])
 *
 * FIX: added s.vs_inst_idx = 0 hypothesis.  All consumers call exec_block
 * after jump_to which sets vs_inst_idx := 0, so no downstream breakage.
 *)

(* Terminators returning OK preserve vs_vars (JMP/JNZ/DJMP use jump_to). *)
Triviality step_terminator_preserves_vars[local]:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    is_terminator inst.inst_opcode ⇒
    s'.vs_vars = s.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  rpt (pop_assum mp_tac) >> simp[is_terminator_def] >>
  rpt strip_tac >> fs[step_inst_def, step_inst_base_def] >>
  BasicProvers.every_case_tac >> gvs[jump_to_def]
QED
(* For any instruction where step_inst returns OK:
   range_evaluate_inst preserves in_range_state, given appropriate
   hypotheses on the output value.  This wraps range_evaluate_inst_sound
   with the step_inst frame conditions. *)
Triviality step_range_sound[local]:
  ∀fuel ctx inst s s' rs dfg.
    step_inst fuel ctx inst s = OK s' ∧
    in_range_state rs s.vs_vars ∧
    (* single-output non-PHI: eval_range is sound *)
    (∀out. inst.inst_opcode ≠ PHI ∧ inst.inst_outputs = [out] ⇒
      ∀w. FLOOKUP s'.vs_vars out = SOME w ⇒
        in_range (eval_range inst.inst_opcode
                   (MAP (operand_range rs) inst.inst_operands)
                   (MAP operand_lit inst.inst_operands)) w) ⇒
    in_range_state (range_evaluate_inst dfg inst rs) s'.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac range_evaluate_inst_sound >>
  qexists_tac `s.vs_vars` >> rpt conj_tac >> fs[] >>
  rpt strip_tac >>
  reverse (Cases_on `is_terminator inst.inst_opcode`)
  >- (mp_tac step_preserves_non_output_vars >>
      disch_then drule >> simp[] >>
      disch_then (qspec_then `v` mp_tac) >> simp[lookup_var_def])
  >> drule_all step_terminator_preserves_vars >> simp[]
QED

(* range_unwrap distributes through range_transfer_opt *)
Triviality range_unwrap_transfer[local]:
  ∀dfg bbs inst rs.
    range_unwrap (range_transfer_opt (dfg, bbs) inst rs) =
    range_evaluate_inst dfg inst (range_unwrap rs)
Proof
  rpt gen_tac >> Cases_on `rs` >>
  simp[range_transfer_opt_def, range_unwrap_def]
QED

(* bb_well_formed: if a later instruction is PHI, earlier ones are too *)
Triviality wf_phi_earlier[local]:
  ∀bb idx j.
    bb_well_formed bb ∧ idx < j ∧
    j < LENGTH bb.bb_instructions ∧
    (EL j bb.bb_instructions).inst_opcode = PHI ⇒
    (EL idx bb.bb_instructions).inst_opcode = PHI
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >> res_tac
QED

(* MEM in DROP (SUC idx) with opcode = PHI ⇒ EL idx is also PHI *)
Triviality wf_phi_from_drop_suc[local]:
  ∀bb idx inst.
    bb_well_formed bb ∧ idx < LENGTH bb.bb_instructions ∧
    MEM inst (DROP (SUC idx) bb.bb_instructions) ∧
    inst.inst_opcode = PHI ⇒
    (EL idx bb.bb_instructions).inst_opcode = PHI
Proof
  rpt strip_tac
  >> fs[listTheory.MEM_EL]
  >> `n + SUC idx < LENGTH bb.bb_instructions` by DECIDE_TAC
  >> `(DROP (SUC idx) bb.bb_instructions)❲n❳ =
       bb.bb_instructions❲n + SUC idx❳` by
       (irule listTheory.EL_DROP >> DECIDE_TAC)
  >> `idx < n + SUC idx` by DECIDE_TAC
  >> match_mp_tac wf_phi_earlier
  >> qexists_tac `n + SUC idx`
  >> gvs[]
QED

(* Core induction: fold over instructions preserves in_range_state.
   Uses completeInduct_on for clean IH targeting.

   The per-inst hypothesis is weakened for PHI: it only needs to hold
   when rs_val = range_unwrap rs (the initial entry state), because
   range_evaluate_inst is identity for PHI and bb_well_formed ensures
   all PHIs precede non-PHIs, so the accumulated range state at any
   PHI instruction equals the initial entry state. *)
Triviality fold_exec_block_sound[local]:
  ∀idx fuel ctx (bb : basic_block) (bbs : basic_block list)
   s s' rs (dfg : dfg_analysis) (lbl : string) im.
    bb_well_formed bb ∧
    s.vs_inst_idx = idx ∧
    idx ≤ LENGTH bb.bb_instructions ∧
    in_range_state (range_unwrap rs) s.vs_vars ∧
    exec_block fuel ctx bb s = OK s' ∧
    (∀inst rs_val s_pre s_post.
       MEM inst (DROP idx bb.bb_instructions) ∧
       step_inst fuel ctx inst s_pre = OK s_post ∧
       in_range_state rs_val s_pre.vs_vars ⇒
       in_range_state (range_evaluate_inst dfg inst rs_val) s_post.vs_vars) ⇒
    in_range_state
      (range_unwrap (FST (df_fold_forward
        (λinst acc. range_transfer_opt (dfg, bbs) inst acc)
        lbl (DROP idx bb.bb_instructions) idx rs im))) s'.vs_vars
Proof
  completeInduct_on `LENGTH bb.bb_instructions - idx`
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ `∀i. i < LENGTH bb.bb_instructions ∧
          is_terminator (EL i bb.bb_instructions).inst_opcode ⇒
          i = PRE (LENGTH bb.bb_instructions)` by fs[bb_well_formed_def]
  \\ Cases_on `idx = LENGTH bb.bb_instructions`
  >- (
    fs[listTheory.DROP_LENGTH_NIL,
       dfAnalyzeDefsTheory.df_fold_forward_def]
    \\ qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac
    \\ asm_simp_tac std_ss [Once exec_block_def, get_instruction_def]
    \\ simp[]
  )
  \\ `idx < LENGTH bb.bb_instructions` by DECIDE_TAC
  \\ `DROP idx bb.bb_instructions =
      EL idx bb.bb_instructions :: DROP (SUC idx) bb.bb_instructions` by (
       imp_res_tac rich_listTheory.DROP_CONS_EL \\ fs[])
  \\ asm_simp_tac std_ss [dfAnalyzeDefsTheory.df_fold_forward_def, LET_THM]
  \\ qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac
  \\ asm_simp_tac std_ss [Once exec_block_def, get_instruction_def]
  \\ Cases_on `step_inst fuel ctx (EL idx bb.bb_instructions) s`
  \\ simp[] \\ rename [`step_inst _ _ _ _ = OK step_st`]
  \\ reverse (Cases_on `is_terminator (EL idx bb.bb_instructions).inst_opcode`)
  >- (
    (* Non-terminator case *)
    asm_rewrite_tac [] \\ strip_tac
    \\ qpat_x_assum `∀m. m < v ⇒ _`
      (qspec_then `LENGTH bb.bb_instructions - SUC idx` mp_tac)
    \\ impl_tac >- DECIDE_TAC
    \\ disch_then (qspec_then `bb` mp_tac)
    \\ disch_then (qspec_then `SUC idx` mp_tac)
    \\ impl_tac >- DECIDE_TAC
    \\ disch_then (qspecl_then [`fuel`, `ctx`, `bbs`,
         `step_st with vs_inst_idx := SUC idx`,
         `s'`,
         `range_transfer_opt (dfg,bbs) (EL idx bb.bb_instructions) rs`,
         `dfg`, `lbl`,
         `im |+ ((lbl, idx), rs)`] mp_tac)
    \\ simp_tac std_ss [range_unwrap_transfer]
    \\ impl_tac
    >- (
      conj_tac >- fs[] (* bb_well_formed *)
      \\ conj_tac >- simp[] (* vs_inst_idx *)
      \\ conj_tac >- DECIDE_TAC (* SUC idx ≤ LENGTH *)
      \\ conj_tac
      >- (
        (* in_range_state for step_st: per-inst on EL idx *)
        qpat_x_assum `∀inst rs_val s_pre s_post. _`
          (qspecl_then [`EL idx bb.bb_instructions`, `range_unwrap rs`,
                        `s`, `step_st`] mp_tac)
        \\ impl_tac
        >- (
          conj_tac
          >- (qpat_x_assum `DROP idx _ = _ :: _` (fn th =>
                ONCE_REWRITE_TAC [th]) \\ simp[])
          \\ fs[]
        )
        \\ simp[]
      )
      \\ conj_tac >- fs[] (* exec_block *)
      (* Pass per-inst hypothesis to IH: DROP (SUC idx) ⊆ DROP idx *)
      \\ rpt strip_tac
      \\ qpat_x_assum `∀inst rs_val s_pre s_post. _`
           (qspecl_then [`inst`, `rs_val`, `s_pre`, `s_post`] mp_tac)
      \\ impl_tac
      >- (
        conj_tac
        >- (qpat_x_assum `DROP idx _ = _ :: _` (fn th =>
              ONCE_REWRITE_TAC [th]) \\ simp[] \\ fs[])
        \\ fs[]
      )
      \\ simp[]
    )
    \\ simp[arithmeticTheory.ADD1]
  )
  \\ (* Terminator case *)
  `idx = PRE (LENGTH bb.bb_instructions)` by (
    qpat_x_assum `∀i. _ ⇒ i = PRE _`
      (qspec_then `idx` mp_tac)
    \\ asm_rewrite_tac [] \\ DECIDE_TAC)
  \\ `SUC idx = LENGTH bb.bb_instructions` by DECIDE_TAC
  \\ `DROP (SUC idx) bb.bb_instructions = [] : instruction list`
       by asm_simp_tac std_ss [listTheory.DROP_LENGTH_NIL]
  \\ asm_rewrite_tac []
  \\ Cases_on `step_st.vs_halted` \\ asm_rewrite_tac []
  >- simp_tac std_ss [exec_result_distinct]
  \\ qpat_x_assum `∀i. _ ⇒ i = PRE _` kall_tac
  \\ REWRITE_TAC [exec_result_11] \\ strip_tac
  \\ pop_assum SUBST_ALL_TAC
  \\ asm_simp_tac std_ss
    [dfAnalyzeDefsTheory.df_fold_forward_def, range_unwrap_transfer,
     arithmeticTheory.ADD1]
  \\ qpat_x_assum `∀inst rs_val s_pre s_post. _`
    (qspecl_then [`EL idx bb.bb_instructions`, `range_unwrap rs`,
                  `s`, `s'`] mp_tac)
  \\ impl_tac
  >- (
    conj_tac
    >- (qpat_x_assum `DROP idx _ = _ :: _` (fn th =>
          ONCE_REWRITE_TAC [th]) \\ simp[])
    \\ asm_rewrite_tac []
  )
  \\ asm_rewrite_tac []
QED

(* range_transfer_opt always returns SOME *)
Triviality range_transfer_opt_some[local]:
  ∀ctx inst acc. ∃rs. range_transfer_opt ctx inst acc = SOME rs
Proof
  rpt gen_tac >> Cases_on `acc` >>
  simp[range_transfer_opt_def]
QED

(* Folding range_transfer_opt over a SOME accumulator preserves SOME *)
Triviality fold_forward_some_preserves[local]:
  ∀instrs ctx (lbl : string) idx rs
   (im : (string # num |-> (string |-> value_range) option)).
    ∃rs'. FST (df_fold_forward
      (λinst a. range_transfer_opt ctx inst a)
      lbl instrs idx (SOME rs) im) = SOME rs'
Proof
  Induct >>
  simp[dfAnalyzeDefsTheory.df_fold_forward_def, LET_THM] >>
  rpt gen_tac >>
  `∃rs0. range_transfer_opt ctx h (SOME rs) = SOME rs0` by
    simp[range_transfer_opt_def] >>
  simp[]
QED

(* After folding ≥1 instruction, result is always SOME *)
Triviality fold_forward_range_some[local]:
  ∀instrs ctx (lbl : string) idx acc
   (im : (string # num |-> (string |-> value_range) option)).
    instrs ≠ [] ⇒
    ∃rs. FST (df_fold_forward
      (λinst a. range_transfer_opt ctx inst a)
      lbl instrs idx acc im) = SOME rs
Proof
  Cases >> simp[] >> rpt gen_tac >>
  simp[dfAnalyzeDefsTheory.df_fold_forward_def, LET_THM] >>
  `∃rs0. range_transfer_opt ctx h acc = SOME rs0` by
    metis_tac[range_transfer_opt_some] >>
  simp[] >> metis_tac[fold_forward_some_preserves]
QED

(* Combined invariant: range_fixpoint_P + visits bound + unvisited boundary.
   Gives everything needed for block soundness proof.
   Uses df_widen_process_boundary_other from dfAnalyzeWidenProofs. *)
Triviality foldl_update_all_same[local]:
  ∀lbls v fm k w.
    FLOOKUP (FOLDL (λm l. m |+ (l, v)) fm lbls) k = SOME w ⇒
    w = v ∨ FLOOKUP fm k = SOME w
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  res_tac >> simp[] >>
  fs[finite_mapTheory.FLOOKUP_UPDATE] >>
  BasicProvers.every_case_tac >> fs[]
QED

Triviality init_boundary_none[local]:
  ∀lbls lbl.
    df_widen_boundary NONE (init_df_widen_state NONE lbls) lbl = NONE
Proof
  rpt gen_tac >>
  simp[df_widen_boundary_def, init_df_widen_state_def] >>
  CASE_TAC >> simp[] >>
  imp_res_tac foldl_update_all_same >>
  fs[finite_mapTheory.FLOOKUP_EMPTY]
QED

(* Specialize visits_inc to range analysis parameters *)
Triviality range_visits_inc[local]:
  ∀fn lbl st.
    let process = df_process_block_widen Forward NONE
          range_join_opt range_widen_opt WIDEN_THRESHOLD
          range_transfer_opt range_edge_transfer_opt
          (dfg_build_function fn, fn.fn_blocks)
          (OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
          (cfg_analyze fn) fn.fn_blocks in
    let st' = process lbl st in
    st' = st ∨
    (df_widen_visits st' lbl = df_widen_visits st lbl + 1 ∧
     ∀l. l ≠ lbl ⇒ df_widen_visits st' l = df_widen_visits st l)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  mp_tac (INST_TYPE [alpha |-> ``:(string |-> value_range) option``,
                     beta |-> ``:dfg_analysis # basic_block list``]
    (SIMP_RULE std_ss [LET_THM]
      dfAnalyzeWidenProofsTheory.df_widen_process_visits_inc)) >>
  disch_then (qspecl_then [`Forward`, `NONE`,
    `range_join_opt`, `range_widen_opt`, `WIDEN_THRESHOLD`,
    `range_transfer_opt`, `range_edge_transfer_opt`,
    `(dfg_build_function fn, fn.fn_blocks)`,
    `OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)`,
    `cfg_analyze fn`, `fn.fn_blocks`, `lbl`, `st`] mp_tac) >>
  simp[]
QED

(* Specialize boundary_other to range analysis parameters *)
Triviality range_boundary_other[local]:
  ∀fn lbl st l.
    l ≠ lbl ⇒
    df_widen_boundary NONE
      (df_process_block_widen Forward NONE
        range_join_opt range_widen_opt WIDEN_THRESHOLD
        range_transfer_opt range_edge_transfer_opt
        (dfg_build_function fn, fn.fn_blocks)
        (OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
        (cfg_analyze fn) fn.fn_blocks lbl st) l =
    df_widen_boundary NONE st l
Proof
  rpt strip_tac >>
  mp_tac (INST_TYPE [alpha |-> ``:(string |-> value_range) option``,
                     beta |-> ``:dfg_analysis # basic_block list``]
    (SIMP_RULE std_ss [LET_THM]
      dfAnalyzeWidenProofsTheory.df_widen_process_boundary_other)) >>
  disch_then (qspecl_then [`Forward`, `NONE`,
    `range_join_opt`, `range_widen_opt`, `WIDEN_THRESHOLD`,
    `range_transfer_opt`, `range_edge_transfer_opt`,
    `(dfg_build_function fn, fn.fn_blocks)`,
    `OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)`,
    `cfg_analyze fn`, `fn.fn_blocks`, `lbl`, `st`, `l`] mp_tac) >>
  simp[]
QED

(* P-preserved under process for the range worklist invariant *)
Triviality range_invariant_preserved[local]:
  ∀fn lbl st.
    let process = df_process_block_widen Forward NONE
          range_join_opt range_widen_opt WIDEN_THRESHOLD
          range_transfer_opt range_edge_transfer_opt
          (dfg_build_function fn, fn.fn_blocks)
          (OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
          (cfg_analyze fn) fn.fn_blocks in
    range_fixpoint_P fn st ∧
    (∀l. df_widen_visits st l ≤ WIDEN_THRESHOLD + 1) ∧
    (∀l. df_widen_visits st l = 0 ⇒
         df_widen_boundary NONE st l = NONE ∨
         df_widen_boundary NONE st l = SOME FEMPTY) ⇒
    range_fixpoint_P fn (process lbl st) ∧
    (∀l. df_widen_visits (process lbl st) l ≤ WIDEN_THRESHOLD + 1) ∧
    (∀l. df_widen_visits (process lbl st) l = 0 ⇒
         df_widen_boundary NONE (process lbl st) l = NONE ∨
         df_widen_boundary NONE (process lbl st) l = SOME FEMPTY)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  mp_tac (SIMP_RULE std_ss [LET_THM] (Q.SPECL [`fn`, `lbl`, `st`]
    range_visits_inc)) >> strip_tac
  (* Case 1: process = identity *)
  >- (gvs[])
  (* Case 2: visits changed *)
  >> rpt conj_tac
  (* 2a. range_fixpoint_P *)
  >- (irule (SIMP_RULE std_ss [LET_THM] range_fixpoint_P_preserved) >>
      simp[])
  (* 2b. visits bound *)
  >- (rpt strip_tac >> Cases_on `l = lbl` >> fs[] >>
      CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS_EQUAL] >>
      `df_widen_visits st lbl ≥ WIDEN_THRESHOLD + 1` by DECIDE_TAC >>
      mp_tac (SIMP_RULE std_ss [LET_THM]
        range_fixpoint_P_stabilization) >>
      disch_then (qspecl_then [`fn`, `lbl`, `st`] mp_tac) >>
      simp[] >> disch_then SUBST_ALL_TAC >> fs[])
  (* 2c. unvisited boundary preserved *)
  >- (rpt strip_tac >>
      `l ≠ lbl` by (strip_tac >> fs[]) >>
      mp_tac (Q.SPECL [`fn`, `lbl`, `st`, `l`] range_boundary_other) >>
      simp[] >> disch_then (fn th => rewrite_tac [th]) >>
      res_tac >> simp[])
QED

Triviality range_analyze_invariant[local]:
  ∀fn.
    let ra = range_analyze fn in
    range_fixpoint_P fn ra ∧
    (∀lbl. df_widen_visits ra lbl ≤ WIDEN_THRESHOLD + 1) ∧
    (∀lbl. df_widen_visits ra lbl = 0 ⇒
           df_widen_boundary NONE ra lbl = NONE ∨
           df_widen_boundary NONE ra lbl = SOME FEMPTY)
Proof
  gen_tac >> simp_tac std_ss [LET_THM, range_analyze_def,
    df_analyze_widen_def, dfAnalyzeDefsTheory.direction_case_def] >>
  qabbrev_tac `process = df_process_block_widen Forward NONE
    range_join_opt range_widen_opt WIDEN_THRESHOLD
    range_transfer_opt range_edge_transfer_opt
    (dfg_build_function fn, fn.fn_blocks)
    (OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks` >>
  qabbrev_tac `all_lbls = (cfg_analyze fn).cfg_dfs_pre` >>
  qmatch_goalsub_abbrev_tac `range_fixpoint_P fn ra` >>
  `(λst. range_fixpoint_P fn st ∧
         (∀l. df_widen_visits st l ≤ WIDEN_THRESHOLD + 1) ∧
         (∀l. df_widen_visits st l = 0 ⇒
              df_widen_boundary NONE st l = NONE ∨
              df_widen_boundary NONE st l = SOME FEMPTY)) ra`
    suffices_by simp[] >>
  qunabbrev_tac `ra` >>
  irule worklistProofsTheory.wl_iterate_invariant_process_restricted >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  conj_tac >- (
    (* P initial *)
    Cases_on `fn_entry_label fn` >>
    simp[range_fixpoint_P_def, init_df_widen_state_def,
         df_widen_visits_def, finite_mapTheory.FLOOKUP_EMPTY] >>
    rpt strip_tac >>
    Cases_on `l = x` >>
    simp[df_widen_boundary_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    CASE_TAC >> simp[] >>
    imp_res_tac foldl_update_all_same >>
    fs[finite_mapTheory.FLOOKUP_EMPTY]) >>
  qexistsl_tac [
    `(WIDEN_THRESHOLD + 1) * LENGTH all_lbls`,
    `λst. SUM (MAP (λl. df_widen_visits st l) all_lbls)`,
    `λl. MEM l all_lbls`] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt conj_tac >|
  [(* 1: measure bounded *)
   rpt strip_tac >>
   irule dfAnalyzeWidenProofsTheory.sum_bound >>
   simp[markerTheory.Abbrev_def],
   (* 2: P preserved *)
   rpt strip_tac >>
   mp_tac (SIMP_RULE std_ss [LET_THM] (Q.SPECL [`fn`, `lbl`, `st`]
     range_invariant_preserved)) >>
   simp[markerTheory.Abbrev_def],
   (* 3: measure increases *)
   rpt strip_tac >>
   irule dfAnalyzeWidenProofsTheory.sum_map_inc >>
   qexists_tac `lbl` >>
   mp_tac (SIMP_RULE std_ss [LET_THM] (Q.SPECL [`fn`, `lbl`, `st`]
     range_visits_inc)) >>
   simp[markerTheory.Abbrev_def],
   (* 4: deps closure *)
   simp[markerTheory.Abbrev_def, listTheory.EVERY_MEM] >>
   rpt strip_tac >>
   mp_tac (Q.SPECL [`fn`, `lbl`] cfg_succs_closure) >>
   simp[listTheory.EVERY_MEM],
   (* 5: EVERY valid_lbl *)
   simp[listTheory.EVERY_MEM, markerTheory.Abbrev_def]
  ]
QED

(* Bridge: exec_pure2 success extracts operand values and output *)
Triviality exec_pure2_output[local]:
  ∀f inst s r.
    exec_pure2 f inst s = OK r ⇒
    ∃v1 v2 op1 op2 out.
      inst.inst_operands = [op1; op2] ∧
      inst.inst_outputs = [out] ∧
      eval_operand op1 s = SOME v1 ∧
      eval_operand op2 s = SOME v2 ∧
      FLOOKUP r.vs_vars out = SOME (f v1 v2) ∧
      (∀x. x ≠ out ⇒ FLOOKUP r.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  rpt gen_tac >> strip_tac >>
  fs[exec_pure2_def] >>
  BasicProvers.every_case_tac >> fs[] >> gvs[] >>
  simp[update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Triviality exec_pure1_output[local]:
  ∀f inst s r.
    exec_pure1 f inst s = OK r ⇒
    ∃v1 op1 out.
      inst.inst_operands = [op1] ∧
      inst.inst_outputs = [out] ∧
      eval_operand op1 s = SOME v1 ∧
      FLOOKUP r.vs_vars out = SOME (f v1) ∧
      (∀x. x ≠ out ⇒ FLOOKUP r.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  rpt gen_tac >> strip_tac >>
  fs[exec_pure1_def] >>
  BasicProvers.every_case_tac >> fs[] >> gvs[] >>
  simp[update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* operand_range is sound for any successfully-evaluated operand *)
Triviality operand_range_sound[local]:
  ∀rs s op w.
    in_range_state rs s.vs_vars ∧
    eval_operand op s = SOME w ⇒
    in_range (operand_range rs op) w
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[operand_range_def, eval_operand_def, lookup_var_def] >> rpt strip_tac
  >- (gvs[] >> simp[in_range_constant])
  >- (irule rs_lookup_in_range >> qexists_tac `s.vs_vars` >> fs[])
  >> simp[in_range_top]
QED

(* operand_lit is sound: if eval_operand gives SOME w and
   operand_lit gives SOME v, then w2i w = v *)
Triviality operand_lit_sound[local]:
  ∀op s w. eval_operand op s = SOME w ⇒
    ∀v. operand_lit op = SOME v ⇒ w2i w = v
Proof
  Cases >> simp[eval_operand_def, operand_lit_def] >> rpt strip_tac >> gvs[]
QED

(* Specialized compare soundness (case expression doesn't reduce for irule) *)
val eval_range_compare_lt = Q.SPEC `LT` eval_range_compare_sound
  |> SIMP_RULE (srw_ss()) [];
val eval_range_compare_gt = Q.SPEC `GT` eval_range_compare_sound
  |> SIMP_RULE (srw_ss()) [];
val eval_range_compare_slt = Q.SPEC `SLT` eval_range_compare_sound
  |> SIMP_RULE (srw_ss()) [];
val eval_range_compare_sgt = Q.SPEC `SGT` eval_range_compare_sound
  |> SIMP_RULE (srw_ss()) [];

(* Pre-compose soundness theorems with GSYM wrapper-function defs so
   irule can match directly against exec_pure2 output (e.g. safe_div,
   evm_byte) without unfolding definitions in the goal. *)
val eval_range_div_composed = eval_range_div_sound
  |> REWRITE_RULE[GSYM venomExecSemanticsTheory.safe_div_def];
val eval_range_mod_composed = eval_range_mod_sound
  |> REWRITE_RULE[GSYM venomExecSemanticsTheory.safe_mod_def];
val eval_range_sdiv_composed = eval_range_sdiv_sound
  |> REWRITE_RULE[GSYM venomExecSemanticsTheory.safe_sdiv_def];
val eval_range_smod_composed = eval_range_smod_sound
  |> REWRITE_RULE[GSYM venomExecSemanticsTheory.safe_smod_def];
val eval_range_byte_composed = eval_range_byte_sound
  |> REWRITE_RULE[GSYM venomExecSemanticsTheory.evm_byte_def];

(* Pre-specialize eval_range for opcodes that escape simp[eval_range_def]
   in batch mode. These are all literal-dependent opcodes. *)
val eval_range_specs = List.map
  (fn opc => SIMP_CONV (srw_ss()) [eval_range_def]
    (list_mk_comb(``eval_range``, [opc, ``ranges:value_range list``,
                                    ``lits:(int option) list``])))
  [``AND``, ``SHL``, ``SHR``, ``SAR``, ``BYTE``];

(* Per-opcode soundness theorems for exec_pure2 dispatch.
   Each conclusion uses the high-level function name from step_inst_base
   (e.g. safe_div, evm_byte) so irule matches without definition unfolding. *)
val range_sound_thms = [
  (* simple 2-op (direct word operations) *)
  eval_range_add_sound, eval_range_sub_sound, eval_range_mul_sound,
  eval_range_eq_sound, eval_range_or_sound,
  REWRITE_RULE [] eval_range_xor_sound,
  eval_range_compare_lt, eval_range_compare_gt,
  eval_range_compare_slt, eval_range_compare_sgt,
  (* wrapper-function 2-op (pre-composed with GSYM def) *)
  eval_range_div_composed, eval_range_mod_composed,
  eval_range_sdiv_composed, eval_range_smod_composed,
  eval_range_byte_composed,
  (* lit-dependent 2-op *)
  eval_range_shl_sound, eval_range_shr_sound,
  eval_range_sar_sound, eval_range_and_sound
];


(* Efficiently unfold step_inst_base when opcode is known.
   Uses SIMP_RULE with both step_inst_base_def and opc equation
   to reduce to exec_pure2/exec_pure1/etc in ~0.27s per opcode. *)
val step_base_unfold_tac =
  qpat_x_assum `inst.inst_opcode = _`
    (fn opc_th =>
      qpat_x_assum `step_inst_base _ _ = OK _`
        (fn base_th =>
          let val th = SIMP_RULE (srw_ss()) [step_inst_base_def, opc_th] base_th
          in ASSUME_TAC opc_th >> ASSUME_TAC th end));

(* bool_to_word b = if b then 1w else 0w — needed because step_inst_base
   uses bool_to_word but soundness theorems use if-then-else *)
val bool_to_word_if = prove(
  ``bool_to_word b = if b then (1w:256 word) else 0w``,
  Cases_on `b` >> simp[venomExecSemanticsTheory.bool_to_word_def]);

(* exec_pure2 opcodes: unfold step_inst_base, get output, forward-chain
   operand soundness, rewrite operands, then dispatch to per-opcode soundness
   theorem via FIRST. Forward-chaining operand_range_sound and operand_lit_sound
   BEFORE irule avoids variable naming mismatches (imp_res_tac creates fresh
   names; irule uses theorem names; gvs[] unifies them from assumptions). *)
val exec_pure2_range_tac =
  step_base_unfold_tac
  >> imp_res_tac exec_pure2_output
  >> imp_res_tac operand_range_sound
  >> imp_res_tac operand_lit_sound
  >> qpat_x_assum `inst.inst_operands = _`
       (fn ops_th => REWRITE_TAC [ops_th])
  >> gvs[finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_if,
         integer_wordTheory.WORD_LTi, integer_wordTheory.WORD_GTi]
  >> simp (eval_range_def :: eval_range_specs)
  >> FIRST (List.map (fn th =>
       irule th >> rpt conj_tac >> gvs[]) range_sound_thms);

val exec_pure1_range_tac =
  step_base_unfold_tac
  >> imp_res_tac exec_pure1_output
  >> imp_res_tac operand_range_sound
  >> gvs[finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_if]
  >> simp[eval_range_def]
  >> FIRST [irule eval_range_iszero_sound,
            irule eval_range_not_sound]
  >> gvs[];

val assign_range_tac =
  step_base_unfold_tac
  >> BasicProvers.every_case_tac >> fs[]
  >> imp_res_tac operand_range_sound
  >> gvs[update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
  >> simp[eval_range_def]
  >> irule eval_range_assign_sound
  >> gvs[];

(* Rewrite: case l of [] => c | _::_ => c  ==>  c
   Can't be stated as a HOL quotation (parser reduces it). Built at SML level. *)
val list_case_const_vr = prove(
  mk_forall(mk_var("l", ``:'a list``),
    mk_eq(
      list_mk_comb(Term.inst [beta |-> ``:value_range``] ``list_CASE``,
        [mk_var("l", ``:'a list``), mk_var("c", ``:value_range``),
         mk_abs(mk_var("h",alpha), mk_abs(mk_var("t",``:'a list``),
           mk_var("c",``:value_range``)))]),
      mk_var("c", ``:value_range``))),
  Cases_on `l` >> simp[]);

(* Per-instruction range soundness for non-PHI single-output opcodes.
   Connects step_inst execution to eval_range abstraction. *)
Triviality step_eval_range_sound[local]:
  ∀fuel ctx inst s r rs.
    step_inst fuel ctx inst s = OK r ∧
    inst.inst_opcode ≠ PHI ∧
    inst.inst_outputs = [out] ∧
    in_range_state rs s.vs_vars ⇒
    ∀w. FLOOKUP r.vs_vars out = SOME w ⇒
      in_range (eval_range inst.inst_opcode
        (MAP (operand_range rs) inst.inst_operands)
        (MAP operand_lit inst.inst_operands)) w
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `inst.inst_opcode` \\ fs[]
  (* INVOKE: separate handling *)
  \\ TRY (rpt strip_tac >> simp[eval_range_def]
           >> BasicProvers.CASE_TAC >> simp[in_range_top] >> NO_TAC)
  (* Non-INVOKE: get step_inst_base *)
  \\ `step_inst_base inst s = OK r` by fs[step_inst_non_invoke]
  \\ rpt strip_tac
  (* VR_Top opcodes *)
  \\ TRY (simp[eval_range_def, eval_range_signextend_def,
               list_case_const_vr, in_range_top]
           >> NO_TAC)
  (* exec_pure2 opcodes *)
  \\ TRY (exec_pure2_range_tac >> NO_TAC)
  (* exec_pure1 opcodes *)
  \\ TRY (exec_pure1_range_tac >> NO_TAC)
  (* ASSIGN *)
  \\ TRY (assign_range_tac >> NO_TAC)
QED

(* Per-instruction soundness: wraps step_range_sound + step_eval_range_sound
   for all output structures. Avoids nested >- in main theorem. *)
Triviality per_inst_range_sound[local]:
  ∀fn fuel ctx inst rs_val s_pre s_post.
    step_inst fuel ctx inst s_pre = OK s_post ∧
    in_range_state rs_val s_pre.vs_vars ⇒
    in_range_state (range_evaluate_inst (dfg_build_function fn) inst rs_val)
                   s_post.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac (INST_TYPE [alpha |-> ``:dfg_analysis``] step_range_sound) >>
  qexistsl_tac [`fuel`, `ctx`, `s_pre`] >> simp[] >>
  rpt strip_tac >>
  drule_all step_eval_range_sound >> simp[]
QED

Theorem range_analyze_block_sound_proof:
  ∀fn lbl bb fuel ctx s s'.
    let ra = range_analyze fn in
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    bb_well_formed bb ∧
    s.vs_inst_idx = 0 ∧
    in_range_state (range_entry_state ra lbl) s.vs_vars ∧
    exec_block fuel ctx bb s = OK s' ⇒
    in_range_state (range_exit_state ra lbl) s'.vs_vars
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `ra = range_analyze fn` >>
  mp_tac (SIMP_RULE std_ss [LET_THM] (Q.SPEC `fn` range_analyze_invariant)) >>
  strip_tac >>
  (* Case split on visits *)
  Cases_on `df_widen_visits ra lbl = 0`
  >- (
    (* visits = 0: boundary is NONE or SOME FEMPTY → exit = FEMPTY *)
    `df_widen_boundary NONE ra lbl = NONE ∨
     df_widen_boundary NONE ra lbl = SOME FEMPTY` by
      (qpat_x_assum `Abbrev _` (SUBST_ALL_TAC o
         REWRITE_RULE [markerTheory.Abbrev_def]) >>
       res_tac >> fs[]) >>
    simp[range_exit_state_def, range_unwrap_def] >>
    fs[] >> simp[range_unwrap_def] >>
    irule in_range_state_fempty_early
  )
  >>
  (* visits > 0: use fixpoint absorption *)
  `df_widen_visits ra lbl > 0` by DECIDE_TAC >>
  (* Get fixpoint_P facts *)
  `range_fixpoint_P fn ra` by fs[markerTheory.Abbrev_def] >>
  fs[range_fixpoint_P_def, markerTheory.Abbrev_def] >>
  pop_assum (qspec_then `lbl` mp_tac) >> simp[] >> strip_tac >>
  (* fold_result is SOME because bb_well_formed → instrs ≠ [] *)
  `bb.bb_instructions ≠ []` by fs[bb_well_formed_def] >>
  mp_tac (Q.SPECL [`bb.bb_instructions`,
    `(dfg_build_function fn, fn.fn_blocks)`,
    `lbl`, `0`, `df_widen_entry NONE ra lbl`, `FEMPTY`]
    fold_forward_range_some) >>
  simp[] >> strip_tac >>
  (* fold_exec_block_sound gives fold result sound *)
  mp_tac (Q.SPECL [`0`, `fuel`, `ctx`, `bb`, `fn.fn_blocks`,
    `s`, `s'`, `df_widen_entry NONE ra lbl`,
    `dfg_build_function fn`, `lbl`, `FEMPTY`]
    fold_exec_block_sound) >>
  simp[listTheory.DROP_0] >>
  impl_tac
  >- (
    conj_tac
    \\ TRY (fs[range_entry_state_def] \\ NO_TAC)
    \\ rpt gen_tac \\ strip_tac
    \\ match_mp_tac per_inst_range_sound
    \\ qexistsl_tac [`fuel`, `ctx`, `s_pre`]
    \\ fs[]
  )
  >>
  (* fold result → exit state via fixpoint absorption *)
  strip_tac >>
  simp[range_exit_state_def] >>
  match_mp_tac range_join_absorb_sound >>
  qexists_tac `rs` >>
  conj_tac >- (
    qpat_x_assum `range_join_opt _ (FST _) = _` mp_tac >>
    simp[range_fold_result_def, dfAnalyzeDefsTheory.df_fold_block_def] >>
    FULL_SIMP_TAC (srw_ss() ++ boolSimps.ETA_ss) []
  ) >>
  fs[range_unwrap_def]
QED

Theorem range_get_range_sound_proof:
  ∀ra lbl idx op w env.
    in_range_state (range_at_inst ra lbl idx) env ∧
    (∀v. op = Var v ⇒ FLOOKUP env v = SOME w) ∧
    (∀v. op = Lit v ⇒ w = v) ⇒
    in_range (range_get_range ra lbl idx op) w
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op` >>
  simp[range_get_range_def, in_range_top, in_range_constant,
       rs_lookup_def] >>
  TRY (CASE_TAC >> simp[in_range_top]) >>
  fs[in_range_state_def] >> res_tac
QED
