(* Obligation: iszero resolution preserves step_inst semantics.
 *
 * Reformulated with chain invariant preconditions.
 *
 * Integration with algebraicOptProofsScript.sml:
 *   1. Extend sinv to: ao_dfg_inv /\ ao_iszero_chain_inv /\ ao_chains_defined
 *   2. ao_transform_inst_sim_inst (line ~1909): replace H_resolve precondition
 *      with ao_iszero_chain_inv + ao_chains_defined from the extended sinv
 *   3. ao_per_inst_sim_fn0 (line ~1981): propagate extended sinv
 *   4. ao_phases123_run_blocks_sim (line ~2028): remove H_resolve from
 *      preconditions, use ao_resolve_iszero_inst_sim with chain invariant
 *      from extended sinv
 *   5. Prove sinv preservation: ao_iszero_chain_inv and ao_chains_defined
 *      are maintained by step_inst (SSA ensures no overwriting)
 *   6. Prove sinv initial: ao_iszero_chain_inv_initial for block entry
 *   7. Prove sinv compat: chain invariant compatible with state_equiv fv
 *)
Theory aoResolveObligation
Ancestors
  algebraicOptDefs venomExecSemantics venomInst venomState venomWf
  stateEquiv passSharedSubst
Libs
  pairLib BasicProvers

(* ===== Definitions ===== *)

(* Adjacent chain elements satisfy the iszero relationship *)
Definition ao_iszero_chain_inv_def:
  ao_iszero_chain_inv targets st <=>
    !v chain. ALOOKUP targets v = SOME chain ==>
      !k. k + 1 < LENGTH chain ==>
        !val_k val_k1.
          eval_operand (EL k chain) st = SOME val_k /\
          eval_operand (EL (k + 1) chain) st = SOME val_k1 ==>
          val_k1 = bool_to_word (val_k = 0w)
End

(* All chain elements are defined *)
Definition ao_chains_defined_def:
  ao_chains_defined targets st <=>
    !v chain k. ALOOKUP targets v = SOME chain /\
                k < LENGTH chain ==>
                ?w. eval_operand (EL k chain) st = SOME w
End

(* Well-formed targets: chain has >= 2 elements, variable is last *)
Definition ao_targets_wf_def:
  ao_targets_wf targets <=>
    !v chain. ALOOKUP targets v = SOME chain ==>
      1 < LENGTH chain /\ LAST chain = Var v
End

(* ===== Structural: ao_compute_fn_iszero_targets produces wf targets ===== *)

Theorem ao_compute_iszero_step_wf:
  !targets inst.
    ao_targets_wf targets ==>
    ao_targets_wf (ao_compute_iszero_step targets inst)
Proof
  rpt strip_tac >>
  simp[ao_compute_iszero_step_def] >>
  IF_CASES_TAC >> gvs[] >>
  every_case_tac >> gvs[] >>
  simp[ao_targets_wf_def] >> rpt strip_tac >>
  pop_assum mp_tac >> IF_CASES_TAC >> strip_tac >>
  gvs[listTheory.LAST_SNOC, listTheory.LENGTH_SNOC, ao_targets_wf_def] >>
  res_tac >> simp[]
QED

Theorem foldl_iszero_step_wf:
  !insts acc. ao_targets_wf acc ==>
              ao_targets_wf (FOLDL ao_compute_iszero_step acc insts)
Proof
  Induct >> simp[] >> metis_tac[ao_compute_iszero_step_wf]
QED

Theorem ao_compute_fn_iszero_targets_wf:
  !fn. ao_targets_wf (ao_compute_fn_iszero_targets fn)
Proof
  simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  simp[foldl_iszero_step_wf, ao_targets_wf_def]
QED

(* ===== Chain invariant preservation ===== *)

(* Chain invariant holds for empty targets *)
Theorem ao_iszero_chain_inv_empty:
  !st. ao_iszero_chain_inv [] st
Proof
  simp[ao_iszero_chain_inv_def]
QED

(* Chain definedness holds for empty targets *)
Theorem ao_chains_defined_empty:
  !st. ao_chains_defined [] st
Proof
  simp[ao_chains_defined_def]
QED

(* Chain invariant preserved by step_inst that doesn't modify chain vars.
   In SSA form, a variable is written at most once, so once the chain
   invariant is established, it is maintained by all subsequent instructions
   (which write different variables). *)
Theorem ao_iszero_chain_inv_step_preserved:
  !targets inst fuel ctx st st'.
    ao_iszero_chain_inv targets st /\
    step_inst fuel ctx inst st = OK st' /\
    (* SSA: inst doesn't overwrite any chain variable *)
    (!v chain k. ALOOKUP targets v = SOME chain /\
                 k < LENGTH chain ==>
                 eval_operand (EL k chain) st' =
                 eval_operand (EL k chain) st) ==>
    ao_iszero_chain_inv targets st'
Proof
  simp[ao_iszero_chain_inv_def] >> rpt strip_tac >>
  `eval_operand (EL k chain) st' = eval_operand (EL k chain) st` by
    (qpat_x_assum `!v chain k. _` irule >> simp[] >>
     qexists_tac `v` >> simp[]) >>
  `eval_operand (EL (k + 1) chain) st' = eval_operand (EL (k + 1) chain) st` by
    (qpat_x_assum `!v chain k. _` irule >> simp[] >>
     qexists_tac `v` >> simp[]) >>
  gvs[] >>
  qpat_x_assum `!v chain. ALOOKUP _ _ = SOME _ ==> _` drule >>
  disch_then (qspec_then `k` mp_tac) >> simp[]
QED

(* Chain definedness preserved similarly *)
Theorem ao_chains_defined_step_preserved:
  !targets inst fuel ctx st st'.
    ao_chains_defined targets st /\
    step_inst fuel ctx inst st = OK st' /\
    (!v chain k. ALOOKUP targets v = SOME chain /\
                 k < LENGTH chain ==>
                 eval_operand (EL k chain) st' =
                 eval_operand (EL k chain) st) ==>
    ao_chains_defined targets st'
Proof
  simp[ao_chains_defined_def] >> rpt strip_tac >>
  qpat_x_assum `!v chain k. _ ==> ?w. _`
    (drule_then (qspec_then `k` strip_assume_tac)) >>
  gvs[] >>
  qpat_x_assum `!v chain k. _ /\ _ ==> (eval_operand _ _ = _)`
    (drule_then (qspec_then `k` mp_tac)) >> simp[]
QED

(* Chain invariant compatible with state_equiv on fresh vars:
   if two states agree on all non-fresh vars, and the chain uses
   only non-fresh vars, then the chain invariant transfers. *)
Theorem eval_operand_var_state_equiv:
  !fv st1 st2 vn.
    state_equiv fv st1 st2 /\ vn NOTIN fv ==>
    eval_operand (Var vn) st2 = eval_operand (Var vn) st1
Proof
  simp[eval_operand_def, state_equiv_def, execution_equiv_def]
QED

Theorem eval_operand_nonvar_state_equiv:
  !fv st1 st2 op.
    state_equiv fv st1 st2 /\ (!x. op <> Var x) ==>
    eval_operand op st2 = eval_operand op st1
Proof
  Cases_on `op` >>
  simp[eval_operand_def, state_equiv_def, execution_equiv_def]
QED

Theorem eval_chain_el_state_equiv:
  !targets fv st1 st2 v chain j.
    state_equiv fv st1 st2 /\
    ALOOKUP targets v = SOME chain /\ j < LENGTH chain /\
    (!v chain k x. ALOOKUP targets v = SOME chain /\
                   k < LENGTH chain /\ EL k chain = Var x ==> x NOTIN fv) ==>
    eval_operand (EL j chain) st2 = eval_operand (EL j chain) st1
Proof
  rpt strip_tac >>
  Cases_on `EL j chain`
  >- simp[eval_operand_def]
  >- (simp[eval_operand_def] >>
      rename1 `EL j chain = Var vname` >>
      `vname NOTIN fv` by
        (qpat_x_assum `!v chain k x. _`
         (qspecl_then [`v`, `chain`, `j`, `vname`] mp_tac) >> simp[]) >>
      fs[state_equiv_def, execution_equiv_def])
  >- (simp[eval_operand_def] >>
      fs[state_equiv_def, execution_equiv_def])
QED

Theorem ao_iszero_chain_inv_state_equiv_compat:
  !targets fv st1 st2.
    ao_iszero_chain_inv targets st1 /\
    state_equiv fv st1 st2 /\
    (!v chain k x. ALOOKUP targets v = SOME chain /\
                   k < LENGTH chain /\ EL k chain = Var x ==> x NOTIN fv) ==>
    ao_iszero_chain_inv targets st2
Proof
  simp[ao_iszero_chain_inv_def] >> rpt strip_tac >>
  `!v' chain' j'. ALOOKUP targets v' = SOME chain' /\ j' < LENGTH chain' ==>
    eval_operand (EL j' chain') st2 = eval_operand (EL j' chain') st1` by
    metis_tac[eval_chain_el_state_equiv] >>
  first_assum (qspecl_then [`v`, `chain`, `k`] assume_tac) >>
  first_x_assum (qspecl_then [`v`, `chain`, `k + 1`] assume_tac) >>
  gvs[] >> metis_tac[]
QED

Theorem ao_chains_defined_state_equiv_compat:
  !targets fv st1 st2.
    ao_chains_defined targets st1 /\
    state_equiv fv st1 st2 /\
    (!v chain k x. ALOOKUP targets v = SOME chain /\
                   k < LENGTH chain /\ EL k chain = Var x ==> x NOTIN fv) ==>
    ao_chains_defined targets st2
Proof
  simp[ao_chains_defined_def] >> rpt strip_tac >>
  `!v' chain' j'. ALOOKUP targets v' = SOME chain' /\ j' < LENGTH chain' ==>
    eval_operand (EL j' chain') st2 = eval_operand (EL j' chain') st1` by
    metis_tac[eval_chain_el_state_equiv] >>
  metis_tac[]
QED

(* ===== Chain property lemmas ===== *)

Theorem chain_val_bool:
  !targets st v chain k w.
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ALOOKUP targets v = SOME chain /\
    k + 1 < LENGTH chain /\
    eval_operand (EL (k + 1) chain) st = SOME w ==>
    w = 0w \/ w = 1w
Proof
  rpt strip_tac >>
  `k < LENGTH chain` by simp[] >>
  `?val_k. eval_operand (EL k chain) st = SOME val_k` by
    metis_tac[ao_chains_defined_def] >>
  `w = bool_to_word (val_k = 0w)` by
    metis_tac[ao_iszero_chain_inv_def] >>
  Cases_on `val_k = 0w` >> gvs[bool_to_word_def]
QED

Theorem chain_period2:
  !targets st v chain m vm vm2.
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ALOOKUP targets v = SOME chain /\
    0 < m /\ m + 2 < LENGTH chain /\
    eval_operand (EL m chain) st = SOME vm /\
    eval_operand (EL (m + 2) chain) st = SOME vm2 ==>
    vm2 = vm
Proof
  rpt strip_tac >>
  `m + 1 < LENGTH chain` by simp[] >>
  `?vm1. eval_operand (EL (m + 1) chain) st = SOME vm1` by
    metis_tac[ao_chains_defined_def] >>
  `(m - 1) + 1 = m` by simp[] >>
  `vm1 = bool_to_word (vm = 0w)` by
    metis_tac[ao_iszero_chain_inv_def] >>
  `m + 1 + 1 = m + 2` by simp[] >>
  `vm2 = bool_to_word (vm1 = 0w)` by
    metis_tac[ao_iszero_chain_inv_def] >>
  `(m - 1) + 1 < LENGTH chain` by simp[] >>
  `vm = 0w \/ vm = 1w` by
    metis_tac[chain_val_bool] >>
  gvs[bool_to_word_def]
QED

Triviality chain_inv_at[local]:
  !targets st v chain k val_k val_k1.
    ao_iszero_chain_inv targets st ==>
    ALOOKUP targets v = SOME chain ==>
    k + 1 < LENGTH chain ==>
    eval_operand (EL k chain) st = SOME val_k ==>
    eval_operand (EL (k + 1) chain) st = SOME val_k1 ==>
    val_k1 = bool_to_word (val_k = 0w)
Proof
  rpt strip_tac >> gvs[ao_iszero_chain_inv_def] >>
  first_x_assum drule >> disch_then (qspec_then `k` mp_tac) >> simp[]
QED

Theorem chain_period2_gen:
  !n targets st v chain m vm vmn.
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ALOOKUP targets v = SOME chain /\
    0 < m /\ m + 2 * n < LENGTH chain /\
    eval_operand (EL m chain) st = SOME vm /\
    eval_operand (EL (m + 2 * n) chain) st = SOME vmn ==>
    vmn = vm
Proof
  Induct_on `n` >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `m + 2 * n < LENGTH chain` by simp[] >>
  `?vmn'. eval_operand (EL (m + 2 * n) chain) st = SOME vmn'` by
    metis_tac[ao_chains_defined_def] >>
  `vmn' = vm` by (first_x_assum irule >> metis_tac[]) >>
  gvs[] >>
  `(m + 2 * n) + 1 < LENGTH chain` by simp[] >>
  `?vm1. eval_operand (EL ((m + 2 * n) + 1) chain) st = SOME vm1` by
    metis_tac[ao_chains_defined_def] >>
  `vm1 = bool_to_word (vm = 0w)` by
    (drule chain_inv_at >> disch_then drule >>
     disch_then (qspec_then `m + 2 * n` mp_tac) >> simp[]) >>
  `vmn = bool_to_word (vm1 = 0w)` by
    (`((m + 2 * n) + 1) + 1 = m + 2 * SUC n` by simp[] >>
     drule chain_inv_at >> disch_then drule >>
     disch_then (qspec_then `(m + 2 * n) + 1` mp_tac) >> simp[]) >>
  `vm = 0w \/ vm = 1w` by
    (qspecl_then [`targets`, `st`, `v`, `chain`, `m - 1`, `vm`]
      mp_tac chain_val_bool >> disch_then irule >> simp[]) >>
  gvs[bool_to_word_def]
QED

Theorem chain_truth_even:
  !n targets st v chain v0 ve.
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ALOOKUP targets v = SOME chain /\
    0 < n /\ 2 * n < LENGTH chain /\
    eval_operand (EL 0 chain) st = SOME v0 /\
    eval_operand (EL (2 * n) chain) st = SOME ve ==>
    (ve = 0w <=> v0 = 0w)
Proof
  rpt strip_tac >>
  `1 < LENGTH chain` by simp[] >>
  `?v1. eval_operand (EL 1 chain) st = SOME v1` by
    metis_tac[ao_chains_defined_def] >>
  `v1 = bool_to_word (v0 = 0w)` by
    (drule chain_inv_at >> disch_then drule >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  `2 < LENGTH chain` by simp[] >>
  `?v2. eval_operand (EL 2 chain) st = SOME v2` by
    metis_tac[ao_chains_defined_def] >>
  `v2 = bool_to_word (v1 = 0w)` by
    (drule chain_inv_at >> disch_then drule >>
     disch_then (qspec_then `1` mp_tac) >> simp[]) >>
  `ve = v2` by
    (Cases_on `n = 1` >- gvs[] >>
     `2 + 2 * (n - 1) = 2 * n` by simp[] >>
     qspecl_then [`n - 1`, `targets`, `st`, `v`, `chain`, `2`, `v2`, `ve`]
       mp_tac chain_period2_gen >>
     disch_then irule >> simp[]) >>
  Cases_on `v0 = 0w` >> gvs[bool_to_word_def]
QED

(* ===== Arithmetic helpers for period-2 instantiation ===== *)

Triviality even_step_eq[local]:
  !n:num. n MOD 2 = 0 /\ 2 < n ==> 2 + 2 * ((n - 2) DIV 2) = n
Proof
  rpt strip_tac >>
  `(n - 2) MOD 2 = 0` by
    (`?k. n = 2 * k` by
       (qexists_tac `n DIV 2` >> simp[bitTheory.DIV_MULT_THM2]) >>
     `n - 2 = 2 * (k - 1)` by simp[] >> simp[]) >>
  simp[bitTheory.DIV_MULT_THM2]
QED

Triviality odd_step_eq[local]:
  !n:num. n MOD 2 = 1 /\ 1 < n ==> 1 + 2 * ((n - 1) DIV 2) = n
Proof
  rpt strip_tac >>
  `(n - 1) MOD 2 = 0` by
    (`?k. n = 2 * k + 1` by
       (qexists_tac `n DIV 2` >> simp[bitTheory.DIV_MULT_THM2]) >>
     `n - 1 = 2 * k` by simp[] >> simp[]) >>
  simp[bitTheory.DIV_MULT_THM2]
QED

Triviality same_parity_period2[local]:
  !targets st v chain k d vk vd.
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ALOOKUP targets v = SOME chain /\
    0 < k /\ k <= d /\ d < LENGTH chain /\
    (d - k) MOD 2 = 0 /\
    eval_operand (EL k chain) st = SOME vk /\
    eval_operand (EL d chain) st = SOME vd ==>
    vd = vk
Proof
  rpt strip_tac >>
  qspecl_then [`(d - k) DIV 2`, `targets`, `st`, `v`, `chain`, `k`, `vk`, `vd`]
    mp_tac chain_period2_gen >> disch_then irule >>
  simp[bitTheory.DIV_MULT_THM2]
QED

Triviality mod2_parity_cancel[local]:
  !n:num. (n - (2 - n MOD 2)) MOD 2 = 0
Proof
  rpt strip_tac >>
  `n MOD 2 = 0 \/ n MOD 2 = 1` by
    (`n MOD 2 < 2` by simp[] >> simp[]) >>
  gvs[] >| [
    Cases_on `n < 2` >- simp[] >>
    qspecl_then [`2`, `n`, `2`] mp_tac gcdTheory.MOD_EQ_DIFF >> simp[],
    qspecl_then [`2`, `n`, `1`] mp_tac gcdTheory.MOD_EQ_DIFF >> simp[]
  ]
QED

(* ===== Operand resolution lemmas ===== *)

Theorem resolve_op_iszero:
  !targets op. ao_resolve_iszero_op targets ISZERO op = op
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[ao_resolve_iszero_op_def, LET_THM] >>
  Cases_on `ALOOKUP targets s` >> simp[]
QED

Theorem resolve_op_label:
  !targets opc lbl. ao_resolve_iszero_op targets opc (Label lbl) = Label lbl
Proof
  simp[ao_resolve_iszero_op_def]
QED

Theorem resolve_op_lit:
  !targets opc v. ao_resolve_iszero_op targets opc (Lit v) = Lit v
Proof
  simp[ao_resolve_iszero_op_def]
QED

(* For non-truthy, non-ISZERO opcodes: resolved operand evals to same value *)
Theorem resolve_op_eval_eq:
  !targets opc op st.
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ao_targets_wf targets /\
    opc <> ISZERO /\ opc <> JNZ /\ opc <> ASSERT /\ opc <> ASSERT_UNREACHABLE ==>
    eval_operand (ao_resolve_iszero_op targets opc op) st = eval_operand op st
Proof
  rpt strip_tac >> Cases_on `op` >> simp[ao_resolve_iszero_op_def] >>
  rename1 `ALOOKUP targets vn` >>
  Cases_on `ALOOKUP targets vn` >> simp[] >>
  rename1 `ALOOKUP targets vn = SOME chain` >>
  IF_CASES_TAC >> simp[] >>
  `1 < LENGTH chain /\ LAST chain = Var vn` by
    (fs[ao_targets_wf_def] >> first_x_assum drule >> simp[]) >>
  `EL (LENGTH chain - 1) chain = Var vn` by
    metis_tac[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1,
              listTheory.LENGTH_NIL, DECIDE ``1 < (n:num) ==> n <> 0``] >>
  qabbrev_tac `keep = 2 - (LENGTH chain - 1) MOD 2` >>
  `0 < keep` by
    (simp[Abbr `keep`] >> `(LENGTH chain - 1) MOD 2 < 2` by simp[] >> simp[]) >>
  `keep <= LENGTH chain - 1` by simp[Abbr `keep`] >>
  `?vd. eval_operand (EL (LENGTH chain - 1) chain) st = SOME vd` by
    metis_tac[ao_chains_defined_def, DECIDE ``1 < (n:num) ==> n - 1 < n``] >>
  `eval_operand (Var vn) st = SOME vd` by gvs[] >>
  `keep < LENGTH chain` by simp[] >>
  `?vk. eval_operand (EL keep chain) st = SOME vk` by
    metis_tac[ao_chains_defined_def] >>
  `vd = vk` by
    (qspecl_then [`targets`, `st`, `vn`, `chain`, `keep`,
                  `LENGTH chain - 1`, `vk`, `vd`]
      mp_tac same_parity_period2 >>
     simp[Abbr `keep`, mod2_parity_cancel]) >>
  gvs[]
QED

(* For truthy opcodes: resolved operand has same truthiness *)
Theorem resolve_op_truthy_eq:
  !targets opc op st v1 v2.
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ao_targets_wf targets /\
    (opc = JNZ \/ opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\
    eval_operand (ao_resolve_iszero_op targets opc op) st = SOME v1 /\
    eval_operand op st = SOME v2 ==>
    (v1 = 0w <=> v2 = 0w)
Proof
  rpt strip_tac >> Cases_on `op` >> gvs[ao_resolve_iszero_op_def] >>
  rename1 `Var vn` >>
  Cases_on `ALOOKUP targets vn` >> gvs[] >>
  rename1 `ALOOKUP targets vn = SOME chain` >>
  gvs[LET_THM] >>
  qpat_x_assum `eval_operand (if _ then _ else _) _ = _` mp_tac >>
  reverse IF_CASES_TAC >> strip_tac >> gvs[] >>
  `1 < LENGTH chain /\ LAST chain = Var vn` by
    (fs[ao_targets_wf_def] >> first_x_assum drule >> simp[]) >>
  `EL (LENGTH chain - 1) chain = Var vn` by
    metis_tac[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1,
              listTheory.LENGTH_NIL, DECIDE ``1 < (n:num) ==> n <> 0``] >>
  `(LENGTH chain - 1) MOD 2 = 0 \/ (LENGTH chain - 1) MOD 2 = 1` by
    (`(LENGTH chain - 1) MOD 2 < 2` by simp[] >> simp[]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  ((`eval_operand (EL 0 chain) st = SOME v1` by simp[] >>
    `LENGTH chain >= 3` by (CCONTR_TAC >> gvs[]) >>
    `0 < (LENGTH chain - 1) DIV 2` by simp[arithmeticTheory.X_LT_DIV] >>
    qspecl_then [`(LENGTH chain - 1) DIV 2`, `targets`, `st`, `vn`,
                 `chain`, `v1`, `v2`]
      mp_tac chain_truth_even >>
    simp[bitTheory.DIV_MULT_THM2])
  ORELSE
   (`?vd. eval_operand (EL (LENGTH chain - 1) chain) st = SOME vd` by
      metis_tac[ao_chains_defined_def,
                DECIDE ``1 < (n:num) ==> n - 1 < n``] >>
    `v2 = vd` by gvs[] >>
    `v2 = v1` suffices_by simp[] >>
    qspecl_then [`targets`, `st`, `vn`, `chain`, `1`,
                 `LENGTH chain - 1`, `v1`, `v2`]
      mp_tac same_parity_period2 >> simp[] >>
    qspecl_then [`2`, `LENGTH chain - 1`, `1`]
      mp_tac gcdTheory.MOD_EQ_DIFF >> simp[]))
QED

(* ===== Main theorem ===== *)

(* ao_resolve_iszero_inst only changes operands *)
Theorem resolve_inst_fields:
  !targets inst.
    (ao_resolve_iszero_inst targets inst).inst_opcode = inst.inst_opcode /\
    (ao_resolve_iszero_inst targets inst).inst_outputs = inst.inst_outputs /\
    (ao_resolve_iszero_inst targets inst).inst_id = inst.inst_id
Proof
  simp[ao_resolve_iszero_inst_def]
QED

(* For non-truthy opcodes: all resolved operands eval the same *)
Triviality resolve_op_eval_all[local]:
  !targets opc op st.
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ao_targets_wf targets /\
    opc <> JNZ /\ opc <> ASSERT /\ opc <> ASSERT_UNREACHABLE ==>
    eval_operand (ao_resolve_iszero_op targets opc op) st = eval_operand op st
Proof
  rpt strip_tac >>
  Cases_on `opc = ISZERO`
  >- simp[resolve_op_iszero]
  >- metis_tac[resolve_op_eval_eq]
QED

(* MAP of resolve over all-Lit operands is identity *)
Triviality map_resolve_lit_id[local]:
  !targets opc ops.
    EVERY (\op. ?v. op = Lit v) ops ==>
    MAP (ao_resolve_iszero_op targets opc) ops = ops
Proof
  gen_tac >> gen_tac >> Induct >> simp[] >>
  rpt strip_tac >> gvs[] >> simp[resolve_op_lit]
QED

(* If original operand is SOME, resolved is also SOME *)
Triviality resolve_op_some[local]:
  !targets opc op st v.
    ao_chains_defined targets st /\ ao_targets_wf targets /\
    eval_operand op st = SOME v ==>
    ?w. eval_operand (ao_resolve_iszero_op targets opc op) st = SOME w
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[ao_resolve_iszero_op_def, eval_operand_def] >>
  rename1 `ALOOKUP targets vn` >>
  Cases_on `ALOOKUP targets vn` >> gvs[eval_operand_def] >>
  rename1 `ALOOKUP targets vn = SOME chain` >>
  simp[LET_THM] >>
  IF_CASES_TAC >> gvs[eval_operand_def] >>
  IF_CASES_TAC >> gvs[eval_operand_def] >>
  fs[ao_chains_defined_def] >>
  first_x_assum (qspecl_then [`vn`, `chain`] mp_tac) >> simp[]
QED

(* If original operand is NONE, resolved is also NONE *)
Triviality resolve_op_none[local]:
  !targets opc op st.
    ao_chains_defined targets st /\ ao_targets_wf targets /\
    eval_operand op st = NONE ==>
    eval_operand (ao_resolve_iszero_op targets opc op) st = NONE
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[ao_resolve_iszero_op_def, eval_operand_def] >>
  rename1 `ALOOKUP targets vn` >>
  Cases_on `ALOOKUP targets vn` >> gvs[eval_operand_def] >>
  rename1 `ALOOKUP targets vn = SOME chain` >>
  `1 < LENGTH chain /\ LAST chain = Var vn` by
    (fs[ao_targets_wf_def] >> first_x_assum drule >> simp[]) >>
  `EL (LENGTH chain - 1) chain = Var vn` by
    metis_tac[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1,
              listTheory.LENGTH_NIL, DECIDE ``1 < (n:num) ==> n <> 0``] >>
  `LENGTH chain - 1 < LENGTH chain` by simp[] >>
  `?w. eval_operand (EL (LENGTH chain - 1) chain) st = SOME w` by
    metis_tac[ao_chains_defined_def] >>
  gvs[eval_operand_def]
QED

(* Truthy opcodes: step_inst congruence under same truthiness *)
Triviality resolve_truthy_step[local]:
  !targets inst fuel ctx st.
    inst_wf inst /\
    (inst.inst_opcode = JNZ \/ inst.inst_opcode = ASSERT \/
     inst.inst_opcode = ASSERT_UNREACHABLE) /\
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ao_targets_wf targets ==>
    step_inst fuel ctx (ao_resolve_iszero_inst targets inst) st =
    step_inst fuel ctx inst st
Proof
  rpt strip_tac >> gvs[ao_resolve_iszero_inst_def] >>
  gvs[step_inst_def, inst_wf_def, step_inst_base_def] >| [
    simp[resolve_op_label] >>
    Cases_on `eval_operand c st`
    >- (drule_all resolve_op_none >> simp[])
    >- (rename1 `_ = SOME cval` >>
        `?w. eval_operand (ao_resolve_iszero_op targets JNZ c) st = SOME w` by
          metis_tac[resolve_op_some] >> simp[] >>
        `(w = 0w <=> cval = 0w)` by metis_tac[resolve_op_truthy_eq] >>
        Cases_on `cval = 0w` >> gvs[]),
    `?cop. inst.inst_operands = [cop]` by
      (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[]) >>
    gvs[] >> Cases_on `eval_operand cop st`
    >- (drule_all resolve_op_none >> simp[])
    >- (rename1 `_ = SOME cval` >>
        `?w. eval_operand (ao_resolve_iszero_op targets ASSERT cop) st =
             SOME w` by metis_tac[resolve_op_some] >> simp[] >>
        `(w = 0w <=> cval = 0w)` by metis_tac[resolve_op_truthy_eq] >>
        Cases_on `cval = 0w` >> gvs[]),
    `?cop. inst.inst_operands = [cop]` by
      (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[]) >>
    gvs[] >> Cases_on `eval_operand cop st`
    >- (drule_all resolve_op_none >> simp[])
    >- (rename1 `_ = SOME cval` >>
        `?w. eval_operand (ao_resolve_iszero_op targets ASSERT_UNREACHABLE
               cop) st = SOME w` by metis_tac[resolve_op_some] >> simp[] >>
        `(w = 0w <=> cval = 0w)` by metis_tac[resolve_op_truthy_eq] >>
        Cases_on `cval = 0w` >> gvs[])
  ]
QED

Theorem ao_resolve_iszero_inst_sim:
  !targets inst fuel ctx st.
    inst_wf inst /\ inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> PHI /\
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ao_targets_wf targets ==>
    step_inst fuel ctx (ao_resolve_iszero_inst targets inst) st =
    step_inst fuel ctx inst st
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = JNZ \/ inst.inst_opcode = ASSERT \/
            inst.inst_opcode = ASSERT_UNREACHABLE`
  >- metis_tac[resolve_truthy_step]
  >- (
    Cases_on `inst.inst_opcode = PARAM`
    >- (gvs[inst_wf_def] >>
        `ao_resolve_iszero_inst targets inst = inst` suffices_by simp[] >>
        simp[ao_resolve_iszero_inst_def, instruction_component_equality,
             resolve_op_lit]) >>
    Cases_on `is_alloca_op inst.inst_opcode`
    >- (Cases_on `inst.inst_opcode` >>
        gvs[inst_wf_def, is_alloca_op_def] >>
        `ao_resolve_iszero_inst targets inst = inst` suffices_by simp[] >>
        simp[ao_resolve_iszero_inst_def, instruction_component_equality,
             resolve_op_lit]) >>
    simp[ao_resolve_iszero_inst_def] >>
    irule step_inst_operands_equiv >>
    simp[listTheory.LENGTH_MAP] >> rpt strip_tac >>
    simp[listTheory.EL_MAP, resolve_op_label] >>
    TRY (irule resolve_op_eval_all >> simp[]) >>
    gvs[inst_wf_def] >> simp[listTheory.MAP, resolve_op_lit]
  )
QED
