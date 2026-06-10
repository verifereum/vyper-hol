(* Obligation: iszero resolution preserves step_inst semantics.
 *
 * Reformulated with chain invariant preconditions.
 *
 * Integration: the chain invariant defined here is a component of sinv
 * (ao_dfg_inv /\ ao_iszero_chain_inv /\ ao_chains_defined), which
 * ao_block_sim_local (aoBlockSimLocalScript.sml) threads through the block
 * and aoPhase3ProofScript.sml composes at function level.  Its step
 * preservation, block-entry establishment, and state_equiv compatibility
 * are proved in aoStepInvObligationScript.sml and
 * aoBlockInvObligationScript.sml / aoBlockInvPreservedScript.sml.
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

(* Conditional chain definedness: chain elements are defined whenever
   the chain endpoint (Var v) is defined. Vacuously true at function
   entry when no instruction outputs are defined. *)
Definition ao_chains_defined_at_def:
  ao_chains_defined_at targets st <=>
    !v chain. ALOOKUP targets v = SOME chain /\
              (?w. eval_operand (Var v) st = SOME w) ==>
              !k. k < LENGTH chain ==>
                ?w. eval_operand (EL k chain) st = SOME w
End
val _ = delsimps ["ao_chains_defined_at_def"]

(* Chain definedness forms a prefix: if chain[j] is undefined, all
   chain[j'] for j' > j are also undefined. This is the natural
   consequence of SSA execution: each chain element at position k > 0
   is an ISZERO output reading position k-1, so it can only be defined
   if position k-1 was defined when the ISZERO executed. *)
Definition ao_chain_defined_prefix_def:
  ao_chain_defined_prefix targets st <=>
    !v chain j1 j2.
      ALOOKUP targets v = SOME chain /\
      j1 <= j2 /\ j2 < LENGTH chain /\
      (?w. eval_operand (EL j2 chain) st = SOME w) ==>
      ?w. eval_operand (EL j1 chain) st = SOME w
End
val _ = delsimps ["ao_chain_defined_prefix_def"]

(* Well-formed targets: chain has >= 2 elements, variable is last *)
Definition ao_targets_wf_def:
  ao_targets_wf targets <=>
    !v chain. ALOOKUP targets v = SOME chain ==>
      1 < LENGTH chain /\ LAST chain = Var v
End

(* DFG-based iszero invariant: for each variable defined by an ISZERO
   in the DFG, if both the output and operand are defined, the output
   equals bool_to_word(operand = 0w). Unlike ao_iszero_chain_inv, this
   is preserved at block boundaries because it references defining
   instructions (stable under SSA) rather than chain sequences. *)
Definition ao_iszero_dfg_inv_def:
  ao_iszero_dfg_inv dfg s <=>
    !x inst op.
      dfg_get_def dfg x = SOME inst /\
      inst.inst_opcode = ISZERO /\ inst.inst_operands = [op] ==>
      !val_x val_op.
        lookup_var x s = SOME val_x /\
        eval_operand op s = SOME val_op ==>
        val_x = bool_to_word (val_op = 0w)
End
val _ = delsimps ["ao_iszero_dfg_inv_def"]


Triviality eval_operand_state_equiv_chain_el[local]:
  !fv st1 st2 op.
    state_equiv fv st1 st2 /\
    (!x. op = Var x ==> x NOTIN fv) ==>
    eval_operand op st2 = eval_operand op st1
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[eval_operand_def, state_equiv_def, execution_equiv_def]
QED


(* ===== ao_chain_defined_prefix properties ===== *)

Theorem ao_chain_defined_prefix_implies_at:
  !targets st.
    ao_chain_defined_prefix targets st /\ ao_targets_wf targets ==>
    ao_chains_defined_at targets st
Proof
  rw[ao_chain_defined_prefix_def, ao_chains_defined_at_def,
     ao_targets_wf_def] >>
  rpt strip_tac >>
  `1 < LENGTH chain /\ LAST chain = Var v` by metis_tac[] >>
  `EL (LENGTH chain - 1) chain = Var v` by
    metis_tac[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1,
              listTheory.LENGTH_NIL, DECIDE ``1 < n ==> n <> (0:num)``] >>
  `LENGTH chain - 1 < LENGTH chain` by simp[] >>
  `?w'. eval_operand (EL (LENGTH chain - 1) chain) st = SOME w'` by
    metis_tac[] >>
  `k <= LENGTH chain - 1` by simp[] >>
  metis_tac[]
QED

Theorem ao_chain_defined_prefix_step_preserved:
  !targets inst fuel ctx st st'.
    ao_chain_defined_prefix targets st /\
    step_inst fuel ctx inst st = OK st' /\
    (!v chain k. ALOOKUP targets v = SOME chain /\
                 k < LENGTH chain ==>
                 eval_operand (EL k chain) st' =
                 eval_operand (EL k chain) st) ==>
    ao_chain_defined_prefix targets st'
Proof
  rw[ao_chain_defined_prefix_def] >> rpt strip_tac >>
  `eval_operand (EL j2 chain) st' = eval_operand (EL j2 chain) st` by
    metis_tac[] >>
  `?w'. eval_operand (EL j2 chain) st = SOME w'` by metis_tac[] >>
  `j1 < LENGTH chain` by simp[] >>
  `?w''. eval_operand (EL j1 chain) st = SOME w''` by metis_tac[] >>
  `eval_operand (EL j1 chain) st' = eval_operand (EL j1 chain) st` by
    metis_tac[] >>
  metis_tac[]
QED

Theorem ao_chain_defined_prefix_state_equiv_compat:
  !targets fv st1 st2.
    ao_chain_defined_prefix targets st1 /\
    state_equiv fv st1 st2 /\
    (!v chain k x. ALOOKUP targets v = SOME chain /\
                   k < LENGTH chain /\ EL k chain = Var x ==> x NOTIN fv) ==>
    ao_chain_defined_prefix targets st2
Proof
  rw[ao_chain_defined_prefix_def] >> rpt strip_tac >>
  `eval_operand (EL j2 chain) st2 = eval_operand (EL j2 chain) st1` by
    (qspecl_then [`fv`, `st1`, `st2`, `EL j2 chain`]
       mp_tac eval_operand_state_equiv_chain_el >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  `?w'. eval_operand (EL j2 chain) st1 = SOME w'` by metis_tac[] >>
  `?w''. eval_operand (EL j1 chain) st1 = SOME w''` by
    metis_tac[] >>
  `eval_operand (EL j1 chain) st2 = eval_operand (EL j1 chain) st1` by
    (qspecl_then [`fv`, `st1`, `st2`, `EL j1 chain`]
       mp_tac eval_operand_state_equiv_chain_el >>
     impl_tac >- (simp[] >> `j1 < LENGTH chain` by simp[] >> metis_tac[]) >>
     simp[]) >>
  metis_tac[]
QED

Theorem eval_operand_inst_idx_irrel:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED


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

(* Chain definedness holds for empty targets *)

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

(* Chain invariant compatible with state_equiv on fresh vars:
   if two states agree on all non-fresh vars, and the chain uses
   only non-fresh vars, then the chain invariant transfers. *)


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

Triviality chain_val_bool_local[local]:
  !targets st v chain k w.
    ao_iszero_chain_inv targets st /\
    ALOOKUP targets v = SOME chain /\
    (!k. k < LENGTH chain ==> ?w. eval_operand (EL k chain) st = SOME w) /\
    k + 1 < LENGTH chain /\
    eval_operand (EL (k + 1) chain) st = SOME w ==>
    w = 0w \/ w = 1w
Proof
  rpt strip_tac >>
  `k < LENGTH chain` by simp[] >>
  `?val_k. eval_operand (EL k chain) st = SOME val_k` by metis_tac[] >>
  `w = bool_to_word (val_k = 0w)` by
    metis_tac[ao_iszero_chain_inv_def] >>
  Cases_on `val_k = 0w` >> gvs[bool_to_word_def]
QED

Triviality chain_period2_gen_local[local]:
  !n targets st v chain m vm vmn.
    ao_iszero_chain_inv targets st /\
    ALOOKUP targets v = SOME chain /\
    (!k. k < LENGTH chain ==> ?w. eval_operand (EL k chain) st = SOME w) /\
    0 < m /\ m + 2 * n < LENGTH chain /\
    eval_operand (EL m chain) st = SOME vm /\
    eval_operand (EL (m + 2 * n) chain) st = SOME vmn ==>
    vmn = vm
Proof
  Induct_on `n` >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `m + 2 * n < LENGTH chain` by simp[] >>
  `?vmn'. eval_operand (EL (m + 2 * n) chain) st = SOME vmn'` by
    metis_tac[] >>
  `vmn' = vm` by (first_x_assum irule >> metis_tac[]) >>
  gvs[] >>
  `(m + 2 * n) + 1 < LENGTH chain` by simp[] >>
  `?vm1. eval_operand (EL ((m + 2 * n) + 1) chain) st = SOME vm1` by
    metis_tac[] >>
  `vm1 = bool_to_word (vm = 0w)` by
    (drule chain_inv_at >> disch_then drule >>
     disch_then (qspec_then `m + 2 * n` mp_tac) >> simp[]) >>
  `vmn = bool_to_word (vm1 = 0w)` by
    (`((m + 2 * n) + 1) + 1 = m + 2 * SUC n` by simp[] >>
     drule chain_inv_at >> disch_then drule >>
     disch_then (qspec_then `(m + 2 * n) + 1` mp_tac) >> simp[]) >>
  `vm = 0w \/ vm = 1w` by
    (qspecl_then [`targets`, `st`, `v`, `chain`, `m - 1`, `vm`]
      mp_tac chain_val_bool_local >> disch_then irule >> simp[]) >>
  gvs[bool_to_word_def]
QED

Triviality same_parity_period2_local[local]:
  !targets st v chain k d vk vd.
    ao_iszero_chain_inv targets st /\
    ALOOKUP targets v = SOME chain /\
    (!k. k < LENGTH chain ==> ?w. eval_operand (EL k chain) st = SOME w) /\
    0 < k /\ k <= d /\ d < LENGTH chain /\
    (d - k) MOD 2 = 0 /\
    eval_operand (EL k chain) st = SOME vk /\
    eval_operand (EL d chain) st = SOME vd ==>
    vd = vk
Proof
  rpt strip_tac >>
  qspecl_then [`(d - k) DIV 2`, `targets`, `st`, `v`, `chain`, `k`, `vk`, `vd`]
    mp_tac chain_period2_gen_local >> disch_then irule >>
  simp[bitTheory.DIV_MULT_THM2]
QED

(* ===== Arithmetic helpers for period-2 instantiation ===== *)


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

(* Variant using ao_chains_defined_at: if the operand is defined, the
   resolved operand evaluates to the same value. *)
Theorem resolve_op_eval_eq_at:
  !targets opc op st.
    ao_iszero_chain_inv targets st /\
    ao_chains_defined_at targets st /\
    ao_targets_wf targets /\
    opc <> ISZERO /\ opc <> JNZ /\ opc <> ASSERT /\ opc <> ASSERT_UNREACHABLE /\
    (?w. eval_operand op st = SOME w) ==>
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
  `?vd. eval_operand (Var vn) st = SOME vd` by
    gvs[eval_operand_def] >>
  `!k. k < LENGTH chain ==>
    ?w. eval_operand (EL k chain) st = SOME w` by
    (rpt strip_tac >>
     qpat_x_assum `ao_chains_defined_at _ _` mp_tac >>
     simp[ao_chains_defined_at_def] >>
     disch_then (qspecl_then [`vn`, `chain`] mp_tac) >> simp[]) >>
  qabbrev_tac `keep = 2 - (LENGTH chain - 1) MOD 2` >>
  `0 < keep` by
    (simp[Abbr `keep`] >> `(LENGTH chain - 1) MOD 2 < 2` by simp[] >> simp[]) >>
  `keep <= LENGTH chain - 1` by simp[Abbr `keep`] >>
  `?vd'. eval_operand (EL (LENGTH chain - 1) chain) st = SOME vd'` by
    metis_tac[DECIDE ``1 < (n:num) ==> n - 1 < n``] >>
  `keep < LENGTH chain` by simp[] >>
  `?vk. eval_operand (EL keep chain) st = SOME vk` by metis_tac[] >>
  `vd' = vd` by gvs[] >>
  `vd = vk` by
    (qspecl_then [`targets`, `st`, `vn`, `chain`, `keep`,
                  `LENGTH chain - 1`, `vk`, `vd`]
      mp_tac same_parity_period2_local >>
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
    inst_wf inst /\
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

(* Per-operand variant: only requires chain conditions for operands of inst.
   This avoids requiring ao_chains_defined globally, which is false at
   function entry when chain variables are undefined instruction outputs. *)
Theorem ao_resolve_iszero_inst_sim_local:
  !targets inst fuel ctx st.
    inst_wf inst /\
    inst.inst_opcode <> PHI /\
    ao_targets_wf targets /\
    (!v chain k. MEM (Var v) inst.inst_operands /\
                 ALOOKUP targets v = SOME chain /\ k < LENGTH chain ==>
                 ?w. eval_operand (EL k chain) st = SOME w) /\
    (!v chain k. MEM (Var v) inst.inst_operands /\
                 ALOOKUP targets v = SOME chain /\ k + 1 < LENGTH chain ==>
                 !val_k val_k1.
                   eval_operand (EL k chain) st = SOME val_k /\
                   eval_operand (EL (k + 1) chain) st = SOME val_k1 ==>
                   val_k1 = bool_to_word (val_k = 0w)) ==>
    step_inst fuel ctx (ao_resolve_iszero_inst targets inst) st =
    step_inst fuel ctx inst st
Proof
  rpt strip_tac >>
  qabbrev_tac `P = \v:string. MEM (Var v) inst.inst_operands` >>
  qabbrev_tac `rt = FILTER (\(v, chain). P v) targets` >>
  `!v. P v ==> ALOOKUP rt v = ALOOKUP targets v` by
    simp[Abbr `rt`, alistTheory.ALOOKUP_FILTER] >>
  `!v. ~P v ==> ALOOKUP rt v = NONE` by
    simp[Abbr `rt`, alistTheory.ALOOKUP_FILTER] >>
  `ao_resolve_iszero_inst targets inst =
   ao_resolve_iszero_inst rt inst` by
    (simp[ao_resolve_iszero_inst_def, instruction_component_equality] >>
     irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
     Cases_on `x` >> simp[ao_resolve_iszero_op_def] >>
     rename1 `Var vn` >>
     `P vn` by simp[Abbr `P`] >>
     first_x_assum drule >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  `ao_targets_wf rt` by
    (rw[ao_targets_wf_def] >> rpt strip_tac >> (
     `P v` by
       (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >>
     metis_tac[ao_targets_wf_def])) >>
  `ao_iszero_chain_inv rt st` by
    (rw[ao_iszero_chain_inv_def] >> rpt strip_tac >>
     `P v` by
       (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >>
     `MEM (Var v) inst.inst_operands` by fs[Abbr `P`] >>
     qpat_x_assum `!v chain k. MEM _ _ /\ _ /\ k + 1 < _ ==> _`
       (qspecl_then [`v`, `chain`, `k`] mp_tac) >> simp[]) >>
  `ao_chains_defined rt st` by
    (rw[ao_chains_defined_def] >> rpt strip_tac >>
     `P v` by
       (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >>
     `MEM (Var v) inst.inst_operands` by fs[Abbr `P`] >>
     qpat_x_assum `!v chain k. MEM _ _ /\ _ /\ k < _ ==> _`
       (qspecl_then [`v`, `chain`, `k`] mp_tac) >> simp[]) >>
  metis_tac[ao_resolve_iszero_inst_sim]
QED

(* Variant using ao_chains_defined_at instead of ao_chains_defined.
   Requires the operand (Var v) to be defined, which together with
   ao_chains_defined_at implies chain definedness for that variable. *)

(* ===== PHI resolution sim (loop-robust) ===== *)

Theorem eval_operands_mem_defined:
  !ops s vals. eval_operands ops s = SOME vals ==>
    !op. MEM op ops ==> ?w. eval_operand op s = SOME w
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  BasicProvers.EVERY_CASE_TAC >> simp[] >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Triviality ao_resolve_iszero_op_not_label[local]:
  !targets op lbl.
    (!v chain k. ALOOKUP targets v = SOME chain /\
      0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w) ==>
    ao_resolve_iszero_op targets PHI op = Label lbl ==>
    op = Label lbl
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op` >> simp[ao_resolve_iszero_op_def] >>
  rename1 `ALOOKUP targets vn` >>
  Cases_on `ALOOKUP targets vn` >> simp[] >>
  rename1 `SOME chain` >>
  simp[LET_THM] >>
  qabbrev_tac `keep = 2 - (LENGTH chain - 1) MOD 2` >>
  COND_CASES_TAC >> simp[] >>
  strip_tac >>
  `0 < keep /\ keep < LENGTH chain` by
    (qunabbrev_tac `keep` >> fs[] >>
     `(LENGTH chain - 1) MOD 2 < 2` by simp[] >> DECIDE_TAC) >>
  first_x_assum (qspecl_then [`vn`, `chain`, `keep`] mp_tac) >>
  simp[] >> strip_tac >> fs[operand_distinct]
QED

Triviality resolve_phi_map_label_pres[local]:
  !prev ops g.
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op lbl. g op = Label lbl ==> op = Label lbl) ==>
    resolve_phi prev (MAP g ops) = OPTION_MAP g (resolve_phi prev ops)
Proof
  rpt gen_tac >> strip_tac >>
  qid_spec_tac `ops` >> qid_spec_tac `prev` >>
  ho_match_mp_tac resolve_phi_ind >> rw[resolve_phi_def] >| [
    `!lbl. g (Lit v8) <> Label lbl` by
      (rpt strip_tac >> `Lit v8 = Label lbl` by metis_tac[] >>
       gvs[operand_distinct]) >>
    Cases_on `g (Lit v8)` >> gvs[resolve_phi_def],
    `!lbl. g (Var v9) <> Label lbl` by
      (rpt strip_tac >> `Var v9 = Label lbl` by metis_tac[] >>
       gvs[operand_distinct]) >>
    Cases_on `g (Var v9)` >> gvs[resolve_phi_def]
  ]
QED

(* PHI resolution sim using global chain invariant. *)
Theorem ao_resolve_phi_sim:
  !targets inst s fuel ctx.
    inst.inst_opcode = PHI /\
    ao_iszero_chain_inv targets s /\
    ao_chains_defined_at targets s /\
    ao_targets_wf targets /\
    (!v chain k. ALOOKUP targets v = SOME chain /\
      0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w) /\
    ~(?e. step_inst fuel ctx inst s = Error e) ==>
    step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    simp[step_inst_non_invoke] >>
  `step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
   step_inst_base (ao_resolve_iszero_inst targets inst) s` by
    simp[step_inst_non_invoke, ao_resolve_iszero_inst_def] >>
  simp[] >>
  simp[Once step_inst_base_def, SimpRHS] >>
  simp[Once step_inst_base_def, ao_resolve_iszero_inst_def] >>
  qabbrev_tac `g = ao_resolve_iszero_op targets PHI` >>
  `!lbl. g (Label lbl) = Label lbl` by
    simp[Abbr `g`, ao_resolve_iszero_op_def] >>
  `!op lbl. g op = Label lbl ==> op = Label lbl` by
    metis_tac[ao_resolve_iszero_op_not_label] >>
  `!prev. resolve_phi prev (MAP g inst.inst_operands) =
   OPTION_MAP g (resolve_phi prev inst.inst_operands)` by
    (gen_tac >> irule resolve_phi_map_label_pres >> simp[]) >>
  Cases_on `s.vs_prev_bb` >> simp[] >>
  rename1 `SOME prev` >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `resolve_phi prev inst.inst_operands` >> simp[] >>
  rename1 `resolve_phi prev _ = SOME val_op` >>
  simp[] >>
  `eval_operand (g val_op) s = eval_operand val_op s` by
    (qunabbrev_tac `g` >>
     irule resolve_op_eval_eq_at >> simp[] >>
     qpat_x_assum `~_` mp_tac >> simp[Once step_inst_def] >>
     simp[Once step_inst_base_def] >>
     BasicProvers.EVERY_CASE_TAC >> simp[]) >>
  simp[]
QED

(* PHI resolution sim with per-operand (loop-robust) hypotheses. Mirrors
   ao_resolve_iszero_inst_sim_local: filters targets to the PHI's operand
   keys, on which the global chain invariant holds, then reduces to
   ao_resolve_phi_sim. *)
Theorem ao_resolve_phi_sim_local:
  !targets inst fuel ctx st.
    inst.inst_opcode = PHI /\
    ao_targets_wf targets /\
    (!v chain k. ALOOKUP targets v = SOME chain /\
      0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w) /\
    (!v chain k. MEM (Var v) inst.inst_operands /\
                 ALOOKUP targets v = SOME chain /\
                 (?w0. eval_operand (Var v) st = SOME w0) /\
                 k < LENGTH chain ==>
                 ?w. eval_operand (EL k chain) st = SOME w) /\
    (!v chain k. MEM (Var v) inst.inst_operands /\
                 ALOOKUP targets v = SOME chain /\ k + 1 < LENGTH chain ==>
                 !val_k val_k1.
                   eval_operand (EL k chain) st = SOME val_k /\
                   eval_operand (EL (k + 1) chain) st = SOME val_k1 ==>
                   val_k1 = bool_to_word (val_k = 0w)) /\
    ~(?e. step_inst fuel ctx inst st = Error e) ==>
    step_inst fuel ctx (ao_resolve_iszero_inst targets inst) st =
    step_inst fuel ctx inst st
Proof
  rpt strip_tac >>
  qabbrev_tac `P = \v:string. MEM (Var v) inst.inst_operands` >>
  qabbrev_tac `rt = FILTER (\(v, chain). P v) targets` >>
  `!v. P v ==> ALOOKUP rt v = ALOOKUP targets v` by
    simp[Abbr `rt`, alistTheory.ALOOKUP_FILTER] >>
  `!v. ~P v ==> ALOOKUP rt v = NONE` by
    simp[Abbr `rt`, alistTheory.ALOOKUP_FILTER] >>
  `ao_resolve_iszero_inst targets inst =
   ao_resolve_iszero_inst rt inst` by
    (simp[ao_resolve_iszero_inst_def, instruction_component_equality] >>
     irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
     Cases_on `x` >> simp[ao_resolve_iszero_op_def] >>
     rename1 `Var vn` >>
     `P vn` by simp[Abbr `P`] >>
     first_x_assum drule >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  `ao_targets_wf rt` by
    (rw[ao_targets_wf_def] >> rpt strip_tac >> (
     `P v` by
       (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >>
     metis_tac[ao_targets_wf_def])) >>
  `!v chain k. ALOOKUP rt v = SOME chain /\ 0 < k /\ k < LENGTH chain ==>
     ?w. EL k chain = Var w` by
    (rpt strip_tac >>
     `P v` by
       (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >>
     metis_tac[]) >>
  `ao_iszero_chain_inv rt st` by
    (rw[ao_iszero_chain_inv_def] >> rpt strip_tac >>
     `P v` by
       (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >>
     `MEM (Var v) inst.inst_operands` by fs[Abbr `P`] >>
     qpat_x_assum `!v chain k. MEM _ _ /\ _ /\ k + 1 < _ ==> _`
       (qspecl_then [`v`, `chain`, `k`] mp_tac) >> simp[]) >>
  `ao_chains_defined_at rt st` by
    (rw[ao_chains_defined_at_def] >> rpt strip_tac >>
     `P v` by
       (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >>
     `MEM (Var v) inst.inst_operands` by fs[Abbr `P`] >>
     qpat_x_assum `!v chain k. _ /\ _ /\ _ /\ k < _ ==> ?w. _`
       (qspecl_then [`v`, `chain`, `k`] mp_tac) >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  irule ao_resolve_phi_sim >> simp[] >>
  conj_tac
  >- first_assum ACCEPT_TAC
  >- (qpat_x_assum `~(?e. _)` mp_tac >> simp[])
QED

(* ===== Small step helpers (loop-robust per-inst sim support) ===== *)

Theorem ao_resolve_iszero_op_iszero:
  !targets op. ao_resolve_iszero_op targets ISZERO op = op
Proof
  rpt gen_tac >> Cases_on `op` >> simp[ao_resolve_iszero_op_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem invoke_operand_defined:
  !fuel ctx inst s v.
    inst.inst_opcode = INVOKE /\
    ~(?e. step_inst fuel ctx inst s = Error e) /\
    MEM (Var v) inst.inst_operands ==>
    v IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  gvs[Once step_inst_def, decode_invoke_def, AllCaseEqs()] >>
  drule eval_operands_mem_defined >>
  disch_then (qspec_then `Var v` mp_tac) >>
  simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem step_inst_base_zero_eval_op_irrel:
  !inst ops s.
    MEM inst.inst_opcode [NOP; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MEMTOP] ==>
    step_inst_base (inst with inst_operands := ops) s =
    step_inst_base inst s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM _ _` mp_tac >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  gvs[step_inst_base_def, exec_read0_def]
QED

(* ==========================================================================
   PHI iszero-resolution: eval_phis-level bridge.

   ao_transform_inst maps PHI -> [inst]; PHI iszero-use resolution is run as a
   post-pass (ao_resolve_phis_block).  The simulation engine relates a block to
   its pre-resolution transformed body at the run_block level.  These lemmas
   bridge run_block (ao_resolve_phis_block targets tbb) s to run_block tbb s by
   showing the PHI resolution preserves eval_phis (value-preserving on defined
   PHI operands) and leaves the non-PHI body untouched.
   ========================================================================== *)

(* eval_one_phi agreement under the global chain invariant: if the original
   PHI evaluates to SOME (out, w), so does the resolved PHI. *)
Theorem ao_resolve_eval_one_phi_eq_global:
  !targets inst s out w.
    inst.inst_opcode = PHI /\
    ao_iszero_chain_inv targets s /\
    ao_chains_defined_at targets s /\
    ao_targets_wf targets /\
    (!v chain k. ALOOKUP targets v = SOME chain /\ 0 < k /\ k < LENGTH chain ==>
       ?u. EL k chain = Var u) /\
    eval_one_phi s inst = SOME (out, w) ==>
    eval_one_phi s (ao_resolve_iszero_inst targets inst) = SOME (out, w)
Proof
  rpt strip_tac >>
  qabbrev_tac `g = ao_resolve_iszero_op targets PHI` >>
  `(ao_resolve_iszero_inst targets inst).inst_outputs = inst.inst_outputs /\
   (ao_resolve_iszero_inst targets inst).inst_operands = MAP g inst.inst_operands`
    by simp[ao_resolve_iszero_inst_def, Abbr `g`] >>
  `!lbl. g (Label lbl) = Label lbl` by simp[Abbr `g`, ao_resolve_iszero_op_def] >>
  `!op lbl. g op = Label lbl ==> op = Label lbl` by
    metis_tac[ao_resolve_iszero_op_not_label] >>
  qpat_x_assum `eval_one_phi s inst = SOME (out, w)` mp_tac >>
  simp[eval_one_phi_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `s.vs_prev_bb` >> simp[] >>
  rename1 `s.vs_prev_bb = SOME prev` >>
  Cases_on `resolve_phi prev inst.inst_operands` >> simp[] >>
  rename1 `resolve_phi prev inst.inst_operands = SOME val_op` >>
  Cases_on `eval_operand val_op s` >> simp[] >>
  strip_tac >>
  simp[eval_one_phi_def] >>
  `resolve_phi prev (MAP g inst.inst_operands) =
   OPTION_MAP g (resolve_phi prev inst.inst_operands)` by
    (irule resolve_phi_map_label_pres >> simp[]) >>
  simp[] >>
  `eval_operand (g val_op) s = eval_operand val_op s` by
    (qunabbrev_tac `g` >> irule resolve_op_eval_eq_at >> simp[]) >>
  gvs[]
QED

(* Loop-robust per-operand version: filters targets to the PHI's operand keys
   (mirrors ao_resolve_phi_sim_local) so only per-operand chain facts are
   needed, then reduces to the global version. *)
Theorem ao_resolve_eval_one_phi_eq:
  !targets inst s out w.
    inst.inst_opcode = PHI /\
    ao_targets_wf targets /\
    (!v chain k. ALOOKUP targets v = SOME chain /\ 0 < k /\ k < LENGTH chain ==>
       ?u. EL k chain = Var u) /\
    (!v chain k. MEM (Var v) inst.inst_operands /\
                 ALOOKUP targets v = SOME chain /\
                 (?w0. eval_operand (Var v) s = SOME w0) /\
                 k < LENGTH chain ==>
                 ?u. eval_operand (EL k chain) s = SOME u) /\
    (!v chain k. MEM (Var v) inst.inst_operands /\
                 ALOOKUP targets v = SOME chain /\ k + 1 < LENGTH chain ==>
                 !val_k val_k1.
                   eval_operand (EL k chain) s = SOME val_k /\
                   eval_operand (EL (k + 1) chain) s = SOME val_k1 ==>
                   val_k1 = bool_to_word (val_k = 0w)) /\
    eval_one_phi s inst = SOME (out, w) ==>
    eval_one_phi s (ao_resolve_iszero_inst targets inst) = SOME (out, w)
Proof
  rpt strip_tac >>
  qabbrev_tac `P = \v:string. MEM (Var v) inst.inst_operands` >>
  qabbrev_tac `rt = FILTER (\(v, chain). P v) targets` >>
  `!v. P v ==> ALOOKUP rt v = ALOOKUP targets v` by
    simp[Abbr `rt`, alistTheory.ALOOKUP_FILTER] >>
  `!v. ~P v ==> ALOOKUP rt v = NONE` by
    simp[Abbr `rt`, alistTheory.ALOOKUP_FILTER] >>
  `ao_resolve_iszero_inst targets inst = ao_resolve_iszero_inst rt inst` by
    (simp[ao_resolve_iszero_inst_def, instruction_component_equality] >>
     irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
     Cases_on `x` >> simp[ao_resolve_iszero_op_def] >>
     rename1 `Var vn` >> `P vn` by simp[Abbr `P`] >>
     first_x_assum drule >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  `ao_targets_wf rt` by
    (rw[ao_targets_wf_def] >> rpt strip_tac >> (
     `P v` by (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >>
     metis_tac[ao_targets_wf_def])) >>
  `!v chain k. ALOOKUP rt v = SOME chain /\ 0 < k /\ k < LENGTH chain ==>
     ?u. EL k chain = Var u` by
    (rpt strip_tac >>
     `P v` by (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >> metis_tac[]) >>
  `ao_iszero_chain_inv rt s` by
    (rw[ao_iszero_chain_inv_def] >> rpt strip_tac >>
     `P v` by (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >>
     `MEM (Var v) inst.inst_operands` by fs[Abbr `P`] >>
     qpat_x_assum `!v chain k. MEM _ _ /\ _ /\ k + 1 < _ ==> _`
       (qspecl_then [`v`, `chain`, `k`] mp_tac) >> simp[]) >>
  `ao_chains_defined_at rt s` by
    (rw[ao_chains_defined_at_def] >> rpt strip_tac >>
     `P v` by (CCONTR_TAC >> `ALOOKUP rt v = NONE` by metis_tac[] >> gvs[]) >>
     `ALOOKUP targets v = SOME chain` by metis_tac[] >>
     `MEM (Var v) inst.inst_operands` by fs[Abbr `P`] >>
     qpat_x_assum `!v chain k. MEM _ _ /\ _ /\ _ /\ k < _ ==> ?u. _`
       (qspecl_then [`v`, `chain`, `k`] mp_tac) >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  irule ao_resolve_eval_one_phi_eq_global >> simp[] >>
  first_assum ACCEPT_TAC
QED

(* phi_prefix_length is determined by opcodes, so an opcode-preserving map
   leaves it unchanged. *)
Triviality phi_prefix_length_map_opcode_pres[local]:
  !hf l. (!x. (hf x).inst_opcode = x.inst_opcode) ==>
    phi_prefix_length (MAP hf l) = phi_prefix_length l
Proof
  ntac 2 strip_tac >> Induct_on `l` >> rw[phi_prefix_length_def]
QED

(* ao_resolve_phis_block only rewrites PHI operands; at every execution step a
   PHI errors identically and a non-PHI is untouched, so exec_block is
   unaffected. *)
Triviality exec_block_resolve_phis_eq[local]:
  !n fuel ctx targets tbb s.
    LENGTH tbb.bb_instructions - s.vs_inst_idx = n ==>
    exec_block fuel ctx (ao_resolve_phis_block targets tbb) s =
    exec_block fuel ctx tbb s
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `hf = \inst:instruction.
    if inst.inst_opcode = PHI then ao_resolve_iszero_inst targets inst else inst` >>
  qabbrev_tac `R = ao_resolve_phis_block targets tbb` >>
  `R.bb_instructions = MAP hf tbb.bb_instructions` by
    simp[Abbr `R`, Abbr `hf`, ao_resolve_phis_block_def] >>
  `!x. (hf x).inst_opcode = x.inst_opcode` by
    (rw[Abbr `hf`] >> simp[ao_resolve_iszero_inst_def]) >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  reverse (Cases_on `s.vs_inst_idx < LENGTH tbb.bb_instructions`)
  >- (`get_instruction R s.vs_inst_idx = NONE /\
       get_instruction tbb s.vs_inst_idx = NONE` by
        simp[get_instruction_def] >> simp[]) >>
  `get_instruction R s.vs_inst_idx = SOME (hf (EL s.vs_inst_idx tbb.bb_instructions)) /\
   get_instruction tbb s.vs_inst_idx = SOME (EL s.vs_inst_idx tbb.bb_instructions)` by
    simp[get_instruction_def, listTheory.EL_MAP] >>
  qabbrev_tac `inst = EL s.vs_inst_idx tbb.bb_instructions` >>
  simp[] >>
  Cases_on `inst.inst_opcode = PHI`
  >- (`(hf inst).inst_opcode = PHI` by simp[] >>
      `inst.inst_opcode <> INVOKE /\ (hf inst).inst_opcode <> INVOKE` by simp[] >>
      `step_inst fuel ctx (hf inst) s = Error "phi outside prefix" /\
       step_inst fuel ctx inst s = Error "phi outside prefix"` by
        simp[step_inst_non_invoke, step_inst_base_def] >>
      simp[]) >>
  `hf inst = inst` by simp[Abbr `hf`] >>
  simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK s'` >>
  first_x_assum (qspec_then `LENGTH tbb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `targets`, `tbb`,
    `s' with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[Abbr `R`]
QED

(* ===== Generic FLAT/MAPi prefix helpers ===== *)

Triviality phi_prefix_len_le[local]:
  !l. phi_prefix_length l <= LENGTH l
Proof
  Induct >> rw[phi_prefix_length_def]
QED

(* eval_phis OK means every prefix PHI evaluates to SOME. *)
Theorem eval_phis_ok_prefix_phi_some:
  !insts s s'.
    eval_phis s insts = OK s' ==>
    !idx. idx < phi_prefix_length insts ==>
      ?out w. eval_one_phi s (EL idx insts) = SOME (out, w)
Proof
  Induct >- simp[phi_prefix_length_def] >>
  rpt strip_tac >>
  rename1 `eval_phis s (phi::insts) = OK s'` >>
  `phi.inst_opcode = PHI` by (CCONTR_TAC >> fs[phi_prefix_length_def]) >>
  qpat_x_assum `eval_phis s (phi::insts) = OK s'` mp_tac >>
  simp[Once eval_phis_def] >>
  Cases_on `eval_one_phi s phi` >> simp[] >>
  rename1 `eval_one_phi s phi = SOME outv` >> Cases_on `outv` >> simp[] >>
  Cases_on `eval_phis s insts` >> simp[] >> strip_tac >>
  Cases_on `idx` >> gvs[] >>
  rename1 `eval_phis s insts = OK s''` >>
  first_x_assum (qspecl_then [`s`, `s''`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `n` mp_tac) >>
  impl_tac >- fs[phi_prefix_length_def] >>
  simp[]
QED

(* For a map that is identity-as-singleton on the PHI prefix, FLAT over the
   prefix is the prefix itself. *)
Triviality flat_take_phi_prefix_eq[local]:
  !f l.
    (!i. i < phi_prefix_length l ==> f i (EL i l) = [EL i l]) ==>
    FLAT (TAKE (phi_prefix_length l) (MAPi f l)) = TAKE (phi_prefix_length l) l
Proof
  Induct_on `l` >- simp[phi_prefix_length_def] >>
  rpt strip_tac >> simp[phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  `f 0 h = [h]` by (first_x_assum (qspec_then `0` mp_tac) >> simp[phi_prefix_length_def]) >>
  simp[indexedListsTheory.MAPi_def, combinTheory.o_DEF] >>
  first_x_assum ho_match_mp_tac >> rpt strip_tac >>
  rename1 `j < phi_prefix_length l` >>
  qpat_x_assum `!i. i < phi_prefix_length (h::l) ==> _`
    (qspec_then `SUC j` mp_tac) >> simp[phi_prefix_length_def]
QED

(* Within the PHI prefix, FLAT (MAPi f l) agrees pointwise with l. *)
Theorem prefix_el_flat_mapi:
  !f l idx.
    (!i. i < phi_prefix_length l ==> f i (EL i l) = [EL i l]) /\
    idx < phi_prefix_length l ==>
    EL idx (FLAT (MAPi f l)) = EL idx l
Proof
  rpt strip_tac >>
  `phi_prefix_length l <= LENGTH l` by simp[phi_prefix_len_le] >>
  `FLAT (TAKE (phi_prefix_length l) (MAPi f l)) = TAKE (phi_prefix_length l) l` by
    (irule flat_take_phi_prefix_eq >> simp[]) >>
  `MAPi f l = TAKE (phi_prefix_length l) (MAPi f l) ++
              DROP (phi_prefix_length l) (MAPi f l)` by simp[] >>
  `FLAT (MAPi f l) = TAKE (phi_prefix_length l) l ++
                     FLAT (DROP (phi_prefix_length l) (MAPi f l))` by
    metis_tac[listTheory.FLAT_APPEND] >>
  pop_assum SUBST1_TAC >>
  `idx < LENGTH (TAKE (phi_prefix_length l) l)` by simp[listTheory.LENGTH_TAKE] >>
  simp[rich_listTheory.EL_APPEND1, listTheory.EL_TAKE]
QED

(* eval_phis is preserved by PHI resolution given per-prefix-index eval_one_phi
   agreement (established by callers from the chain invariant). *)
Theorem eval_phis_resolve_eq:
  !targets s insts s_phi.
    eval_phis s insts = OK s_phi /\
    (!idx. idx < phi_prefix_length insts ==>
       eval_one_phi s (ao_resolve_iszero_inst targets (EL idx insts)) =
       eval_one_phi s (EL idx insts)) ==>
    eval_phis s
      (MAP (\inst. if inst.inst_opcode = PHI
                   then ao_resolve_iszero_inst targets inst else inst) insts) =
    OK s_phi
Proof
  Induct_on `insts` >- simp[eval_phis_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `eval_phis s (phi::insts) = OK s_phi` >>
  reverse (Cases_on `phi.inst_opcode = PHI`)
  >- (qpat_x_assum `eval_phis s (phi::insts) = OK s_phi` mp_tac >>
      simp[eval_phis_def]) >>
  `eval_one_phi s (ao_resolve_iszero_inst targets phi) = eval_one_phi s phi` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[phi_prefix_length_def]) >>
  `(ao_resolve_iszero_inst targets phi).inst_opcode = PHI` by
    simp[ao_resolve_iszero_inst_def] >>
  qpat_x_assum `eval_phis s (phi::insts) = OK s_phi` mp_tac >>
  simp[Once eval_phis_def] >>
  Cases_on `eval_one_phi s phi` >> simp[] >>
  rename1 `eval_one_phi s phi = SOME outv` >> Cases_on `outv` >> simp[] >>
  rename1 `eval_one_phi s phi = SOME (out, w)` >>
  Cases_on `eval_phis s insts` >> simp[] >>
  rename1 `eval_phis s insts = OK s'` >> strip_tac >>
  `eval_phis s (MAP (\inst. if inst.inst_opcode = PHI
                   then ao_resolve_iszero_inst targets inst else inst) insts) =
   OK s'` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC idx` mp_tac) >>
     simp[phi_prefix_length_def]) >>
  simp[Once eval_phis_def]
QED

(* Top-level bridge: run_block is unchanged by the PHI resolution post-pass,
   given eval_one_phi agreement on the prefix PHIs at the entry state. *)
Theorem run_block_resolve_phis_bridge:
  !targets tbb fuel ctx s s_phi.
    eval_phis s tbb.bb_instructions = OK s_phi /\
    (!idx. idx < phi_prefix_length tbb.bb_instructions ==>
       eval_one_phi s (ao_resolve_iszero_inst targets (EL idx tbb.bb_instructions)) =
       eval_one_phi s (EL idx tbb.bb_instructions)) ==>
    run_block fuel ctx (ao_resolve_phis_block targets tbb) s =
    run_block fuel ctx tbb s
Proof
  rpt strip_tac >>
  `eval_phis s (ao_resolve_phis_block targets tbb).bb_instructions = OK s_phi` by
    (simp[ao_resolve_phis_block_def] >> irule eval_phis_resolve_eq >>
     first_assum (irule_at Any) >> simp[]) >>
  `phi_prefix_length (ao_resolve_phis_block targets tbb).bb_instructions =
   phi_prefix_length tbb.bb_instructions` by
    (simp[ao_resolve_phis_block_def] >> irule phi_prefix_length_map_opcode_pres >>
     rw[] >> simp[ao_resolve_iszero_inst_def]) >>
  simp[run_block_def] >>
  qspecl_then [`LENGTH tbb.bb_instructions - phi_prefix_length tbb.bb_instructions`,
    `fuel`, `ctx`, `targets`, `tbb`,
    `s_phi with vs_inst_idx := phi_prefix_length tbb.bb_instructions`]
    mp_tac exec_block_resolve_phis_eq >>
  simp[]
QED
