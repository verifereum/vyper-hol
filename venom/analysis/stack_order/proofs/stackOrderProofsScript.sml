(*
 * Stack Order Analysis — Proofs
 *
 * Internal lemmas and proofs of consumer-facing properties.
 *
 * Internal lemmas:
 *   so_handle_inst_stack_top_proof  — operands on top after handle_inst
 *   so_analyze_block_needed_distinct_proof — needed list has no duplicates
 *   so_needed_are_live_proof        — needed vars are live at block entry
 *
 * API proofs (consumed by stackOrderProps via ACCEPT_TAC):
 *   so_get_stack_sound_proof
 *   so_merge_prefix_proof
 *   so_from_to_includes_live_proof
 *   so_from_to_includes_base_proof
 *)

Theory stackOrderProofs
Ancestors
  stackOrderDefs cfgAnalysisProps
Libs
  rich_listTheory listTheory arithmeticTheory pred_setTheory finite_mapTheory
  venomInstTheory stackOrderInternalDefsTheory stackOrderDefsTheory

val _ = Parse.hide "from_to";

(* ==========================================================================
   Helper lemmas — prefix
   ========================================================================== *)

(* max_same_prefix = lcp2 from rich_list *)
Theorem max_same_prefix_eq_lcp2[local]:
  ∀xs ys. max_same_prefix xs ys = lcp2 xs ys
Proof
  Induct >> simp[max_same_prefix_def, Once lcp2_thm] >>
  gen_tac >> Cases_on ‘ys’ >> simp[max_same_prefix_def] >>
  ONCE_REWRITE_TAC[lcp2_thm] >> simp[]
QED

(* FOLDL of lcp2: result is prefix of every element *)
Theorem foldl_lcp2_prefix[local]:
  ∀ns n x. MEM x (n::ns) ⇒ isPREFIX (FOLDL lcp2 n ns) x
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >> (
    irule IS_PREFIX_TRANS >>
    qexists_tac `lcp2 n h` >> conj_tac
    >- simp[lcp2_prefix]
    >- (first_x_assum match_mp_tac >> simp[]))
QED

(* ==========================================================================
   Helper lemmas — FOLDL conditional SNOC
   ========================================================================== *)

(* FOLDL conditional SNOC preserves membership of base *)
Theorem foldl_cond_snoc_mem_base[local]:
  ∀ls tgt v.
    MEM v tgt ⇒
    MEM v (FOLDL (λtgt v. if MEM v tgt then tgt else SNOC v tgt) tgt ls)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum match_mp_tac >>
  rw[] >> simp[SNOC_APPEND]
QED

(* FOLDL conditional SNOC includes every element of the input *)
Theorem foldl_cond_snoc_mem_input[local]:
  ∀ls tgt v.
    MEM v ls ⇒
    MEM v (FOLDL (λtgt v. if MEM v tgt then tgt else SNOC v tgt) tgt ls)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  irule foldl_cond_snoc_mem_base >>
  rw[] >> simp[SNOC_APPEND]
QED

(* ==========================================================================
   Helper lemmas — so_add_needed
   ========================================================================== *)

(* so_add_needed preserves ALL_DISTINCT *)
Theorem so_add_needed_distinct[local]:
  ∀needed v. ALL_DISTINCT needed ⇒ ALL_DISTINCT (so_add_needed needed v)
Proof
  simp[so_add_needed_def] >> rpt strip_tac >>
  rw[] >> simp[ALL_DISTINCT_SNOC]
QED

(* so_add_needed preserves membership *)
Theorem so_add_needed_mem[local]:
  ∀needed v w. MEM w needed ⇒ MEM w (so_add_needed needed v)
Proof
  simp[so_add_needed_def] >> rpt strip_tac >>
  rw[] >> simp[SNOC_APPEND]
QED

(* ==========================================================================
   API proofs — easy three (standalone, no deps on other theorems)
   ========================================================================== *)

(* Merge is a prefix of every input order *)
Theorem so_merge_prefix_proof:
  ∀orders n. MEM n orders ⇒
    isPREFIX (so_merge orders) n
Proof
  Cases >> simp[so_merge_def] >> rpt strip_tac >> gvs[] >> (
    qsuff_tac `FOLDL max_same_prefix h t = FOLDL lcp2 h t`
    >- (disch_then (fn eq => REWRITE_TAC[eq]) >>
        irule foldl_lcp2_prefix >> simp[])
    >- (AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
        simp[FUN_EQ_THM, max_same_prefix_eq_lcp2]))
QED

(* from_to query includes base *)
Theorem so_from_to_includes_base_proof:
  ∀lr fn from_to origin succ v needed.
    FLOOKUP from_to (origin, succ) = SOME needed ∧
    MEM v needed ⇒
    MEM v (so_from_to_query lr fn from_to origin succ)
Proof
  rpt strip_tac >>
  simp[so_from_to_query_def, LET_THM] >>
  Cases_on `lookup_block succ fn.fn_blocks` >> simp[] >>
  irule foldl_cond_snoc_mem_base >> simp[]
QED

(* from_to query includes live input vars *)
Theorem so_from_to_includes_live_proof:
  ∀lr fn from_to origin succ v succ_bb.
    lookup_block succ fn.fn_blocks = SOME succ_bb ∧
    MEM v (input_vars_from origin succ_bb.bb_instructions
             (live_vars_at lr succ 0)) ⇒
    MEM v (so_from_to_query lr fn from_to origin succ)
Proof
  rpt strip_tac >>
  simp[so_from_to_query_def, LET_THM] >>
  irule foldl_cond_snoc_mem_input >> simp[]
QED

(* ==========================================================================
   ALL_DISTINCT preservation through handlers
   ========================================================================== *)

(* FOLDL pair-accumulator: needed component stays ALL_DISTINCT
   when each step only uses so_add_needed or identity on needed *)
Theorem handle_inst_foldl_distinct[local]:
  ∀ops s0 n0.
    ALL_DISTINCT n0 ⇒
    ALL_DISTINCT (SND (FOLDL (λ(s,n) op.
      (if MEM op s then s else SNOC op s,
       case op of
         Var v => if ¬MEM op s then so_add_needed n v else n
       | _ => n)) (s0,n0) ops))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  Cases_on `h` >> simp[so_add_needed_distinct] >>
  rw[] >> simp[so_add_needed_distinct]
QED

(* so_handle_inst preserves ALL_DISTINCT of needed *)
Theorem so_handle_inst_needed_distinct[local]:
  ∀stack needed inst stack' needed'.
    ALL_DISTINCT needed ∧
    (stack', needed') = so_handle_inst (stack, needed) inst ⇒
    ALL_DISTINCT needed'
Proof
  rpt strip_tac >>
  fs[so_handle_inst_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  metis_tac[handle_inst_foldl_distinct, pairTheory.SND]
QED

(* FOLDL preserves ALL_DISTINCT when each step does *)
Theorem foldl_all_distinct[local]:
  ∀ls f n0.
    ALL_DISTINCT n0 ∧
    (∀n x. ALL_DISTINCT n ⇒ ALL_DISTINCT (f n x)) ⇒
    ALL_DISTINCT (FOLDL f n0 ls)
Proof
  Induct >> simp[]
QED

(* so_handle_terminator preserves ALL_DISTINCT of needed *)
Theorem so_handle_terminator_needed_distinct[local]:
  ∀cfg from_to lbl stack needed inst stack' needed'.
    ALL_DISTINCT needed ∧
    (stack', needed') =
      so_handle_terminator cfg from_to lbl (stack, needed) inst ⇒
    ALL_DISTINCT needed'
Proof
  rpt strip_tac >>
  fs[so_handle_terminator_def, LET_THM] >> gvs[] >>
  irule foldl_all_distinct >> conj_tac
  >- (rpt strip_tac >> rw[] >> simp[so_add_needed_distinct])
  >- (irule foldl_all_distinct >> simp[] >> rpt strip_tac >>
      Cases_on `x` >> simp[so_add_needed_distinct] >>
      rw[] >> simp[so_add_needed_distinct])
QED

(* so_handle_assign preserves ALL_DISTINCT of needed *)
Theorem so_handle_assign_needed_distinct[local]:
  ∀lr lbl idx stack needed inst stack' needed'.
    ALL_DISTINCT needed ∧
    (stack', needed') =
      so_handle_assign lr lbl idx (stack, needed) inst ⇒
    ALL_DISTINCT needed'
Proof
  rpt strip_tac >>
  fs[so_handle_assign_def, LET_THM] >>
  Cases_on `HD inst.inst_operands` >> fs[] >> gvs[so_add_needed_distinct] >>
  Cases_on `MEM s (live_vars_at lr lbl (idx + 1))` >> gvs[so_add_needed_distinct] >>
  Cases_on `MEM (Var s) stack` >> gvs[so_add_needed_distinct]
QED

(* so_step preserves ALL_DISTINCT of sobs_needed *)
Theorem so_step_needed_distinct[local]:
  ∀cfg lr from_to lbl st inst.
    ALL_DISTINCT st.sobs_needed ⇒
    ALL_DISTINCT (so_step cfg lr from_to lbl st inst).sobs_needed
Proof
  rpt strip_tac >>
  simp[so_step_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  rw[] >> simp[] >>
  metis_tac[so_handle_assign_needed_distinct, so_handle_terminator_needed_distinct,
            so_handle_inst_needed_distinct, pairTheory.PAIR, pairTheory.SND, pairTheory.FST]
QED

(* ==========================================================================
   Remaining proofs
   ========================================================================== *)

(* --- Length preservation --- *)

Theorem stack_swap_length[local]:
  ∀stack op. LENGTH (stack_swap stack op) = LENGTH stack
Proof
  rw[stack_swap_def, LET_THM] >> CASE_TAC >> simp[]
QED

Theorem stack_swap_to_length[local]:
  ∀stack d. LENGTH (stack_swap_to stack d) = LENGTH stack
Proof
  simp[stack_swap_to_def, LET_THM]
QED

Theorem so_reorder_aux_length[local]:
  ∀ops stack count idx.
    LENGTH (so_reorder_aux stack count idx ops) = LENGTH stack
Proof
  Induct >> simp[so_reorder_aux_def, LET_THM, stack_swap_length, stack_swap_to_length]
QED

(* --- FOLDL phase: membership and length --- *)

(* After the FOLDL in handle_inst, every input operand is on the result stack *)
Theorem handle_inst_foldl_mem[local]:
  ∀ops s0 n0 op.
    MEM op ops ∨ MEM op s0 ⇒
    MEM op (FST (FOLDL (λ(s,n) op'.
      (if MEM op' s then s else SNOC op' s,
       case op' of
         Var v => if ¬MEM op' s then so_add_needed n v else n
       | _ => n)) (s0,n0) ops))
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum irule >> rw[]
QED

(* The FOLDL only grows the stack (never shrinks) *)
Theorem handle_inst_foldl_length_ge[local]:
  ∀ops s0 n0.
    LENGTH s0 ≤
    LENGTH (FST (FOLDL (λ(s,n) op.
      (if MEM op s then s else SNOC op s,
       case op of
         Var v => if ¬MEM op s then so_add_needed n v else n
       | _ => n)) (s0,n0) ops))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`if MEM h s0 then s0 else SNOC h s0`,
    `case h of Var v => if ¬MEM h s0 then so_add_needed n0 v else n0
     | _ => n0`] mp_tac) >>
  rw[]
QED

(* --- stack_find properties --- *)

Theorem stack_find_correct[local]:
  ∀op stack i. stack_find op stack = SOME i ⇒
    i < LENGTH stack ∧ EL i stack = op
Proof
  Induct_on `stack` >> simp[stack_find_def] >>
  rpt gen_tac >> Cases_on `h = op` >> gvs[] >>
  Cases_on `stack_find op stack` >> gvs[] >>
  strip_tac >> gvs[] >> res_tac
QED

Theorem stack_find_exists[local]:
  ∀op stack. MEM op stack ⇒ ∃i. stack_find op stack = SOME i
Proof
  Induct_on `stack` >> simp[stack_find_def] >>
  rpt strip_tac >> gvs[] >> rw[]
QED

(* --- stack_swap EL properties --- *)

(* Combined: stack_swap preserves length and puts op at top *)
Theorem stack_swap_top[local]:
  ∀stack op. MEM op stack ∧ stack <> [] ⇒
    EL (LENGTH stack - 1) (stack_swap stack op) = op
Proof
  rpt strip_tac >>
  simp[stack_swap_def, LET_THM] >>
  `∃i. stack_find op stack = SOME i` by metis_tac[stack_find_exists] >>
  simp[] >> imp_res_tac stack_find_correct >> simp[LUPDATE_SEM]
QED

Theorem stack_swap_el_other[local]:
  ∀stack op j i.
    stack_find op stack = SOME i ∧
    j < LENGTH stack ∧ j <> i ∧ j <> LENGTH stack - 1 ⇒
    EL j (stack_swap stack op) = EL j stack
Proof
  simp[stack_swap_def, LET_THM, LUPDATE_SEM]
QED

(* --- stack_swap_to EL properties --- *)

Theorem stack_swap_to_at_depth[local]:
  ∀stack d.
    d < LENGTH stack ⇒
    EL (LENGTH stack - 1 - d) (stack_swap_to stack d) =
    EL (LENGTH stack - 1) stack
Proof
  simp[stack_swap_to_def, LET_THM, LUPDATE_SEM]
QED

Theorem stack_swap_to_el_other[local]:
  ∀stack d j.
    j < LENGTH stack ∧ j <> LENGTH stack - 1 ∧ j <> LENGTH stack - 1 - d ⇒
    EL j (stack_swap_to stack d) = EL j stack
Proof
  simp[stack_swap_to_def, LET_THM, LUPDATE_SEM]
QED

(* --- so_reorder_aux correctness ---
   Inductive invariant for so_reorder_aux stack count idx ops:
   After processing, EL (len-count+k) result = EL k (placed ++ ops)
   where placed are the idx already-correct elements.

   We first prove a single-step lemma, then the full induction. *)

(* One step: stack_swap + stack_swap_to places op at the target position
   and preserves already-placed elements *)
Theorem reorder_one_step[local]:
  ∀stack op count idx.
    MEM op stack ∧
    count ≤ LENGTH stack ∧ idx < count ∧
    (* op is not in the already-placed region *)
    (∀j. LENGTH stack - count ≤ j ∧ j < LENGTH stack - count + idx ⇒
         EL j stack <> op)
    ⇒
    let s' = stack_swap stack op in
    let s'' = stack_swap_to s' (count - idx - 1) in
    (* op is placed correctly *)
    EL (LENGTH stack - count + idx) s'' = op ∧
    (* previously placed positions are preserved *)
    (∀j. LENGTH stack - count ≤ j ∧ j < LENGTH stack - count + idx ⇒
         EL j s'' = EL j stack) ∧
    (* length preserved *)
    LENGTH s'' = LENGTH stack
Proof
  rpt strip_tac >> simp[LET_THM, stack_swap_to_length, stack_swap_length] >>
  `∃i. stack_find op stack = SOME i` by metis_tac[stack_find_exists] >>
  imp_res_tac stack_find_correct >>
  rpt conj_tac
  (* op placed correctly *)
  >- (simp[stack_swap_to_def, LET_THM, LUPDATE_SEM, stack_swap_length] >>
      simp[stack_swap_def, LET_THM, LUPDATE_SEM])
  (* placed positions preserved *)
  >- (rpt strip_tac >>
      simp[stack_swap_to_def, LET_THM, LUPDATE_SEM, stack_swap_length] >>
      simp[stack_swap_def, LET_THM, LUPDATE_SEM] >>
      Cases_on `j = i` >> gvs[])
QED

(* MEM preserved through swap operations *)
Theorem stack_swap_mem[local]:
  ∀stack op x. MEM x stack ⇒ MEM x (stack_swap stack op)
Proof
  rpt strip_tac >> simp[stack_swap_def, LET_THM] >>
  CASE_TAC >> simp[] >>
  imp_res_tac stack_find_correct >>
  fs[MEM_EL] >>
  simp[EL_LUPDATE] >>
  Cases_on `n = x'`
  >- (qexists_tac `LENGTH stack - 1` >> simp[EL_LUPDATE])
  >> Cases_on `n = LENGTH stack - 1`
  >- (qexists_tac `x'` >> simp[EL_LUPDATE])
  >> qexists_tac `n` >> simp[EL_LUPDATE]
QED

Theorem stack_swap_to_mem[local]:
  ∀stack d x. MEM x stack ⇒ MEM x (stack_swap_to stack d)
Proof
  rpt strip_tac >> simp[stack_swap_to_def, LET_THM] >>
  fs[MEM_EL] >>
  simp[EL_LUPDATE] >>
  Cases_on `n = LENGTH stack - 1`
  >- (qexists_tac `LENGTH stack - (d + 1)` >> simp[EL_LUPDATE])
  >> Cases_on `n = LENGTH stack - (d + 1)`
  >- (qexists_tac `LENGTH stack - 1` >> simp[EL_LUPDATE])
  >> qexists_tac `n` >> simp[EL_LUPDATE]
QED

(* Full induction on ops *)
(* Reorder one step — restated to match so_reorder_aux_def pattern directly *)
Theorem reorder_one_step_alt[local]:
  ∀stack op cnt idx.
    MEM op stack ∧ cnt ≤ LENGTH stack ∧ idx < cnt ∧
    (∀j. LENGTH stack - cnt ≤ j ∧ j < LENGTH stack - cnt + idx ⇒
         EL j stack <> op) ⇒
    let s'' = stack_swap_to (stack_swap stack op) (cnt - (idx + 1)) in
    EL (LENGTH stack - cnt + idx) s'' = op ∧
    (∀j. LENGTH stack - cnt ≤ j ∧ j < LENGTH stack - cnt + idx ⇒
         EL j s'' = EL j stack) ∧
    LENGTH s'' = LENGTH stack
Proof
  rpt strip_tac >>
  REWRITE_TAC[LET_THM] >> BETA_TAC >>
  REWRITE_TAC[SUB_PLUS] >>
  irule (CONV_RULE (DEPTH_CONV BETA_CONV)
           (REWRITE_RULE [LET_THM] reorder_one_step)) >>
  simp[]
QED

(* Helper: placed-correct extends by one step *)
Theorem placed_correct_step[local]:
  ∀s'' stack cnt idx placed h.
    (* s'' properties *)
    EL (LENGTH stack - cnt + idx) s'' = h ∧
    (∀j. LENGTH stack - cnt ≤ j ∧ j < LENGTH stack - cnt + idx ⇒
         EL j s'' = EL j stack) ∧
    LENGTH s'' = LENGTH stack ∧
    (* original placed-correct *)
    LENGTH placed = idx ∧
    cnt ≤ LENGTH stack ∧
    (∀k. k < idx ⇒ EL (LENGTH stack - cnt + k) stack = EL k placed) ⇒
    ∀k'. k' < idx + 1 ⇒
         EL (LENGTH stack - cnt + k') s'' = EL k' (SNOC h placed)
Proof
  rpt strip_tac >> Cases_on `k' < idx`
  >- (`EL (LENGTH stack - cnt + k') s'' =
       EL (LENGTH stack - cnt + k') stack` by
        (first_x_assum irule >> DECIDE_TAC) >>
      `EL (LENGTH stack - cnt + k') stack = EL k' placed` by
        (first_x_assum (qspec_then `k'` mp_tac) >> simp[]) >>
      simp[EL_SNOC] >> fs[])
  >- (`k' = idx` by DECIDE_TAC >> gvs[EL_LENGTH_SNOC])
QED

(* Helper: not-in-placed extends by one step *)
Theorem notin_placed_step[local]:
  ∀s'' stack cnt idx h ops.
    (* s'' properties *)
    EL (LENGTH stack - cnt + idx) s'' = h ∧
    (∀j. LENGTH stack - cnt ≤ j ∧ j < LENGTH stack - cnt + idx ⇒
         EL j s'' = EL j stack) ∧
    (* ALL_DISTINCT (h::ops) *)
    ¬MEM h ops ∧
    cnt ≤ LENGTH stack ∧
    idx < cnt ∧
    (* original notin *)
    (∀op. MEM op ops ⇒
          ∀j. LENGTH stack - cnt ≤ j ∧ j < LENGTH stack - cnt + idx ⇒
              EL j stack ≠ op) ⇒
    ∀op. MEM op ops ⇒
         ∀j. LENGTH stack - cnt ≤ j ∧ j < LENGTH stack - cnt + (idx + 1) ⇒
             EL j s'' ≠ op
Proof
  rpt strip_tac >>
  Cases_on `j < LENGTH stack - cnt + idx`
  >- (`EL j s'' = EL j stack` by
        (first_x_assum irule >> DECIDE_TAC) >>
      `EL j stack <> op` by res_tac >>
      fs[])
  >- (`j = LENGTH stack - cnt + idx` by DECIDE_TAC >>
      gvs[])
QED

Theorem so_reorder_aux_el[local]:
  ∀ops stack count idx placed.
    idx + LENGTH ops = count ∧
    count ≤ LENGTH stack ∧
    ALL_DISTINCT ops ∧
    (∀op. MEM op ops ⇒ MEM op stack) ∧
    LENGTH placed = idx ∧
    (∀k. k < idx ⇒
         EL (LENGTH stack - count + k) stack = EL k placed) ∧
    (∀op. MEM op ops ⇒
          ∀j. LENGTH stack - count ≤ j ∧ j < LENGTH stack - count + idx ⇒
              EL j stack <> op)
    ⇒
    ∀k. k < count ⇒
        EL (LENGTH stack - count + k)
            (so_reorder_aux stack count idx ops) =
        EL k (placed ++ ops)
Proof
  Induct
  >- (rpt strip_tac >> gvs[so_reorder_aux_def] >> simp[EL_APPEND1])
  >> rpt strip_tac
  >> simp[so_reorder_aux_def, LET_THM]
  >> qmatch_goalsub_abbrev_tac `so_reorder_aux s'' _ _ _`
  >> qunabbrev_tac `s''`
  >> qspecl_then [`stack`, `h`, `count'`, `idx`]
      mp_tac (CONV_RULE (DEPTH_CONV BETA_CONV)
                (REWRITE_RULE [LET_THM] reorder_one_step_alt))
  >> impl_tac >- (fs[] >> rpt strip_tac >> res_tac >> simp[])
  >> REWRITE_TAC[LET_THM] >> BETA_TAC
  >> qmatch_goalsub_abbrev_tac `so_reorder_aux s'' _ _ _`
  >> strip_tac
  >> first_x_assum (qspecl_then [`s''`, `count'`, `idx + 1`, `SNOC h placed`] mp_tac)
  >> qpat_x_assum `LENGTH s'' = _` (fn eq => REWRITE_TAC[eq])
  >> `LENGTH s'' = LENGTH stack` by
      (qunabbrev_tac `s''` >> simp[stack_swap_to_length, stack_swap_length])
  >> impl_tac
  >- (
    rpt conj_tac
    >- (`LENGTH (h::ops) = LENGTH ops + 1` by simp[] >> DECIDE_TAC)
    >- simp[]
    >- gvs[]
    >- (rpt strip_tac >> qunabbrev_tac `s''` >>
        irule stack_swap_to_mem >> irule stack_swap_mem >>
        first_x_assum irule >> simp[])
    >- (REWRITE_TAC[LENGTH_SNOC] >> simp[])
    >- (rpt strip_tac >>
        qspecl_then [`s''`, `stack`, `count'`, `idx`, `placed`, `h`]
          mp_tac placed_correct_step >>
        impl_tac >- simp[] >>
        disch_then (qspec_then `k'` mp_tac) >> simp[])
    >- (rpt strip_tac >>
        qspecl_then [`s''`, `stack`, `count'`, `idx`, `h`, `ops`]
          mp_tac notin_placed_step >>
        impl_tac >- (
          rpt conj_tac
          >- simp[]
          >- simp[]
          >- (fs[ALL_DISTINCT])
          >- simp[]
          >- (`LENGTH (h::ops) = LENGTH ops + 1` by simp[] >> DECIDE_TAC)
          >> rpt strip_tac >>
          qpat_x_assum `!op. MEM op (h::ops) ==> _`
            (qspec_then `op'` mp_tac) >>
          impl_tac >- simp[] >>
          disch_then (qspec_then `j'` mp_tac) >>
          simp[]) >>
        strip_tac >> res_tac >> fs[]))
  >> disch_then (qspec_then `k` mp_tac)
  >> impl_tac >- simp[]
  >> `k + LENGTH stack - count' = LENGTH stack - count' + k` by DECIDE_TAC
  >> pop_assum (fn eq => REWRITE_TAC[eq])
  >> REWRITE_TAC[SNOC_APPEND, GSYM APPEND_ASSOC, APPEND]
  >> simp[]
QED

(* Wrapper: DROP formulation *)
Theorem so_reorder_correct[local]:
  ∀stack ops.
    ALL_DISTINCT ops ∧
    (∀op. MEM op ops ⇒ MEM op stack) ∧
    LENGTH ops ≤ LENGTH stack ⇒
    DROP (LENGTH stack - LENGTH ops) (so_reorder stack ops) = ops
Proof
  rpt strip_tac >>
  simp[so_reorder_def] >>
  irule LIST_EQ
  >- (rpt strip_tac >>
      fs[LENGTH_DROP, so_reorder_aux_length] >>
      simp[EL_DROP, so_reorder_aux_length] >>
      qspecl_then [`ops`, `stack`, `LENGTH ops`, `0`, `[]`]
        mp_tac so_reorder_aux_el >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `x` mp_tac) >> simp[])
  >> simp[LENGTH_DROP, so_reorder_aux_length]
QED

(* --- Main theorem --- *)

Theorem so_handle_inst_stack_top_proof:
  ∀stack needed inst stack' needed'.
    ALL_DISTINCT inst.inst_operands ∧
    (stack', needed') = so_handle_inst (stack, needed) inst ⇒
    let n = LENGTH inst.inst_operands in
    n ≤ LENGTH stack' ∧
    DROP (LENGTH stack' - n) stack' = inst.inst_operands
Proof
  rpt strip_tac >>
  fs[so_handle_inst_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  qabbrev_tac `ops = inst.inst_operands` >>
  `∀op. MEM op ops ⇒ MEM op stack''` by
    (rpt strip_tac >> qunabbrev_tac `ops` >>
     qspecl_then [`inst.inst_operands`, `stack`, `needed`]
       mp_tac handle_inst_foldl_mem >> simp[]) >>
  `LENGTH ops ≤ LENGTH stack''` by
    (`set ops ⊆ set stack''` by (simp[SUBSET_DEF] >> metis_tac[]) >>
     `CARD (set ops) ≤ CARD (set stack'')` by
       (irule CARD_SUBSET >> simp[]) >>
     `CARD (set ops) = LENGTH ops` by
       simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
     `CARD (set stack'') ≤ LENGTH stack''` by simp[CARD_LIST_TO_SET] >>
     DECIDE_TAC) >>
  simp[so_reorder_aux_length, so_reorder_def] >>
  qspecl_then [`stack''`, `ops`] mp_tac so_reorder_correct >>
  impl_tac >- simp[] >>
  simp[so_reorder_def]
QED

Theorem foldl_step_distinct[local]:
  ∀insts cfg lr from_to lbl st.
    ALL_DISTINCT st.sobs_needed ⇒
    ALL_DISTINCT (FOLDL (so_step cfg lr from_to lbl) st insts).sobs_needed
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[so_step_needed_distinct]
QED

Theorem so_analyze_block_needed_distinct_proof:
  ∀cfg lr from_to lbl insts needed stack.
    (needed, stack) = so_analyze_block cfg lr from_to lbl insts ⇒
    ALL_DISTINCT needed
Proof
  rpt strip_tac >>
  fs[so_analyze_block_def, LET_THM] >> gvs[] >>
  irule foldl_step_distinct >> simp[]
QED

(* so_needed_are_live_proof: DROPPED — FALSE without single_use_form.
   See stackOrderCexScript.sml for counterexample. *)

(* ==========================================================================
   so_get_stack_sound — ALL_DISTINCT preservation through the analysis
   ========================================================================== *)

Theorem prefix_all_distinct[local]:
  ∀p l. isPREFIX p l ∧ ALL_DISTINCT l ⇒ ALL_DISTINCT p
Proof
  rw[IS_PREFIX_APPEND] >> metis_tac[ALL_DISTINCT_APPEND]
QED

Theorem foldl_update_other_snd[local]:
  ∀preds ft lbl needed a b.
    b <> lbl ⇒
    FLOOKUP (FOLDL (\ft pred. ft |+ ((pred,lbl),needed)) ft preds) (a,b) =
    FLOOKUP ft (a,b)
Proof
  Induct >> rw[FOLDL, FLOOKUP_UPDATE]
QED

Theorem so_record_from_to_other_key[local]:
  ∀cfg ft lbl needed a b.
    b <> lbl ⇒
    FLOOKUP (so_record_from_to cfg ft lbl needed) (a,b) = FLOOKUP ft (a,b)
Proof
  rw[so_record_from_to_def] >> irule foldl_update_other_snd >> simp[]
QED

Theorem so_analyze_succ_other_key[local]:
  ∀cfg lr fn ft succ_lbl a b.
    b <> succ_lbl ⇒
    FLOOKUP (so_analyze_succ cfg lr fn ft succ_lbl) (a,b) = FLOOKUP ft (a,b)
Proof
  rw[so_analyze_succ_def] >>
  Cases_on `lookup_block succ_lbl fn.fn_blocks` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  irule so_record_from_to_other_key >> simp[]
QED

Theorem foldl_succ_preserves[local]:
  ∀succs cfg lr fn ft a b.
    ~MEM b succs ⇒
    FLOOKUP (FOLDL (so_analyze_succ cfg lr fn) ft succs) (a,b) =
    FLOOKUP ft (a,b)
Proof
  Induct >> rw[FOLDL] >>
  `FLOOKUP (FOLDL (so_analyze_succ cfg lr fn)
              (so_analyze_succ cfg lr fn ft h) succs) (a,b) =
   FLOOKUP (so_analyze_succ cfg lr fn ft h) (a,b)` by metis_tac[] >>
  `FLOOKUP (so_analyze_succ cfg lr fn ft h) (a,b) = FLOOKUP ft (a,b)`
    by (irule so_analyze_succ_other_key >> simp[]) >>
  gvs[]
QED

Theorem mem_map_find[local]:
  ∀bbs lbl. MEM lbl (MAP (\bb. bb.bb_label) bbs) ⇒
    ∃bb. FIND (\bb. bb.bb_label = lbl) bbs = SOME bb
Proof
  Induct >> rw[FIND_thm] >> metis_tac[]
QED

Theorem cfg_succ_has_block[local]:
  ∀fn lbl succ.
    wf_function fn ∧
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ⇒
    ∃bb. lookup_block succ fn.fn_blocks = SOME bb
Proof
  rw[lookup_block_def] >>
  irule mem_map_find >>
  metis_tac[cfg_analyze_succ_labels, fn_labels_def]
QED

Theorem foldl_update_other_fst[local]:
  ∀preds ft lbl v a.
    ~MEM a preds ⇒
    FLOOKUP (FOLDL (\ft p. ft |+ ((p,lbl),v)) ft preds) (a,lbl) =
    FLOOKUP ft (a,lbl)
Proof
  Induct >> rw[FOLDL, FLOOKUP_UPDATE]
QED

Theorem foldl_update_mem_writes[local]:
  ∀preds ft lbl v pred.
    MEM pred preds ⇒
    FLOOKUP (FOLDL (\ft p. ft |+ ((p,lbl),v)) ft preds) (pred,lbl) = SOME v
Proof
  Induct >> rw[FOLDL, FLOOKUP_UPDATE] >>
  Cases_on `pred = h` >> gvs[] >>
  Cases_on `MEM h preds` >> gvs[] >>
  simp[foldl_update_other_fst, FLOOKUP_UPDATE]
QED

Theorem analyze_succ_writes[local]:
  ∀cfg lr fn ft succ_lbl pred.
    (∃bb. lookup_block succ_lbl fn.fn_blocks = SOME bb) ∧
    MEM pred (cfg_preds_of cfg succ_lbl) ⇒
    ∃ns. FLOOKUP (so_analyze_succ cfg lr fn ft succ_lbl) (pred, succ_lbl) =
           SOME ns ∧
         ALL_DISTINCT ns
Proof
  rw[so_analyze_succ_def] >> gvs[] >>
  pairarg_tac >> gvs[so_record_from_to_def] >>
  qexists_tac `needed` >> conj_tac >-
  (irule foldl_update_mem_writes >> simp[]) >>
  qpat_x_assum `so_analyze_block _ _ _ _ _ = _` (assume_tac o GSYM) >>
  metis_tac[so_analyze_block_needed_distinct_proof]
QED

Theorem foldl_update_value[local]:
  ∀preds ft lbl v a ns.
    FLOOKUP (FOLDL (\ft p. ft |+ ((p,lbl),v)) ft preds) (a,lbl) = SOME ns ∧
    FLOOKUP ft (a,lbl) <> SOME ns ⇒
    ns = v
Proof
  Induct >> rw[FOLDL] >>
  first_x_assum (qspecl_then [`ft |+ ((h,lbl),v)`, `lbl`, `v`, `a`, `ns`] mp_tac) >>
  Cases_on `ns = v` >> gvs[] >>
  simp[FLOOKUP_UPDATE] >> rw[]
QED

Theorem so_record_from_to_value[local]:
  ∀cfg ft lbl needed a b ns.
    FLOOKUP (so_record_from_to cfg ft lbl needed) (a,b) = SOME ns ∧
    FLOOKUP ft (a,b) <> SOME ns ⇒
    ns = needed
Proof
  rw[so_record_from_to_def] >>
  Cases_on `b = lbl` >-
  (gvs[] >> metis_tac[foldl_update_value]) >>
  `FLOOKUP (FOLDL (\ft pred. ft |+ ((pred,lbl),needed)) ft
     (cfg_preds_of cfg lbl)) (a,b) = FLOOKUP ft (a,b)` by
    (irule foldl_update_other_snd >> simp[]) >>
  gvs[]
QED

Theorem so_analyze_succ_writes_distinct[local]:
  ∀cfg lr fn ft succ_lbl a b ns.
    FLOOKUP (so_analyze_succ cfg lr fn ft succ_lbl) (a,b) = SOME ns ∧
    FLOOKUP ft (a,b) <> SOME ns ⇒
    ALL_DISTINCT ns
Proof
  rw[so_analyze_succ_def] >>
  Cases_on `lookup_block succ_lbl fn.fn_blocks` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  drule_all so_record_from_to_value >> strip_tac >> gvs[] >>
  qpat_x_assum `so_analyze_block _ _ _ _ _ = _` (assume_tac o GSYM) >>
  metis_tac[so_analyze_block_needed_distinct_proof]
QED

Theorem foldl_succ_values[local]:
  ∀succs cfg lr fn ft a b ns.
    FLOOKUP (FOLDL (so_analyze_succ cfg lr fn) ft succs) (a,b) = SOME ns ⇒
    FLOOKUP ft (a,b) = SOME ns ∨ ALL_DISTINCT ns
Proof
  Induct >> rw[FOLDL] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  metis_tac[so_analyze_succ_writes_distinct]
QED

Theorem so_get_stack_sound_proof:
  ∀fn cfg lr from_to lbl merged from_to'.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    (merged, from_to') = so_get_stack cfg lr fn from_to lbl ⇒
    ALL_DISTINCT merged
Proof
  rw[so_get_stack_def, LET_THM] >>
  Cases_on `cfg_succs_of (cfg_analyze fn) lbl`
  >- simp[so_merge_def] >>
  `ALL_DISTINCT (case FLOOKUP (FOLDL (so_analyze_succ (cfg_analyze fn) lr fn)
     from_to (h::t)) (lbl,h) of NONE => [] | SOME n => n)` suffices_by
    (strip_tac >> irule prefix_all_distinct >>
     qexists_tac `case FLOOKUP (FOLDL (so_analyze_succ (cfg_analyze fn) lr fn)
       from_to (h::t)) (lbl,h) of NONE => [] | SOME n => n` >>
     simp[] >> match_mp_tac so_merge_prefix_proof >> simp[MEM]) >>
  Cases_on `FLOOKUP (FOLDL (so_analyze_succ (cfg_analyze fn) lr fn) from_to
              (h::t)) (lbl,h)` >> simp[] >>
  qpat_x_assum `FLOOKUP (FOLDL _ _ (h::t)) _ = _`
    (mp_tac o REWRITE_RULE [FOLDL]) >>
  disch_then (mp_tac o MATCH_MP foldl_succ_values) >>
  strip_tac >> gvs[] >>
  `MEM h (cfg_succs_of (cfg_analyze fn) lbl)` by simp[MEM] >>
  `MEM lbl (cfg_preds_of (cfg_analyze fn) h)` by
    metis_tac[cfg_edge_symmetry_uncond] >>
  `∃bb. lookup_block h fn.fn_blocks = SOME bb` by
    metis_tac[cfg_succ_has_block] >>
  mp_tac analyze_succ_writes >>
  disch_then (qspecl_then [`cfg_analyze fn`, `lr`, `fn`, `from_to`,
                           `h`, `lbl`] mp_tac) >>
  simp[]
QED
