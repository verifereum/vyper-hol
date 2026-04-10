(*
 * Simplify CFG Pass — Collapse DFS Correctness (Main Proofs)
 *
 * Imports infrastructure from simplifyCfgCollapseBase.
 * Contains: merge_step_equiv, merge_step_correct,
 *   try_bypass_correct, collapse_dfs_correct,
 *   collapse_dfs_subst_correct.
 *)

Theory simplifyCfgCollapse
Ancestors
  simplifyCfgCollapseBase
  venomInst venomState cfgTransform simplifyCfgDefs venomExecSemantics
  venomWf stateEquiv stateEquivProps cfgTransformProps venomExecProps
  simplifyCfgHelpers simplifyCfgWf passSimulationProps cfgTransformProofs
  venomExecProofs jumpIndep instIdxIndep simplifyCfgPrevBB

(* prev_bb_equiv_refl lives in simplifyCfgPrevBBTheory *)
val prev_bb_equiv_refl = simplifyCfgPrevBBTheory.prev_bb_equiv_refl;

(* Kill all universally-quantified assumptions.
   Use after applying IH from recInduct to prevent simp/gvs
   from rewriting IH in subsequent by-blocks. *)
val KILL_FORALLS : tactic =
  rpt (first_x_assum (fn th =>
    if is_forall (concl th) then ALL_TAC else FAIL_TAC "not forall"));

(* Unfold run_blocks once, reducing case-on-fuel and beta *)
val UNFOLD_RF_CONV =
  ONCE_REWRITE_CONV [venomExecSemanticsTheory.run_blocks_def]
  THENC PURE_REWRITE_CONV [arithmeticTheory.num_case_def]
  THENC TRY_CONV BETA_CONV
  THENC PURE_REWRITE_CONV [GSYM venomExecSemanticsTheory.run_block_def];

(* ================================================================
   RF-unfold ML tactics: reduce boilerplate in rf-simulation proofs.

   UNFOLD_RF_STEP_TAC side:
     Unfold run_blocks on one side of result_equiv, then simplify.
     side = (RATOR_CONV o RAND_CONV) for func (left), RAND_CONV for func' (right).
     Assumes lookup_block and run_block facts in scope for ASM_REWRITE_TAC.

   FUEL_MONO_RB_TAC:
     Derive run_block m ctx bb s = OK v from run_block n ... = OK v and n ≤ m.
   ================================================================ *)
fun UNFOLD_RF_STEP_TAC side =
  CONV_TAC (side UNFOLD_RF_CONV) >>
  ASM_REWRITE_TAC[] >>
  simp[optionTheory.option_case_def,
       exec_result_case_def];

(* ================================================================
   UNFOLD_RF_ASSUME_TAC: Unfold a run_blocks (SUC n) call found in
   the goal, simplify with a matching lookup_block assumption, and
   add the resulting equation as an assumption. Works with 40+ asms
   (no ASM_REWRITE_TAC). The rf_finder extracts the run_blocks
   term from the goal.
   ================================================================ *)
fun UNFOLD_RF_ASSUME_TAC (rf_finder : term -> term) : tactic = fn (asl, g) =>
  let
    val rf_tm = rf_finder g
    val unf_th = UNFOLD_RF_CONV rf_tm
    (* Extract the lookup_block call from the unfolded RHS *)
    val rhs_tm = rhs (concl unf_th)
    (* rhs is: option_CASE (lookup_block cb fn_blocks) (Error ...) (\bb. ...) *)
    val lookup_tm = rand (rator (rator rhs_tm))
    val fn_blocks_tm = rand lookup_tm
    val cb_tm = rand (rator lookup_tm)
    (* Find matching lookup assumption: lookup_block cb fn_blocks = SOME bb *)
    fun match_lookup t =
      let val (l, _) = dest_eq t
          val fn_blocks_tm' = rand l       (* fn_blocks *)
          val cb_tm' = rand (rator l)      (* cb *)
      in aconv fn_blocks_tm' fn_blocks_tm andalso aconv cb_tm' cb_tm
      end handle _ => false
    val lookup_asm = first match_lookup asl
    val lookup_th = ASSUME lookup_asm
    val full_th = CONV_RULE (RAND_CONV
      (REWRITE_CONV [lookup_th, optionTheory.option_case_def]
       THENC BETA_CONV)) unf_th
  in
    ASSUME_TAC full_th (asl, g)
  end;

(* Common rf_finders for UNFOLD_RF_ASSUME_TAC *)
(* For goal: ?fuel'. _ /\ result_equiv _ _ (run_blocks (SUC n) ctx func' s2) *)
fun rf_in_exists_rhs g =
  let val body = snd (dest_abs (rand g))
  in rand (rand body) end;

(* ================================================================
   SIMPLIFY_CASE_RULE: simplify case-of-constructor in a theorem
   using only exec_result_case_def + BETA. Does NOT use assumptions
   or the simplifier, so won't expand abbreviations like a'.
   ================================================================ *)
val SIMPLIFY_CASE_RULE =
  PURE_REWRITE_RULE [venomExecSemanticsTheory.exec_result_case_def]
  o BETA_RULE;

(* ================================================================
   FUEL_MONO_RB_TAC: Given assumption `run_block n ctx bb s = OK v`
   and `n <= m` in scope, derive `run_block m ctx bb s = OK v`.
   Uses fuel_mono for run_block.
   Usage: FUEL_MONO_RB_TAC [`n`,`m`,`ctx`,`bb`,`s`,`v`]
   ================================================================ *)
val fuel_mono_rb = CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono));

(* FUEL_MONO_RB_TAC: inline the pattern instead.
   mp_tac fuel_mono_rb >>
   disch_then (qspecl_then [`n`,`m`,`ctx`,`bb`,`s`,`OK v`] mp_tac) >>
   (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
   disch_then assume_tac
*)

(* ================================================================
   FIND_A'_DEF: find the a' = (block with bb_instructions := MAP (subst_label_inst ...) ...)
   definition among assumptions. Returns the assumption term.
   ================================================================ *)
fun find_subst_label_def asl =
  first (fn t =>
    is_eq t andalso
    can (find_term (fn t' => is_const t' andalso
      fst (dest_const t') = "subst_label_inst")) (rhs t)) asl;

(* ================================================================
   Helper: resolve_phi with label subst is identity when prev_bb
   doesn't match old or new and operands are phi_well_formed.
   ================================================================ *)

Theorem resolve_phi_subst_irrelevant:
  !old new p ops.
    p <> old /\ p <> new /\ phi_well_formed ops ==>
    resolve_phi p (MAP (subst_label_op old new) ops) = resolve_phi p ops
Proof
  ntac 2 gen_tac >>
  ho_match_mp_tac resolve_phi_ind >>
  rw[resolve_phi_def, subst_label_op_def, phi_well_formed_def,
     listTheory.MAP] >>
  Cases_on `val_op` >>
  gvs[phi_well_formed_def, subst_label_op_def]
QED

(* step_inst_all_prev_bb_equiv now in simplifyCfgPrevBBTheory *)
val step_inst_all_prev_bb_equiv =
  simplifyCfgPrevBBTheory.step_inst_all_prev_bb_equiv;

(* ================================================================
   Idempotence of subst_label_op/inst and phi_map
   ================================================================ *)

Theorem subst_label_op_idem[local]:
  !old new op. subst_label_op old new (subst_label_op old new op) =
    subst_label_op old new op
Proof
  Cases_on `op` >> rw[subst_label_op_def]
QED

Theorem phi_map_idem[local]:
  !old new insts.
    MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old new inst)
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old new inst) insts) =
    MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old new inst) insts
Proof
  ntac 2 gen_tac >> Induct >> rw[] >>
  gvs[subst_label_inst_def, listTheory.MAP_MAP_o,
      combinTheory.o_DEF, subst_label_op_idem] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> rw[]
QED

(* ================================================================
   Block-level equivalence: running a PHI-substituted block from a
   state where prev_bb doesn't match old/new gives the same result.
   ================================================================ *)

(* Helper: phi_operands_wf implies phi_well_formed *)
Triviality phi_operands_wf_implies_phi_well_formed_early:
  !ops. phi_operands_wf ops ==> phi_well_formed ops
Proof
  ho_match_mp_tac phi_operands_wf_ind >>
  rw[phi_operands_wf_def, phi_well_formed_def]
QED

(* Step-level: PHI instruction with irrelevant prev_bb gives same result *)
Theorem step_phi_subst_irrelevant[local]:
  !fuel ctx inst s old new.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    s.vs_prev_bb <> SOME old /\ s.vs_prev_bb <> SOME new ==>
    step_inst fuel ctx (subst_label_inst old new inst) s =
    step_inst fuel ctx inst s
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `(subst_label_inst old new inst).inst_opcode <> INVOKE` by
    rw[subst_label_inst_def] >>
  rw[venomExecSemanticsTheory.step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[] >>
  simp[subst_label_inst_def] >>
  Cases_on `s.vs_prev_bb` >> gvs[] >>
  `phi_well_formed inst.inst_operands` by (
    qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def] >> strip_tac >>
    metis_tac[phi_operands_wf_implies_phi_well_formed_early]) >>
  simp[resolve_phi_subst_irrelevant]
QED

(* Block-level: running PHI-substituted block from irrelevant prev_bb state
   gives the same result as the original block.
   Proof: induction on remaining instruction count. At each step:
   - Non-PHI: instruction identical → same step_inst result
   - PHI: step_phi_subst_irrelevant → same step_inst result
   prev_bb invariant preserved by non-terminators (step_inst_preserves_prev_bb). *)
Theorem subst_phi_opcode_preserved[local]:
  !inst old new.
    (if inst.inst_opcode <> PHI then inst
     else subst_label_inst old new inst).inst_opcode = inst.inst_opcode
Proof
  rw[subst_label_inst_def]
QED

(* Helper: eval_one_phi on substituted PHI = eval_one_phi on original
   when prev_bb doesn't match old/new and operands are phi_well_formed. *)
Theorem eval_one_phi_subst_irrelevant[local]:
  !s inst old new.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    s.vs_prev_bb <> SOME old /\ s.vs_prev_bb <> SOME new ==>
    eval_one_phi s (subst_label_inst old new inst) = eval_one_phi s inst
Proof
  rpt strip_tac >>
  simp[eval_one_phi_def, subst_label_inst_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `s.vs_prev_bb` >> simp[] >>
  `phi_well_formed inst.inst_operands` by (
    qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def] >> strip_tac >>
    metis_tac[phi_operands_wf_implies_phi_well_formed_early]) >>
  `x <> old /\ x <> new` by gvs[] >>
  simp[resolve_phi_subst_irrelevant]
QED

(* Helper: eval_phis on mapped instruction list = eval_phis on original *)
Theorem eval_phis_subst_irrelevant[local]:
  !insts s old new.
    (!inst. MEM inst insts ==> inst_wf inst) /\
    s.vs_prev_bb <> SOME old /\ s.vs_prev_bb <> SOME new ==>
    eval_phis s
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old new inst) insts) =
    eval_phis s insts
Proof
  Induct_on `insts` >>
  simp[eval_phis_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[subst_label_inst_def, eval_phis_def] >>
  `inst_wf h` by (res_tac >> fs[]) >>
  `eval_one_phi s (subst_label_inst old new h) = eval_one_phi s h` by (
    irule eval_one_phi_subst_irrelevant >> simp[]) >>
  fs[subst_label_inst_def]
QED

(* Helper: phi_prefix_length preserved by the PHI-map *)
Theorem phi_prefix_length_subst_preserved[local]:
  !insts old new.
    phi_prefix_length
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old new inst) insts) =
    phi_prefix_length insts
Proof
  Induct >> simp[phi_prefix_length_def] >>
  rw[subst_label_inst_def, phi_prefix_length_def] >> gvs[]
QED

(* Helper: run_block_non_phis on PHI-substituted block = original.
   PHI step uses step_phi_subst_irrelevant (prev_bb irrelevant).
   Non-PHI instructions are identical. prev_bb invariant via
   step_inst_preserves_prev_bb. *)
Theorem run_block_non_phis_phi_subst_eq[local]:
  !n fuel ctx bb s old new.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    EVERY inst_wf bb.bb_instructions /\
    s.vs_prev_bb <> SOME old /\ s.vs_prev_bb <> SOME new ==>
    run_block_non_phis fuel ctx
      (bb with bb_instructions :=
        MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else subst_label_inst old new inst)
            bb.bb_instructions) s =
    run_block_non_phis fuel ctx bb s
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `bb' = bb with bb_instructions :=
    MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old new inst)
        bb.bb_instructions` >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    simp[Abbr `bb'`, listTheory.LENGTH_MAP] >>
  ONCE_REWRITE_TAC[run_block_non_phis_def] >>
  simp[get_instruction_def] >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[] >>
  qabbrev_tac `idx = s.vs_inst_idx` >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `EL idx bb'.bb_instructions =
    (if inst.inst_opcode <> PHI then inst
     else subst_label_inst old new inst)` by
    simp[Abbr `bb'`, Abbr `inst`, rich_listTheory.EL_MAP] >>
  `inst_wf inst` by
    (simp[Abbr `inst`] >> fs[listTheory.EVERY_EL]) >>
  (* Step equality: PHI uses step_phi_subst_irrelevant, non-PHI is identity *)
  `step_inst fuel ctx
    (if inst.inst_opcode <> PHI then inst
     else subst_label_inst old new inst) s =
   step_inst fuel ctx inst s` by (
    Cases_on `inst.inst_opcode = PHI` >> ASM_REWRITE_TAC[]
    >- (irule step_phi_subst_irrelevant >> simp[]) >>
    simp[]) >>
  ASM_REWRITE_TAC[] >>
  `is_terminator (if inst.inst_opcode <> PHI then inst
                  else subst_label_inst old new inst).inst_opcode =
   is_terminator inst.inst_opcode` by
    (Cases_on `inst.inst_opcode = PHI` >> simp[subst_label_inst_def]) >>
  ASM_REWRITE_TAC[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  (* Non-terminator OK: prev_bb preserved, recurse with IH *)
  `v.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[venomExecProofsTheory.step_inst_preserves_prev_bb] >>
  first_x_assum (qspec_then
    `LENGTH bb.bb_instructions - SUC idx` mp_tac) >>
  (impl_tac >- (
    qpat_x_assum `n = _` SUBST_ALL_TAC >> simp[Abbr `idx`])) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`,
    `v with vs_inst_idx := SUC idx`, `old`, `new`] mp_tac) >>
  simp[Abbr `bb'`]
QED

(* Block-level: running PHI-substituted block gives the same result as original
   when prev_bb doesn't match old/new.
   run_block = run_block_non_phis (s with idx:=0), delegates directly. *)
Theorem run_block_phi_subst_irrelevant[local]:
  !fuel ctx bb s old new.
    (!inst. MEM inst bb.bb_instructions ==> inst_wf inst) /\
    s.vs_prev_bb <> SOME old /\ s.vs_prev_bb <> SOME new ==>
    run_block fuel ctx
      (bb with bb_instructions :=
        MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else subst_label_inst old new inst)
            bb.bb_instructions) s =
    run_block fuel ctx bb s
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
  irule run_block_non_phis_phi_subst_eq >>
  simp[listTheory.EVERY_MEM]
QED

(* Exact block content after update_succ_phi_labels for cb ∈ succs.
   Key idea: each step of FOLDL replaces block h with phi-rewritten copy.
   If cb=h, the result is the phi-rewritten orig_bb (idempotent by phi_map_idem).
   If cb≠h, replace doesn't touch cb, and IH applies directly. *)
Theorem lookup_block_uspl_in_succs[local]:
  !old new bbs succs cb orig_bb.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    lookup_block cb bbs = SOME orig_bb /\
    MEM cb succs ==>
    lookup_block cb (update_succ_phi_labels old new bbs succs) =
      SOME (orig_bb with bb_instructions :=
        MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else subst_label_inst old new inst) orig_bb.bb_instructions)
Proof
  ntac 2 gen_tac >> Induct_on `succs`
  >- rw[]
  >> rpt gen_tac >> strip_tac >>
  PURE_REWRITE_TAC[update_succ_phi_labels_cons] >>
  Cases_on `lookup_block h bbs`
  >- (
    ASM_REWRITE_TAC[optionTheory.option_case_def] >>
    `cb <> h` by (strip_tac >> gvs[]) >>
    qpat_x_assum `!bbs cb orig_bb. _ ==> _` irule >>
    gvs[listTheory.MEM])
  >> ASM_REWRITE_TAC[optionTheory.option_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  `x.bb_label = h` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  (* let ob' = phi-rewritten x, bbs' = replace h with ob' *)
  qabbrev_tac `ob' = x with bb_instructions :=
    MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old new inst)
        x.bb_instructions` >>
  `ob'.bb_label = h` by (qunabbrev_tac `ob'` >> rw[]) >>
  qabbrev_tac `bbs' = replace_block h ob' bbs` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs')` by (
    qunabbrev_tac `bbs'` >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
    ASM_REWRITE_TAC[]) >>
  qpat_x_assum `MEM cb (h::succs)` mp_tac >>
  (* Shared tactic: when cb = h, derive x = orig_bb, establish lookup in bbs',
     apply IH with phi_map_idem *)
  let val cb_eq_h_IH_idem_tac =
    `x = orig_bb` by
      (qpat_x_assum `lookup_block h bbs = SOME x` mp_tac >>
       qpat_x_assum `lookup_block h bbs = SOME orig_bb` mp_tac >>
       rw[]) >>
    qpat_x_assum `x = orig_bb` SUBST_ALL_TAC >>
    `lookup_block h bbs' = SOME ob'` by (
      qunabbrev_tac `bbs'` >>
      match_mp_tac cfgTransformPropsTheory.lookup_block_replace_eq >>
      ASM_REWRITE_TAC[] >> metis_tac[]) >>
    qpat_x_assum `!bbs cb orig_bb. _ ==> _`
      (qspecl_then [`bbs'`, `h`, `ob'`] mp_tac) >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    qunabbrev_tac `bbs'` >> qunabbrev_tac `ob'` >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    simp[phi_map_idem]
  in
  PURE_REWRITE_TAC[listTheory.MEM] >> strip_tac >| [
    (* Case cb = h *)
    qpat_x_assum `cb = h` SUBST_ALL_TAC >>
    Cases_on `MEM h succs` >| [
      cb_eq_h_IH_idem_tac,
      (* h ∉ succs: uspl doesn't touch h, lookup = lookup in bbs' = SOME ob' *)
      `x = orig_bb` by
        (qpat_x_assum `lookup_block h bbs = SOME x` mp_tac >>
         qpat_x_assum `lookup_block h bbs = SOME orig_bb` mp_tac >>
         rw[]) >>
      qpat_x_assum `x = orig_bb` SUBST_ALL_TAC >>
      `lookup_block h bbs' = SOME ob'` by (
        qunabbrev_tac `bbs'` >>
        match_mp_tac cfgTransformPropsTheory.lookup_block_replace_eq >>
        ASM_REWRITE_TAC[] >> metis_tac[]) >>
      qpat_x_assum `~MEM h succs`
        (fn th => REWRITE_TAC[MATCH_MP lookup_block_update_succ_phi_not_in_succs th]) >>
      ASM_REWRITE_TAC[] >>
      qunabbrev_tac `ob'` >> REWRITE_TAC[]
    ],
    (* Case MEM cb succs *)
    Cases_on `cb = h` >| [
      qpat_x_assum `cb = h` SUBST_ALL_TAC >> cb_eq_h_IH_idem_tac,
      (* cb ≠ h: replace doesn't touch cb, IH directly *)
      `lookup_block cb bbs' = SOME orig_bb` by (
        qunabbrev_tac `bbs'` >>
        `cb <> h` by ASM_REWRITE_TAC[] >>
        rw[cfgTransformProofsTheory.lookup_block_replace_neq]) >>
      qpat_x_assum `!bbs cb orig_bb. _ ==> _` irule >>
      ASM_REWRITE_TAC[]
    ]
  ]
  end
QED

(* When prev_bb is neither old_lbl nor new_lbl, executing a block from
   update_succ_phi_labels gives the same result as executing the original *)
Theorem run_block_uspl_irrelevant[local]:
  !fuel ctx old_lbl new_lbl bbs succs cb orig_bb merged_bb s.
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
    lookup_block cb bbs = SOME orig_bb /\
    lookup_block cb (update_succ_phi_labels old_lbl new_lbl bbs succs) =
      SOME merged_bb /\
    EVERY inst_wf orig_bb.bb_instructions /\
    orig_bb.bb_instructions <> [] /\
    s.vs_prev_bb <> SOME old_lbl /\ s.vs_prev_bb <> SOME new_lbl /\
    s.vs_inst_idx < LENGTH orig_bb.bb_instructions /\ ~s.vs_halted ==>
    run_block fuel ctx merged_bb s = run_block fuel ctx orig_bb s
Proof
  rpt strip_tac >>
  Cases_on `MEM cb succs`
  >- (
    (* cb in succs: merged_bb is PHI-rewritten orig_bb *)
    `lookup_block cb (update_succ_phi_labels old_lbl new_lbl bbs succs) =
       SOME (orig_bb with bb_instructions :=
         MAP (\inst. if inst.inst_opcode <> PHI then inst
                     else subst_label_inst old_lbl new_lbl inst)
           orig_bb.bb_instructions)` by (
      irule lookup_block_uspl_in_succs >> ASM_REWRITE_TAC[]) >>
    `merged_bb = orig_bb with bb_instructions :=
       MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old_lbl new_lbl inst)
         orig_bb.bb_instructions` by metis_tac[optionTheory.SOME_11] >>
    pop_assum SUBST_ALL_TAC >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `orig_bb`, `s`, `old_lbl`, `new_lbl`]
      run_block_phi_subst_irrelevant) >>
    simp[venomInstTheory.basic_block_component_equality] >>
    disch_then match_mp_tac >>
    fs[listTheory.EVERY_MEM]
  )
  >>
  (* cb not in succs: merged_bb = orig_bb *)
  `lookup_block cb (update_succ_phi_labels old_lbl new_lbl bbs succs) =
   lookup_block cb bbs` by metis_tac[lookup_block_update_succ_phi_not_in_succs] >>
  `merged_bb = orig_bb` by metis_tac[optionTheory.SOME_11] >>
  ASM_REWRITE_TAC[]
QED

(* ================================================================
   Helper: lookup of cb in func' when cb ≠ lbl, cb ≠ next_lbl.
   For cb ∉ msuccs: gives same block as func.
   For any cb: gives SOME iff func gives SOME.
   ================================================================ *)

Theorem lookup_block_merge_other[local]:
  !func lbl next_lbl bb next_bb cb.
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    wf_function func /\ cb <> lbl /\ cb <> next_lbl ==>
    let bbs2 = replace_block lbl (merge_blocks bb next_bb)
                 (remove_block next_lbl func.fn_blocks) in
    let func' = func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl bbs2
        (bb_succs (merge_blocks bb next_bb)) in
    lookup_block cb bbs2 = lookup_block cb func.fn_blocks /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs2) /\
    ((?orig_bb. lookup_block cb func.fn_blocks = SOME orig_bb) <=>
     (?mod_bb. lookup_block cb func'.fn_blocks = SOME mod_bb)) /\
    (!orig_bb. ~MEM cb (bb_succs (merge_blocks bb next_bb)) /\
      lookup_block cb func.fn_blocks = SOME orig_bb ==>
      lookup_block cb func'.fn_blocks = SOME orig_bb)
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
  `(merge_blocks bb next_bb).bb_label = lbl` by (
    rw[simplifyCfgDefsTheory.merge_blocks_def] >>
    imp_res_tac venomExecProofsTheory.lookup_block_label) >>
  (* lookup through remove+replace *)
  `lookup_block cb (replace_block lbl (merge_blocks bb next_bb)
     (remove_block next_lbl func.fn_blocks)) =
   lookup_block cb func.fn_blocks` by
    rw[cfgTransformProofsTheory.lookup_block_replace_neq,
       cfgTransformProofsTheory.lookup_block_remove_neq] >>
  (* ALL_DISTINCT *)
  `ALL_DISTINCT (MAP (\b. b.bb_label) (replace_block lbl (merge_blocks bb next_bb)
     (remove_block next_lbl func.fn_blocks)))` by (
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >> rw[] >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >> rw[]) >>
  rw[]
  >- metis_tac[lookup_block_update_succ_phi_labels_exists]
  >> rw[lookup_block_update_succ_phi_not_in_succs]
QED

(* ================================================================
   lookup_block_merge_other_bb: for cb ≠ lbl, cb ≠ next_lbl,
   characterize the exact block lookup in func' (merged function).
   Either identical to original (cb ∉ msuccs) or phi-subst'd.
   ================================================================ *)
Theorem lookup_block_merge_other_bb[local]:
  !func lbl next_lbl bb next_bb cb cur_bb.
    wf_function func /\ fn_inst_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    lookup_block cb func.fn_blocks = SOME cur_bb /\
    cb <> lbl /\ cb <> next_lbl ==>
    let msuccs = bb_succs (merge_blocks bb next_bb) in
    let bbs' = replace_block lbl (merge_blocks bb next_bb)
                 (remove_block next_lbl func.fn_blocks) in
    (MEM cb msuccs ==>
      lookup_block cb
        (update_succ_phi_labels next_lbl lbl bbs' msuccs) =
        SOME (cur_bb with bb_instructions :=
          MAP (\inst. if inst.inst_opcode <> PHI then inst
                      else subst_label_inst next_lbl lbl inst)
              cur_bb.bb_instructions)) /\
    (~MEM cb msuccs ==>
      lookup_block cb
        (update_succ_phi_labels next_lbl lbl bbs' msuccs) =
        SOME cur_bb)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
  `(merge_blocks bb next_bb).bb_label = lbl` by (
    rw[simplifyCfgDefsTheory.merge_blocks_def] >>
    imp_res_tac venomExecProofsTheory.lookup_block_label) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label)
     (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks)))` by (
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >> rw[] >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >> rw[]) >>
  `lookup_block cb (replace_block lbl (merge_blocks bb next_bb)
     (remove_block next_lbl func.fn_blocks)) = SOME cur_bb` by
    rw[cfgTransformProofsTheory.lookup_block_replace_neq,
       cfgTransformProofsTheory.lookup_block_remove_neq] >>
  conj_tac
  >- (strip_tac >>
      irule (REWRITE_RULE[PULL_EXISTS] lookup_block_uspl_in_succs) >> rw[])
  >> (strip_tac >> rw[lookup_block_update_succ_phi_not_in_succs])
QED

(* ================================================================
   Helper: at block cb ≠ lbl, ≠ next_lbl in func', if prev_bb is
   irrelevant (∉ {SOME next_lbl, SOME lbl}), running the block in
   func' gives the same result as in func. Abstracts away the
   MEM/~MEM case split + phi_subst_irrelevant pattern.
   ================================================================ *)
Theorem run_block_merge_other_equiv[local]:
  !func lbl next_lbl bb next_bb cb cur_bb fuel ctx s.
    wf_function func /\ fn_inst_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    lookup_block cb func.fn_blocks = SOME cur_bb /\
    cb <> lbl /\ cb <> next_lbl /\
    s.vs_prev_bb <> SOME next_lbl /\ s.vs_prev_bb <> SOME lbl /\
    s.vs_inst_idx = 0 ==>
    let msuccs = bb_succs (merge_blocks bb next_bb) in
    let bbs' = replace_block lbl (merge_blocks bb next_bb)
                 (remove_block next_lbl func.fn_blocks) in
    ?cur_bb'.
      lookup_block cb
        (update_succ_phi_labels next_lbl lbl bbs' msuccs) =
        SOME cur_bb' /\
      run_block fuel ctx cur_bb' s = run_block fuel ctx cur_bb s
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`,
                    `cb`, `cur_bb`]
    lookup_block_merge_other_bb) >>
  simp[] >> strip_tac >>
  Cases_on `MEM cb (bb_succs (merge_blocks bb next_bb))` >| [
    (* MEM: phi-subst'd block *)
    res_tac >> qexists_tac `cur_bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst next_lbl lbl inst)
          cur_bb.bb_instructions` >>
    simp[] >>
    drule_all lookup_block_wf_facts >> strip_tac >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `cur_bb`, `s`,
                      `next_lbl`, `lbl`]
      run_block_phi_subst_irrelevant) >>
    (impl_tac >- fs[listTheory.EVERY_MEM]) >> simp[],
    (* ~MEM: identical block *)
    res_tac >> qexists_tac `cur_bb` >> simp[]
  ]
QED

(* ================================================================
   Induction invariant for merge correctness.
   Two disjuncts:
   1. States equal, prev_bb not involved in merge
   2. States differ in prev_bb as (next_lbl, lbl)
      — at successor blocks, PHI substitution compensates
   ================================================================ *)
Definition merge_R_def:
  merge_R lbl next_lbl s1 s2 <=>
    (s1 = s2 /\ s1.vs_prev_bb <> SOME next_lbl /\ s1.vs_prev_bb <> SOME lbl) \/
    (prev_bb_equiv s1 s2 /\
     s1.vs_prev_bb = SOME next_lbl /\ s2.vs_prev_bb = SOME lbl)
End

(* ================================================================
   Helper: after run_block OK at block cb (≠ lbl, ≠ next_lbl),
   the post-state satisfies merge_R v v, idx=0, and cb' ≠ next_lbl.
   Captures the common IH-discharge pattern used 3+ times.
   ================================================================ *)
Theorem merge_ok_post_state[local]:
  !func lbl next_lbl bb next_bb cur_bb n ctx s v.
    wf_function func /\ fn_inst_wf func /\
    can_merge_blocks func bb next_bb /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME cur_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_current_bb <> lbl /\
    s.vs_current_bb <> next_lbl /\
    run_block n ctx cur_bb s = OK v ==>
    merge_R lbl next_lbl v v /\
    v.vs_inst_idx = 0 /\
    v.vs_current_bb <> next_lbl
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lookup_block_wf_facts >> strip_tac >>
  `bb.bb_label = lbl` by
    metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `next_bb.bb_label = next_lbl` by
    metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `MEM bb func.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `v.vs_prev_bb = SOME s.vs_current_bb` by (
    mp_tac (Q.SPECL [`n`, `ctx`, `cur_bb`, `s`, `v`]
      venomExecPropsTheory.run_block_ok_prev_bb) >> simp[]) >>
  `v.vs_inst_idx = 0` by (
    mp_tac (Q.SPECL [`n`, `ctx`, `cur_bb`, `s`, `v`]
      venomExecPropsTheory.run_block_OK_inst_idx_0) >> simp[]) >>
  `MEM v.vs_current_bb (bb_succs cur_bb)` by (
    mp_tac (Q.SPECL [`n`, `ctx`, `cur_bb`, `s`, `v`]
      venomExecPropsTheory.run_block_current_bb_in_succs) >> simp[]) >>
  conj_tac
  >- (rw[merge_R_def] >> simp[])
  >> conj_tac >- rw[]
  >> (* v.vs_current_bb ≠ next_lbl: unique predecessor *)
  CCONTR_TAC >> fs[] >>
  qpat_x_assum `can_merge_blocks _ _ _`
    (STRIP_ASSUME_TAC o PURE_REWRITE_RULE[can_merge_blocks_def]) >>
  `cur_bb = bb` suffices_by (strip_tac >> gvs[]) >>
  irule num_preds_1_unique_pred >>
  qexists_tac `func` >> qexists_tac `next_lbl` >>
  gvs[listTheory.MEM]
QED

(* ================================================================
   lookup_block_merge_func_none: if a block doesn't exist in func
   and cb ≠ lbl, cb ≠ next_lbl, it doesn't exist in func' either.
   ================================================================ *)
Theorem lookup_block_merge_func_none[local]:
  !func lbl next_lbl bb next_bb cb msuccs.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    lookup_block cb func.fn_blocks = NONE /\
    cb <> lbl /\ cb <> next_lbl ==>
    lookup_block cb
      (update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks)) msuccs) = NONE
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
  `bb.bb_label = lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `(merge_blocks bb next_bb).bb_label = lbl` by simp[simplifyCfgDefsTheory.merge_blocks_def] >>
  `lookup_block cb (replace_block lbl (merge_blocks bb next_bb)
     (remove_block next_lbl func.fn_blocks)) = NONE` by
    rw[cfgTransformProofsTheory.lookup_block_replace_neq,
       cfgTransformProofsTheory.lookup_block_remove_neq] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label)
     (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks)))` by
    metis_tac[cfgTransformProofsTheory.ALL_DISTINCT_replace_block,
              cfgTransformProofsTheory.ALL_DISTINCT_remove_block] >>
  mp_tac (Q.SPECL [`next_lbl`, `lbl`,
    `replace_block lbl (merge_blocks bb next_bb)
       (remove_block next_lbl func.fn_blocks)`,
    `msuccs`, `cb`] lookup_block_update_succ_phi_labels_exists) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  Cases_on `lookup_block cb
    (update_succ_phi_labels next_lbl lbl
      (replace_block lbl (merge_blocks bb next_bb)
         (remove_block next_lbl func.fn_blocks)) msuccs)` >>
  fs[]
QED

(* state_equiv {} implies state equality *)
Theorem state_equiv_empty_eq[local]:
  !s1 s2. state_equiv {} s1 s2 ==> s1 = s2
Proof
  rw[state_equiv_def, execution_equiv_def] >>
  rw[venom_state_component_equality] >>
  rw[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM] >>
  fs[lookup_var_def]
QED

(* ================================================================
   merge_rf_step_eq: factor out run_blocks unfolding for the case
   where both sides execute the same block (possibly different states).
   REVERSED fuel direction: func (original) gets existential fuel >= n,
   func' (merged) gets fixed fuel SUC n.
   Accepts result_equiv {} between run_block results (generalizes
   literal equality — use result_equiv_empty_refl for equal results).
   ================================================================ *)
Theorem merge_rf_step_eq[local]:
  !func func' cb cur_bb cur_bb' n ctx s1 s2.
    lookup_block cb func.fn_blocks = SOME cur_bb /\
    lookup_block cb func'.fn_blocks = SOME cur_bb' /\
    s1.vs_current_bb = cb /\ s2.vs_current_bb = cb /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    result_equiv {} (run_block n ctx cur_bb s1)
                    (run_block n ctx cur_bb' s2) /\
    (!v. run_block n ctx cur_bb s1 = OK v /\ ~v.vs_halted ==>
      ?fuel. n <= fuel /\
             result_equiv {} (run_blocks fuel ctx func v)
                             (run_blocks n ctx func' v)) ==>
    ?fuel. SUC n <= fuel /\
           result_equiv {} (run_blocks fuel ctx func s1)
                           (run_blocks (SUC n) ctx func' s2)
Proof
  rpt strip_tac >>
  Cases_on `run_block n ctx cur_bb s1` >| [
    (* OK v1: derive OK v2 on func' side, v1 = v2 *)
    qpat_x_assum `result_equiv _ (OK _) _` mp_tac >>
    Cases_on `run_block n ctx cur_bb' s2` >>
    REWRITE_TAC[stateEquivTheory.result_equiv_def] >>
    strip_tac >>
    qpat_x_assum `state_equiv _ _ _`
      (ASSUME_TAC o MATCH_MP state_equiv_empty_eq) >>
    rpt BasicProvers.VAR_EQ_TAC >>
    (* Both sides give OK v. Simplify IH callback: OK v = OK v' => v = v' *)
    qpat_x_assum `!v'. OK v = OK v' /\ _ ==> _`
      (ASSUME_TAC o SIMP_RULE std_ss [exec_result_11]) >>
    (* Cases on halted *)
    Cases_on `v.vs_halted` >| [
      (* halted: both sides give Halt v *)
      qexists_tac `SUC n` >>
      REWRITE_TAC[arithmeticTheory.LESS_EQ_REFL] >>
      CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
      CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
      ASM_REWRITE_TAC[optionTheory.option_case_def] >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      ASM_REWRITE_TAC[exec_result_case_def] >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      ASM_REWRITE_TAC[result_equiv_empty_refl],
      (* ok, not halted: IH callback gives fuel >= n with result_equiv *)
      qpat_x_assum `~v.vs_halted ==> _` mp_tac >>
      ASM_REWRITE_TAC[] >> strip_tac >>
      qexists_tac `SUC fuel` >>
      conj_tac >- simp[] >>
      CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
      CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
      ASM_REWRITE_TAC[optionTheory.option_case_def] >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      `run_block fuel ctx cur_bb s1 = OK v` by (
        mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
        disch_then (qspecl_then [`n`, `fuel`, `ctx`, `cur_bb`, `s1`, `OK v`] mp_tac) >>
        ASM_REWRITE_TAC[exec_result_distinct]) >>
      ASM_REWRITE_TAC[exec_result_case_def] >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      ASM_REWRITE_TAC[]
    ],
    (* 4 non-OK cases: extract matching constructor from result_equiv *)
    ALL_TAC, ALL_TAC, ALL_TAC, ALL_TAC
  ] >>
  (* All 4 non-OK cases: same tactic *)
  qpat_x_assum `result_equiv _ _ _` mp_tac >>
  Cases_on `run_block n ctx cur_bb' s2` >>
  REWRITE_TAC[stateEquivTheory.result_equiv_def] >>
  rpt strip_tac >>
  qexists_tac `SUC n` >>
  REWRITE_TAC[arithmeticTheory.LESS_EQ_REFL] >>
  CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
  CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
  ASM_REWRITE_TAC[optionTheory.option_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  ASM_REWRITE_TAC[exec_result_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  REWRITE_TAC[stateEquivTheory.result_equiv_def] >>
  TRY (first_assum ACCEPT_TAC)
QED

(* ================================================================
   merge_other_block_step: combines merge_rf_step_eq + merge_ok_post_state
   + IH discharge. For the "other block" case (cb ≠ lbl, cb ≠ next_lbl),
   given run_block equivalence and the IH, produces the fuel witness.
   Reusable across D1, D2a, D2b.
   ================================================================ *)
Theorem merge_other_block_step[local]:
  !func func' lbl next_lbl bb next_bb cur_bb cur_bb' n ctx s1 s2.
    wf_function func /\ fn_inst_wf func /\
    can_merge_blocks func bb next_bb /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    lookup_block s1.vs_current_bb func.fn_blocks = SOME cur_bb /\
    lookup_block s1.vs_current_bb func'.fn_blocks = SOME cur_bb' /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    s1.vs_current_bb <> lbl /\ s1.vs_current_bb <> next_lbl /\
    result_equiv {} (run_block n ctx cur_bb s1)
                    (run_block n ctx cur_bb' s2) /\
    (!m. m < SUC n ==>
      !ctx' s1' s2'. merge_R lbl next_lbl s1' s2' /\
        s1'.vs_current_bb = s2'.vs_current_bb /\
        s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
        s1'.vs_current_bb <> next_lbl /\
        ~s1'.vs_halted ==>
        ?fuel'. m <= fuel' /\
          result_equiv {} (run_blocks fuel' ctx' func s1')
                          (run_blocks m ctx' func' s2'))
    ==>
    ?fuel'. SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s1)
                      (run_blocks (SUC n) ctx func' s2)
Proof
  rpt strip_tac >>
  irule merge_rf_step_eq >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`s1.vs_current_bb`, `cur_bb`, `cur_bb'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
  TRY (ONCE_REWRITE_TAC[EQ_SYM_EQ] >> first_assum ACCEPT_TAC) >>
  (* IH callback: v post-state from run_block OK not-halted *)
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`,
                    `cur_bb`, `n`, `ctx`, `s1`, `v`]
    merge_ok_post_state) >>
  (impl_tac >- (
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >>
  REWRITE_TAC[prim_recTheory.LESS_SUC_REFL] >>
  disch_tac >> pop_assum (qspecl_then [`ctx`, `v`, `v`] mp_tac) >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
    imp_res_tac venomExecPropsTheory.run_block_OK_not_halted)) >>
  strip_tac >>
  qexists_tac `fuel'` >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* Helper: prev_bb_equiv + same prev_bb => equal *)
Theorem prev_bb_equiv_same_eq[local]:
  !s1 s2. prev_bb_equiv s1 s2 /\ s1.vs_prev_bb = s2.vs_prev_bb ==> s1 = s2
Proof
  rw[prev_bb_equiv_def] >>
  qpat_x_assum `_ = s2` (SUBST_ALL_TAC o GSYM) >>
  simp[venom_state_component_equality]
QED

(* Bridge: prev_bb_equiv implies execution_equiv {} *)
Theorem prev_bb_equiv_implies_execution_equiv[local]:
  !s1 s2. prev_bb_equiv s1 s2 ==> execution_equiv {} s1 s2
Proof
  rw[prev_bb_equiv_def, execution_equiv_def] >>
  qpat_x_assum `_ = s2` (SUBST_ALL_TAC o GSYM) >>
  simp[lookup_var_def]
QED

(* result_equiv {} for OK implies state equality *)
Theorem result_equiv_empty_OK_eq[local]:
  !v1 v2. result_equiv {} (OK v1) (OK v2) ==> v1 = v2
Proof
  rw[result_equiv_def] >> irule state_equiv_empty_eq >> first_assum ACCEPT_TAC
QED

(* result_equiv {} is symmetric *)
Theorem result_equiv_empty_sym[local]:
  !r1 r2. result_equiv {} r1 r2 ==> result_equiv {} r2 r1
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  REWRITE_TAC[stateEquivTheory.result_equiv_def] >>
  rpt strip_tac >>
  TRY (irule stateEquivPropsTheory.state_equiv_sym >> first_assum ACCEPT_TAC) >>
  fs[stateEquivTheory.execution_equiv_def, lookup_var_def]
QED

(* result_prev_bb_equiv on run_block with wf blocks and same current_bb
   gives result_equiv {} (bridging prev_bb_equiv to result_equiv) *)
Theorem result_prev_bb_equiv_wf_to_result_equiv[local]:
  !n ctx bb1 bb2 s1 s2.
    EVERY inst_wf bb1.bb_instructions /\ bb1.bb_instructions <> [] /\
    (!i. i < LENGTH bb1.bb_instructions - 1 ==>
         ~is_terminator (EL i bb1.bb_instructions).inst_opcode) /\
    EVERY inst_wf bb2.bb_instructions /\ bb2.bb_instructions <> [] /\
    (!i. i < LENGTH bb2.bb_instructions - 1 ==>
         ~is_terminator (EL i bb2.bb_instructions).inst_opcode) /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    result_prev_bb_equiv
      (run_block n ctx bb1 s1) (run_block n ctx bb2 s2) ==>
    result_equiv {}
      (run_block n ctx bb1 s1) (run_block n ctx bb2 s2)
Proof
  rpt strip_tac >>
  Cases_on `run_block n ctx bb1 s1` >>
  Cases_on `run_block n ctx bb2 s2` >>
  fs[simplifyCfgPrevBBTheory.result_prev_bb_equiv_def, result_equiv_def]
  >- (
    (* OK/OK: prev_bb_equiv v v'. Both have prev_bb = SOME current_bb → equal *)
    `v.vs_prev_bb = SOME s1.vs_current_bb` by (
      mp_tac venomExecPropsTheory.run_block_ok_prev_bb >>
      disch_then (qspecl_then [`n`, `ctx`, `bb1`, `s1`, `v`] mp_tac) >>
      ASM_REWRITE_TAC[]) >>
    `v'.vs_prev_bb = SOME s2.vs_current_bb` by (
      mp_tac venomExecPropsTheory.run_block_ok_prev_bb >>
      disch_then (qspecl_then [`n`, `ctx`, `bb2`, `s2`, `v'`] mp_tac) >>
      ASM_REWRITE_TAC[]) >>
    `v = v'` by (
      irule prev_bb_equiv_same_eq >> ASM_REWRITE_TAC[]) >>
    rw[stateEquivPropsTheory.state_equiv_refl])
  >>
  (* non-OK: prev_bb_equiv → execution_equiv *)
  TRY (irule prev_bb_equiv_implies_execution_equiv >> first_assum ACCEPT_TAC)
QED

(* merge_other_block_step_prev_bb: variant of merge_other_block_step
   for the D2b case where run_blocks give result_prev_bb_equiv (not equality).
   Uses result_prev_bb_equiv_wf_to_result_equiv to bridge to result_equiv {},
   then result_equiv_empty_OK_eq for the OK case to reduce to literal equality. *)
Theorem merge_other_block_step_prev_bb[local]:
  !func func' lbl next_lbl bb next_bb cur_bb cur_bb' n ctx s1 s2.
    wf_function func /\ fn_inst_wf func /\
    can_merge_blocks func bb next_bb /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    lookup_block s1.vs_current_bb func.fn_blocks = SOME cur_bb /\
    lookup_block s1.vs_current_bb func'.fn_blocks = SOME cur_bb' /\
    EVERY inst_wf cur_bb'.bb_instructions /\
    cur_bb'.bb_instructions <> [] /\
    (!i. i < LENGTH cur_bb'.bb_instructions - 1 ==>
         ~is_terminator (EL i cur_bb'.bb_instructions).inst_opcode) /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    s1.vs_current_bb <> lbl /\ s1.vs_current_bb <> next_lbl /\
    result_prev_bb_equiv
      (run_block n ctx cur_bb s1) (run_block n ctx cur_bb' s2) /\
    (!m. m < SUC n ==>
      !ctx' s1' s2'. merge_R lbl next_lbl s1' s2' /\
        s1'.vs_current_bb = s2'.vs_current_bb /\
        s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
        s1'.vs_current_bb <> next_lbl /\
        ~s1'.vs_halted ==>
        ?fuel'. m <= fuel' /\
          result_equiv {} (run_blocks fuel' ctx' func s1')
                          (run_blocks m ctx' func' s2'))
    ==>
    ?fuel'. SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s1)
                      (run_blocks (SUC n) ctx func' s2)
Proof
  rpt strip_tac >>
  (* Hide IH immediately to protect from fs/simp *)
  qpat_x_assum `!m. m < SUC n ==> _` (markerLib.hide_tac "IH") >>
  drule_all lookup_block_wf_facts >> strip_tac >>
  (* Bridge: result_prev_bb_equiv → result_equiv {} *)
  mp_tac (Q.SPECL [`n`, `ctx`, `cur_bb`, `cur_bb'`, `s1`, `s2`]
    result_prev_bb_equiv_wf_to_result_equiv) >>
  (impl_tac >- fs[]) >>
  strip_tac >>
  (* Case split on func side run_block *)
  Cases_on `run_block n ctx cur_bb s1`
  >- (
    (* OK v1: derive rb2 = OK v2 and v1 = v2 *)
    qpat_x_assum `result_equiv _ (OK _) _` mp_tac >>
    Cases_on `run_block n ctx cur_bb' s2` >>
    REWRITE_TAC[stateEquivTheory.result_equiv_def] >>
    strip_tac >>
    (* Targeted: state_equiv {} v v' ==> v = v' *)
    qpat_x_assum `state_equiv _ _ _` (ASSUME_TAC o MATCH_MP state_equiv_empty_eq) >>
    rpt BasicProvers.VAR_EQ_TAC >>
    (* Now both run_blocks give OK v, literal equality holds *)
    markerLib.unhide_x_assum "IH" ASSUME_TAC >>
    mp_tac (Q.SPECL [`func`, `func'`, `lbl`, `next_lbl`, `bb`, `next_bb`,
                      `cur_bb`, `cur_bb'`, `n`, `ctx`, `s1`, `s2`]
      merge_other_block_step) >>
    (impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY REFL_TAC >>
      TRY (ASM_REWRITE_TAC[simplifyCfgCollapseBaseTheory.result_equiv_empty_refl]) >>
      ONCE_REWRITE_TAC[EQ_SYM_EQ] >> first_assum ACCEPT_TAC)) >>
    REWRITE_TAC[])
  >>
  (* non-OK: both sides give matching non-OK, rf just wraps them *)
  qexists_tac `SUC n` >>
  REWRITE_TAC[arithmeticTheory.LESS_EQ_REFL] >>
  CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
  CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
  qpat_x_assum `s1.vs_current_bb = s2.vs_current_bb` (fn th =>
    REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
  ASM_REWRITE_TAC[optionTheory.option_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  ASM_REWRITE_TAC[exec_result_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  (* func' side: extract non-OK form from result_equiv *)
  qpat_x_assum `result_equiv _ _ _` mp_tac >>
  Cases_on `run_block n ctx cur_bb' s2` >>
  REWRITE_TAC[stateEquivTheory.result_equiv_def] >>
  rpt strip_tac >>
  ASM_REWRITE_TAC[exec_result_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  REWRITE_TAC[stateEquivTheory.result_equiv_def] >>
  TRY (first_assum ACCEPT_TAC)
QED

(* ================================================================
   merge_step_equiv_strong: the main inductive theorem
   REVERSED fuel direction: universally quantify over func' fuel,
   existentially provide func fuel >= func' fuel.
   func' (merged) is more fuel-efficient.
   ================================================================ *)
Theorem merge_step_equiv_strong[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_lbl ==>
    let func' = func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)) in
    !fuel ctx s1 s2.
      merge_R lbl next_lbl s1 s2 /\
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
      s1.vs_current_bb <> next_lbl /\
      ~s1.vs_halted ==>
    ?fuel'. fuel <= fuel' /\
      result_equiv {}
        (run_blocks fuel' ctx func s1)
        (run_blocks fuel ctx func' s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac `func' = func with fn_blocks :=
    update_succ_phi_labels next_lbl lbl
      (replace_block lbl (merge_blocks bb next_bb)
         (remove_block next_lbl func.fn_blocks))
      (bb_succs (merge_blocks bb next_bb))` >>
  qabbrev_tac `msuccs = bb_succs (merge_blocks bb next_bb)` >>
  (* Derive func'.fn_blocks before induction — avoids unabbrev with IH *)
  `func'.fn_blocks = update_succ_phi_labels next_lbl lbl
     (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks)) msuccs` by (
    qunabbrev_tac `func'` >> simp[]) >>
  completeInduct_on `fuel` >>
  rpt gen_tac >> strip_tac >>
  Cases_on `fuel`
  >- (qexists_tac `0` >>
      REWRITE_TAC[arithmeticTheory.LESS_EQ_REFL] >>
      CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
      CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
      REWRITE_TAC[stateEquivTheory.result_equiv_def]) >>
  rename1 `SUC n` >>
  Cases_on `lookup_block s1.vs_current_bb func.fn_blocks`
  >- (
      (* lookup=NONE in func ⇒ NONE in func' *)
      `s1.vs_current_bb <> lbl` by (CCONTR_TAC >> gvs[]) >>
      `lookup_block s1.vs_current_bb func'.fn_blocks = NONE` by (
        qpat_x_assum `func'.fn_blocks = _` (fn th => REWRITE_TAC[th]) >>
        mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`,
                          `s1.vs_current_bb`, `msuccs`] lookup_block_merge_func_none) >>
        ASM_REWRITE_TAC[]) >>
      qexists_tac `SUC n` >>
      REWRITE_TAC[arithmeticTheory.LESS_EQ_REFL] >>
      CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
      CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
      qpat_x_assum `s1.vs_current_bb = s2.vs_current_bb` (SUBST_ALL_TAC o GSYM) >>
      ASM_REWRITE_TAC[stateEquivTheory.result_equiv_def,
                       optionTheory.option_case_def]) >>
  rename1 `_ = SOME cur_bb` >>
  Cases_on `s1.vs_current_bb = lbl`
  >- suspend "at_lbl"
  >> suspend "other_block"
QED

(* Helper: resolve_phi returns NONE when the label is not in operands *)
Theorem resolve_phi_none_no_label[local]:
  !p ops. ~MEM (Label p) ops ==> resolve_phi p ops = NONE
Proof
  recInduct resolve_phi_ind >>
  rw[resolve_phi_def, listTheory.MEM]
QED

(* Helper: PHI step with both prev_bb values absent from operands
   gives result_prev_bb_equiv (both Error) *)
Theorem step_phi_missing_labels_equiv[local]:
  !fuel ctx inst s1 s2 p1 p2.
    inst.inst_opcode = PHI /\
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME p1 /\ s2.vs_prev_bb = SOME p2 /\
    ~MEM (Label p1) inst.inst_operands /\
    ~MEM (Label p2) inst.inst_operands ==>
    result_prev_bb_equiv (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (gvs[] >> EVAL_TAC) >>
  rw[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[] >>
  `resolve_phi p1 inst.inst_operands = NONE` by
    (irule resolve_phi_none_no_label >> ASM_REWRITE_TAC[]) >>
  `resolve_phi p2 inst.inst_operands = NONE` by
    (irule resolve_phi_none_no_label >> ASM_REWRITE_TAC[]) >>
  gvs[] >>
  Cases_on `inst.inst_outputs` >> simp[result_prev_bb_equiv_def] >>
  Cases_on `t` >> simp[result_prev_bb_equiv_def]
QED

(* Helper: subst_label_op preserves get_label *)
Theorem get_label_subst_label_op[local]:
  !old new op. IS_SOME (get_label op) ==>
    IS_SOME (get_label (subst_label_op old new op))
Proof
  Cases_on `op` >> rw[subst_label_op_def, get_label_def]
QED

(* Helper: inst_wf preserved by subst_label_inst *)
Theorem inst_wf_subst_label_inst[local]:
  !old new inst. inst_wf inst ==> inst_wf (subst_label_inst old new inst)
Proof
  rw[subst_label_inst_def, inst_wf_def] >>
  Cases_on `inst.inst_opcode` >>
  fs[inst_wf_def, listTheory.LENGTH_MAP, subst_label_op_def] >> rw[] >>
  TRY (simp[subst_label_op_def] >> NO_TAC) >>
  TRY (REWRITE_TAC[listTheory.EVERY_MAP] >>
       irule listTheory.EVERY_MONOTONIC >>
       qexists_tac `\op. IS_SOME (get_label op)` >>
       ASM_REWRITE_TAC[combinTheory.o_DEF] >>
       BETA_TAC >> metis_tac[get_label_subst_label_op] >> NO_TAC) >>
  (* PHI: phi_operands_wf preserved *)
  qpat_x_assum `phi_operands_wf _` mp_tac >>
  qspec_tac (`inst.inst_operands`, `ops`) >>
  ho_match_mp_tac phi_operands_wf_ind >>
  rw[phi_operands_wf_def, subst_label_op_def]
QED

(* Helper: wf facts for the phi-rewritten block in func' *)
Theorem phi_rewrite_block_wf[local]:
  !old new bb.
    EVERY inst_wf bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    let bb' = bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst old new inst)
          bb.bb_instructions in
    EVERY inst_wf bb'.bb_instructions /\
    bb'.bb_instructions <> [] /\
    (!i. i < LENGTH bb'.bb_instructions - 1 ==>
         ~is_terminator (EL i bb'.bb_instructions).inst_opcode)
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >> simp[] >>
  (conj_tac >- (
    fs[listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
    rpt strip_tac >> res_tac >>
    BasicProvers.every_case_tac >> fs[] >>
    irule inst_wf_subst_label_inst >> ASM_REWRITE_TAC[])) >>
  rw[rich_listTheory.EL_MAP] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[] >> rw[subst_label_inst_def]
QED

Theorem not_MEM_next_lbl_succs[local]:
  !func lbl next_lbl bb next_bb cur_bb.
    can_merge_blocks func bb next_bb /\
    bb.bb_label = lbl /\
    next_bb.bb_label = next_lbl /\
    MEM bb func.fn_blocks /\
    MEM cur_bb func.fn_blocks /\
    cur_bb.bb_label <> lbl ==>
    ~MEM next_lbl (bb_succs cur_bb)
Proof
  rpt strip_tac >>
  fs[can_merge_blocks_def] >>
  `cur_bb = bb` by (
    mp_tac (Q.SPECL [`func`, `next_bb.bb_label`, `bb`] num_preds_1_unique_pred) >>
    (impl_tac >- simp[]) >>
    disch_tac >> pop_assum (qspec_then `cur_bb` mp_tac) >>
    simp[]) >>
  fs[]
QED

(* Bridge: merged_bb (from USPL) behaves like merge_blocks when prev_bb is fresh.
   Bundles ALL_DISTINCT, lookup, and run_block_uspl_irrelevant setup. *)
Theorem at_lbl_uspl_bridge[local]:
  !fuel ctx func lbl next_lbl bb next_bb merged_bb s.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    lbl <> next_lbl /\
    lookup_block lbl
      (update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
          (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))) = SOME merged_bb /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY inst_wf next_bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    bb_well_formed next_bb /\
    s.vs_prev_bb <> SOME next_lbl /\
    s.vs_prev_bb <> SOME lbl /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    run_block fuel ctx merged_bb s =
    run_block fuel ctx (merge_blocks bb next_bb) s
Proof
  rpt strip_tac >>
  qabbrev_tac `bbs2 = replace_block lbl (merge_blocks bb next_bb)
    (remove_block next_lbl func.fn_blocks)` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by (
    qpat_x_assum `wf_function func` mp_tac >>
    simp[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `bb.bb_label = lbl` by
    metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs2)` by (
    qunabbrev_tac `bbs2` >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
    simp[merge_blocks_def, venomInstTheory.basic_block_component_equality] >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >>
    first_assum ACCEPT_TAC) >>
  `lookup_block lbl bbs2 = SOME (merge_blocks bb next_bb)` by (
    qunabbrev_tac `bbs2` >>
    match_mp_tac cfgTransformPropsTheory.lookup_block_replace_eq >>
    simp[merge_blocks_def, venomInstTheory.basic_block_component_equality] >>
    `lookup_block lbl (remove_block next_lbl func.fn_blocks) =
     lookup_block lbl func.fn_blocks`
      by (irule cfgTransformPropsTheory.lookup_block_remove_neq >>
          ASM_REWRITE_TAC[]) >>
    metis_tac[]) >>
  `(merge_blocks bb next_bb).bb_instructions <> []` by (
    simp[merge_blocks_def] >>
    Cases_on `next_bb.bb_instructions` >> fs[bb_well_formed_def]) >>
  `EVERY inst_wf (merge_blocks bb next_bb).bb_instructions` by (
    simp[merge_blocks_def, listTheory.EVERY_APPEND, listTheory.EVERY_MEM] >>
    rpt strip_tac >>
    `MEM e (FRONT bb.bb_instructions) \/ MEM e next_bb.bb_instructions` by
      metis_tac[listTheory.MEM_APPEND] >>
    metis_tac[listTheory.EVERY_MEM, rich_listTheory.MEM_FRONT_NOT_NIL]) >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `next_lbl`, `lbl`, `bbs2`,
    `bb_succs (merge_blocks bb next_bb)`, `lbl`,
    `merge_blocks bb next_bb`, `merged_bb`, `s`]
    run_block_uspl_irrelevant) >>
  ASM_REWRITE_TAC[] >>
  `0 < LENGTH (merge_blocks bb next_bb).bb_instructions` by
    (Cases_on `(merge_blocks bb next_bb).bb_instructions` >> fs[]) >>
  ASM_REWRITE_TAC[]
QED

(* ================================================================
   at_lbl_D1_nonOK: when bb succeeds and merged block gives non-OK,
   derive the fuel witness for the rf simulation.
   Works uniformly for Halt, Abort, IntRet, Error.
   Takes the bridge equation and lift_result directly.
   ================================================================ *)
Theorem at_lbl_D1_nonOK[local]:
  !func func' lbl next_lbl bb next_bb merged_bb n ctx s2 v.
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    lookup_block lbl func'.fn_blocks = SOME merged_bb /\
    s2.vs_current_bb = lbl /\
    s2.vs_inst_idx = 0 /\ ~s2.vs_halted /\
    v.vs_current_bb = next_lbl /\
    v.vs_inst_idx = 0 /\ ~v.vs_halted /\
    run_block n ctx bb s2 = OK v /\
    run_block n ctx merged_bb s2 =
      run_block n ctx (merge_blocks bb next_bb) s2 /\
    (!s. run_block n ctx (merge_blocks bb next_bb) s2 <> OK s) /\
    lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {})
      (run_block n ctx (merge_blocks bb next_bb) s2)
      (run_block n ctx next_bb v) ==>
    ?fuel'. SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s2)
                      (run_blocks (SUC n) ctx func' s2)
Proof
  rpt strip_tac >>
  (* Case split on both results to resolve lift_result *)
  Cases_on `run_block n ctx (merge_blocks bb next_bb) s2` >>
  Cases_on `run_block n ctx next_bb v` >>
  qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
  simp[stateEquivTheory.lift_result_def] >>
  rpt strip_tac >> (
    (* Kill OK case via contradiction with !s. ... <> OK s *)
    TRY (fs[] >> NO_TAC) >>
    (* Witness fuel' = SUC (SUC n) *)
    qexists_tac `SUC (SUC n)` >> simp[] >>
    (* fuel_mono: run_block (SUC n) ctx bb s2 = OK v *)
    `run_block (SUC n) ctx bb s2 = OK v` by (
      mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
      disch_then (qspecl_then [`n`, `SUC n`, `ctx`, `bb`, `s2`, `OK v`]
        mp_tac) >>
      ASM_REWRITE_TAC[exec_result_distinct] >> simp[]) >>
    (* Unfold func side: 2 steps *)
    CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
    ASM_REWRITE_TAC[] >> simp[optionTheory.option_case_def] >>
    CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
    ASM_REWRITE_TAC[] >> simp[optionTheory.option_case_def] >>
    (* Unfold func' side: 1 step *)
    CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
    ASM_REWRITE_TAC[] >> simp[optionTheory.option_case_def] >>
    (* Link *)
    simp[stateEquivTheory.result_equiv_def] >>
    metis_tac[stateEquivTheory.execution_equiv_def]
  )
QED


(* ================================================================
   at_lbl_D2_nonOK: D2 version of the non-OK helper.
   func runs bb(s1) then maybe next_bb; func' runs merged_bb(s2).
   Bridge gives result_equiv {} for the non-OK results.
   Handles both bb-nonOK and bb-OK-then-next_bb-nonOK sub-cases.
   ================================================================ *)
Theorem at_lbl_D2_nonOK[local]:
  !func func' lbl next_lbl bb next_bb merged_bb n ctx s1 s2.
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    lookup_block lbl func'.fn_blocks = SOME merged_bb /\
    s1.vs_current_bb = lbl /\ s2.vs_current_bb = lbl /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    ~s1.vs_halted /\ ~s2.vs_halted /\
    single_succ_jmp bb next_lbl /\ bb_succs bb = [next_lbl] /\
    bb_well_formed bb /\ bb_well_formed next_bb /\
    EVERY inst_wf bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    result_equiv {} (run_block n ctx (merge_blocks bb next_bb) s1)
                    (run_block n ctx merged_bb s2) /\
    (!s. run_block n ctx (merge_blocks bb next_bb) s1 <> OK s) /\
    (case run_block n ctx bb s1 of
       OK s'' =>
         lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {})
           (run_block n ctx (merge_blocks bb next_bb) s1)
           (run_block n ctx next_bb (s'' with vs_inst_idx := 0))
     | _ => T) ==>
    ?fuel'. SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s1)
                      (run_blocks (SUC n) ctx func' s2)
Proof
  rpt strip_tac >>
  Cases_on `run_block n ctx bb s1`
  >- suspend "bb_ok"
  (* Non-OK: all 4 constructors handled inline with >> *)
  >> (
    `run_block n ctx (merge_blocks bb next_bb) s1 =
     run_block n ctx bb s1` by (
      mp_tac (Q.SPECL [`PRE (LENGTH bb.bb_instructions) - 0`,
        `n`, `ctx`, `bb`, `next_bb`, `s1`] run_block_merge_nonOK_same) >>
      (impl_tac >- (
        ASM_REWRITE_TAC[] >> rpt conj_tac
        >- simp[] >- fs[single_succ_jmp_def]
        >- simp[] >> simp[exec_result_distinct])) >>
      simp[]) >>
    fs[] >> qexists_tac `SUC n` >> simp[] >>
    CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
    ASM_REWRITE_TAC[] >> simp[optionTheory.option_case_def] >>
    CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
    ASM_REWRITE_TAC[] >> simp[optionTheory.option_case_def] >>
    Cases_on `run_block n ctx merged_bb s2` >>
    qpat_x_assum `result_equiv _ _ _` mp_tac >>
    simp[stateEquivTheory.result_equiv_def, exec_result_case_def])
QED

Resume at_lbl_D2_nonOK[bb_ok]:
  rename1 `run_block n ctx bb s1 = OK v_bb` >>
  `v_bb.vs_inst_idx = 0` by
    metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  `~v_bb.vs_halted` by
    metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `MEM v_bb.vs_current_bb (bb_succs bb)` by (
    mp_tac (Q.SPECL [`n`, `ctx`, `bb`, `s1`, `v_bb`]
      simplifyCfgCollapseBaseTheory.run_block_current_bb_in_succs_wf) >>
    ASM_REWRITE_TAC[]) >>
  `v_bb.vs_current_bb = next_lbl` by gvs[listTheory.MEM] >>
  `v_bb with vs_inst_idx := 0 = v_bb` by
    simp[venomStateTheory.venom_state_component_equality] >>
  qpat_x_assum `case OK v_bb of _ => _`
    (ASSUME_TAC o SIMP_RULE std_ss [exec_result_case_def]) >>
  fs[] >>
  Cases_on `run_block n ctx (merge_blocks bb next_bb) s1` >>
  Cases_on `run_block n ctx next_bb v_bb` >>
  qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
  simp[stateEquivTheory.lift_result_def] >>
  rpt strip_tac >> TRY (fs[] >> NO_TAC) >>
  qexists_tac `SUC (SUC n)` >> simp[] >>
  `run_block (SUC n) ctx bb s1 = OK v_bb` by (
    mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
    disch_then (qspecl_then [`n`, `SUC n`, `ctx`, `bb`, `s1`, `OK v_bb`]
      mp_tac) >>
    ASM_REWRITE_TAC[exec_result_distinct] >> simp[]) >>
  CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
  ASM_REWRITE_TAC[] >> simp[optionTheory.option_case_def] >>
  CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
  ASM_REWRITE_TAC[] >> simp[optionTheory.option_case_def] >>
  CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
  ASM_REWRITE_TAC[] >> simp[optionTheory.option_case_def] >>
  (* Resolve case on merged_bb(s2) using bridge result_equiv *)
  Cases_on `run_block n ctx merged_bb s2` >>
  qpat_x_assum `result_equiv _ _ _` mp_tac >>
  simp[stateEquivTheory.result_equiv_def, exec_result_case_def] >>
  rpt strip_tac >>
  simp[stateEquivTheory.result_equiv_def] >>
  metis_tac[stateEquivTheory.execution_equiv_def]
QED

Finalise at_lbl_D2_nonOK;

Resume merge_step_equiv_strong[at_lbl]:
  qpat_x_assum `!m. m < SUC n ==> _` (markerLib.hide_tac "IH") >>
  (* === Setup: derive basic facts === *)
  drule_all lookup_block_wf_facts >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `next_bb.bb_label = next_lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `MEM bb func.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `MEM next_bb func.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `no_phis next_bb` by fs[can_merge_blocks_def] >>
  `single_succ_jmp bb next_lbl` by fs[can_merge_blocks_def] >>
  `bb_well_formed next_bb` by (fs[wf_function_def] >> res_tac) >>
  `EVERY inst_wf next_bb.bb_instructions` by (
    REWRITE_TAC[listTheory.EVERY_MEM] >> rpt strip_tac >>
    qpat_x_assum `fn_inst_wf func` mp_tac >>
    REWRITE_TAC[venomWfTheory.fn_inst_wf_def] >>
    disch_then (qspecl_then [`next_bb`, `e`] mp_tac) >>
    ASM_REWRITE_TAC[]) >>
  `cur_bb = bb` by metis_tac[optionTheory.SOME_11] >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `s1.vs_current_bb = lbl` SUBST_ALL_TAC >>
  qpat_x_assum `lbl = s2.vs_current_bb`
    (fn th => SUBST_ALL_TAC (GSYM th) >> ASSUME_TAC (GSYM th)) >>
  (* Normalize msuccs *)
  qpat_x_assum `Abbrev (msuccs = _)` (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  (* Lookup merged block in func' *)
  mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`]
    lookup_block_merge_lbl) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  (* === Case split on merge_R === *)
  qpat_x_assum `merge_R _ _ _ _` mp_tac >>
  PURE_REWRITE_TAC[merge_R_def] >> strip_tac
  >- (
    (* === Disjunct 1: s1 = s2, prev_bb fresh === *)
    qpat_x_assum `s1 = s2` SUBST_ALL_TAC >>
    suspend "D1"
  )
  >>
  (* === Disjunct 2: prev_bb_equiv === *)
  suspend "D2"
QED

Resume merge_step_equiv_strong[D1]:
  (* Step 1: Bridge merged_bb to merge_blocks via at_lbl_uspl_bridge *)
  mp_tac (Q.SPECL [`n`, `ctx`, `func`, `lbl`, `next_lbl`, `bb`, `next_bb`,
    `merged_bb`, `s2`] at_lbl_uspl_bridge) >>
  ASM_REWRITE_TAC[] >>
  disch_tac >>
  suspend "D1_cont"
QED

Resume merge_step_equiv_strong[D1_cont]:
  `bb_succs bb = [next_lbl]` by fs[can_merge_blocks_def] >>
  Cases_on `run_block n ctx bb s2`
  >- (
    rename1 `run_block n ctx bb s2 = OK v` >>
    suspend "D1_OK"
  )
  >> (
    (* Non-OK case: both sides give same non-OK result *)
    (* merged = bb result since bb is non-OK *)
    `run_block n ctx (merge_blocks bb next_bb) s2 = run_block n ctx bb s2` by (
      mp_tac (Q.SPECL [`PRE (LENGTH bb.bb_instructions) - 0`,
        `n`, `ctx`, `bb`, `next_bb`, `s2`] run_block_merge_nonOK_same) >>
      (impl_tac >- (ASM_REWRITE_TAC[] >> fs[single_succ_jmp_def])) >>
      simp[]) >>
    qexists_tac `SUC n` >> simp[] >>
    (* Unfold func side: lookup lbl -> bb, run_block gives non-OK result *)
    CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
    ASM_REWRITE_TAC[] >> simp[optionTheory.option_case_def] >>
    (* Unfold func' side: lookup lbl -> merged_bb, run_block gives same result *)
    CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
    qpat_x_assum `func'.fn_blocks = _` (fn fneq => REWRITE_TAC[fneq]) >>
    ASM_REWRITE_TAC[] >> simp[optionTheory.option_case_def] >>
    simp[result_equiv_empty_refl]
  )
QED

Resume merge_step_equiv_strong[D1_OK]:
  (* Derive v properties *)
  `v.vs_inst_idx = 0` by metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  `~v.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `v.vs_prev_bb = SOME lbl` by (
    mp_tac (Q.SPECL [`n`, `ctx`, `bb`, `s2`, `v`]
      venomExecPropsTheory.run_block_ok_prev_bb) >>
    ASM_REWRITE_TAC[] >> simp[]) >>
  `v.vs_current_bb = next_lbl` by (
    mp_tac (Q.SPECL [`n`, `ctx`, `bb`, `s2`, `v`]
      venomExecPropsTheory.run_block_current_bb_in_succs) >>
    ASM_REWRITE_TAC[] >> simp[listTheory.MEM]) >>
  (* Apply merge equiv: merge_blocks vs next_bb *)
  mp_tac (Q.SPECL [`n`, `ctx`, `bb`,
    `next_bb`, `s2`] simplifyCfgCollapseBaseTheory.run_block_merge_equiv) >>
  (impl_tac >- (ASM_REWRITE_TAC[] >> simp[])) >>
  ASM_REWRITE_TAC[] >>
  disch_tac >>
  (* Case split on merged block result *)
  Cases_on `run_block n ctx (merge_blocks bb next_bb) s2`
  >- (
    (* OK w1: lift_result gives OK w2 for next_bb with prev_bb_equiv *)
    rename1 `run_block n ctx (merge_blocks bb next_bb) s2 = OK w1` >>
    suspend "D1_OK_OK"
  )
  >> (
    (* All 4 non-OK cases: Halt, Abort, IntRet, Error *)
    (* Simplify case expression to get lift_result *)
    qpat_x_assum `case OK v of _ => _`
      (ASSUME_TAC o SIMP_RULE std_ss [exec_result_case_def]) >>
    (* Simplify: v with vs_inst_idx := 0 = v, then case expression *)
    `v with vs_inst_idx := 0 = v`
      by simp[venomStateTheory.venom_state_component_equality] >>
    fs[exec_result_case_def] >>
    mp_tac (Q.SPECL [`func`, `func'`, `lbl`, `next_lbl`, `bb`,
      `next_bb`, `merged_bb`, `n`, `ctx`, `s2`, `v`] at_lbl_D1_nonOK) >>
    ASM_REWRITE_TAC[] >>
    simp[exec_result_distinct]
  )
QED

Resume merge_step_equiv_strong[D1_OK_OK]:
  (* Step 1: Simplify case expr + vs_inst_idx *)
  `v with vs_inst_idx := 0 = v`
    by simp[venomStateTheory.venom_state_component_equality] >>
  fs[exec_result_case_def] >>
  pop_assum (K ALL_TAC) >>
  (* Cases_on next_bb result; kill non-OK with contradiction *)
  Cases_on `run_block n ctx next_bb v` >> (
    TRY (qpat_x_assum `lift_result _ _ _ (OK _) _` mp_tac >>
         simp[stateEquivTheory.lift_result_def] >> NO_TAC)) >>
  (* Only OK case remains *)
  rename1 `run_block n ctx next_bb v = OK w2` >>
  qpat_x_assum `lift_result _ _ _ (OK _) (OK _)` mp_tac >>
  simp[stateEquivTheory.lift_result_def] >> strip_tac >>
  (* Step 2: Derive w1, w2 properties *)
  `w1.vs_inst_idx = 0` by metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  `w2.vs_inst_idx = 0` by metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  `~w1.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `~w2.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `bb_well_formed (merge_blocks bb next_bb)` by
    metis_tac[simplifyCfgHelpersTheory.bb_well_formed_merge_blocks] >>
  `EVERY inst_wf (merge_blocks bb next_bb).bb_instructions` by (
    simp[simplifyCfgDefsTheory.merge_blocks_def, listTheory.EVERY_APPEND] >>
    Cases_on `bb.bb_instructions` >- fs[] >>
    rw[listTheory.EVERY_MEM] >> rpt strip_tac >>
    `MEM e (h::t)` by metis_tac[rich_listTheory.MEM_FRONT] >>
    fs[listTheory.EVERY_MEM]) >>
  `w1.vs_prev_bb = SOME lbl` by
    metis_tac[run_block_ok_prev_bb_wf] >>
  `w2.vs_prev_bb = SOME next_lbl` by
    metis_tac[run_block_ok_prev_bb_wf] >>
  `w1.vs_current_bb = w2.vs_current_bb` by (
    qpat_x_assum `prev_bb_equiv _ _` mp_tac >>
    simp[simplifyCfgPrevBBTheory.prev_bb_equiv_def,
       venomStateTheory.venom_state_component_equality]) >>
  (* Step 3: w2.vs_current_bb ≠ next_lbl *)
  `~MEM next_lbl (bb_succs next_bb)` by (
    mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`, `next_bb`]
      not_MEM_next_lbl_succs) >>
    ASM_REWRITE_TAC[] >> simp[]) >>
  `MEM w2.vs_current_bb (bb_succs next_bb)` by
    metis_tac[run_block_current_bb_in_succs_wf] >>
  `w2.vs_current_bb <> next_lbl` by metis_tac[listTheory.MEM] >>
  (* Step 4: Establish merge_R *)
  `prev_bb_equiv w2 w1` by
    metis_tac[simplifyCfgPrevBBTheory.prev_bb_equiv_sym] >>
  `merge_R lbl next_lbl w2 w1` by (
    simp[merge_R_def] >> DISJ2_TAC >> ASM_REWRITE_TAC[]) >>
  (* Step 5: Apply IH *)
  markerLib.unhide_x_assum "IH" ASSUME_TAC >>
  first_x_assum (qspec_then `n` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`ctx`, `w2`, `w1`] mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >>
  rename1 `n <= fuel_ih` >>
  (* Step 6: Witness + fuel_mono setup *)
  qexists_tac `SUC (SUC fuel_ih)` >> conj_tac >- simp[] >>
  `run_block (SUC n) ctx merged_bb s2 = OK w1` by (
    mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
    disch_then (qspecl_then [`n`, `SUC n`, `ctx`, `merged_bb`, `s2`, `OK w1`] mp_tac) >>
    simp[exec_result_distinct]) >>
  `w1 with vs_inst_idx := 0 = w1`
    by simp[venomStateTheory.venom_state_component_equality] >>
  `run_block (SUC fuel_ih) ctx bb s2 = OK v` by (
    mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
    disch_then (qspecl_then [`n`, `SUC fuel_ih`, `ctx`, `bb`, `s2`, `OK v`] mp_tac) >>
    simp[exec_result_distinct]) >>
  `run_block fuel_ih ctx next_bb v = OK w2` by (
    mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
    disch_then (qspecl_then [`n`, `fuel_ih`, `ctx`, `next_bb`, `v`, `OK w2`] mp_tac) >>
    simp[exec_result_distinct]) >>
  (* Step 7-9: Unfold rf on both sides.
     UNFOLD_RF_STEP_TAC does UNFOLD_RF_CONV + ASM_REWRITE_TAC + simp.
     func' side needs fn_blocks rewrite after each UNFOLD_RF_CONV. *)
  UNFOLD_RF_STEP_TAC RAND_CONV >>
  UNFOLD_RF_STEP_TAC (RATOR_CONV o RAND_CONV) >>
  UNFOLD_RF_STEP_TAC (RATOR_CONV o RAND_CONV)
QED

Resume merge_step_equiv_strong[other_block]:
  qpat_x_assum `!m. m < SUC n ==> _` (markerLib.hide_tac "IH") >>
  drule_all lookup_block_wf_facts >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `next_bb.bb_label = next_lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `MEM bb func.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`, `cur_bb`]
    not_MEM_next_lbl_succs) >>
  (impl_tac >- (
    rpt conj_tac
    >| [qpat_assum `can_merge_blocks _ _ _` ACCEPT_TAC,
        qpat_assum `bb.bb_label = _` ACCEPT_TAC,
        qpat_assum `next_bb.bb_label = _` ACCEPT_TAC,
        qpat_assum `MEM bb _` ACCEPT_TAC,
        qpat_assum `MEM cur_bb _` ACCEPT_TAC,
        qpat_assum `cur_bb.bb_label = _` (fn th =>
          REWRITE_TAC[th]) >>
        qpat_assum `s1.vs_current_bb <> lbl` ACCEPT_TAC])) >>
  strip_tac >>
  (* Normalize: unfold msuccs Abbrev, fold func' lookup *)
  qpat_x_assum `Abbrev (msuccs = _)` (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_x_assum `func'.fn_blocks = _`
    (fn fneq => ASSUME_TAC fneq >> ASSUME_TAC (GSYM fneq)) >>
  qpat_x_assum `merge_R _ _ _ _` mp_tac >>
  PURE_REWRITE_TAC[merge_R_def] >> strip_tac
  >- suspend "D1"
  >> Cases_on `lbl = next_lbl`
  >- suspend "D2a"
  >> suspend "D2b"
QED

(* D1: s1 = s2, prev_bb neither SOME next_lbl nor SOME lbl *)
Resume merge_step_equiv_strong[D1]:
  qpat_x_assum `s1 = s2` SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`,
                    `s2.vs_current_bb`, `cur_bb`, `n`, `ctx`, `s2`]
    run_block_merge_other_equiv) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  (* Fold lookup to use func'.fn_blocks (GSYM already in scope) *)
  qpat_x_assum `lookup_block _ (update_succ_phi_labels _ _ _ _) = SOME cur_bb'`
    (fn th => qpat_assum `update_succ_phi_labels _ _ _ _ = func'.fn_blocks`
      (fn fneq => ASSUME_TAC (ONCE_REWRITE_RULE [fneq] th))) >>
  (* Bridge: literal equality → result_equiv {} *)
  `result_equiv {} (run_block n ctx cur_bb s2) (run_block n ctx cur_bb' s2)` by (
    qpat_x_assum `run_block _ _ cur_bb' _ = _` (SUBST1_TAC o GSYM) >>
    REWRITE_TAC[result_equiv_empty_refl]) >>
  (* Apply combined helper *)
  markerLib.unhide_x_assum "IH" (fn ih =>
  mp_tac (Q.SPECL [`func`, `func'`, `lbl`, `next_lbl`, `bb`, `next_bb`,
                    `cur_bb`, `cur_bb'`, `n`, `ctx`, `s2`, `s2`]
    merge_other_block_step) >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY REFL_TAC >> ACCEPT_TAC ih)) >>
  simp_tac std_ss [])
QED

(* D2a: lbl = next_lbl — identity subst.
   When lbl = next_lbl, prev_bb values match so s1 = s2.
   subst_label_inst lbl lbl = id, so all blocks identical ⟹ reduces to D1. *)
Resume merge_step_equiv_strong[D2a]:
  (* Step 1: lbl = next_lbl => prev_bb's match => s1 = s2 *)
  `s1.vs_prev_bb = s2.vs_prev_bb` by (
    qpat_assum `lbl = next_lbl` SUBST_ALL_TAC >>
    qpat_assum `s1.vs_prev_bb = _` (fn a =>
    qpat_assum `s2.vs_prev_bb = _` (fn b =>
    REWRITE_TAC[a, b]))) >>
  `s1 = s2` by (
    mp_tac (Q.SPECL [`s1`, `s2`] prev_bb_equiv_same_eq) >>
    qpat_assum `prev_bb_equiv _ _` (fn a =>
    qpat_assum `s1.vs_prev_bb = s2.vs_prev_bb` (fn b =>
    REWRITE_TAC[a, b]))) >>
  qpat_x_assum `s1 = s2` SUBST_ALL_TAC >>
  (* Step 2: Unhide IH before SUBST so lbl→next_lbl penetrates *)
  markerLib.unhide_x_assum "IH" ASSUME_TAC >>
  qpat_x_assum `lbl = next_lbl` SUBST_ALL_TAC >>
  qpat_x_assum `!m. m < SUC n ==> _` (markerLib.hide_tac "IH") >>
  `SOME bb = SOME next_bb` by (
    qpat_assum `lookup_block next_lbl func.fn_blocks = SOME next_bb`
      (fn a => qpat_assum `lookup_block next_lbl func.fn_blocks = SOME bb`
        (fn b => ACCEPT_TAC (TRANS (SYM b) a)))) >>
  pop_assum (ASSUME_TAC o REWRITE_RULE [optionTheory.SOME_11]) >>
  (* Unhide IH again before bb=next_bb SUBST *)
  markerLib.unhide_x_assum "IH" ASSUME_TAC >>
  qpat_x_assum `bb = next_bb` SUBST_ALL_TAC >>
  qpat_x_assum `!m. m < SUC n ==> _` (markerLib.hide_tac "IH") >>
  suspend "D2a_lookup"
QED

Theorem bb_update_insts_id[local]:
  (bb:basic_block) with bb_instructions := bb.bb_instructions = bb
Proof
  Cases_on `bb` >>
  REWRITE_TAC[venomInstTheory.basic_block_fn_updates,
              combinTheory.K_THM, venomInstTheory.basic_block_accessors]
QED

Resume merge_step_equiv_strong[D2a_lookup]:
  mp_tac (Q.SPECL [`func`, `next_lbl`, `next_lbl`, `next_bb`, `next_bb`,
                    `s2.vs_current_bb`, `cur_bb`] lookup_block_merge_other_bb) >>
  (impl_tac >- (
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac std_ss [LET_THM] >>
  (* Simplify identity subst: subst_label_inst l l = id, then COND_ID, MAP_ID *)
  PURE_REWRITE_TAC[cfgTransformProofsTheory.subst_label_inst_id,
                   boolTheory.COND_ID, listTheory.MAP_ID, bb_update_insts_id] >>
  strip_tac >>
  (* Both MEM and ~MEM branches now give lookup = SOME cur_bb *)
  `lookup_block s2.vs_current_bb
     (update_succ_phi_labels next_lbl next_lbl
        (replace_block next_lbl (merge_blocks next_bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks next_bb next_bb))) = SOME cur_bb` by (
    Cases_on `MEM s2.vs_current_bb (bb_succs (merge_blocks next_bb next_bb))`
    >> first_x_assum (fn th => first_assum (ACCEPT_TAC o MATCH_MP th))) >>
  (* Fold to func'.fn_blocks *)
  qpat_x_assum `lookup_block _ (update_succ_phi_labels _ _ _ _) = SOME cur_bb`
    (fn th => qpat_assum `update_succ_phi_labels _ _ _ _ = func'.fn_blocks`
      (fn fneq => ASSUME_TAC (ONCE_REWRITE_RULE [fneq] th))) >>
  (* Apply merge_other_block_step (IH now has next_lbl/next_lbl after D2a fix) *)
  markerLib.unhide_x_assum "IH" (fn ih =>
  mp_tac (Q.SPECL [`func`, `func'`, `next_lbl`, `next_lbl`, `next_bb`, `next_bb`,
                    `cur_bb`, `cur_bb`, `n`, `ctx`, `s2`, `s2`]
    merge_other_block_step) >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY REFL_TAC >>
    TRY (REWRITE_TAC[result_equiv_empty_refl]) >>
    ACCEPT_TAC ih)) >>
  simp_tac std_ss [])
QED

(* subst_label_inst is identity when the old label doesn't appear *)
Theorem subst_label_op_irrelevant:
  !old new op. op <> Label old ==> subst_label_op old new op = op
Proof
  Cases_on `op` >> rw[subst_label_op_def]
QED

Theorem MAP_subst_label_op_irrelevant[local]:
  !old new ops. ~MEM (Label old) ops ==>
    MAP (subst_label_op old new) ops = ops
Proof
  Induct_on `ops` >> rw[subst_label_op_def] >>
  Cases_on `h` >> fs[subst_label_op_def]
QED

Theorem subst_label_inst_irrelevant[local]:
  !old new inst. ~MEM (Label old) inst.inst_operands ==>
    subst_label_inst old new inst = inst
Proof
  rpt strip_tac >>
  simp[subst_label_inst_def, MAP_subst_label_op_irrelevant,
       venomInstTheory.instruction_component_equality]
QED

(* Helper: label not in PHI operands when not a predecessor.
   If block x has bb_succs not containing cb, and x.bb_label = lbl,
   then Label lbl not in PHI operands of cb's instructions. *)
Theorem label_not_in_phi_ops_no_pred[local]:
  !func lbl cur_bb.
    fn_phi_preds_wf func /\ wf_function func /\
    MEM cur_bb func.fn_blocks /\
    (!x. MEM x func.fn_blocks /\ x.bb_label = lbl ==>
         ~MEM cur_bb.bb_label (bb_succs x)) ==>
    !inst. MEM inst cur_bb.bb_instructions /\ inst.inst_opcode = PHI ==>
      ~MEM (Label lbl) inst.inst_operands
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `MEM lbl (pred_labels func cur_bb.bb_label)` by (
    fs[fn_phi_preds_wf_def] >>
    first_x_assum irule >>
    metis_tac[]) >>
  fs[pred_labels_def, listTheory.MEM_FLAT, listTheory.MEM_MAP,
     block_preds_def, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

Theorem result_prev_bb_equiv_sym[local]:
  !r1 r2. result_prev_bb_equiv r1 r2 ==> result_prev_bb_equiv r2 r1
Proof
  Cases >> Cases >>
  rw[result_prev_bb_equiv_def, prev_bb_equiv_sym]
QED

(* phi_well_formed for PHI instructions from inst_wf *)
(* phi_operands_wf implies phi_well_formed (stricter => looser) *)
val phi_operands_wf_implies_phi_well_formed =
  phi_operands_wf_implies_phi_well_formed_early;

Theorem inst_wf_phi_well_formed[local]:
  !insts. EVERY inst_wf insts ==>
    EVERY (\inst. phi_well_formed inst.inst_operands)
          (FILTER (\inst. inst.inst_opcode = PHI) insts)
Proof
  simp[listTheory.EVERY_MEM, listTheory.MEM_FILTER] >>
  rpt strip_tac >> res_tac >>
  qpat_x_assum `inst.inst_opcode = PHI` (fn th =>
    FULL_SIMP_TAC (srw_ss()) [inst_wf_def, th]) >>
  irule phi_operands_wf_implies_phi_well_formed >> first_assum ACCEPT_TAC
QED

(* Label next_lbl absent from PHI operands of cur_bb when
   cur_bb is NOT a successor of merge_blocks bb next_bb.
   Uses: bb_succs(merge_blocks bb next_bb) = bb_succs(next_bb). *)
Theorem phi_label_next_lbl_absent[local]:
  !func lbl next_lbl bb next_bb cur_bb.
    fn_phi_preds_wf func /\ wf_function func /\
    bb_well_formed bb /\ bb_well_formed next_bb /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    bb.bb_label = lbl /\ next_bb.bb_label = next_lbl /\
    MEM cur_bb func.fn_blocks /\
    ~MEM cur_bb.bb_label (bb_succs (merge_blocks bb next_bb)) ==>
    !inst. MEM inst cur_bb.bb_instructions /\ inst.inst_opcode = PHI ==>
      ~MEM (Label next_lbl) inst.inst_operands
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `MEM next_lbl (pred_labels func cur_bb.bb_label)` by (
    fs[fn_phi_preds_wf_def] >> first_x_assum irule >> metis_tac[]) >>
  fs[pred_labels_def, listTheory.MEM_FLAT, listTheory.MEM_MAP,
     block_preds_def, listTheory.MEM_FILTER] >>
  `bb' = next_bb` by (
    `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
      fs[wf_function_def, venomInstTheory.fn_labels_def] >>
    `lookup_block next_lbl func.fn_blocks = SOME bb'` by
      (irule venomExecPropsTheory.MEM_lookup_block >> ASM_REWRITE_TAC[]) >>
    metis_tac[optionTheory.SOME_11]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  metis_tac[bb_succs_merge_blocks]
QED

(* Label lbl absent from PHI operands of any block cur_bb with
   cur_bb.bb_label ≠ next_lbl (since bb only jumps to next_lbl).
   Standalone helper to avoid label_not_in_phi_ops_no_pred in heavy contexts. *)
Theorem phi_label_lbl_absent[local]:
  !func lbl bb next_bb cur_bb.
    fn_phi_preds_wf func /\ wf_function func /\
    can_merge_blocks func bb next_bb /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    MEM cur_bb func.fn_blocks /\
    cur_bb.bb_label <> next_bb.bb_label ==>
    !inst. MEM inst cur_bb.bb_instructions /\ inst.inst_opcode = PHI ==>
      ~MEM (Label lbl) inst.inst_operands
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `MEM lbl (pred_labels func cur_bb.bb_label)` by (
    fs[fn_phi_preds_wf_def] >> first_x_assum irule >> metis_tac[]) >>
  fs[pred_labels_def, listTheory.MEM_FLAT, listTheory.MEM_MAP,
     block_preds_def, listTheory.MEM_FILTER] >>
  `bb' = bb` by (
    `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
      fs[wf_function_def, venomInstTheory.fn_labels_def] >>
    `lookup_block lbl func.fn_blocks = SOME bb'` by
      (irule venomExecPropsTheory.MEM_lookup_block >> ASM_REWRITE_TAC[]) >>
    metis_tac[optionTheory.SOME_11]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  gvs[can_merge_blocks_def, listTheory.MEM]
QED

(* merge_blocks PHI instructions come only from bb (via FRONT), not next_bb.
   So any property of bb's PHI operands transfers to merge_blocks. *)
Theorem merge_blocks_phi_operands[local]:
  !bb next_bb P.
    bb.bb_instructions <> [] /\
    no_phis next_bb /\
    (!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==> P inst) ==>
    !inst. MEM inst (merge_blocks bb next_bb).bb_instructions /\
           inst.inst_opcode = PHI ==> P inst
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM inst (merge_blocks _ _).bb_instructions` mp_tac >>
  simp[simplifyCfgDefsTheory.merge_blocks_def] >>
  simp[listTheory.MEM_APPEND] >>
  strip_tac
  >- metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL]
  >> fs[no_phis_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

(* Helper: In D2b context (prev_bb_equiv, different prev_bb, cb ≠ lbl/next_lbl),
   get func' lookup + wf + result_prev_bb_equiv between run_blocks.
   Produces exactly what merge_other_block_step_prev_bb needs.
   Both MEM/~MEM branches handled via run_block_prev_bb_equiv_subst. *)
Theorem D2b_lookup_prev_bb_equiv[local]:
  !func lbl next_lbl bb next_bb cur_bb n ctx s1 s2.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\
    can_merge_blocks func bb next_bb /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    lookup_block s1.vs_current_bb func.fn_blocks = SOME cur_bb /\
    bb.bb_label = lbl /\ next_bb.bb_label = next_lbl /\
    ~MEM next_lbl (bb_succs cur_bb) /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    s1.vs_current_bb <> lbl /\ s1.vs_current_bb <> next_lbl /\
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME next_lbl /\ s2.vs_prev_bb = SOME lbl /\
    lbl <> next_lbl ==>
    let msuccs = bb_succs (merge_blocks bb next_bb) in
    ?cur_bb'.
      lookup_block s1.vs_current_bb
        (update_succ_phi_labels next_lbl lbl
           (replace_block lbl (merge_blocks bb next_bb)
              (remove_block next_lbl func.fn_blocks)) msuccs) = SOME cur_bb' /\
      EVERY inst_wf cur_bb'.bb_instructions /\
      cur_bb'.bb_instructions <> [] /\
      (!i. i < LENGTH cur_bb'.bb_instructions - 1 ==>
           ~is_terminator (EL i cur_bb'.bb_instructions).inst_opcode) /\
      result_prev_bb_equiv
        (run_block n ctx cur_bb s1) (run_block n ctx cur_bb' s2)
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  drule_all lookup_block_wf_facts >> strip_tac >>
  (* Get wf facts for bb and next_bb *)
  `MEM bb func.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `MEM next_bb func.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb_well_formed bb` by
    (fs[wf_function_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `bb_well_formed next_bb` by
    (fs[wf_function_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  (* Label lbl absent from PHI operands of cur_bb *)
  `!inst'. MEM inst' cur_bb.bb_instructions /\ inst'.inst_opcode = PHI ==>
      ~MEM (Label lbl) inst'.inst_operands` by (
    mp_tac (Q.SPECL [`func`, `lbl`, `bb`, `next_bb`, `cur_bb`]
      phi_label_lbl_absent) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      metis_tac[])) >>
    simp_tac std_ss []) >>
  (* phi_well_formed for PHIs of cur_bb *)
  `EVERY (\inst'. phi_well_formed inst'.inst_operands)
         (FILTER (\inst'. inst'.inst_opcode = PHI) cur_bb.bb_instructions)` by
    (irule inst_wf_phi_well_formed >> first_assum ACCEPT_TAC) >>
  (* ~MEM (Label lbl) for PHIs of cur_bb *)
  `EVERY (\inst'. ~MEM (Label lbl) inst'.inst_operands)
         (FILTER (\inst'. inst'.inst_opcode = PHI) cur_bb.bb_instructions)` by (
    simp[listTheory.EVERY_MEM, listTheory.MEM_FILTER] >>
    rpt strip_tac >> first_x_assum irule >> ASM_REWRITE_TAC[]) >>
  (* Get cur_bb' from func' via lookup_block_merge_other_bb *)
  mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`,
                    `s1.vs_current_bb`, `cur_bb`] lookup_block_merge_other_bb) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  (* Shared: prev_bb_equiv s2 s1 *)
  `prev_bb_equiv s2 s1` by
    (irule prev_bb_equiv_sym >> first_assum ACCEPT_TAC) >>
  (* MEM/~MEM split — both use run_block_prev_bb_equiv_subst *)
  Cases_on `MEM s1.vs_current_bb (bb_succs (merge_blocks bb next_bb))`
  >- (
    (* MEM: cur_bb' = phi-subst cur_bb *)
    first_x_assum (fn th => first_assum (ASSUME_TAC o MATCH_MP th)) >>
    qexists_tac `cur_bb with bb_instructions :=
      MAP (\inst'. if inst'.inst_opcode <> PHI then inst'
                   else subst_label_inst next_lbl lbl inst')
          cur_bb.bb_instructions` >>
    ASM_REWRITE_TAC[] >>
    mp_tac (Q.SPECL [`next_lbl`, `lbl`, `cur_bb`] phi_rewrite_block_wf) >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    simp_tac std_ss [LET_THM] >> strip_tac >> ASM_REWRITE_TAC[] >>
    irule result_prev_bb_equiv_sym >>
    mp_tac (Q.SPECL
      [`LENGTH cur_bb.bb_instructions`, `n`, `ctx`, `next_lbl`, `lbl`,
       `cur_bb with bb_instructions :=
         MAP (\inst'. if inst'.inst_opcode <> PHI then inst'
                      else subst_label_inst next_lbl lbl inst')
             cur_bb.bb_instructions`,
       `cur_bb`, `s2`, `s1`]
      run_block_prev_bb_equiv_subst) >>
    (impl_tac >- (
      ASM_REWRITE_TAC[] >> rpt conj_tac
      >- simp[]
      >- simp[listTheory.LENGTH_MAP]
      >> (rpt strip_tac >> simp[rich_listTheory.EL_MAP] >>
          BasicProvers.every_case_tac >> simp[]))) >>
    simp_tac std_ss []
  ) >>
  (* ~MEM: cur_bb' = cur_bb *)
  first_x_assum (fn th => first_assum (ASSUME_TAC o MATCH_MP th)) >>
  qexists_tac `cur_bb` >> ASM_REWRITE_TAC[] >>
  (* Label next_lbl also absent (cur_bb not a successor of merged block) *)
  `!inst'. MEM inst' cur_bb.bb_instructions /\ inst'.inst_opcode = PHI ==>
      ~MEM (Label next_lbl) inst'.inst_operands` by (
    mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`, `cur_bb`]
      phi_label_next_lbl_absent) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      metis_tac[])) >>
    simp_tac std_ss []) >>
  `EVERY (\inst'. ~MEM (Label next_lbl) inst'.inst_operands)
         (FILTER (\inst'. inst'.inst_opcode = PHI) cur_bb.bb_instructions)` by (
    simp[listTheory.EVERY_MEM, listTheory.MEM_FILTER] >>
    rpt strip_tac >> first_x_assum irule >> ASM_REWRITE_TAC[]) >>
  (* Derive element-wise subst identity for PHI instructions *)
  `!i. i < LENGTH cur_bb.bb_instructions /\
       (EL i cur_bb.bb_instructions).inst_opcode = PHI ==>
       EL i cur_bb.bb_instructions =
         subst_label_inst next_lbl lbl (EL i cur_bb.bb_instructions)` by (
    rpt strip_tac >>
    irule (GSYM subst_label_inst_irrelevant) >>
    metis_tac[listTheory.MEM_EL]) >>
  irule result_prev_bb_equiv_sym >>
  mp_tac (Q.SPECL
    [`LENGTH cur_bb.bb_instructions`, `n`, `ctx`, `next_lbl`, `lbl`,
     `cur_bb`, `cur_bb`, `s2`, `s1`]
    run_block_prev_bb_equiv_subst) >>
  (impl_tac >- (
    fs[] >> rpt strip_tac >> res_tac >> simp[])) >>
  simp_tac std_ss []
QED

(* D2 at_lbl bridge: relate merged_bb(s2) to merge_blocks(s1) via prev_bb_equiv.
   Bundles ALL_DISTINCT, lookup, run_block_prev_bb_equiv_subst setup, and
   result_prev_bb_equiv_wf_to_result_equiv conversion to result_equiv. *)
Theorem at_lbl_D2_bridge[local]:
  !func lbl next_lbl bb next_bb merged_bb n ctx s1 s2.
    wf_function func /\ fn_inst_wf func /\ fn_phi_preds_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_lbl /\
    lookup_block lbl
      (update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
          (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))) = SOME merged_bb /\
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME next_lbl /\ s2.vs_prev_bb = SOME lbl /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    s1.vs_current_bb = lbl /\ s2.vs_current_bb = lbl /\
    ~s1.vs_halted ==>
    result_equiv {}
      (run_block n ctx (merge_blocks bb next_bb) s1)
      (run_block n ctx merged_bb s2)
Proof
  rpt strip_tac >>
  (* Setup: wf facts *)
  `bb.bb_label = lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `next_bb.bb_label = next_lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `MEM bb func.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `MEM next_bb func.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb_well_formed bb` by (fs[wf_function_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `bb_well_formed next_bb` by (fs[wf_function_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `no_phis next_bb` by fs[can_merge_blocks_def] >>
  `bb_well_formed (merge_blocks bb next_bb)` by
    metis_tac[simplifyCfgHelpersTheory.bb_well_formed_merge_blocks] >>
  `bb.bb_instructions <> []` by (fs[bb_well_formed_def]) >>
  `(merge_blocks bb next_bb).bb_instructions <> []` by (
    simp[simplifyCfgDefsTheory.merge_blocks_def] >>
    Cases_on `next_bb.bb_instructions` >> fs[bb_well_formed_def]) >>
  `EVERY inst_wf bb.bb_instructions` by (
    REWRITE_TAC[listTheory.EVERY_MEM] >> rpt strip_tac >>
    fs[venomWfTheory.fn_inst_wf_def] >> metis_tac[]) >>
  `EVERY inst_wf next_bb.bb_instructions` by (
    REWRITE_TAC[listTheory.EVERY_MEM] >> rpt strip_tac >>
    fs[venomWfTheory.fn_inst_wf_def] >> metis_tac[]) >>
  `EVERY inst_wf (merge_blocks bb next_bb).bb_instructions` by (
    simp[simplifyCfgDefsTheory.merge_blocks_def, listTheory.EVERY_APPEND] >>
    Cases_on `bb.bb_instructions` >- fs[] >>
    rw[listTheory.EVERY_MEM] >> rpt strip_tac >>
    `MEM e (h::t)` by metis_tac[rich_listTheory.MEM_FRONT] >>
    fs[listTheory.EVERY_MEM]) >>
  (* no interior terminators for merge_blocks *)
  `!i. i < LENGTH (merge_blocks bb next_bb).bb_instructions - 1 ==>
     ~is_terminator (EL i (merge_blocks bb next_bb).bb_instructions).inst_opcode` by
    metis_tac[bb_wf_no_interior_terminators] >>
  (* Step 1: result_prev_bb_equiv via run_block_prev_bb_equiv_subst *)
  `prev_bb_equiv s2 s1` by
    metis_tac[simplifyCfgPrevBBTheory.prev_bb_equiv_sym] >>
  `~s2.vs_halted` by (
    qpat_x_assum `prev_bb_equiv s1 s2` mp_tac >>
    simp[simplifyCfgPrevBBTheory.prev_bb_equiv_def,
         venomStateTheory.venom_state_component_equality]) >>
  (* ALL_DISTINCT for update_succ_phi_labels lookup *)
  qabbrev_tac `bbs2 = replace_block lbl (merge_blocks bb next_bb)
    (remove_block next_lbl func.fn_blocks)` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by (
    fs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs2)` by (
    qunabbrev_tac `bbs2` >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
    simp[simplifyCfgDefsTheory.merge_blocks_def,
         venomInstTheory.basic_block_component_equality] >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >>
    first_assum ACCEPT_TAC) >>
  `lookup_block lbl bbs2 = SOME (merge_blocks bb next_bb)` by (
    qunabbrev_tac `bbs2` >>
    match_mp_tac cfgTransformPropsTheory.lookup_block_replace_eq >>
    simp[simplifyCfgDefsTheory.merge_blocks_def,
         venomInstTheory.basic_block_component_equality] >>
    `lookup_block lbl (remove_block next_lbl func.fn_blocks) =
     lookup_block lbl func.fn_blocks`
      by (irule cfgTransformPropsTheory.lookup_block_remove_neq >>
          ASM_REWRITE_TAC[]) >>
    metis_tac[]) >>
  (* PHI label absence: ~MEM (Label lbl) in merge_blocks PHIs *)
  `bb.bb_label <> next_bb.bb_label` by ASM_REWRITE_TAC[] >>
  `!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
     ~MEM (Label lbl) inst.inst_operands` by
    metis_tac[phi_label_lbl_absent] >>
  mp_tac (Q.SPECL [`bb`, `next_bb`,
    `\inst. ~MEM (Label lbl) inst.inst_operands`]
    merge_blocks_phi_operands) >>
  (impl_tac >- (ASM_REWRITE_TAC[] >> BETA_TAC >> ASM_REWRITE_TAC[])) >>
  BETA_TAC >> disch_tac >>
  (* phi_well_formed for merge_blocks PHIs *)
  `EVERY (\inst. phi_well_formed inst.inst_operands)
     (FILTER (\inst. inst.inst_opcode = PHI)
             (merge_blocks bb next_bb).bb_instructions)` by (
    irule inst_wf_phi_well_formed >> first_assum ACCEPT_TAC) >>
  `EVERY (\inst. ~MEM (Label lbl) inst.inst_operands)
     (FILTER (\inst. inst.inst_opcode = PHI)
             (merge_blocks bb next_bb).bb_instructions)` by (
    simp[listTheory.EVERY_MEM, listTheory.MEM_FILTER] >>
    rpt strip_tac >> first_x_assum irule >> ASM_REWRITE_TAC[]) >>
  (* MEM/~MEM split for update_succ_phi_labels *)
  Cases_on `MEM lbl (bb_succs (merge_blocks bb next_bb))`
  >- (
    (* MEM: merged_bb has PHIs rewritten *)
    `lookup_block lbl (update_succ_phi_labels next_lbl lbl bbs2
       (bb_succs (merge_blocks bb next_bb))) =
     SOME ((merge_blocks bb next_bb) with bb_instructions :=
       MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst next_lbl lbl inst)
           (merge_blocks bb next_bb).bb_instructions)` by (
      irule lookup_block_uspl_in_succs >> ASM_REWRITE_TAC[]) >>
    `merged_bb = (merge_blocks bb next_bb) with bb_instructions :=
       MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst next_lbl lbl inst)
           (merge_blocks bb next_bb).bb_instructions`
      by metis_tac[optionTheory.SOME_11] >>
    (* Substitute merged_bb once, use phi_rewrite_block_wf for WF *)
    mp_tac (Q.SPECL [`next_lbl`, `lbl`, `merge_blocks bb next_bb`]
      phi_rewrite_block_wf) >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    simp_tac std_ss [LET_THM] >> strip_tac >>
    mp_tac (Q.SPECL
      [`LENGTH (merge_blocks bb next_bb).bb_instructions`,
       `n`, `ctx`, `next_lbl`, `lbl`,
       `merged_bb`, `merge_blocks bb next_bb`, `s2`, `s1`]
      run_block_prev_bb_equiv_subst) >>
    (impl_tac >- (
      ASM_REWRITE_TAC[] >> rpt conj_tac
      >- simp[venomInstTheory.basic_block_component_equality,
              listTheory.LENGTH_MAP]
      >- simp[venomInstTheory.basic_block_component_equality,
              listTheory.LENGTH_MAP]
      >> (rpt strip_tac >>
          simp[venomInstTheory.basic_block_component_equality,
               rich_listTheory.EL_MAP] >>
          BasicProvers.every_case_tac >> simp[]))) >>
    disch_tac >>
    (* Convert result_prev_bb_equiv to result_equiv {} *)
    `result_prev_bb_equiv
       (run_block n ctx (merge_blocks bb next_bb) s1)
       (run_block n ctx merged_bb s2)` by
      metis_tac[result_prev_bb_equiv_sym] >>
    mp_tac (Q.SPECL [`n`, `ctx`, `merge_blocks bb next_bb`, `merged_bb`,
                      `s1`, `s2`] result_prev_bb_equiv_wf_to_result_equiv) >>
    (impl_tac >- (
      ASM_REWRITE_TAC[] >>
      qpat_x_assum `merged_bb = _` SUBST_ALL_TAC >>
      simp[venomInstTheory.basic_block_component_equality,
           listTheory.MAP_EQ_NIL] >>
      ASM_REWRITE_TAC[])) >>
    disch_tac >>
    first_assum ACCEPT_TAC) >>
    (* ~MEM: merged_bb = merge_blocks bb next_bb *)
    `lookup_block lbl (update_succ_phi_labels next_lbl lbl bbs2
       (bb_succs (merge_blocks bb next_bb))) = lookup_block lbl bbs2` by
      metis_tac[lookup_block_update_succ_phi_not_in_succs] >>
    `merged_bb = merge_blocks bb next_bb` by metis_tac[optionTheory.SOME_11] >>
    qpat_x_assum `merged_bb = _` SUBST_ALL_TAC >>
    (* Both labels absent from merge_blocks PHIs => use identity subst *)
    `!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
       ~MEM (Label next_lbl) inst.inst_operands` by
      metis_tac[phi_label_next_lbl_absent] >>
    mp_tac (Q.SPECL [`bb`, `next_bb`,
      `\inst. ~MEM (Label next_lbl) inst.inst_operands`]
      merge_blocks_phi_operands) >>
    (impl_tac >- (ASM_REWRITE_TAC[] >> BETA_TAC >> ASM_REWRITE_TAC[])) >>
    BETA_TAC >> disch_tac >>
    `EVERY (\inst. ~MEM (Label next_lbl) inst.inst_operands)
       (FILTER (\inst. inst.inst_opcode = PHI)
               (merge_blocks bb next_bb).bb_instructions)` by (
      simp[listTheory.EVERY_MEM, listTheory.MEM_FILTER] >>
      rpt strip_tac >> first_x_assum irule >> ASM_REWRITE_TAC[]) >>
    mp_tac (Q.SPECL
      [`LENGTH (merge_blocks bb next_bb).bb_instructions`,
       `n`, `ctx`, `next_lbl`, `lbl`,
       `merge_blocks bb next_bb`, `merge_blocks bb next_bb`, `s2`, `s1`]
      run_block_prev_bb_equiv_subst) >>
    (impl_tac >- (
      ASM_REWRITE_TAC[] >>
      `next_lbl <> lbl` by metis_tac[] >>
      ASM_REWRITE_TAC[] >> rpt conj_tac
      >> (rpt strip_tac >>
          Cases_on `(EL i (merge_blocks bb next_bb).bb_instructions).inst_opcode = PHI`
          >> simp[] >>
          irule (GSYM subst_label_inst_irrelevant) >>
          metis_tac[listTheory.MEM_EL]))) >>
    disch_tac >>
    (* Convert result_prev_bb_equiv to result_equiv {} —
       merged_bb already substituted to merge_blocks bb next_bb *)
    `result_prev_bb_equiv
       (run_block n ctx (merge_blocks bb next_bb) s1)
       (run_block n ctx (merge_blocks bb next_bb) s2)` by
      metis_tac[result_prev_bb_equiv_sym] >>
    mp_tac (Q.SPECL [`n`, `ctx`, `merge_blocks bb next_bb`,
                      `merge_blocks bb next_bb`,
                      `s1`, `s2`] result_prev_bb_equiv_wf_to_result_equiv) >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    disch_tac >>
    first_assum ACCEPT_TAC
QED

(* D2: at_lbl case, prev_bb_equiv s1 s2.
   s1.vs_prev_bb = SOME next_lbl, s2.vs_prev_bb = SOME lbl.
   Strategy: bridge gives result_equiv {} for run_block merged_bb(s2) vs merge_blocks(s1).
   Then merge_equiv_gen relates merge_blocks(s1) to next_bb(v).
   Case split on results, establish merge_R, apply IH. *)
Resume merge_step_equiv_strong[D2]:
  (* D2: prev_bb_equiv s1 s2, s1.prev_bb=SOME next_lbl, s2.prev_bb=SOME lbl.
     Bridge gives result_equiv {} (run_block merge_blocks s1) (run_block merged_bb s2).
     merge_equiv_gen decomposes merge_blocks(s1) into bb(s1)+next_bb.
     Case split: OK → IH on continuation; non-OK → direct. *)
  (* Derive s1.vs_current_bb = lbl from prev_bb_equiv *)
  `s1.vs_current_bb = lbl` by (
    qpat_x_assum `prev_bb_equiv s1 s2` mp_tac >>
    simp[simplifyCfgPrevBBTheory.prev_bb_equiv_def,
         venomStateTheory.venom_state_component_equality]) >>
  (* Step 1: Apply the D2 bridge *)
  mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`,
    `merged_bb`, `n`, `ctx`, `s1`, `s2`] at_lbl_D2_bridge) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >> strip_tac >>
  (* Step 2: Apply merge_equiv_gen *)
  `bb_succs bb = [next_lbl]` by fs[can_merge_blocks_def] >>
  mp_tac (Q.SPECL [`n`, `ctx`, `bb`,
    `next_bb`, `s1`] simplifyCfgCollapseBaseTheory.run_block_merge_equiv) >>
  (impl_tac >- (ASM_REWRITE_TAC[] >> simp[])) >>
  ASM_REWRITE_TAC[] >> disch_tac >>
  (* Step 3: Case split on merged block result *)
  Cases_on `run_block n ctx (merge_blocks bb next_bb) s1`
  >- (rename1 `_ = OK w1` >> suspend "D2_OK")
  (* Non-OK: apply at_lbl_D2_nonOK helper directly *)
  >> (
    `lookup_block lbl func'.fn_blocks = SOME merged_bb` by (
      qpat_x_assum `func'.fn_blocks = _`
        (fn fneq => REWRITE_TAC[fneq]) >>
      ASM_REWRITE_TAC[]) >>
    `~s2.vs_halted` by (
      qpat_x_assum `prev_bb_equiv s1 s2` mp_tac >>
      simp[simplifyCfgPrevBBTheory.prev_bb_equiv_def,
           venomStateTheory.venom_state_component_equality]) >>
    mp_tac (Q.SPECL [`func`, `func'`, `lbl`, `next_lbl`, `bb`, `next_bb`,
      `merged_bb`, `n`, `ctx`, `s1`, `s2`] at_lbl_D2_nonOK) >>
    (impl_tac >- (
      ASM_REWRITE_TAC[] >> rpt conj_tac
      >- simp[exec_result_distinct]
      >> fs[exec_result_case_def])) >>
    strip_tac >> qexists `fuel'` >> simp[])
QED

Resume merge_step_equiv_strong[D2_OK]:
  (* OK case: bridge + merge_equiv_gen → state_equiv continuation.
     Decompose merge_blocks(s1) into bb(s1)→v_bb→next_bb(v_bb)→w_next.
     Bridge gives w1=w2. Then prev_bb_equiv(w_next,w2), merge_R DISJ2, IH. *)
  (* Step 1: Case split on bb(s1); non-OK makes merge_blocks non-OK = contradiction *)
  Cases_on `run_block n ctx bb s1` >> (
    TRY (qpat_x_assum `_ = OK w1` mp_tac >>
         mp_tac (Q.SPECL [`PRE (LENGTH bb.bb_instructions) - 0`,
           `n`, `ctx`, `bb`, `next_bb`, `s1`] run_block_merge_nonOK_same) >>
         (impl_tac >- (ASM_REWRITE_TAC[] >> fs[single_succ_jmp_def])) >>
         disch_then (fn th => REWRITE_TAC[th]) >>
         simp[exec_result_distinct] >> NO_TAC)) >>
  rename1 `run_block n ctx bb s1 = OK v_bb` >>
  (* Step 2: v_bb properties *)
  `v_bb.vs_inst_idx = 0` by metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  `v_bb with vs_inst_idx := 0 = v_bb`
    by simp[venomStateTheory.venom_state_component_equality] >>
  fs[exec_result_case_def] >>
  pop_assum (K ALL_TAC) >>
  `~v_bb.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `v_bb.vs_current_bb = next_lbl` by (
    `MEM v_bb.vs_current_bb (bb_succs bb)` by
      metis_tac[run_block_current_bb_in_succs_wf] >>
    gvs[listTheory.MEM]) >>
  (* Step 3: Case split on next_bb result; non-OK kills lift_result(OK) *)
  Cases_on `run_block n ctx next_bb v_bb` >> (
    TRY (qpat_x_assum `lift_result _ _ _ (OK _) _` mp_tac >>
         simp[stateEquivTheory.lift_result_def] >> NO_TAC)) >>
  rename1 `run_block n ctx next_bb v_bb = OK w_next` >>
  (* Step 4: Extract w2 from bridge via state_equiv_empty_eq *)
  qpat_x_assum `lift_result _ _ _ (OK _) (OK _)` mp_tac >>
  simp[stateEquivTheory.lift_result_def] >> strip_tac >>
  Cases_on `run_block n ctx merged_bb s2` >> (
    TRY (qpat_x_assum `result_equiv _ (OK _) _` mp_tac >>
         simp[stateEquivTheory.result_equiv_def] >> NO_TAC)) >>
  rename1 `run_block n ctx merged_bb s2 = OK w2` >>
  qpat_x_assum `result_equiv _ (OK _) (OK _)` mp_tac >>
  simp[stateEquivTheory.result_equiv_def] >> strip_tac >>
  (* Step 5: Derive properties BEFORE substituting w1=w2 *)
  `bb_well_formed (merge_blocks bb next_bb)` by
    metis_tac[simplifyCfgHelpersTheory.bb_well_formed_merge_blocks] >>
  `EVERY inst_wf (merge_blocks bb next_bb).bb_instructions` by (
    simp[simplifyCfgDefsTheory.merge_blocks_def, listTheory.EVERY_APPEND] >>
    Cases_on `bb.bb_instructions` >- fs[] >>
    rw[listTheory.EVERY_MEM] >> rpt strip_tac >>
    `MEM e (h::t)` by metis_tac[rich_listTheory.MEM_FRONT] >>
    fs[listTheory.EVERY_MEM]) >>
  `w1.vs_prev_bb = SOME lbl` by
    metis_tac[run_block_ok_prev_bb_wf] >>
  `w_next.vs_prev_bb = SOME next_lbl` by
    metis_tac[run_block_ok_prev_bb_wf] >>
  `w_next.vs_current_bb = w1.vs_current_bb` by (
    qpat_x_assum `prev_bb_equiv w1 w_next` mp_tac >>
    simp[simplifyCfgPrevBBTheory.prev_bb_equiv_def,
         venomStateTheory.venom_state_component_equality]) >>
  (* Substitute w1 = w2 explicitly — avoid gvs which renames lbl/next_lbl *)
  `w1 = w2` by metis_tac[state_equiv_empty_eq] >>
  qpat_x_assum `w1 = w2` SUBST_ALL_TAC >>
  `w2.vs_inst_idx = 0` by
    metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  `w_next.vs_inst_idx = 0` by
    metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  `~w_next.vs_halted` by
    metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `~w2.vs_halted` by
    metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  (* Step 6: current_bb ≠ next_lbl *)
  `w_next.vs_current_bb = w2.vs_current_bb` by (
    qpat_x_assum `prev_bb_equiv w2 w_next` mp_tac >>
    simp[simplifyCfgPrevBBTheory.prev_bb_equiv_def,
         venomStateTheory.venom_state_component_equality]) >>
  `~MEM next_lbl (bb_succs next_bb)` by (
    mp_tac (Q.SPECL [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`, `next_bb`]
      not_MEM_next_lbl_succs) >>
    ASM_REWRITE_TAC[] >> simp[]) >>
  `MEM w_next.vs_current_bb (bb_succs next_bb)` by
    metis_tac[run_block_current_bb_in_succs_wf] >>
  `w_next.vs_current_bb <> next_lbl` by metis_tac[listTheory.MEM] >>
  (* Step 7: Establish prev_bb_equiv w_next w2 and merge_R *)
  `prev_bb_equiv w_next w2` by (
    simp[simplifyCfgPrevBBTheory.prev_bb_equiv_def,
         venomStateTheory.venom_state_component_equality] >>
    qpat_x_assum `prev_bb_equiv w2 w_next` mp_tac >>
    simp[simplifyCfgPrevBBTheory.prev_bb_equiv_def,
         venomStateTheory.venom_state_component_equality]) >>
  `merge_R lbl next_lbl w_next w2` by (
    simp[merge_R_def] >> DISJ2_TAC >> ASM_REWRITE_TAC[]) >>
  (* Step 8: Apply IH *)
  markerLib.unhide_x_assum "IH" ASSUME_TAC >>
  first_x_assum (qspec_then `n` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`ctx`, `w_next`, `w2`] mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >>
  rename1 `n <= fuel_ih` >>
  (* Step 9: Witness + fuel_mono bumps *)
  qexists_tac `SUC (SUC fuel_ih)` >> conj_tac >- simp[] >>
  `run_block (SUC n) ctx merged_bb s2 = OK w2` by (
    mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
    disch_then (qspecl_then [`n`, `SUC n`, `ctx`, `merged_bb`, `s2`,
      `OK w2`] mp_tac) >>
    simp[exec_result_distinct]) >>
  `w2 with vs_inst_idx := 0 = w2`
    by simp[venomStateTheory.venom_state_component_equality] >>
  `run_block (SUC fuel_ih) ctx bb s1 = OK v_bb` by (
    mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
    disch_then (qspecl_then [`n`, `SUC fuel_ih`, `ctx`, `bb`, `s1`,
      `OK v_bb`] mp_tac) >>
    simp[exec_result_distinct]) >>
  `run_block fuel_ih ctx next_bb v_bb = OK w_next` by (
    mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
    disch_then (qspecl_then [`n`, `fuel_ih`, `ctx`, `next_bb`, `v_bb`,
      `OK w_next`] mp_tac) >>
    simp[exec_result_distinct]) >>
  `w_next with vs_inst_idx := 0 = w_next`
    by simp[venomStateTheory.venom_state_component_equality] >>
  (* Step 10: Unfold run_blocks on both sides *)
  UNFOLD_RF_STEP_TAC RAND_CONV >>
  UNFOLD_RF_STEP_TAC (RATOR_CONV o RAND_CONV) >>
  UNFOLD_RF_STEP_TAC (RATOR_CONV o RAND_CONV)
QED

Resume merge_step_equiv_strong[D2b]:
  drule_all D2b_lookup_prev_bb_equiv >>
  simp_tac std_ss [LET_THM] >>
  disch_then (qspecl_then [`n`, `ctx`] strip_assume_tac) >>
  qpat_x_assum `func'.fn_blocks = _`
    (fn fneq => ASSUME_TAC fneq >> ASSUME_TAC (GSYM fneq)) >>
  (* Fold lookup to func' *)
  qpat_x_assum `lookup_block _ (update_succ_phi_labels _ _ _ _) = SOME _`
    (fn th => qpat_assum `update_succ_phi_labels _ _ _ _ = func'.fn_blocks`
      (fn fneq => ASSUME_TAC (ONCE_REWRITE_RULE [fneq] th))) >>
  markerLib.unhide_x_assum "IH" (fn ih =>
  mp_tac (Q.SPECL [`func`, `func'`, `lbl`, `next_lbl`, `bb`, `next_bb`,
                    `cur_bb`, `cur_bb'`, `n`, `ctx`, `s1`, `s2`]
    merge_other_block_step_prev_bb) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                TRY REFL_TAC >> ACCEPT_TAC ih)) >>
  simp_tac std_ss [])
QED

Finalise merge_step_equiv_strong;

(* Original theorem: same state, prev_bb = NONE
   Uses merge_step_equiv_strong with reversed fuel direction.
   Strong gives: ∃fuel'. fuel ≤ fuel' ∧ result_equiv (rf fuel' func s) (rf fuel func' s)
   Wrapper exposes: ∃fuel1 fuel2. result_equiv (rf fuel1 func s) (rf fuel2 func' s)
*)
Theorem merge_step_equiv[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_lbl ==>
    let func' = func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)) in
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      s.vs_current_bb <> next_lbl /\
      s.vs_prev_bb = NONE /\
      ~s.vs_halted ==>
    ?fuel'. fuel <= fuel' /\
      result_equiv {}
        (run_blocks fuel' ctx func s)
        (run_blocks fuel ctx func' s)
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  rpt gen_tac >> strip_tac >>
  `merge_R lbl next_lbl s s` by
    (REWRITE_TAC[merge_R_def] >>
     DISJ1_TAC >> ASM_REWRITE_TAC[optionTheory.NOT_NONE_SOME]) >>
  qspecl_then [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`]
    mp_tac merge_step_equiv_strong >>
  ASM_REWRITE_TAC[] >>
  simp_tac std_ss [LET_THM] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
  ASM_REWRITE_TAC[]
QED

(* Entry-restricted version: entry <> next_lbl from can_merge_blocks *)
Theorem merge_step_correct[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_lbl ==>
    let func' = func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)) in
    !fuel ctx s.
      fn_entry_label func = SOME s.vs_current_bb /\
      s.vs_inst_idx = 0 /\
      s.vs_prev_bb = NONE /\
      ~s.vs_halted ==>
    ?fuel'. fuel <= fuel' /\
      result_equiv {}
        (run_blocks fuel' ctx func s)
        (run_blocks fuel ctx func' s)
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `can_merge_blocks _ _ _` (fn th =>
    mp_tac merge_step_equiv >> ASSUME_TAC th) >>
  disch_then (qspecl_then [`func`, `lbl`, `next_lbl`, `bb`, `next_bb`] mp_tac) >>
  ASM_REWRITE_TAC[] >>
  simp_tac std_ss [LET_THM] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  impl_tac
  >- (ASM_REWRITE_TAC[] >>
      PURE_REWRITE_TAC[can_merge_blocks_def] >>
      qpat_x_assum `can_merge_blocks _ _ _`
        (ASSUME_TAC o PURE_REWRITE_RULE [can_merge_blocks_def]) >>
      `next_bb.bb_label = next_lbl` by
        (imp_res_tac lookup_block_label >> ASM_REWRITE_TAC[]) >>
      CCONTR_TAC >> gvs[])
  >> REWRITE_TAC[]
QED

(* ================================================================
   Section 3: try_bypass preserves run_blocks semantics
   ================================================================ *)

(* --- PHI bypass helpers --- *)

(* Well-formed PHI resolves to Var (never Lit or Label) *)
Theorem phi_wf_resolve_is_Var[local]:
  !ops c x. phi_well_formed ops /\ resolve_phi c ops = SOME x ==>
    ?v. x = Var v
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  rw[resolve_phi_def, phi_well_formed_def] >>
  Cases_on `lbl = c` >> gvs[] >> metis_tac[]
QED

(* Case 2: a not in ops, relabel b→a. resolve_phi a on relabeled = resolve_phi b on original *)
Theorem resolve_phi_relabel_b_to_a[local]:
  !ops a b.
    a <> b /\ ~MEM (Label a) ops /\ phi_well_formed ops ==>
    resolve_phi a (MAP (\op. case op of
        Label l => if l = b then Label a else Label l
      | _ => op) ops) = resolve_phi b ops
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  rw[resolve_phi_def, phi_well_formed_def, listTheory.MEM] >>
  Cases_on `lbl = b` >> gvs[resolve_phi_def]
QED

(* Core PHI bypass lemma: after update_phi_bypass a b, resolving with prev_bb=a
   gives the same result as resolving with prev_bb=b on the original operands.
   Case 1 (a present and resolves): phi_values_agree ensures same value.
   Case 2 (a absent): relabeling b→a makes a find b's value.
   Extra case (a present but doesn't resolve): stays NONE after update. *)
Theorem resolve_phi_update_bypass[local]:
  !a b inst.
    a <> b /\ inst.inst_opcode = PHI /\
    phi_well_formed inst.inst_operands /\
    (case (resolve_phi a inst.inst_operands, resolve_phi b inst.inst_operands) of
       (SOME va, SOME vb) => va = vb
     | _ => T) ==>
    resolve_phi a (update_phi_bypass a b inst).inst_operands =
    (if MEM (Label a) inst.inst_operands
     then resolve_phi a inst.inst_operands
     else resolve_phi b inst.inst_operands)
Proof
  rw[update_phi_bypass_def, LET_THM] >>
  simp[cfgTransformProofsTheory.resolve_phi_remove_other,
       resolve_phi_relabel_b_to_a]
QED

(* Other predecessors (c ≠ a, c ≠ b) unaffected by update_phi_bypass *)
Theorem resolve_phi_update_bypass_other[local]:
  !a b c inst.
    c <> a /\ c <> b /\ inst.inst_opcode = PHI /\
    phi_well_formed inst.inst_operands ==>
    resolve_phi c (update_phi_bypass a b inst).inst_operands =
    resolve_phi c inst.inst_operands
Proof
  rw[update_phi_bypass_def, LET_THM] >>
  simp[cfgTransformProofsTheory.resolve_phi_remove_other] >>
  (* Case 2: relabel b→a is just subst_label_op b a *)
  `MAP (\op. case op of Label l => if l = b then Label a else Label l | _ => op)
       inst.inst_operands =
   MAP (subst_label_op b a) inst.inst_operands` by (
    irule listTheory.MAP_CONG >> rw[] >> Cases_on `x` >>
    simp[cfgTransformTheory.subst_label_op_def]) >>
  pop_assum (fn eq => REWRITE_TAC[eq]) >>
  mp_tac (Q.SPECL [`b`, `a`, `c`] cfgTransformProofsTheory.resolve_phi_subst_other) >>
  ASM_REWRITE_TAC[] >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  Cases_on `resolve_phi c inst.inst_operands` >>
  simp[optionTheory.OPTION_MAP_DEF] >>
  imp_res_tac phi_wf_resolve_is_Var >>
  gvs[cfgTransformTheory.subst_label_op_def]
QED

(* ---- PHI update_phi_bypass step-level helpers ---- *)

Triviality update_phi_bypass_opcode[simp]:
  (update_phi_bypass a b inst).inst_opcode = inst.inst_opcode
Proof
  rw[update_phi_bypass_def]
QED

(* Extract per-instruction fact from phi_values_agree *)
(* phi_values_agree extracts per-instruction fact for PHIs.
   Requires PHIs-first ordering (the last conjunct of bb_well_formed). *)
Triviality phi_values_agree_EL:
  !a b insts k.
    phi_values_agree a b insts /\ k < LENGTH insts /\
    (EL k insts).inst_opcode = PHI /\
    (!i j. i < j /\ j < LENGTH insts /\
           (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI) ==>
    case (resolve_phi a (EL k insts).inst_operands,
          resolve_phi b (EL k insts).inst_operands) of
      (SOME va, SOME vb) => va = vb
    | _ => T
Proof
  Induct_on `insts` >> rw[phi_values_agree_def] >>
  Cases_on `k`
  >- (
    (* k = 0: EL 0 = h, h is PHI *)
    gvs[LET_THM] >> BasicProvers.every_case_tac >> gvs[])
  >> rename1 `SUC k'` >>
  (* k > 0: h must also be PHI (PHIs-first) *)
  `h.inst_opcode = PHI` by (
    first_x_assum (qspecl_then [`0`, `SUC k'`] mp_tac) >> simp[]) >>
  (* Derive PHIs-first for tail *)
  `!i j. i < j /\ j < LENGTH insts /\
         (EL j insts).inst_opcode = PHI ==>
         (EL i insts).inst_opcode = PHI` by (
    rpt strip_tac >>
    first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
    simp[rich_listTheory.EL]) >>
  gvs[LET_THM] >>
  BasicProvers.every_case_tac >> gvs[] >>
  (* Use IH *)
  first_x_assum (qspecl_then [`a`, `b`, `k'`] mp_tac) >>
  ASM_REWRITE_TAC[] >> simp[]
QED

(* NOTE: phi_wf_MEM_resolve_SOME was FALSE.
   Counterexample: phi_well_formed [Label "x"] = T, MEM (Label "x") = T,
   but resolve_phi "x" [Label "x"] = NONE (singleton, no value pair).
   The proof of step_phi_update_bypass_prev_bb_equiv handles NONE cases directly. *)

(* D1 step: update_phi_bypass preserves step result when prev_bb ≠ b.
   Why: PHI resolves via prev_bb. Since prev_bb ≠ b, the b-branch (the only one
   changed by update_phi_bypass) is never used. The resolution is identical. *)
Triviality step_phi_update_bypass_eq:
  !fuel ctx inst s a b.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    s.vs_prev_bb <> SOME b /\
    (s.vs_prev_bb = SOME a ==> MEM (Label a) inst.inst_operands) /\
    (case (resolve_phi a inst.inst_operands, resolve_phi b inst.inst_operands) of
       (SOME va, SOME vb) => va = vb | _ => T) ==>
    step_inst fuel ctx (update_phi_bypass a b inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `phi_well_formed inst.inst_operands` by
    (irule phi_operands_wf_implies_phi_well_formed >>
     qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `inst.inst_opcode <> INVOKE` by (gvs[] >> EVAL_TAC) >>
  (* Reduce both sides to step_inst_base using mp_tac *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`]
    venomExecSemanticsTheory.step_inst_non_invoke) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `update_phi_bypass a b inst`, `s`]
    venomExecSemanticsTheory.step_inst_non_invoke) >>
  (impl_tac >- simp[update_phi_bypass_def]) >> DISCH_TAC >>
  ASM_REWRITE_TAC[] >>
  (* Now: step_inst_base (update_phi_bypass a b inst) s = step_inst_base inst s *)
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[] >>
  `(update_phi_bypass a b inst).inst_outputs = inst.inst_outputs` by
    (rw[update_phi_bypass_def, LET_THM]) >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `s.vs_prev_bb` >> gvs[] >>
  rename1 `s.vs_prev_bb = SOME prev` >>
  Cases_on `prev = a` >> gvs[]
  >- ((* prev = a: use resolve_phi_update_bypass *)
    `MEM (Label a) inst.inst_operands` by gvs[] >>
    mp_tac (Q.SPECL [`a`, `b`, `inst`] resolve_phi_update_bypass) >>
    simp[] >> disch_tac >> gvs[])
  >- ((* prev ≠ a, prev ≠ b: use resolve_phi_update_bypass_other *)
    `resolve_phi prev (update_phi_bypass a b inst).inst_operands =
     resolve_phi prev inst.inst_operands` by
      (irule resolve_phi_update_bypass_other >> simp[]) >>
    simp[])
QED


(* eval_operand only reads vs_vars and vs_labels, not vs_prev_bb *)
Triviality eval_operand_prev_bb_irrel:
  !op s pb. eval_operand op (s with vs_prev_bb := pb) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

(* D2 step: update_phi_bypass + prev_bb swap gives result_prev_bb_equiv.
   Why: s1.prev_bb = SOME b resolves original PHI via b. s2.prev_bb = SOME a
   resolves modified PHI via a (update_phi_bypass removes b, keeps a). Both
   resolve to the same operand v. eval_operand doesn't depend on vs_prev_bb,
   so update_var produces prev_bb_equiv results. *)
(* Generalized: takes resolve_phi results directly, no MEM (Label a) needed *)
Triviality step_phi_update_bypass_prev_bb_equiv:
  !fuel ctx inst s1 s2 a b v.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME b /\ s2.vs_prev_bb = SOME a /\
    resolve_phi b inst.inst_operands = SOME v /\
    resolve_phi a (update_phi_bypass a b inst).inst_operands = SOME v ==>
    result_prev_bb_equiv
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx (update_phi_bypass a b inst) s2)
Proof
  rpt strip_tac >>
  `s2 = s1 with vs_prev_bb := SOME a` by
    fs[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  `inst.inst_opcode <> INVOKE` by (CCONTR_TAC >> gvs[]) >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s1`]
    venomExecSemanticsTheory.step_inst_non_invoke) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >> disch_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `update_phi_bypass a b inst`,
    `s1 with vs_prev_bb := SOME a`]
    venomExecSemanticsTheory.step_inst_non_invoke) >>
  (impl_tac >- simp[update_phi_bypass_def]) >> disch_tac >>
  ASM_REWRITE_TAC[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[] >>
  `(update_phi_bypass a b inst).inst_outputs = inst.inst_outputs` by
    (rw[update_phi_bypass_def, LET_THM]) >>
  Cases_on `inst.inst_outputs` >> gvs[result_prev_bb_equiv_def] >>
  Cases_on `t` >> gvs[result_prev_bb_equiv_def] >>
  gvs[eval_operand_prev_bb_irrel] >>
  Cases_on `eval_operand v s1` >> gvs[result_prev_bb_equiv_def] >>
  simp[result_prev_bb_equiv_def, prev_bb_equiv_def,
       update_var_def, venomStateTheory.venom_state_component_equality]
QED

(* Strengthened fn_phi_preds_complete: for each predecessor, resolve_phi succeeds.
   This is stronger than fn_phi_preds_complete (which only gives MEM).
   Needed because MEM (Label lbl) ops does not imply resolve_phi lbl ops = SOME _
   when the Label is at a value position (odd index) rather than a label position.
   Trivially true for real compiler PHIs where labels are at even positions. *)
Definition fn_phi_resolve_complete_def:
  fn_phi_resolve_complete func <=>
    !bb inst lbl.
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI /\
      MEM lbl (pred_labels func bb.bb_label) ==>
      ?v. resolve_phi lbl inst.inst_operands = SOME v
End

(* resolve_phi SOME implies MEM (Label lbl) *)
Triviality resolve_phi_SOME_MEM_Label:
  !lbl ops v. resolve_phi lbl ops = SOME v ==> MEM (Label lbl) ops
Proof
  ho_match_mp_tac venomExecSemanticsTheory.resolve_phi_ind >>
  rw[venomExecSemanticsTheory.resolve_phi_def]
QED

(* fn_phi_resolve_complete implies fn_phi_preds_complete *)
Triviality fn_phi_resolve_implies_complete:
  !func. fn_phi_resolve_complete func ==> fn_phi_preds_complete func
Proof
  rw[fn_phi_resolve_complete_def, fn_phi_preds_complete_def] >>
  res_tac >> metis_tac[resolve_phi_SOME_MEM_Label]
QED

(* phi_values_agree + both resolve_phi SOME ==> equal values *)
(* phi_values_agree + both resolve_phi SOME + PHIs-first ⇒ equal values.
   Uses phi_values_agree_EL (already proved) via MEM → EL conversion. *)
Triviality phi_values_agree_resolve_eq:
  !a b insts inst va vb.
    phi_values_agree a b insts /\ MEM inst insts /\
    inst.inst_opcode = PHI /\
    resolve_phi a inst.inst_operands = SOME va /\
    resolve_phi b inst.inst_operands = SOME vb /\
    (* PHIs-first: bb_well_formed guarantees this *)
    (!i j. i < j /\ j < LENGTH insts /\
           (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI) ==>
    va = vb
Proof
  rpt strip_tac >>
  imp_res_tac listTheory.MEM_EL >> rename1 `EL k insts` >>
  mp_tac (Q.SPECL [`a`, `b`, `insts`, `k`] phi_values_agree_EL) >>
  (impl_tac >- (
    qpat_x_assum `inst = _` (SUBST_ALL_TAC) >>
    ASM_REWRITE_TAC[])) >>
  qpat_x_assum `inst = _` (SUBST_ALL_TAC) >>
  ASM_REWRITE_TAC[] >> simp[]
QED

(* D2 step for PHI: handles both MEM (Label a) and ¬MEM (Label a) cases.
   Key insight: when ¬MEM (Label a), update_phi_bypass relabels b→a, so
   resolve_phi a (modified) = resolve_phi b (original) — both sides same.
   When MEM (Label a), fn_phi_preds_wf gives a ∈ pred_labels, then
   fn_phi_resolve_complete guarantees both resolve_phi a and b succeed. *)
(* Case A helper: MEM (Label a) ⇒ both resolve, equal values ⇒ delegate *)
Triviality step_phi_update_bypass_D2_MEM:
  !fuel ctx inst s1 s2 a b func bb.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME b /\ s2.vs_prev_bb = SOME a /\
    a <> b /\
    MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    MEM (Label a) inst.inst_operands /\
    fn_phi_preds_wf func /\
    fn_phi_resolve_complete func /\
    MEM b (pred_labels func bb.bb_label) /\
    phi_values_agree a b bb.bb_instructions /\
    (* PHIs-first ordering: from bb_well_formed *)
    (!i j. i < j /\ j < LENGTH bb.bb_instructions /\
           (EL j bb.bb_instructions).inst_opcode = PHI ==>
           (EL i bb.bb_instructions).inst_opcode = PHI) ==>
    result_prev_bb_equiv
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx (update_phi_bypass a b inst) s2)
Proof
  rpt strip_tac >>
  `phi_well_formed inst.inst_operands` by
    (irule phi_operands_wf_implies_phi_well_formed >> gvs[inst_wf_def]) >>
  (* derive a ∈ pred_labels from fn_phi_preds_wf *)
  qpat_assum `fn_phi_preds_wf _`
    (mp_tac o REWRITE_RULE[fn_phi_preds_wf_def]) >>
  disch_then (qspecl_then [`bb`, `inst`, `a`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  (* resolve_phi a on original succeeds *)
  qpat_assum `fn_phi_resolve_complete _`
    (mp_tac o REWRITE_RULE[fn_phi_resolve_complete_def]) >>
  disch_then (qspecl_then [`bb`, `inst`, `a`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> rename1 `resolve_phi a inst.inst_operands = SOME va` >>
  (* resolve_phi b succeeds *)
  qpat_assum `fn_phi_resolve_complete _`
    (mp_tac o REWRITE_RULE[fn_phi_resolve_complete_def]) >>
  disch_then (qspecl_then [`bb`, `inst`, `b`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> rename1 `resolve_phi b _ = SOME vb` >>
  (* phi_values_agree gives va = vb *)
  mp_tac (Q.SPECL [`a`, `b`, `bb.bb_instructions`, `inst`, `va`, `vb`]
    phi_values_agree_resolve_eq) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_tac >> gvs[] >>
  (* resolve_phi a on modified ops: MEM case → remove b, a stays *)
  `resolve_phi a (update_phi_bypass a b inst).inst_operands = SOME va` by (
    mp_tac (Q.SPECL [`a`, `b`, `inst`] resolve_phi_update_bypass) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      ASM_REWRITE_TAC[] >> simp[])) >>
    ASM_REWRITE_TAC[]) >>
  (* delegate to generalized helper *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s1`, `s2`, `a`, `b`, `va`]
    step_phi_update_bypass_prev_bb_equiv) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  REWRITE_TAC[]
QED

(* PHI + LENGTH outputs = 1 + SOME prev + resolve_phi NONE → step_inst = Error *)
(* PHI step is now a no-op in step_inst_base (eval_phis handles PHI resolution).
   step_inst for PHI always gives OK s. *)
(* step_phi_OK removed: FALSE in new semantics where PHI does resolve_phi *)

(* Case B helper: ¬MEM (Label a) ⇒ relabel b→a, both resolve same way *)
Triviality step_phi_update_bypass_D2_noMEM:
  !fuel ctx inst s1 s2 a b.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME b /\ s2.vs_prev_bb = SOME a /\
    a <> b /\
    ~MEM (Label a) inst.inst_operands ==>
    result_prev_bb_equiv
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx (update_phi_bypass a b inst) s2)
Proof
  rpt strip_tac >>
  (* Extract phi_well_formed and LENGTH outputs from inst_wf
     gvs needed for case reduction; by-clause scopes the destruction *)
  `phi_well_formed inst.inst_operands` by
    (irule phi_operands_wf_implies_phi_well_formed >> gvs[inst_wf_def]) >>
  `LENGTH inst.inst_outputs = 1` by gvs[inst_wf_def] >>
  (* Key: resolve_phi a (modified) = resolve_phi b (original) *)
  `resolve_phi a (update_phi_bypass a b inst).inst_operands =
   resolve_phi b inst.inst_operands` by (
    simp[update_phi_bypass_def, LET_THM] >>
    irule resolve_phi_relabel_b_to_a >> ASM_REWRITE_TAC[]) >>
  Cases_on `resolve_phi b inst.inst_operands`
  >- (
    (* NONE: both sides produce Error "phi: no matching predecessor" *)
    `s2 = s1 with vs_prev_bb := SOME a` by
      fs[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality] >>
    `inst.inst_opcode <> INVOKE` by (CCONTR_TAC >> gvs[]) >>
    `(update_phi_bypass a b inst).inst_opcode <> INVOKE` by
      simp[update_phi_bypass_def] >>
    rw[step_inst_non_invoke] >>
    PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[] >>
    `(update_phi_bypass a b inst).inst_outputs = inst.inst_outputs` by
      (rw[update_phi_bypass_def, LET_THM]) >>
    Cases_on `inst.inst_outputs` >> gvs[result_prev_bb_equiv_def] >>
    Cases_on `t` >> gvs[result_prev_bb_equiv_def])
  >> rename1 `SOME val_op` >>
  (* SOME: delegate to generalized prev_bb_equiv helper *)
  gvs[] >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s1`, `s2`, `a`, `b`, `val_op`]
    step_phi_update_bypass_prev_bb_equiv) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  REWRITE_TAC[]
QED

(* Combined D2 step: dispatches to MEM/noMEM cases *)
Triviality step_phi_update_bypass_D2:
  !fuel ctx inst s1 s2 a b func bb.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME b /\ s2.vs_prev_bb = SOME a /\
    a <> b /\
    MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    fn_phi_preds_wf func /\
    fn_phi_resolve_complete func /\
    MEM b (pred_labels func bb.bb_label) /\
    phi_values_agree a b bb.bb_instructions /\
    (* PHIs-first ordering: from bb_well_formed *)
    (!i j. i < j /\ j < LENGTH bb.bb_instructions /\
           (EL j bb.bb_instructions).inst_opcode = PHI ==>
           (EL i bb.bb_instructions).inst_opcode = PHI) ==>
    result_prev_bb_equiv
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx (update_phi_bypass a b inst) s2)
Proof
  rpt strip_tac >>
  Cases_on `MEM (Label a) inst.inst_operands`
  >- metis_tac[step_phi_update_bypass_D2_MEM]
  >> metis_tac[step_phi_update_bypass_D2_noMEM]
QED

(* ---- do_merge_jump correctness ---- *)

(* If b_lbl has exactly one predecessor (num_preds = 1) and a is that
   predecessor, then no other block in func has b_lbl in its successors. *)
Triviality sole_pred_no_other_succ:
  !func a b_lbl cur_bb.
    num_preds func b_lbl = 1 /\
    MEM b_lbl (bb_succs a) /\ MEM a func.fn_blocks /\
    MEM cur_bb func.fn_blocks /\ cur_bb.bb_label <> a.bb_label /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) ==>
    ~MEM b_lbl (bb_succs cur_bb)
Proof
  rw[num_preds_def, block_preds_def] >>
  fs[listTheory.LENGTH_EQ_1] >> rename1 `_ = [only_pred]` >>
  `MEM a (FILTER (\bb. MEM b_lbl (bb_succs bb)) func.fn_blocks)` by
    simp[listTheory.MEM_FILTER] >>
  `a = only_pred` by (fs[listTheory.MEM] >> gvs[]) >>
  spose_not_then strip_assume_tac >>
  `MEM cur_bb (FILTER (\bb. MEM b_lbl (bb_succs bb)) func.fn_blocks)` by
    simp[listTheory.MEM_FILTER] >>
  `cur_bb = only_pred` by (fs[listTheory.MEM] >> gvs[]) >>
  gvs[]
QED

(* Lookup in the bypass-transformed function: if lbl is none of a, target, b,
   then lookup is unchanged. Reusable across other_block, at_a, at_target. *)
Triviality lookup_block_bypass_other:
  !lbl a_lbl t_lbl b_lbl a' t' bbs.
    lbl <> a_lbl /\ lbl <> t_lbl /\ lbl <> b_lbl /\
    a'.bb_label = a_lbl /\ t'.bb_label = t_lbl ==>
    lookup_block lbl
      (replace_block a_lbl a'
        (replace_block t_lbl t' (remove_block b_lbl bbs))) =
    lookup_block lbl bbs
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`lbl`, `a_lbl`, `a'`,
    `replace_block t_lbl t' (remove_block b_lbl bbs)`]
    cfgTransformPropsTheory.lookup_block_replace_neq) >>
  mp_tac (Q.SPECL [`lbl`, `t_lbl`, `t'`,
    `remove_block b_lbl bbs`]
    cfgTransformPropsTheory.lookup_block_replace_neq) >>
  mp_tac (Q.SPECL [`lbl`, `b_lbl`, `bbs`]
    cfgTransformPropsTheory.lookup_block_remove_neq) >>
  ASM_REWRITE_TAC[] >> simp[]
QED

Triviality lookup_block_bypass_full:
  !a_lbl t_lbl b_lbl a' t' bbs.
    a'.bb_label = a_lbl /\ t'.bb_label = t_lbl /\
    a_lbl <> t_lbl /\ a_lbl <> b_lbl /\ t_lbl <> b_lbl /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    (?bb. lookup_block a_lbl bbs = SOME bb) /\
    (?bb. lookup_block t_lbl bbs = SOME bb) ==>
    lookup_block a_lbl
      (replace_block a_lbl a'
        (replace_block t_lbl t' (remove_block b_lbl bbs))) = SOME a' /\
    lookup_block t_lbl
      (replace_block a_lbl a'
        (replace_block t_lbl t' (remove_block b_lbl bbs))) = SOME t' /\
    lookup_block b_lbl
      (replace_block a_lbl a'
        (replace_block t_lbl t' (remove_block b_lbl bbs))) = NONE /\
    (!lbl. lbl <> a_lbl /\ lbl <> t_lbl /\ lbl <> b_lbl ==>
           lookup_block lbl
             (replace_block a_lbl a'
               (replace_block t_lbl t' (remove_block b_lbl bbs))) =
           lookup_block lbl bbs)
Proof
  rpt strip_tac >>
  simp[cfgTransformPropsTheory.lookup_block_replace_eq,
       cfgTransformPropsTheory.lookup_block_replace_neq,
       cfgTransformPropsTheory.lookup_block_remove_eq,
       cfgTransformPropsTheory.lookup_block_remove_neq]
QED

(* prev_bb is a valid predecessor of current_bb.
   Invariant preserved by execution: after run_block OK,
   prev_bb = SOME current_bb and current_bb ∈ succs(lookup current_bb). *)
Definition prev_bb_valid_def:
  prev_bb_valid func s <=>
    !lbl. s.vs_prev_bb = SOME lbl ==>
      MEM lbl (pred_labels func s.vs_current_bb)
End

(* State relation for bypass: either states agree, or prev_bb differs
   (original has b_label, transformed has a_label = bb.bb_label). *)
Definition bypass_R_def:
  bypass_R a_lbl b_lbl target_lbl s1 s2 <=>
    (s1 = s2 /\ s1.vs_prev_bb <> SOME b_lbl) \/
    (prev_bb_equiv s1 s2 /\
     s1.vs_prev_bb = SOME b_lbl /\ s2.vs_prev_bb = SOME a_lbl /\
     s1.vs_current_bb = target_lbl)
End

(* prev_bb_valid is preserved by run_block OK *)
Triviality prev_bb_valid_preserved:
  !func fuel ctx cur_bb s v.
    wf_function func /\ fn_inst_wf func /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME cur_bb /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx cur_bb s = OK v ==>
    prev_bb_valid func v
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func`, `s.vs_current_bb`, `cur_bb`]
    lookup_block_wf_facts) >>
  (impl_tac >- fs[]) >> strip_tac >>
  `v.vs_prev_bb = SOME s.vs_current_bb` by
    metis_tac[run_block_ok_prev_bb_wf] >>
  `MEM v.vs_current_bb (bb_succs cur_bb)` by
    metis_tac[run_block_current_bb_in_succs_wf] >>
  `MEM cur_bb func.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  simp[prev_bb_valid_def] >> rpt strip_tac >> gvs[] >>
  simp[cfgTransformTheory.pred_labels_def,
       cfgTransformTheory.block_preds_def,
       listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  qexists_tac `cur_bb` >> simp[]
QED

(* prev_bb_valid is trivially true for NONE prev_bb *)
Triviality prev_bb_valid_NONE:
  !func s. s.vs_prev_bb = NONE ==> prev_bb_valid func s
Proof
  simp[prev_bb_valid_def]
QED

(* remove_phi_label is identity when lbl doesn't appear *)
Triviality remove_phi_label_noop[local]:
  !lbl ops. ~MEM (Label lbl) ops ==> remove_phi_label lbl ops = ops
Proof
  ho_match_mp_tac cfgTransformTheory.remove_phi_label_ind >>
  rw[remove_phi_label_def]
QED

(* update_phi_bypass is identity when b_lbl doesn't appear in operands *)
Triviality update_phi_bypass_no_b_lbl[local]:
  !a_lbl b_lbl inst.
    ~MEM (Label b_lbl) inst.inst_operands ==>
    update_phi_bypass a_lbl b_lbl inst = inst
Proof
  rpt strip_tac >>
  simp[update_phi_bypass_def] >>
  rw[]
  >- simp[remove_phi_label_noop, instruction_component_equality]
  >> (simp[instruction_component_equality] >>
      irule MAP_ID_ON >> rpt strip_tac >>
      Cases_on `x` >> simp[] >> IF_CASES_TAC >> gvs[])
QED

(* MAP update_phi_bypass is identity on a-block instructions when
   b is not a predecessor of a (b_lbl not in any PHI operand of a). *)
Triviality MAP_upb_cs_a_identity[local]:
  !func a b target_lbl f.
    wf_function func /\
    fn_phi_preds_wf func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    bb_succs b = [target_lbl] /\
    a.bb_label <> target_lbl /\
    (!inst. MEM inst a.bb_instructions /\ inst.inst_opcode = PHI ==>
            f inst = inst) /\
    (!inst. MEM inst a.bb_instructions ==>
            (f inst).inst_opcode = inst.inst_opcode) ==>
    MAP (update_phi_bypass a.bb_label b.bb_label) (MAP f a.bb_instructions) =
        MAP f a.bb_instructions
Proof
  rpt strip_tac >>
  irule MAP_ID_ON >> rpt strip_tac >>
  gvs[listTheory.MEM_MAP] >> rename1 `MEM inst a.bb_instructions` >>
  Cases_on `inst.inst_opcode = PHI`
  >- (`f inst = inst` by metis_tac[] >> gvs[] >>
      irule update_phi_bypass_no_b_lbl >>
      CCONTR_TAC >> gvs[] >>
      suspend "phi_case")
  >> (`(f inst).inst_opcode <> PHI` by metis_tac[] >>
      simp[update_phi_bypass_def])
QED

Resume MAP_upb_cs_a_identity[phi_case]:
  (* b is not a predecessor of a: bb_succs b = [target_lbl] ≠ a.bb_label *)
  `~MEM a.bb_label (bb_succs b)` by gvs[] >>
  `ALL_DISTINCT (MAP (\blk. blk.bb_label) func.fn_blocks)` by
    fs[wf_function_def, venomInstTheory.fn_labels_def] >>
  `~MEM b.bb_label (pred_labels func a.bb_label)` by
    (suspend "not_mem_pred") >>
  (* But fn_phi_preds_wf says Label b.bb_label in PHI operands implies b ∈ preds *)
  fs[fn_phi_preds_wf_def] >> res_tac
QED

Resume MAP_upb_cs_a_identity[not_mem_pred]:
  rw[pred_labels_def, block_preds_def,
     listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  rename1 `_ \/ ~MEM bb' _` >>
  Cases_on `MEM bb' func.fn_blocks` >> simp[] >>
  `lookup_block bb'.bb_label func.fn_blocks = SOME bb'` by
    metis_tac[MEM_lookup_block] >>
  `bb' = b` by
    (`bb'.bb_label = b.bb_label` by metis_tac[] >>
     `lookup_block bb'.bb_label func.fn_blocks = SOME b` by
       metis_tac[MEM_lookup_block] >>
     rfs[]) >>
  rw[]
QED

Finalise MAP_upb_cs_a_identity

(* When do_merge_jump succeeds, it preserves execution semantics.
   Strong version: relates states via bypass_R with fuel offset. *)
Theorem do_merge_jump_equiv_strong[local]:
  !func a b label_map func' lm' target_lbl target.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\
    fn_phi_preds_complete func /\
    fn_phi_resolve_complete func /\
    fn_bypass_safe func /\
    MEM a func.fn_blocks /\
    MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    bb_succs b = [target_lbl] /\
    lookup_block target_lbl func.fn_blocks = SOME target /\
    phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
    do_merge_jump func a b label_map = SOME (func', lm') /\
    a.bb_label <> b.bb_label /\
    a.bb_label <> target_lbl /\
    b.bb_label <> target_lbl ==>
    !fuel ctx s1 s2.
      bypass_R a.bb_label b.bb_label target_lbl s1 s2 /\
      prev_bb_valid func s1 /\
      s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
      ~s1.vs_halted /\ ~s2.vs_halted /\
      s1.vs_current_bb <> b.bb_label ==>
    ?fuel'.
      fuel <= fuel' /\
      result_equiv {}
        (run_blocks fuel' ctx func s1)
        (run_blocks fuel ctx func' s2)
Proof
  rpt gen_tac >> strip_tac >>
  (* Derive func' structure from do_merge_jump *)
  qpat_x_assum `do_merge_jump _ _ _ _ = _` mp_tac >>
  simp[do_merge_jump_def] >>
  strip_tac >> gvs[] >>
  (* Simplify: MAP upb on a-block is identity (b not a pred of a) *)
  `MAP (update_phi_bypass a.bb_label b.bb_label)
       (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                    else subst_label_inst b.bb_label target_lbl inst)
            a.bb_instructions) =
   MAP (\inst. if ~is_terminator inst.inst_opcode then inst
               else subst_label_inst b.bb_label target_lbl inst)
       a.bb_instructions` by (
    match_mp_tac MAP_upb_cs_a_identity >>
    qexistsl [`func`, `target_lbl`] >>
    simp[is_terminator_def, subst_label_inst_fields] >>
    rpt strip_tac >> IF_CASES_TAC >>
    simp[subst_label_inst_fields]) >>
  gvs[] >>
  (* Name the modified blocks *)
  qabbrev_tac `a' = a with bb_instructions :=
    MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                else subst_label_inst b.bb_label target_lbl inst)
      a.bb_instructions` >>
  qabbrev_tac `target' = target with bb_instructions :=
    MAP (update_phi_bypass a.bb_label b.bb_label)
      target.bb_instructions` >>
  (* Derive key facts *)
  `a'.bb_label = a.bb_label` by (qunabbrev_tac `a'` >> simp[]) >>
  `target'.bb_label = target.bb_label` by (qunabbrev_tac `target'` >> simp[]) >>
  `target.bb_label = target_lbl` by (
    imp_res_tac venomExecPropsTheory.lookup_block_label) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks)` by
    fs[wf_function_def, venomInstTheory.fn_labels_def] >>
  `lookup_block a.bb_label func.fn_blocks = SOME a` by
    metis_tac[venomExecPropsTheory.MEM_lookup_block] >>
  `lookup_block b.bb_label func.fn_blocks = SOME b` by
    metis_tac[venomExecPropsTheory.MEM_lookup_block] >>
  (* Main induction *)
  completeInduct_on `fuel` >>
  rpt gen_tac >> strip_tac >>
  (* bypass_R with target_lbl constraint: D2 implies current_bb=target_lbl,
     so in the other_block case, s1=s2 *)
  `s1.vs_current_bb = s2.vs_current_bb` by (
    fs[bypass_R_def, prev_bb_equiv_def,
       venomStateTheory.venom_state_component_equality]) >>
  Cases_on `fuel`
  >- ((* fuel = 0: both timeout *)
      qexists_tac `0` >>
      REWRITE_TAC[arithmeticTheory.LESS_EQ_REFL] >>
      CONV_TAC (RATOR_CONV (RAND_CONV UNFOLD_RF_CONV)) >>
      CONV_TAC (RAND_CONV UNFOLD_RF_CONV) >>
      REWRITE_TAC[stateEquivTheory.result_equiv_def]) >>
  rename1 `SUC n` >>
  Cases_on `s1.vs_current_bb = a.bb_label`
  >- suspend "at_a"
  >> Cases_on `s1.vs_current_bb = target_lbl`
  >- suspend "at_target"
  >> (* other_block: bypass_R D2 impossible (needs current_bb = target_lbl),
        so s1 = s2 *)
  `s1 = s2` by (
    fs[bypass_R_def] >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >>
  suspend "other_block"
QED

(* Helper: "same-block" simulation step.
   If lookup_block in func' = lookup_block in func at current_bb,
   and the IH gives simulation for all recursive calls at fuel < n,
   then simulation holds at fuel SUC n. *)
(* Same-block simulation: if func and func' agree on the current block's
   lookup, and IH gives simulation at lower fuel, then one step simulates. *)
(* Parameterized same-block simulation step.
   P is a state predicate preserved by block execution.
   If P holds, both sides look up the same block, and the IH applies
   to the successor state (which also satisfies P), then we get
   simulation at SUC n. *)
Triviality same_block_sim_step:
  !P func func' n ctx s.
    wf_function func /\ fn_inst_wf func /\ P s /\
    lookup_block s.vs_current_bb func'.fn_blocks =
      lookup_block s.vs_current_bb func.fn_blocks /\
    (* P is preserved by block execution (OK case) *)
    (!cur_bb v. lookup_block s.vs_current_bb func.fn_blocks = SOME cur_bb /\
       run_block n ctx cur_bb s = OK v ==> P v) /\
    (!m ctx' v.
       m <= n /\ P v /\
       v.vs_inst_idx = 0 /\ ~v.vs_halted ==>
       ?fuel'.
         m <= fuel' /\
         result_equiv {}
           (run_blocks fuel' ctx' func v)
           (run_blocks m ctx' func' v)) ==>
    ?fuel'.
      SUC n <= fuel' /\
      result_equiv {}
        (run_blocks fuel' ctx func s)
        (run_blocks (SUC n) ctx func' s)
Proof
  rpt strip_tac >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks`
  >- ((* NONE: both sides Error *)
      qexists_tac `SUC n` >>
      simp[Once run_blocks_def, GSYM run_block_def] >>
      simp[Once run_blocks_def, GSYM run_block_def, result_equiv_def])
  >> rename1 `_ = SOME cur_bb` >>
  `MEM cur_bb func.fn_blocks /\ bb_well_formed cur_bb /\
   cur_bb.bb_instructions <> [] /\ EVERY inst_wf cur_bb.bb_instructions /\
   cur_bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_wf_facts] >>
  Cases_on `run_block n ctx cur_bb s`
  >- (rename1 `_ = OK v` >>
      `P v` by metis_tac[] >>
      `v.vs_inst_idx = 0` by
        metis_tac[run_block_OK_inst_idx_0] >>
      `~v.vs_halted` by
        metis_tac[run_block_OK_not_halted] >>
      first_x_assum (qspecl_then [`n`, `ctx`, `v`] mp_tac) >>
      simp[] >>
      strip_tac >>
      `run_block fuel' ctx cur_bb s = OK v` by (
        mp_tac fuel_mono_rb >>
        disch_then (qspecl_then [`n`, `fuel'`, `ctx`, `cur_bb`, `s`, `OK v`] mp_tac) >>
        simp[]) >>
      qexists_tac `SUC fuel'` >>
      conj_tac >- simp[] >>
      UNFOLD_RF_STEP_TAC (RATOR_CONV o RAND_CONV) >>
      UNFOLD_RF_STEP_TAC RAND_CONV >>
      first_assum ACCEPT_TAC)
  (* Non-OK: identical result *)
  >> (qexists_tac `SUC n` >>
      simp[Once run_blocks_def, GSYM run_block_def] >>
      simp[Once run_blocks_def, GSYM run_block_def,
        result_equiv_def, execution_equiv_def,
        observable_equiv_def])
QED

Triviality fn_blocks_with[simp]:
  !f X. (f:ir_function with fn_blocks := X).fn_blocks = X
Proof
  Cases >> REWRITE_TAC[venomInstTheory.ir_function_accessors,
    venomInstTheory.recordtype_ir_function_seldef_fn_blocks_fupd_def,
    combinTheory.K_THM]
QED

(* Helper: bypass_R is preserved by running a non-a block *)
Triviality bypass_R_preserved:
  !func a b target_lbl n ctx cur_bb s2 v.
    wf_function func /\ fn_inst_wf func /\
    MEM a func.fn_blocks /\
    can_bypass_jump func a b /\
    s2.vs_current_bb <> a.bb_label /\
    s2.vs_current_bb <> b.bb_label /\
    s2.vs_inst_idx = 0 /\
    lookup_block s2.vs_current_bb func.fn_blocks = SOME cur_bb /\
    run_block n ctx cur_bb s2 = OK v ==>
    bypass_R a.bb_label b.bb_label target_lbl v v /\
    v.vs_current_bb <> b.bb_label
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `s2.vs_current_bb`, `cur_bb`]
    lookup_block_wf_facts) >>
  (impl_tac >- fs[]) >>
  strip_tac >>
  `v.vs_prev_bb = SOME s2.vs_current_bb` by
    metis_tac[run_block_ok_prev_bb_wf] >>
  `MEM v.vs_current_bb (bb_succs cur_bb)` by
    metis_tac[run_block_current_bb_in_succs_wf] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks)` by
    fs[wf_function_def, venomInstTheory.fn_labels_def] >>
  `~MEM b.bb_label (bb_succs cur_bb)` by
    metis_tac[sole_pred_no_other_succ, can_bypass_jump_def] >>
  conj_tac
  >- (simp[bypass_R_def])
  >> metis_tac[]
QED

(* Helper: run_block on a block with terminator labels substituted.
   If all non-terminator instructions are unchanged (MAP with identity on
   non-terminators, subst_label_inst on terminators), then:
   - Non-OK results are identical
   - OK results differ only in vs_current_bb: old_lbl → new_lbl *)
(* step_inst_base on subst_label_inst for terminators: JNZ and JMP.
   Result differs only in vs_current_bb (old_lbl -> new_lbl).
   For JNZ: condition operand must not be Label (Var or Lit). *)
(* JNZ with eval_operand NONE produces Error regardless of other operands.
   General: works with any operand list whose first element is cond_op. *)
Triviality step_jnz_none:
  !cond_op l1 l2 id s.
    eval_operand cond_op s = NONE ==>
    step_inst_base
      <|inst_id := id; inst_opcode := JNZ;
        inst_operands := [cond_op; Label l1; Label l2];
        inst_outputs := []|> s = Error "undefined condition"
Proof
  simp[Once step_inst_base_def]
QED

(* subst_label_inst on JNZ: preserves structure, gives concrete new labels *)
Triviality subst_label_inst_jnz_structure:
  !old_lbl new_lbl cond_op l1 l2 id.
    cond_op <> Label old_lbl ==>
    let inst = <|inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label l1; Label l2];
                 inst_outputs := []|> in
    let l1' = if l1 = old_lbl then new_lbl else l1 in
    let l2' = if l2 = old_lbl then new_lbl else l2 in
      subst_label_inst old_lbl new_lbl inst =
        <|inst_id := id; inst_opcode := JNZ;
          inst_operands := [cond_op; Label l1'; Label l2'];
          inst_outputs := []|>
Proof
  rpt gen_tac >> strip_tac >>
  simp[subst_label_inst_def, subst_label_op_def] >>
  (Cases_on `cond_op` >> fs[subst_label_op_def]) >>
  Cases_on `l1 = old_lbl` >> Cases_on `l2 = old_lbl` >> simp[]
QED

Triviality step_inst_base_subst_label_jnz:
  !cond_op l1 l2 id s old_lbl new_lbl.
    cond_op <> Label old_lbl ==>
    let inst = <|inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label l1; Label l2];
                 inst_outputs := []|> in
    case step_inst_base inst s of
      OK v =>
        (v.vs_current_bb <> old_lbl ==>
           step_inst_base (subst_label_inst old_lbl new_lbl inst) s = OK v) /\
        (v.vs_current_bb = old_lbl ==>
           step_inst_base (subst_label_inst old_lbl new_lbl inst) s =
             OK (v with vs_current_bb := new_lbl))
    | Halt h => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = Halt h
    | Abort a' h => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = Abort a' h
    | IntRet vals h => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = IntRet vals h
    | Error e => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = Error e
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  (* Get the substituted instruction's structure *)
  mp_tac (Q.SPECL [`old_lbl`, `new_lbl`, `cond_op`, `l1`, `l2`, `id`]
    subst_label_inst_jnz_structure) >>
  ASM_REWRITE_TAC[] >> simp_tac std_ss [LET_THM] >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  Cases_on `eval_operand cond_op s`
  >- simp[step_jnz_none]
  >> (
    rename1 `_ = SOME cval` >>
    `step_inst_base
       <|inst_id := id; inst_opcode := JNZ;
         inst_operands := [cond_op; Label l1; Label l2];
         inst_outputs := []|> s =
     if cval <> 0w then OK (jump_to l1 s) else OK (jump_to l2 s)` by
      (irule step_jnz_behavior >> first_assum ACCEPT_TAC) >>
    ASM_REWRITE_TAC[] >>
    `!l1' l2'. step_inst_base
       <|inst_id := id; inst_opcode := JNZ;
         inst_operands := [cond_op; Label l1'; Label l2'];
         inst_outputs := []|> s =
     if cval <> 0w then OK (jump_to l1' s) else OK (jump_to l2' s)` by
      (rpt gen_tac >> irule step_jnz_behavior >> first_assum ACCEPT_TAC) >>
    ASM_REWRITE_TAC[] >>
    Cases_on `cval <> 0w` >> simp[jump_to_def])
QED

Triviality step_inst_base_subst_label_jmp:
  !lbl id s old_lbl new_lbl.
    let inst = <|inst_id := id; inst_opcode := JMP;
                 inst_operands := [Label lbl]; inst_outputs := []|> in
    case step_inst_base inst s of
      OK v =>
        (v.vs_current_bb <> old_lbl ==>
           step_inst_base (subst_label_inst old_lbl new_lbl inst) s = OK v) /\
        (v.vs_current_bb = old_lbl ==>
           step_inst_base (subst_label_inst old_lbl new_lbl inst) s =
             OK (v with vs_current_bb := new_lbl))
    | Halt h => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = Halt h
    | Abort a' h => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = Abort a' h
    | IntRet vals h => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = IntRet vals h
    | Error e => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = Error e
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  simp[subst_label_inst_def, subst_label_op_def,
       step_jmp_behavior, jump_to_def]
QED

(* Helper: well-formed block → LAST = EL at terminator index *)
Triviality bb_wf_last_el:
  !bb idx. bb_well_formed bb /\ idx = PRE (LENGTH bb.bb_instructions) ==>
    LAST bb.bb_instructions = EL idx bb.bb_instructions
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  simp[listTheory.LAST_EL]
QED

(* Helper: non-terminator at idx → SUC idx still in bounds *)
Triviality bb_wf_nonterm_suc:
  !bb idx. bb_well_formed bb /\ idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode ==>
    SUC idx < LENGTH bb.bb_instructions
Proof
  rpt strip_tac >> CCONTR_TAC >>
  `idx = PRE (LENGTH bb.bb_instructions)` by simp[] >>
  `LAST bb.bb_instructions = EL idx bb.bb_instructions` by
    metis_tac[bb_wf_last_el] >>
  metis_tac[bb_well_formed_def]
QED

(* Bridge: run_block at terminator reduces to step_inst_base *)
Triviality run_block_term_step_base:
  !fuel ctx bb s.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE ==>
    run_block_non_phis fuel ctx bb s =
    case step_inst_base (EL s.vs_inst_idx bb.bb_instructions) s of
      OK v => if v.vs_halted then Halt v else OK v
    | Halt s' => Halt s'
    | Abort a' h => Abort a' h
    | IntRet vals h => IntRet vals h
    | Error e => Error e
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`]
    simplifyCfgCollapseBaseTheory.run_block_non_phis_term_step) >>
  impl_tac >- fs[] >>
  `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s =
   step_inst_base (EL s.vs_inst_idx bb.bb_instructions) s` by
    (irule step_inst_non_invoke >> fs[]) >>
  simp[]
QED

(* Helper: step_inst_base on subst_label_inst produces related result.
   Works for any instruction with JNZ or JMP opcode that is inst_wf. *)
Triviality step_inst_base_subst_label_term:
  !inst old_lbl new_lbl s.
    (inst.inst_opcode = JNZ \/ inst.inst_opcode = JMP) /\
    inst_wf inst /\
    (!c l1 l2. inst.inst_operands = [c; Label l1; Label l2]
       ==> c <> Label old_lbl) ==>
    case step_inst_base inst s of
      OK v =>
        (v.vs_current_bb <> old_lbl ==>
           step_inst_base (subst_label_inst old_lbl new_lbl inst) s = OK v) /\
        (v.vs_current_bb = old_lbl ==>
           step_inst_base (subst_label_inst old_lbl new_lbl inst) s =
             OK (v with vs_current_bb := new_lbl))
    | Halt h => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = Halt h
    | Abort a' h => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = Abort a' h
    | IntRet vals h => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = IntRet vals h
    | Error e => step_inst_base (subst_label_inst old_lbl new_lbl inst) s = Error e
Proof
  rpt strip_tac >> gvs[inst_wf_def] (* 2 goals: JNZ, JMP *)
  >- (
    (* JNZ case *)
    mp_tac (Q.SPECL [`c`, `l1`, `l2`, `inst.inst_id`, `s`, `old_lbl`, `new_lbl`]
      step_inst_base_subst_label_jnz) >>
    simp_tac std_ss [LET_THM] >> disch_tac >>
    `inst = <|inst_id := inst.inst_id; inst_opcode := JNZ;
              inst_operands := [c; Label l1; Label l2]; inst_outputs := []|>` by
      simp[venomInstTheory.instruction_component_equality] >>
    pop_assum SUBST_ALL_TAC >> fs[])
  >- (
    (* JMP case *)
    mp_tac (Q.SPECL [`lbl`, `inst.inst_id`, `s`, `old_lbl`, `new_lbl`]
      step_inst_base_subst_label_jmp) >>
    simp_tac std_ss [LET_THM] >> disch_tac >>
    `inst = <|inst_id := inst.inst_id; inst_opcode := JMP;
              inst_operands := [Label lbl]; inst_outputs := []|>` by
      simp[venomInstTheory.instruction_component_equality] >>
    pop_assum SUBST_ALL_TAC >> fs[])
QED

(* Lift step_inst_base subst_label relationship through the run_block wrapper:
   case result of OK v => if halted then Halt v else OK v | ... *)
Triviality step_base_subst_label_wrapped:
  !inst old_lbl new_lbl s.
    (inst.inst_opcode = JNZ \/ inst.inst_opcode = JMP) /\
    inst_wf inst /\ ~s.vs_halted /\
    (!c l1 l2. inst.inst_operands = [c; Label l1; Label l2]
       ==> c <> Label old_lbl) ==>
    let wrap = \r. case r of OK v => if v.vs_halted then Halt v else OK v
                   | Halt h => Halt h | Abort a h => Abort a h
                   | IntRet vals h => IntRet vals h | Error e => Error e in
    case wrap (step_inst_base inst s) of
      OK v =>
        (v.vs_current_bb <> old_lbl ==>
           wrap (step_inst_base (subst_label_inst old_lbl new_lbl inst) s) = OK v) /\
        (v.vs_current_bb = old_lbl ==>
           wrap (step_inst_base (subst_label_inst old_lbl new_lbl inst) s) =
             OK (v with vs_current_bb := new_lbl))
    | Halt h => wrap (step_inst_base (subst_label_inst old_lbl new_lbl inst) s) = Halt h
    | Abort a' h => wrap (step_inst_base (subst_label_inst old_lbl new_lbl inst) s) = Abort a' h
    | IntRet vals h => wrap (step_inst_base (subst_label_inst old_lbl new_lbl inst) s) = IntRet vals h
    | Error e => wrap (step_inst_base (subst_label_inst old_lbl new_lbl inst) s) = Error e
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`inst`, `old_lbl`, `new_lbl`, `s`]
    step_inst_base_subst_label_term) >>
  (impl_tac >- fs[]) >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  Cases_on `step_inst_base inst s` >> gvs[] >>
  (* OK case: step_inst_base preserves ~halted *)
  `~v.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
  simp[]
QED

(* Core inductive lemma: run_block on bb vs bb' where bb' has
   terminators modified by subst_label_inst. Generalized to any inst_idx.
   Requires: terminator is JMP or JNZ (covers can_bypass_jump cases). *)
Triviality run_block_subst_label_term_gen:
  !n bb old_lbl new_lbl fuel ctx s.
    let bb' = bb with bb_instructions :=
      MAP (\i. if ~is_terminator i.inst_opcode then i
               else subst_label_inst old_lbl new_lbl i) bb.bb_instructions in
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    ((LAST bb.bb_instructions).inst_opcode = JNZ \/
     (LAST bb.bb_instructions).inst_opcode = JMP) /\
    (!c l1 l2. (LAST bb.bb_instructions).inst_operands = [c; Label l1; Label l2]
       ==> c <> Label old_lbl) /\
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    ~s.vs_halted ==>
    case run_block_non_phis fuel ctx bb s of
      OK v =>
        (v.vs_current_bb <> old_lbl ==>
           run_block_non_phis fuel ctx bb' s = OK v) /\
        (v.vs_current_bb = old_lbl ==>
           run_block_non_phis fuel ctx bb' s =
             OK (v with vs_current_bb := new_lbl))
    | Halt h => run_block_non_phis fuel ctx bb' s = Halt h
    | Abort a' h => run_block_non_phis fuel ctx bb' s = Abort a' h
    | IntRet vals h => run_block_non_phis fuel ctx bb' s = IntRet vals h
    | Error e => run_block_non_phis fuel ctx bb' s = Error e
Proof
  completeInduct_on `n` >>
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >>
  (* Strip without splitting the JNZ∨JMP disjunction *)
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qabbrev_tac `bb' = bb with bb_instructions :=
    MAP (\i. if ~is_terminator i.inst_opcode then i
             else subst_label_inst old_lbl new_lbl i) bb.bb_instructions` >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    (unabbrev_all_tac >> simp[basic_block_accfupds]) >>
  Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode`
  >- (
    (* === TERMINATOR CASE === *)
    `EL s.vs_inst_idx bb'.bb_instructions =
     subst_label_inst old_lbl new_lbl (EL s.vs_inst_idx bb.bb_instructions)` by
      (unabbrev_all_tac >> simp[listTheory.EL_MAP, basic_block_accfupds]) >>
    `is_terminator (EL s.vs_inst_idx bb'.bb_instructions).inst_opcode` by
      (ASM_REWRITE_TAC[subst_label_inst_fields]) >>
    `(EL s.vs_inst_idx bb'.bb_instructions).inst_opcode <> INVOKE` by
      (ASM_REWRITE_TAC[subst_label_inst_fields] >>
       irule is_terminator_not_INVOKE >> first_assum ACCEPT_TAC) >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb'`, `s`] run_block_term_step_base) >>
    (impl_tac >- fs[]) >> strip_tac >>
    `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE` by
      (irule is_terminator_not_INVOKE >> first_assum ACCEPT_TAC) >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`] run_block_term_step_base) >>
    (impl_tac >- fs[]) >> strip_tac >>
    ASM_REWRITE_TAC[] >>
    `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
      fs[bb_well_formed_def] >>
    `LAST bb.bb_instructions = EL s.vs_inst_idx bb.bb_instructions` by
      metis_tac[bb_wf_last_el] >>
    `inst_wf (EL s.vs_inst_idx bb.bb_instructions)` by
      metis_tac[listTheory.EVERY_EL] >>
    `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JNZ \/
     (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JMP` by
      metis_tac[] >>
    mp_tac (Q.SPECL [`EL s.vs_inst_idx bb.bb_instructions`,
      `old_lbl`, `new_lbl`, `s`] step_base_subst_label_wrapped) >>
    simp_tac std_ss [LET_THM] >>
    (impl_tac >- fs[]) >>
    disch_then (fn th => REWRITE_TAC[th]))
  >- (
    (* === NON-TERMINATOR CASE === *)
    `EL s.vs_inst_idx bb'.bb_instructions =
     EL s.vs_inst_idx bb.bb_instructions` by
      (unabbrev_all_tac >> simp[listTheory.EL_MAP, basic_block_accfupds]) >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`]
      simplifyCfgCollapseBaseTheory.run_block_non_phis_nonterm_step_full) >>
    (impl_tac >- fs[]) >> strip_tac >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb'`, `s`]
      simplifyCfgCollapseBaseTheory.run_block_non_phis_nonterm_step_full) >>
    (impl_tac >- fs[]) >> strip_tac >>
    ASM_REWRITE_TAC[] >>
    Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
    simp[] >>
    rename1 `step_inst _ _ _ _ = OK v` >>
    `SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
      metis_tac[bb_wf_nonterm_suc] >>
    first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx`
      mp_tac) >>
    (impl_tac >- simp[]) >>
    simp_tac bool_ss [LET_THM] >>
    disch_then (qspecl_then [`bb`, `old_lbl`, `new_lbl`, `fuel`, `ctx`,
      `v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
    (impl_tac >- (
       `~v.vs_halted` by
         metis_tac[venomInstProofsTheory.step_preserves_halted] >>
       rpt conj_tac >>
       TRY (first_assum ACCEPT_TAC) >>
       simp[])) >>
    simp[Abbr `bb'`])
QED
(* Running block b (single JMP) always produces jump_to target_lbl.
   Preconditions: single-instruction JMP block to target_lbl. *)
Triviality run_block_single_jmp:
  !fuel ctx b s target_lbl.
    (LAST b.bb_instructions).inst_opcode = JMP /\
    (LAST b.bb_instructions).inst_operands = [Label target_lbl] /\
    (LAST b.bb_instructions).inst_outputs = [] /\
    LENGTH b.bb_instructions = 1 /\
    bb_well_formed b /\
    ~s.vs_halted /\ s.vs_inst_idx = 0 ==>
    run_block fuel ctx b s = OK (jump_to target_lbl s)
Proof
  rpt strip_tac >>
  (* LENGTH = 1 means instructions = [inst] for some inst *)
  `?inst. b.bb_instructions = [inst]` by (
    Cases_on `b.bb_instructions` >> fs[] >>
    Cases_on `t` >> fs[]) >>
  fs[listTheory.LAST_DEF] >>
  simp[Once venomExecSemanticsTheory.run_block_def,
       venomExecSemanticsTheory.eval_phis_def,
       venomExecSemanticsTheory.phi_prefix_length_def] >>
  simp[Once venomExecSemanticsTheory.run_block_non_phis_def,
       venomInstTheory.get_instruction_def] >>
  (* step_inst = step_inst_base since JMP <> INVOKE *)
  `inst.inst_opcode <> INVOKE` by (ASM_REWRITE_TAC[] >> EVAL_TAC) >>
  ASM_SIMP_TAC bool_ss [venomExecSemanticsTheory.step_inst_non_invoke] >>
  (* Reconstruct instruction for step_jmp_behavior *)
  `inst = <| inst_id := inst.inst_id; inst_opcode := JMP;
             inst_operands := [Label target_lbl]; inst_outputs := [] |>` by
    fs[venomInstTheory.instruction_component_equality] >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  REWRITE_TAC[venomExecPropsTheory.step_jmp_behavior,
              venomInstTheory.is_terminator_def] >>
  simp[venomStateTheory.jump_to_def, venomStateTheory.venom_state_component_equality]
QED

(* --- other_block helper: standalone Triviality for debugging --- *)
Triviality other_block_sim:
  !func a b target_lbl target a' target' n ctx s2.
    wf_function func /\ fn_inst_wf func /\
    MEM a func.fn_blocks /\
    can_bypass_jump func a b /\
    a'.bb_label = a.bb_label /\
    target'.bb_label = target.bb_label /\
    target.bb_label = target_lbl /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    a.bb_label <> b.bb_label /\
    a.bb_label <> target_lbl /\
    b.bb_label <> target_lbl /\
    s2.vs_current_bb <> a.bb_label /\
    s2.vs_current_bb <> b.bb_label /\
    s2.vs_current_bb <> target_lbl /\
    bypass_R a.bb_label b.bb_label target_lbl s2 s2 /\
    prev_bb_valid func s2 /\
    s2.vs_inst_idx = 0 /\ ~s2.vs_halted /\
    lookup_block s2.vs_current_bb
      (replace_block a.bb_label a'
        (replace_block target_lbl target'
          (remove_block b.bb_label func.fn_blocks))) =
      lookup_block s2.vs_current_bb func.fn_blocks /\
    (!m. m < SUC n ==>
      !ctx' s1' s2'.
        bypass_R a.bb_label b.bb_label target_lbl s1' s2' /\
        prev_bb_valid func s1' /\
        s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
        ~s1'.vs_halted /\ ~s2'.vs_halted /\
        s1'.vs_current_bb <> b.bb_label ==>
        ?fuel'. m <= fuel' /\
          result_equiv {} (run_blocks fuel' ctx' func s1')
            (run_blocks m ctx'
              (func with fn_blocks :=
                replace_block a.bb_label a'
                  (replace_block target_lbl target'
                    (remove_block b.bb_label func.fn_blocks))) s2')) ==>
    ?fuel'.
      SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s2)
        (run_blocks (SUC n) ctx
          (func with fn_blocks :=
            replace_block a.bb_label a'
              (replace_block target_lbl target'
                (remove_block b.bb_label func.fn_blocks))) s2)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`\v. bypass_R a.bb_label b.bb_label target_lbl v v /\
                         v.vs_current_bb <> b.bb_label /\
                         prev_bb_valid func v`,
                    `func`,
                    `func with fn_blocks :=
                       replace_block a.bb_label a'
                         (replace_block target_lbl target'
                           (remove_block b.bb_label func.fn_blocks))`,
                    `n`, `ctx`, `s2`]
    same_block_sim_step) >>
  BETA_TAC >>
  impl_tac
  >- (rpt conj_tac >| [
    (* 1: wf_function *) first_assum ACCEPT_TAC,
    (* 2: fn_inst_wf *) first_assum ACCEPT_TAC,
    (* 3: bypass_R ... s2 s2 *) first_assum ACCEPT_TAC,
    (* 4: s2.vs_current_bb <> b.bb_label *) first_assum ACCEPT_TAC,
    (* 5: prev_bb_valid func s2 *) first_assum ACCEPT_TAC,
    (* 6: lookup agrees *)
    PURE_REWRITE_TAC[fn_blocks_with] >> first_assum ACCEPT_TAC,
    (* 7: P preserved *)
    (rpt gen_tac >> strip_tac >>
     `bypass_R a.bb_label b.bb_label target_lbl v v /\
      v.vs_current_bb <> b.bb_label` by (
       mp_tac bypass_R_preserved >>
       disch_then (qspecl_then [`func`, `a`, `b`, `target_lbl`, `n`, `ctx`,
                                `cur_bb`, `s2`, `v`] mp_tac) >>
       (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
       strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
     `prev_bb_valid func v` by (
       match_mp_tac prev_bb_valid_preserved >>
       qexistsl_tac [`n`, `ctx`, `cur_bb`, `s2`] >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> first_assum ACCEPT_TAC),
    (* 8: IH *)
    (rpt strip_tac >>
     first_x_assum (qspec_then `m` mp_tac) >>
     (impl_tac >- DECIDE_TAC) >>
     disch_then (qspecl_then [`ctx'`, `v`, `v`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >> qexists_tac `fuel'` >>
     conj_tac >> first_assum ACCEPT_TAC)
  ])
  >> strip_tac >> qexists_tac `fuel'` >>
     conj_tac >> first_assum ACCEPT_TAC
QED

(* --- other_block: current_bb is not a, b, or target, s1=s2 --- *)
Resume do_merge_jump_equiv_strong[other_block]:
  (* lookup_block agrees *)
  `lookup_block s2.vs_current_bb
     (replace_block a.bb_label a'
       (replace_block target_lbl target'
         (remove_block b.bb_label func.fn_blocks))) =
   lookup_block s2.vs_current_bb func.fn_blocks` by (
    irule lookup_block_bypass_other >>
    qpat_x_assum `a'.bb_label = _` (fn th => REWRITE_TAC[th]) >>
    qpat_x_assum `target'.bb_label = _` (fn th => REWRITE_TAC[th]) >>
    qpat_x_assum `target.bb_label = _` (fn th => REWRITE_TAC[th]) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`func`, `a`, `b`, `target_lbl`, `target`, `a'`, `target'`,
                    `n`, `ctx`, `s2`] other_block_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `fuel'` >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* Small helpers for high-assumption contexts — proved in clean context *)
Triviality inst_wf_jmp_operands:
  inst_wf inst /\ inst.inst_opcode = JMP ==>
  ?lbl. inst.inst_operands = [Label lbl] /\ inst.inst_outputs = []
Proof strip_tac >> gvs[venomWfTheory.inst_wf_def]
QED

Triviality last_mem_nonempty:
  l <> [] ==> MEM (LAST l) (l:'a list)
Proof Cases_on `l` >> simp[rich_listTheory.MEM_LAST]
QED

Triviality single_succ_jmp_from_wf:
  bb.bb_instructions <> [] /\
  (LAST bb.bb_instructions).inst_opcode = JMP /\
  EVERY inst_wf bb.bb_instructions /\
  bb_succs bb = [lbl] ==>
  single_succ_jmp bb lbl
Proof
  strip_tac >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions` by
    metis_tac[last_mem_nonempty] >>
  `inst_wf (LAST bb.bb_instructions)` by metis_tac[listTheory.EVERY_MEM] >>
  drule_all inst_wf_jmp_operands >> strip_tac >>
  simp[cfgTransformTheory.single_succ_jmp_def] >>
  qpat_x_assum `bb_succs _ = _` mp_tac >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  simp[venomInstTheory.bb_succs_def, venomInstTheory.get_successors_def,
       venomStateTheory.get_label_def, venomInstTheory.is_terminator_def,
       listTheory.nub_def]
QED

(* Terminator-only MAP preserves eval_phis *)
Triviality eval_phis_term_map_eq:
  !s insts old new.
    eval_phis s (MAP (\i. if ~is_terminator i.inst_opcode then i
                          else subst_label_inst old new i) insts) =
    eval_phis s insts
Proof
  Induct_on `insts` >> simp[eval_phis_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`~is_terminator h.inst_opcode` by (ASM_REWRITE_TAC[] >> EVAL_TAC) >>
      simp[] >>
      Cases_on `eval_one_phi s h` >> simp[] >>
      Cases_on `x` >> simp[] >>
      Cases_on `eval_phis s insts` >> simp[])
  >> (Cases_on `is_terminator h.inst_opcode`
    >- simp[subst_label_inst_fields]
    >> simp[])
QED

(* Terminator-only MAP preserves phi_prefix_length *)
Triviality phi_prefix_length_term_map_eq:
  !insts old new.
    phi_prefix_length (MAP (\i. if ~is_terminator i.inst_opcode then i
                                else subst_label_inst old new i) insts) =
    phi_prefix_length insts
Proof
  Induct_on `insts` >> simp[phi_prefix_length_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`~is_terminator h.inst_opcode` by (ASM_REWRITE_TAC[] >> EVAL_TAC) >>
      simp[])
  >> (Cases_on `is_terminator h.inst_opcode`
    >- simp[subst_label_inst_fields]
    >> simp[])
QED

(* eval_phis preserves vs_halted *)
Triviality eval_phis_preserves_halted:
  !s insts s'. eval_phis s insts = OK s' ==> (s'.vs_halted = s.vs_halted)
Proof
  Induct_on `insts` >> simp[eval_phis_def] >>
  rpt gen_tac >> rw[] >>
  Cases_on `eval_one_phi s h` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  Cases_on `eval_phis s insts` >> gvs[] >>
  simp[update_var_def]
QED

(* Corollary: run_block_subst_label_term_gen with inst_idx = 0 *)
Triviality run_block_subst_label_at_zero:
  !bb old_lbl new_lbl fuel ctx s.
    let bb' = bb with bb_instructions :=
      MAP (\i. if ~is_terminator i.inst_opcode then i
               else subst_label_inst old_lbl new_lbl i) bb.bb_instructions in
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    ((LAST bb.bb_instructions).inst_opcode = JNZ \/
     (LAST bb.bb_instructions).inst_opcode = JMP) /\
    (!c l1 l2. (LAST bb.bb_instructions).inst_operands = [c; Label l1; Label l2]
       ==> c <> Label old_lbl) /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    case run_block fuel ctx bb s of
      OK v =>
        (v.vs_current_bb <> old_lbl ==>
           run_block fuel ctx bb' s = OK v) /\
        (v.vs_current_bb = old_lbl ==>
           run_block fuel ctx bb' s =
             OK (v with vs_current_bb := new_lbl))
    | Halt h => run_block fuel ctx bb' s = Halt h
    | Abort a' h => run_block fuel ctx bb' s = Abort a' h
    | IntRet vals h => run_block fuel ctx bb' s = IntRet vals h
    | Error e => run_block fuel ctx bb' s = Error e
Proof
  rpt gen_tac >> PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qabbrev_tac `bb' = bb with bb_instructions :=
    MAP (\i. if ~is_terminator i.inst_opcode then i
             else subst_label_inst old_lbl new_lbl i) bb.bb_instructions` >>
  ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
  simp[Abbr`bb'`] >>
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`, `bb`, `old_lbl`, `new_lbl`,
    `fuel`, `ctx`, `s`]
    run_block_subst_label_term_gen) >>
  PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >>
  disch_then match_mp_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[] >>
  fs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> gvs[]
QED

(* Bundle of run_block OK post-state facts *)
Triviality run_block_OK_facts:
  !fuel ctx bb s v.
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    s.vs_inst_idx = 0 /\ run_block fuel ctx bb s = OK v ==>
    ~v.vs_halted /\ v.vs_inst_idx = 0 /\ v.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac
  >- metis_tac[venomExecPropsTheory.run_block_OK_not_halted]
  >- metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0]
  >> mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `v`]
       simplifyCfgCollapseBaseTheory.run_block_ok_prev_bb_wf) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     REWRITE_TAC[]
QED

(* --- Reusable non-OK simulation helpers --- *)
Triviality result_equiv_nonOK_refl:
  !r:exec_result. (!v. r <> OK v) ==> result_equiv {} r r
Proof
  Cases >> rw[result_equiv_def, stateEquivPropsTheory.execution_equiv_refl]
QED

Triviality rf_nonOK_match:
  !n ctx func bb s R.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    run_block n ctx bb s = R /\ (!v. R <> OK v) /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    run_blocks (SUC n) ctx func s = R
Proof
  rw[] >> simp[Once run_blocks_def, GSYM run_block_def] >>
  Cases_on `run_block n ctx bb s` >> fs[exec_result_case_def]
QED

(* --- Reusable: non-OK run_block implies simulation witness --- *)
Triviality nonOK_block_sim:
  !n ctx func bb bb' s.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    (!v. run_block n ctx bb s <> OK v) /\
    run_block n ctx bb' s = run_block n ctx bb s /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ?fuel'. SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s) (run_block n ctx bb s)
Proof
  rpt strip_tac >>
  qexists_tac `SUC n` >> conj_tac >- simp[] >>
  qabbrev_tac `R = run_block n ctx bb s` >>
  mp_tac (Q.SPECL [`n`, `ctx`, `func`, `bb`, `s`, `R`] rf_nonOK_match) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qunabbrev_tac `R` >> REFL_TAC)) >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  irule result_equiv_nonOK_refl >> first_assum ACCEPT_TAC
QED

(* --- at_a case: non-OK result from run_block on a --- *)
Triviality at_a_nonOK_sim:
  !n ctx func a a' s R func'.
    lookup_block s.vs_current_bb func.fn_blocks = SOME a /\
    run_block n ctx a s = R /\ (!v. R <> OK v) /\
    run_block n ctx a' s = R /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ?fuel'. SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s)
        (case run_block n ctx a' s of
           OK s'' => if s''.vs_halted then Halt s'' else run_blocks n ctx func' s''
         | Halt v8 => Halt v8
         | Abort v9 v10 => Abort v9 v10
         | IntRet vals s' => IntRet vals s'
         | Error v13 => Error v13)
Proof
  rpt strip_tac >>
  (* RHS: case R of ... where R is non-OK, so it's just R *)
  ASM_REWRITE_TAC[] >>
  Cases_on `R` >> gvs[] >>
  REWRITE_TAC[venomExecSemanticsTheory.exec_result_case_def] >>
  qexists_tac `SUC n` >> conj_tac >- simp[] >>
  simp[Once run_blocks_def, GSYM run_block_def] >>
  REWRITE_TAC[stateEquivTheory.result_equiv_def,
              stateEquivPropsTheory.execution_equiv_refl]
QED

(* --- at_a OK→¬b: block a produces OK v, v doesn't go to b --- *)
Triviality at_a_OK_not_b_sim:
  !n ctx func a b s v a' func'.
    wf_function func /\ fn_inst_wf func /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME a /\
    run_block n ctx a s = OK v /\
    run_block n ctx a' s = OK v /\
    v.vs_current_bb <> b.bb_label /\
    bb_well_formed a /\ EVERY inst_wf a.bb_instructions /\
    a.bb_label <> b.bb_label /\
    s.vs_current_bb = a.bb_label /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    (!m. m < SUC n ==>
      !ctx' s1' s2'.
        bypass_R a.bb_label b.bb_label target_lbl s1' s2' /\
        prev_bb_valid func s1' /\
        s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
        ~s1'.vs_halted /\ ~s2'.vs_halted /\
        s1'.vs_current_bb <> b.bb_label ==>
      ?fuel'.
        m <= fuel' /\
        result_equiv {} (run_blocks fuel' ctx' func s1')
          (run_blocks m ctx' func' s2')) ==>
    ?fuel'.
      SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s)
        (case run_block n ctx a' s of
           OK s'' => if s''.vs_halted then Halt s'' else run_blocks n ctx func' s''
         | Halt v8 => Halt v8
         | Abort v9 v10 => Abort v9 v10
         | IntRet vals s' => IntRet vals s'
         | Error v13 => Error v13)
Proof
  rpt strip_tac >>
  (* Derive v facts from run_block OK *)
  `~v.vs_halted /\ v.vs_inst_idx = 0 /\ v.vs_prev_bb = SOME s.vs_current_bb` by
    metis_tac[run_block_OK_facts] >>
  `v.vs_prev_bb = SOME a.bb_label` by ASM_REWRITE_TAC[] >>
  (* Simplify RHS case expression *)
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[venomExecSemanticsTheory.exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  (* bypass_R D1: v.vs_prev_bb = SOME a ≠ SOME b *)
  `bypass_R a.bb_label b.bb_label target_lbl v v` by simp[bypass_R_def] >>
  (* prev_bb_valid for v *)
  `prev_bb_valid func v` by (
    match_mp_tac prev_bb_valid_preserved >>
    qexistsl_tac [`n`, `ctx`, `a`, `s`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* Apply IH at n *)
  first_x_assum (qspec_then `n` mp_tac) >> (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`ctx`, `v`, `v`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Witness: SUC fuel', unfold LHS rf one step *)
  qexists_tac `SUC fuel'` >> conj_tac >- simp[] >>
  simp[Once run_blocks_def, GSYM run_block_def] >>
  `run_block fuel' ctx a s = OK v` by (
    mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
    disch_then (qspecl_then [`n`, `fuel'`, `ctx`, `a`, `s`, `OK v`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
    REWRITE_TAC[]) >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[venomExecSemanticsTheory.exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[]
QED

(* Accessor lemmas — safe for REWRITE_TAC in high-assumption contexts *)
Triviality with_current_bb_accessors:
  (s with vs_current_bb := x).vs_inst_idx = s.vs_inst_idx /\
  ((s with vs_current_bb := x).vs_halted <=> s.vs_halted) /\
  (s with vs_current_bb := x).vs_current_bb = x /\
  (s with vs_current_bb := x).vs_prev_bb = s.vs_prev_bb
Proof
  simp[venomStateTheory.venom_state_accfupds]
QED

Triviality jump_to_accessors:
  (jump_to l s).vs_inst_idx = 0 /\
  (jump_to l s).vs_current_bb = l /\
  (jump_to l s).vs_prev_bb = SOME s.vs_current_bb /\
  ((jump_to l s).vs_halted <=> s.vs_halted)
Proof
  simp[venomStateTheory.jump_to_def]
QED

(* Helper: bypass_R D2 construction from jump_to *)
Triviality bypass_R_D2_jump_to:
  !v a_lbl b_lbl t_lbl.
    v.vs_inst_idx = 0 /\ v.vs_current_bb = b_lbl /\
    v.vs_prev_bb = SOME a_lbl ==>
    bypass_R a_lbl b_lbl t_lbl (jump_to t_lbl v) (v with vs_current_bb := t_lbl)
Proof
  simp[bypass_R_def, venomStateTheory.jump_to_def,
       venomStateTheory.venom_state_accfupds,
       prev_bb_equiv_def,
       venomStateTheory.venom_state_component_equality]
QED

(* --- at_a OK→b: block a produces OK v, v goes to b (single JMP) --- *)
Triviality at_a_OK_to_b_sim:
  !n ctx func a b target_lbl target s v a' target' func'.
    wf_function func /\ fn_inst_wf func /\
    fn_bypass_safe func /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME a /\
    lookup_block b.bb_label func.fn_blocks = SOME b /\
    run_block n ctx a s = OK v /\
    run_block n ctx a' s = OK (v with vs_current_bb := target_lbl) /\
    v.vs_current_bb = b.bb_label /\
    bb_well_formed a /\ EVERY inst_wf a.bb_instructions /\
    bb_well_formed b /\ EVERY inst_wf b.bb_instructions /\
    single_succ_jmp b target_lbl /\
    LENGTH b.bb_instructions = 1 /\
    bb_succs b = [target_lbl] /\
    a.bb_label <> b.bb_label /\
    a.bb_label <> target_lbl /\
    b.bb_label <> target_lbl /\
    s.vs_current_bb = a.bb_label /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    (!m. m < SUC n ==>
      !ctx' s1' s2'.
        bypass_R a.bb_label b.bb_label target_lbl s1' s2' /\
        prev_bb_valid func s1' /\
        s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
        ~s1'.vs_halted /\ ~s2'.vs_halted /\
        s1'.vs_current_bb <> b.bb_label ==>
      ?fuel'.
        m <= fuel' /\
        result_equiv {} (run_blocks fuel' ctx' func s1')
          (run_blocks m ctx' func' s2')) ==>
    ?fuel'.
      SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s)
        (case run_block n ctx a' s of
           OK s'' => if s''.vs_halted then Halt s'' else run_blocks n ctx func' s''
         | Halt v8 => Halt v8
         | Abort v9 v10 => Abort v9 v10
         | IntRet vals s' => IntRet vals s'
         | Error v13 => Error v13)
Proof
  rpt strip_tac >>
  (* Derive v facts from run_block OK *)
  `~v.vs_halted /\ v.vs_inst_idx = 0 /\ v.vs_prev_bb = SOME s.vs_current_bb` by
    metis_tac[run_block_OK_facts] >>
  `v.vs_prev_bb = SOME a.bb_label` by ASM_REWRITE_TAC[] >>
  (* Simplify RHS case expression *)
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[venomExecSemanticsTheory.exec_result_case_def] >> BETA_TAC >>
  `~(v with vs_current_bb := target_lbl).vs_halted` by
    ASM_REWRITE_TAC[venomStateTheory.venom_state_accfupds] >>
  ASM_REWRITE_TAC[] >>
  (* Derive JMP facts from single_succ_jmp *)
  `(LAST b.bb_instructions).inst_opcode = JMP /\ b.bb_instructions <> []` by
    fs[cfgTransformTheory.single_succ_jmp_def] >>
  `(LAST b.bb_instructions).inst_operands = [Label target_lbl]` by
    fs[cfgTransformTheory.single_succ_jmp_def] >>
  `(LAST b.bb_instructions).inst_outputs = []` by (
    `inst_wf (LAST b.bb_instructions)` by
      metis_tac[last_mem_nonempty, listTheory.EVERY_MEM] >>
    metis_tac[inst_wf_jmp_operands]) >>
  (* run_block on b: single JMP → jump_to *)
  `!fuel. run_block fuel ctx b v = OK (jump_to target_lbl v)` by (
    gen_tac >> match_mp_tac run_block_single_jmp >> ASM_REWRITE_TAC[]) >>
  (* bypass_R D2 *)
  mp_tac (Q.SPECL [`v`, `a.bb_label`, `b.bb_label`, `target_lbl`]
            bypass_R_D2_jump_to) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  (* Derive prev_bb_valid for IH *)
  `prev_bb_valid func (jump_to target_lbl v)` by (
    simp[prev_bb_valid_def, jump_to_accessors] >>
    rpt strip_tac >> gvs[] >>
    simp[cfgTransformTheory.pred_labels_def,
         cfgTransformTheory.block_preds_def,
         listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
    qexists_tac `b` >> simp[]) >>
  (* Apply IH at n *)
  qpat_x_assum `!m. m < SUC n ==> _` (qspec_then `n` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`ctx`,
    `jump_to target_lbl v`,
    `v with vs_current_bb := target_lbl`] mp_tac) >>
  REWRITE_TAC[jump_to_accessors, with_current_bb_accessors] >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qpat_x_assum `b.bb_label <> target_lbl` (ACCEPT_TAC o GSYM))) >>
  strip_tac >>
  (* Witness: SUC (SUC fuel') — 2 steps on LHS *)
  qexists_tac `SUC (SUC fuel')` >> conj_tac >- simp[] >>
  (* Unfold LHS rf step 1: lookup a → run_block → OK v *)
  simp[Once run_blocks_def, GSYM run_block_def] >>
  mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
  disch_then (qspecl_then [`n`, `SUC fuel'`, `ctx`, `a`, `s`, `OK v`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  REWRITE_TAC[venomExecSemanticsTheory.exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  (* Unfold LHS rf step 2: lookup b → run_block b v → OK (jump_to target v) *)
  `v.vs_current_bb = b.bb_label` by first_assum ACCEPT_TAC >>
  simp[Once run_blocks_def, GSYM run_block_def] >>
  qpat_x_assum `v.vs_current_bb = b.bb_label`
    (fn th => PURE_REWRITE_TAC[th]) >>
  qpat_x_assum `lookup_block b.bb_label _ = SOME b`
    (fn th => REWRITE_TAC[th]) >>
  REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
  qpat_x_assum `!fuel. run_block fuel ctx b v = _`
    (fn th => REWRITE_TAC[th]) >>
  REWRITE_TAC[venomExecSemanticsTheory.exec_result_case_def] >> BETA_TAC >>
  REWRITE_TAC[jump_to_accessors] >>
  qpat_x_assum `~v.vs_halted`
    (fn th => REWRITE_TAC[th]) >>
  first_assum ACCEPT_TAC
QED

(* --- at_a helper: standalone Triviality --- *)
Triviality at_a_sim:
  !func a b target_lbl target a' target' n ctx s1 s2.
    wf_function func /\ fn_inst_wf func /\
    fn_bypass_safe func /\
    MEM a func.fn_blocks /\
    MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    bb_succs b = [target_lbl] /\
    lookup_block target_lbl func.fn_blocks = SOME target /\
    lookup_block a.bb_label func.fn_blocks = SOME a /\
    lookup_block b.bb_label func.fn_blocks = SOME b /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    a.bb_label <> b.bb_label /\
    a.bb_label <> target_lbl /\
    b.bb_label <> target_lbl /\
    a' = a with bb_instructions :=
      MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                  else subst_label_inst b.bb_label target_lbl inst)
        a.bb_instructions /\
    target' = target with bb_instructions :=
      MAP (update_phi_bypass a.bb_label b.bb_label) target.bb_instructions /\
    target.bb_label = target_lbl /\
    bypass_R a.bb_label b.bb_label target_lbl s1 s2 /\
    prev_bb_valid func s1 /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    ~s1.vs_halted /\ ~s2.vs_halted /\
    s1.vs_current_bb = a.bb_label /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_current_bb <> b.bb_label /\
    bb_well_formed b /\
    EVERY inst_wf b.bb_instructions /\
    (!m. m < SUC n ==>
      !ctx' s1' s2'.
        bypass_R a.bb_label b.bb_label target_lbl s1' s2' /\
        prev_bb_valid func s1' /\
        s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
        ~s1'.vs_halted /\ ~s2'.vs_halted /\
        s1'.vs_current_bb <> b.bb_label ==>
      ?fuel'.
        m <= fuel' /\
        result_equiv {} (run_blocks fuel' ctx' func s1')
          (run_blocks m ctx'
            (func with fn_blocks :=
              replace_block a.bb_label a'
                (replace_block target_lbl target'
                  (remove_block b.bb_label func.fn_blocks))) s2')) ==>
    ?fuel'.
      SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s1)
        (run_blocks (SUC n) ctx
          (func with fn_blocks :=
            replace_block a.bb_label a'
              (replace_block target_lbl target'
                (remove_block b.bb_label func.fn_blocks))) s2)
Proof
  rpt strip_tac >>
  (* D1: s1 = s2 since bypass_R at a.bb_label <> target_lbl *)
  `s1 = s2` by (
    qpat_x_assum `bypass_R _ _ _ _ _` mp_tac >>
    REWRITE_TAC[bypass_R_def] >> strip_tac >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >>
  (* Derive key block facts from lookup_block_wf_facts *)
  mp_tac (Q.SPECL [`func`, `a.bb_label`, `a`] lookup_block_wf_facts) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Derive fn_bypass_safe facts for block a *)
  qpat_assum `fn_bypass_safe _`
    (mp_tac o REWRITE_RULE[fn_bypass_safe_def]) >>
  disch_then (qspec_then `a` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Derive JNZ from num_succs a = 2 *)
  `(LAST a.bb_instructions).inst_opcode = JNZ` by (
    qpat_x_assum `num_succs a = 2 ==> _` match_mp_tac >>
    qpat_x_assum `can_bypass_jump _ _ _` mp_tac >>
    REWRITE_TAC[can_bypass_jump_def] >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  (* Derive b.bb_instructions <> [] from can_bypass_jump LENGTH=1 *)
  `b.bb_instructions <> []` by (
    qpat_x_assum `can_bypass_jump _ _ _`
      (mp_tac o CONJUNCT1 o REWRITE_RULE[can_bypass_jump_def]) >>
    metis_tac[listTheory.LENGTH_NIL, DECIDE ``1n <> 0``]) >>
  (* Derive fn_bypass_safe facts for block b *)
  qpat_assum `fn_bypass_safe _`
    (mp_tac o REWRITE_RULE[fn_bypass_safe_def]) >>
  disch_then (qspec_then `b` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Derive JMP from fn_bypass_safe + num_succs b = 1 *)
  `(LAST b.bb_instructions).inst_opcode = JMP` by (
    qpat_x_assum `num_succs b = 1 ==> _` match_mp_tac >>
    qpat_x_assum `can_bypass_jump _ _ _` mp_tac >>
    REWRITE_TAC[can_bypass_jump_def] >> strip_tac >>
    first_assum ACCEPT_TAC) >>
  (* Derive single_succ_jmp b target_lbl *)
  `single_succ_jmp b target_lbl` by
    metis_tac[single_succ_jmp_from_wf] >>
  (* Derive a'.bb_label and target'.bb_label *)
  `a'.bb_label = a.bb_label` by (
    qpat_x_assum `a' = a with bb_instructions := _` (fn th =>
      REWRITE_TAC[th, basic_block_accfupds])) >>
  `target'.bb_label = target_lbl` by (
    qpat_x_assum `target' = target with bb_instructions := _` (fn th =>
      REWRITE_TAC[th, basic_block_accfupds]) >>
    first_assum ACCEPT_TAC) >>
  (* Get all bypass lookup facts *)
  mp_tac (Q.SPECL [`a.bb_label`, `target_lbl`, `b.bb_label`,
    `a'`, `target'`, `func.fn_blocks`] lookup_block_bypass_full) >>
  (impl_tac >- (
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    TRY (ONCE_REWRITE_TAC[EQ_SYM_EQ] >> first_assum ACCEPT_TAC) >>
    TRY (qexists_tac `a` >> first_assum ACCEPT_TAC) >>
    qexists_tac `target` >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Abbreviate func' *)
  qabbrev_tac `func' = func with fn_blocks :=
    replace_block a.bb_label a'
      (replace_block target_lbl target'
        (remove_block b.bb_label func.fn_blocks))` >>
  (* Establish lookup in func' for RHS *)
  `lookup_block s2.vs_current_bb func'.fn_blocks = SOME a'` by (
    qunabbrev_tac `func'` >> PURE_REWRITE_TAC[fn_blocks_with] >>
    qpat_assum `s2.vs_current_bb = a.bb_label` (fn th => REWRITE_TAC[th]) >>
    first_assum ACCEPT_TAC) >>
  (* Establish lookup in func for LHS *)
  `lookup_block s2.vs_current_bb func.fn_blocks = SOME a` by (
    qpat_assum `s2.vs_current_bb = a.bb_label` (fn th => REWRITE_TAC[th]) >>
    first_assum ACCEPT_TAC) >>
  (* Establish RHS unfolding as a fact *)
  UNFOLD_RF_ASSUME_TAC rf_in_exists_rhs >>
  (* Rewrite RHS with the unfolded run_blocks *)
  qpat_x_assum `run_blocks (SUC n) ctx func' s2 = _`
    (fn th => PURE_REWRITE_TAC[th]) >>
  (* Apply run_block_subst_label_at_zero to relate a' to a *)
  mp_tac (Q.SPECL [`a`, `b.bb_label`, `target_lbl`, `n`, `ctx`, `s2`]
    run_block_subst_label_at_zero) >>
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  (impl_tac >- (
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    TRY (DISJ1_TAC >> first_assum ACCEPT_TAC) >>
    rpt gen_tac >> disch_tac >>
    qpat_assum `!c l1 l2. (LAST a.bb_instructions).inst_opcode = JNZ /\ _ ==> _`
      (mp_tac o Q.SPECL [`c`, `l1`, `l2`]) >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (qspec_then `b.bb_label` ACCEPT_TAC))) >>
  (* at_zero: relates run_block on a to run_block on a'.
     Add as assumption with a' form via ML rewriting. *)
  disch_then (fn at_zero_th => (fn (asl, g) =>
    let val a'_th = ASSUME (find_subst_label_def asl)
        val rewritten = PURE_REWRITE_RULE [GSYM a'_th] at_zero_th
    in ASSUME_TAC rewritten (asl, g) end)) >>
  (* Now at_zero uses a' (not the MAP expression).
     Abbreviate + case-split to get equation in assumptions. *)
  qabbrev_tac `R = run_block n ctx a s2` >>
  Cases_on `R`
  (* OK case *)
  >- (
    (* Top 2: Abbrev(OK v = rb n a s2), at_zero(case OK v of ...)
       Use ML let to pop both correctly *)
    pop_assum (fn abbrev_th =>
      let val rb_a_eq = GSYM (REWRITE_RULE [markerTheory.Abbrev_def] abbrev_th) in
      pop_assum (fn at_zero_th =>
        let val at_zero_ok = SIMPLIFY_CASE_RULE at_zero_th in
        assume_tac rb_a_eq >> assume_tac at_zero_ok end) end) >>
    Cases_on `v.vs_current_bb = b.bb_label`
    >- ( (* Goes to b — extra step *)
      match_mp_tac at_a_OK_to_b_sim >>
      metis_tac[venomExecSemanticsTheory.exec_result_distinct,
                can_bypass_jump_def])
    >> (* Doesn't go to b — direct IH *)
    match_mp_tac at_a_OK_not_b_sim >>
    metis_tac[venomExecSemanticsTheory.exec_result_distinct])
  (* Non-OK cases: Halt, Abort, IntRet, Error — all identical.
     Pop the Abbrev and at_zero theorems, put them back as assumptions,
     then use at_a_nonOK_sim. *)
  >> (
    pop_assum (fn abbrev_th =>
      let val rb_a_eq = GSYM (REWRITE_RULE [markerTheory.Abbrev_def] abbrev_th) in
      pop_assum (fn at_zero_th =>
        let val rb_a'_eq = SIMPLIFY_CASE_RULE at_zero_th in
        assume_tac rb_a_eq >> assume_tac rb_a'_eq end) end) >>
    match_mp_tac at_a_nonOK_sim >>
    metis_tac[venomExecSemanticsTheory.exec_result_distinct])
QED

(* --- at_a: current_bb = a.bb_label --- *)
Resume do_merge_jump_equiv_strong[at_a]:
  match_mp_tac at_a_sim >>
  qexists_tac `target` >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  (* Abbrev → equality *)
  TRY (qpat_assum `Abbrev (a' = _)` (ACCEPT_TAC o
    REWRITE_RULE [markerTheory.Abbrev_def])) >>
  TRY (qpat_assum `Abbrev (target' = _)` (ACCEPT_TAC o
    REWRITE_RULE [markerTheory.Abbrev_def])) >>
  (* bb_well_formed b: from wf_function + MEM b *)
  TRY (qpat_assum `wf_function _` mp_tac >>
       REWRITE_TAC[wf_function_def] >> strip_tac >>
       first_x_assum match_mp_tac >> first_assum ACCEPT_TAC) >>
  (* EVERY inst_wf b.bb_instructions: from fn_inst_wf + MEM b *)
  REWRITE_TAC[listTheory.EVERY_MEM] >> rpt strip_tac >>
  qpat_assum `fn_inst_wf _` (mp_tac o REWRITE_RULE[fn_inst_wf_def]) >>
  disch_then (qspecl_then [`b`, `e`] match_mp_tac) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* ----------------------------------------------------------------
   at_target helpers
   ---------------------------------------------------------------- *)

(* ===== eval_phis + run_block_non_phis decomposition helpers ===== *)
(* These allow proving run_block-level update_phi_bypass theorems
   via separate eval_phis and run_block_non_phis reasoning.
   Key insight: step_inst_base PHI = OK s (no-op), so run_block_non_phis
   is completely insensitive to update_phi_bypass. *)

(* eval_operand is insensitive to prev_bb_equiv *)
Triviality eval_operand_prev_bb_equiv_local:
  !op s1 s2. prev_bb_equiv s1 s2 ==> eval_operand op s1 = eval_operand op s2
Proof
  Cases >> simp[eval_operand_def, lookup_var_def] >>
  rpt strip_tac >>
  fs[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
QED

(* resolve_phi ignores remove_phi_label for different labels *)
Triviality resolve_phi_remove_neq_local:
  !prev ops b. prev <> b ==>
    resolve_phi prev (remove_phi_label b ops) = resolve_phi prev ops
Proof
  ho_match_mp_tac remove_phi_label_ind >> rpt strip_tac >>
  simp[resolve_phi_def, remove_phi_label_def] >>
  rw[] >> fs[resolve_phi_def]
QED

(* resolve_phi on renamed operands when prev <> a, prev <> b, and phi_well_formed *)
Triviality resolve_phi_rename_neq_local:
  !prev ops a b. prev <> a /\ prev <> b /\ phi_well_formed ops ==>
    resolve_phi prev (MAP (\op. case op of Lit v => op | Var v => op
      | Label l => if l = b then Label a else Label l) ops) =
    resolve_phi prev ops
Proof
  ho_match_mp_tac resolve_phi_ind >> rpt strip_tac >>
  gvs[resolve_phi_def, phi_well_formed_def] >>
  Cases_on `val_op` >> gvs[phi_well_formed_def, resolve_phi_def] >>
  Cases_on `lbl = b` >> gvs[resolve_phi_def]
QED

(* resolve_phi a (rename b->a) = resolve_phi b when ~MEM (Label a) and phi_well_formed *)
Triviality resolve_phi_bypass_rename_a_local:
  !b ops a.
    ~MEM (Label a) ops /\ phi_well_formed ops ==>
    resolve_phi a (MAP (\op. case op of Lit v => op | Var v => op
      | Label l => if l = b then Label a else Label l) ops) =
    resolve_phi b ops
Proof
  ho_match_mp_tac resolve_phi_ind >> rpt strip_tac >>
  gvs[resolve_phi_def, phi_well_formed_def] >>
  Cases_on `val_op` >> gvs[phi_well_formed_def, resolve_phi_def] >>
  Cases_on `lbl = b` >> gvs[resolve_phi_def]
QED

(* D1: eval_one_phi unchanged by bypass when prev_bb <> b *)
Triviality eval_one_phi_bypass_eq_D1:
  !s inst a b.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    s.vs_prev_bb <> SOME b /\
    (s.vs_prev_bb = SOME a ==> MEM (Label a) inst.inst_operands)
    ==>
    eval_one_phi s (update_phi_bypass a b inst) = eval_one_phi s inst
Proof
  rpt strip_tac >>
  Cases_on `MEM (Label a) inst.inst_operands`
  >- (
    (* MEM case: remove b. eval_one_phi unaffected since a <> b *)
    simp[eval_one_phi_def, update_phi_bypass_def, LET_THM] >>
    Cases_on `s.vs_prev_bb` >> gvs[] >>
    Cases_on `inst.inst_outputs` >> simp[] >>
    Cases_on `t` >> simp[] >>
    simp[resolve_phi_remove_neq_local])
  >>
  (* ~MEM case: rename b->a *)
  simp[eval_one_phi_def, update_phi_bypass_def, LET_THM] >>
  Cases_on `s.vs_prev_bb` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `x = a` >> gvs[] >>
  (* x <> a, x <> b, ~MEM (Label a): need phi_well_formed for rename *)
  qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def] >>
  strip_tac >>
  `phi_well_formed inst.inst_operands` by
    metis_tac[phi_operands_wf_implies_phi_well_formed] >>
  simp[resolve_phi_rename_neq_local]
QED

(* D1 eval_phis: equal when prev_bb <> b *)
Triviality eval_phis_bypass_eq_D1:
  !insts s a b.
    s.vs_prev_bb <> SOME b /\
    EVERY inst_wf insts /\
    (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==>
       s.vs_prev_bb = SOME a ==> MEM (Label a) inst.inst_operands)
    ==>
    eval_phis s (MAP (update_phi_bypass a b) insts) = eval_phis s insts
Proof
  Induct >> simp[eval_phis_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    `(update_phi_bypass a b h).inst_opcode = PHI` by
      simp[simplifyCfgWfTheory.update_phi_bypass_opcode] >>
    simp[eval_phis_def] >>
    `eval_one_phi s (update_phi_bypass a b h) = eval_one_phi s h` by (
      irule eval_one_phi_bypass_eq_D1 >> simp[] >>
      first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
    simp[])
  >>
  `(update_phi_bypass a b h).inst_opcode <> PHI` by
    simp[simplifyCfgWfTheory.update_phi_bypass_opcode] >>
  simp[eval_phis_def]
QED

(* D2: eval_one_phi literal equality under prev_bb_equiv.
   Requires resolve_phi a ops = resolve_phi b ops (stronger than phi_values_agree).
   Derivable from fn_phi_resolve_complete + phi_values_agree at call sites. *)
Triviality eval_one_phi_bypass_D2:
  !s1 s2 inst a b.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME b /\ s2.vs_prev_bb = SOME a /\
    a <> b /\
    (MEM (Label a) inst.inst_operands ==>
       resolve_phi a inst.inst_operands = resolve_phi b inst.inst_operands)
    ==>
    eval_one_phi s1 inst = eval_one_phi s2 (update_phi_bypass a b inst)
Proof
  rpt strip_tac >>
  Cases_on `MEM (Label a) inst.inst_operands`
  >- (
    (* MEM case: remove b *)
    `resolve_phi a inst.inst_operands = resolve_phi b inst.inst_operands` by
      metis_tac[] >>
    simp[eval_one_phi_def, update_phi_bypass_def, LET_THM] >>
    Cases_on `inst.inst_outputs` >> simp[] >>
    Cases_on `t` >> simp[] >>
    simp[resolve_phi_remove_neq_local] >>
    Cases_on `resolve_phi b inst.inst_operands` >> gvs[] >>
    `eval_operand x s1 = eval_operand x s2` by
      metis_tac[eval_operand_prev_bb_equiv_local] >>
    simp[])
  >>
  (* ~MEM case: rename b->a *)
  `phi_well_formed inst.inst_operands` by
    (qpat_x_assum `inst_wf _` mp_tac >>
     simp[inst_wf_def] >> strip_tac >>
     metis_tac[phi_operands_wf_implies_phi_well_formed]) >>
  simp[eval_one_phi_def, update_phi_bypass_def, LET_THM] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  simp[resolve_phi_bypass_rename_a_local] >>
  Cases_on `resolve_phi b inst.inst_operands` >> simp[] >>
  `eval_operand x s1 = eval_operand x s2` by
    metis_tac[eval_operand_prev_bb_equiv_local] >>
  simp[]
QED

(* update_var preserves prev_bb_equiv *)
Triviality update_var_prev_bb_equiv_local:
  !x v s1 s2. prev_bb_equiv s1 s2 ==>
    prev_bb_equiv (update_var x v s1) (update_var x v s2)
Proof
  rw[update_var_def, prev_bb_equiv_def,
     venomStateTheory.venom_state_component_equality]
QED

(* D2 eval_phis: result_prev_bb_equiv through PHI evaluation.
   Requires literal resolve_phi equality (stronger than phi_values_agree).
   Derivable from fn_phi_resolve_complete + phi_values_agree at caller. *)
(* D2 eval_phis: result_prev_bb_equiv through PHI evaluation.
   Weakened precondition: resolve_phi equality only needed when MEM (Label a).
   In ¬MEM case, update_phi_bypass renames b→a so eval_one_phi still agrees. *)
Triviality eval_phis_bypass_D2:
  !insts s1 s2 a b.
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME b /\ s2.vs_prev_bb = SOME a /\
    a <> b /\
    EVERY inst_wf insts /\
    (!inst. MEM inst insts /\ inst.inst_opcode = PHI /\
            MEM (Label a) inst.inst_operands ==>
       resolve_phi a inst.inst_operands = resolve_phi b inst.inst_operands)
    ==>
    result_prev_bb_equiv
      (eval_phis s1 insts)
      (eval_phis s2 (MAP (update_phi_bypass a b) insts))
Proof
  Induct
  >- rw[eval_phis_def, result_prev_bb_equiv_def]
  >>
  rpt gen_tac >>
  strip_tac >>
  `inst_wf h` by (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    `MEM (Label a) h.inst_operands ==>
       resolve_phi a h.inst_operands = resolve_phi b h.inst_operands` by
      metis_tac[listTheory.MEM] >>
    drule_all eval_one_phi_bypass_D2 >> strip_tac >>
    simp[eval_phis_def, simplifyCfgWfTheory.update_phi_bypass_opcode] >>
    Cases_on `eval_one_phi s2 (update_phi_bypass a b h)` >>
    simp[result_prev_bb_equiv_def] >>
    rename1 `_ = SOME pair` >> Cases_on `pair` >> simp[] >>
    `result_prev_bb_equiv (eval_phis s1 insts)
       (eval_phis s2 (MAP (update_phi_bypass a b) insts))` by (
      last_x_assum irule >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      fs[listTheory.EVERY_DEF] >>
      metis_tac[listTheory.MEM]) >>
    Cases_on `eval_phis s1 insts` >>
    Cases_on `eval_phis s2 (MAP (update_phi_bypass a b) insts)` >>
    gvs[result_prev_bb_equiv_def] >>
    irule update_var_prev_bb_equiv_local >> simp[])
  >>
  simp[eval_phis_def, result_prev_bb_equiv_def,
       simplifyCfgWfTheory.update_phi_bypass_opcode]
QED

(* phi_prefix_length preserved by update_phi_bypass *)
Triviality phi_prefix_length_update_phi_bypass_eq:
  !insts a b. phi_prefix_length (MAP (update_phi_bypass a b) insts) =
              phi_prefix_length insts
Proof
  Induct >> simp[phi_prefix_length_def,
    simplifyCfgWfTheory.update_phi_bypass_opcode]
QED

(* step_inst is insensitive to update_phi_bypass *)
(* In the new semantics, PHI's step_inst_base uses resolve_phi which
   depends on inst_operands. update_phi_bypass modifies PHI operands,
   so equality only holds for non-PHI instructions (where update_phi_bypass
   is the identity). *)
Triviality step_inst_update_phi_bypass_eq:
  !fuel ctx inst s a b.
    inst.inst_opcode <> PHI ==>
    step_inst fuel ctx (update_phi_bypass a b inst) s = step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  simp[simplifyCfgWfTheory.update_phi_bypass_non_phi]
QED

(* D1: step_inst on update_phi_bypass-modified instruction gives same result
   when prev_bb <> SOME b. For PHI, resolve_phi gives same result because:
   - MEM (Label a) case: resolve_phi_remove_neq_local (prev <> b)
   - NOT MEM (Label a) case: can't have prev = a (fn_phi_resolve_complete),
     so prev <> a /\ prev <> b, use resolve_phi_rename_neq_local *)
Triviality step_inst_update_phi_bypass_eq_D1:
  !fuel ctx inst s a_lbl b_lbl func target.
    s.vs_prev_bb <> SOME b_lbl /\
    a_lbl <> b_lbl /\
    inst_wf inst /\
    MEM inst target.bb_instructions /\
    MEM target func.fn_blocks /\
    bb_well_formed target /\
    fn_phi_resolve_complete func /\
    (!lbl. s.vs_prev_bb = SOME lbl ==>
       MEM lbl (pred_labels func target.bb_label)) ==>
    step_inst fuel ctx (update_phi_bypass a_lbl b_lbl inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (
    `(update_phi_bypass a_lbl b_lbl inst).inst_opcode = PHI` by
      simp[simplifyCfgWfTheory.update_phi_bypass_opcode] >>
    `inst.inst_opcode <> INVOKE` by gvs[] >>
    `(update_phi_bypass a_lbl b_lbl inst).inst_opcode <> INVOKE` by gvs[] >>
    NTAC 2 (ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_defs]) >>
    ASM_REWRITE_TAC[] >>
    (* Both sides use step_inst_base for PHI *)
    PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[] >>
    (* inst_outputs preserved *)
    `(update_phi_bypass a_lbl b_lbl inst).inst_outputs = inst.inst_outputs` by
      (rw[update_phi_bypass_def, LET_THM]) >>
    ASM_REWRITE_TAC[] >>
    (* Show resolve_phi gives same result *)
    Cases_on `inst.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    Cases_on `s.vs_prev_bb` >> gvs[] >>
    rename1 `SOME prev` >>
    `prev <> b_lbl` by (CCONTR_TAC >> gvs[]) >>
    rw[update_phi_bypass_def, LET_THM]
    >- simp[resolve_phi_remove_neq_local]
    >>
    (* rename case: prev <> b, need prev <> a *)
    `MEM prev (pred_labels func target.bb_label)` by metis_tac[] >>
    (* Derive resolve_phi SOME from fn_phi_resolve_complete *)
    `?val_op. resolve_phi prev inst.inst_operands = SOME val_op` by (
      mp_tac (REWRITE_RULE[fn_phi_resolve_complete_def]
        (ASSUME ``fn_phi_resolve_complete func``)) >>
      disch_then (qspecl_then [`target`, `inst`, `prev`] mp_tac) >>
      simp[]) >>
    `prev <> a_lbl` by (
      CCONTR_TAC >> gvs[] >>
      imp_res_tac resolve_phi_SOME_MEM_Label >> gvs[]) >>
    `phi_well_formed inst.inst_operands` by (
      fs[venomWfTheory.inst_wf_def] >>
      metis_tac[phi_operands_wf_implies_phi_well_formed_early]) >>
    simp[resolve_phi_rename_neq_local])
  >>
  simp[simplifyCfgWfTheory.update_phi_bypass_non_phi]
QED

(* run_block_non_phis insensitive to update_phi_bypass when all remaining
   instructions (from vs_inst_idx onward) are non-PHI. *)
Triviality run_block_non_phis_update_phi_bypass_eq:
  !fuel ctx bb s a b.
    (!i. s.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions ==>
         (EL i bb.bb_instructions).inst_opcode <> PHI) ==>
    run_block_non_phis fuel ctx
      (bb with bb_instructions := MAP (update_phi_bypass a b) bb.bb_instructions) s =
    run_block_non_phis fuel ctx bb s
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_non_phis_def] >>
  simp[get_instruction_def, listTheory.EL_MAP,
       simplifyCfgWfTheory.update_phi_bypass_opcode] >>
  rw[] >>
  `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> PHI` by (
    first_x_assum irule >> simp[]) >>
  simp[step_inst_update_phi_bypass_eq]
QED

(* D1: run_block_non_phis insensitive to update_phi_bypass when prev <> b.
   Uses step_inst_update_phi_bypass_eq_D1 for each instruction. *)
Triviality run_block_non_phis_update_phi_bypass_eq_D1:
  !fuel ctx target s a_lbl b_lbl func.
    s.vs_prev_bb <> SOME b_lbl /\
    (!lbl. s.vs_prev_bb = SOME lbl ==>
       MEM lbl (pred_labels func target.bb_label)) /\
    a_lbl <> b_lbl /\
    bb_well_formed target /\ EVERY inst_wf target.bb_instructions /\
    MEM target func.fn_blocks /\
    fn_phi_resolve_complete func ==>
    run_block_non_phis fuel ctx
      (target with bb_instructions :=
        MAP (update_phi_bypass a_lbl b_lbl) target.bb_instructions) s =
    run_block_non_phis fuel ctx target s
Proof
  completeInduct_on `LENGTH target.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_non_phis_def] >>
  simp[get_instruction_def, listTheory.EL_MAP,
       simplifyCfgWfTheory.update_phi_bypass_opcode] >>
  rw[] >>
  qabbrev_tac `inst = EL s.vs_inst_idx target.bb_instructions` >>
  `inst_wf inst` by (unabbrev_all_tac >> gvs[listTheory.EVERY_EL]) >>
  `MEM inst target.bb_instructions` by (
    unabbrev_all_tac >> simp[listTheory.MEM_EL] >> metis_tac[]) >>
  `step_inst fuel ctx (update_phi_bypass a_lbl b_lbl inst) s =
   step_inst fuel ctx inst s` by
    metis_tac[step_inst_update_phi_bypass_eq_D1] >>
  ASM_REWRITE_TAC[] >>
  (* After step_inst: result is same, so IH applies to continuation *)
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  (* Non-terminator OK: step_inst preserves prev_bb *)
  `v.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[venomExecProofsTheory.step_inst_preserves_prev_bb] >>
  first_x_assum (qspec_then
    `LENGTH target.bb_instructions - (s.vs_inst_idx + 1)` mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`target`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `a_lbl`, `b_lbl`, `func`] mp_tac) >>
  simp[]
QED

(* run_block_non_phis preserves prev_bb_equiv when starting past PHI prefix.
   PHI instructions use vs_prev_bb which can differ between prev_bb_equiv states. *)
Triviality run_block_non_phis_prev_bb_equiv:
  !m fuel ctx bb s1 s2.
    m = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
    prev_bb_equiv s1 s2 /\ s1.vs_inst_idx = s2.vs_inst_idx /\
    (!i. s1.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions ==>
         (EL i bb.bb_instructions).inst_opcode <> PHI) ==>
    result_prev_bb_equiv
      (run_block_non_phis fuel ctx bb s1)
      (run_block_non_phis fuel ctx bb s2)
Proof
  completeInduct_on `m` >> rpt strip_tac >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_non_phis_def] >>
  simp[get_instruction_def] >>
  Cases_on `s1.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[]
  >- (
    qpat_assum `s1.vs_inst_idx = s2.vs_inst_idx`
      (fn th => REWRITE_TAC[GSYM th]) >>
    qabbrev_tac `inst = EL s1.vs_inst_idx bb.bb_instructions` >>
    (* Current instruction is non-PHI *)
    `inst.inst_opcode <> PHI` by (
      unabbrev_all_tac >> first_x_assum irule >> simp[]) >>
    `result_prev_bb_equiv
      (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)` by
      metis_tac[simplifyCfgPrevBBTheory.step_inst_all_prev_bb_equiv] >>
    Cases_on `step_inst fuel ctx inst s1` >>
    Cases_on `step_inst fuel ctx inst s2` >>
    fs[result_prev_bb_equiv_def] >>
    TRY (simp[result_prev_bb_equiv_def] >> NO_TAC) >>
    rename1 `step_inst fuel ctx inst s1 = OK v1` >>
    rename1 `step_inst _ _ _ s2 = OK v2` >>
    Cases_on `is_terminator inst.inst_opcode` >> simp[]
    >- (
      `v1.vs_halted = v2.vs_halted` by
        fs[prev_bb_equiv_def,
           venomStateTheory.venom_state_component_equality] >>
      Cases_on `v1.vs_halted` >> simp[] >>
      fs[prev_bb_equiv_def])
    >>
    `prev_bb_equiv (v1 with vs_inst_idx := SUC s1.vs_inst_idx)
                   (v2 with vs_inst_idx := SUC s1.vs_inst_idx)` by
      (irule simplifyCfgPrevBBTheory.prev_bb_equiv_update_idx >> simp[]) >>
    qpat_x_assum `!m'. m' < _ ==> _`
      (qspec_then `LENGTH bb.bb_instructions - (s1.vs_inst_idx + 1)` mp_tac) >>
    impl_tac >- simp[] >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bb`,
      `v1 with vs_inst_idx := SUC s1.vs_inst_idx`,
      `v2 with vs_inst_idx := SUC s1.vs_inst_idx`] mp_tac) >>
    simp[])
  >>
  simp[result_prev_bb_equiv_def]
QED

(* ===== End decomposition helpers ===== *)

(* Per-instruction step simulation for update_phi_bypass.
   PHI: uses D2 helper. Non-PHI: identity + step_inst_all_prev_bb_equiv.
   Factored out to avoid duplication in run_block induction. *)
Triviality step_phi_bypass_prev_bb_equiv_inst:
  !fuel ctx inst s1 s2 a_lbl b_lbl func target.
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME b_lbl /\ s2.vs_prev_bb = SOME a_lbl /\
    a_lbl <> b_lbl /\ inst_wf inst /\
    MEM inst target.bb_instructions /\
    MEM target func.fn_blocks /\
    fn_phi_preds_wf func /\ fn_phi_resolve_complete func /\
    MEM b_lbl (pred_labels func target.bb_label) /\
    phi_values_agree a_lbl b_lbl target.bb_instructions /\
    bb_well_formed target ==>
    result_prev_bb_equiv
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx (update_phi_bypass a_lbl b_lbl inst) s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (
    match_mp_tac step_phi_update_bypass_D2 >>
    qexistsl_tac [`func`, `target`] >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    (* PHIs-first ordering from bb_well_formed *)
    fs[bb_well_formed_def])
  >>
  `update_phi_bypass a_lbl b_lbl inst = inst` by
    simp[update_phi_bypass_def] >>
  ASM_REWRITE_TAC[] >>
  metis_tac[simplifyCfgPrevBBTheory.step_inst_all_prev_bb_equiv]
QED

(* Per-block simulation: run_block on target vs target' (MAP update_phi_bypass)
   gives result_prev_bb_equiv.
   Uses step_phi_bypass_prev_bb_equiv_inst for each instruction. *)
Triviality run_block_phi_bypass_prev_bb_equiv_helper:
  !m fuel ctx target s1 s2 a_lbl b_lbl func.
    m = LENGTH target.bb_instructions - s1.vs_inst_idx /\
    prev_bb_equiv s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = SOME b_lbl /\ s2.vs_prev_bb = SOME a_lbl /\
    a_lbl <> b_lbl /\
    bb_well_formed target /\ EVERY inst_wf target.bb_instructions /\
    MEM target func.fn_blocks /\
    fn_phi_preds_wf func /\ fn_phi_resolve_complete func /\
    MEM b_lbl (pred_labels func target.bb_label) /\
    phi_values_agree a_lbl b_lbl target.bb_instructions ==>
    result_prev_bb_equiv
      (run_block_non_phis fuel ctx target s1)
      (run_block_non_phis fuel ctx
        (target with bb_instructions :=
          MAP (update_phi_bypass a_lbl b_lbl) target.bb_instructions) s2)
Proof
  completeInduct_on `m` >> rpt strip_tac >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_non_phis_def] >>
  simp[get_instruction_def, listTheory.EL_MAP,
       simplifyCfgWfTheory.update_phi_bypass_opcode] >>
  Cases_on `s1.vs_inst_idx < LENGTH target.bb_instructions` >> simp[]
  >- (
    qpat_assum `s1.vs_inst_idx = s2.vs_inst_idx`
      (fn th => REWRITE_TAC[GSYM th]) >>
    qabbrev_tac `inst = EL s1.vs_inst_idx target.bb_instructions` >>
    `inst_wf inst` by (unabbrev_all_tac >> gvs[listTheory.EVERY_EL]) >>
    `MEM inst target.bb_instructions` by (
      unabbrev_all_tac >> simp[listTheory.MEM_EL] >> metis_tac[]) >>
    (* Use step_phi_bypass_prev_bb_equiv_inst *)
    `result_prev_bb_equiv
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx (update_phi_bypass a_lbl b_lbl inst) s2)` by
      metis_tac[step_phi_bypass_prev_bb_equiv_inst] >>
    Cases_on `step_inst fuel ctx inst s1` >>
    Cases_on `step_inst fuel ctx (update_phi_bypass a_lbl b_lbl inst) s2` >>
    fs[result_prev_bb_equiv_def] >>
    TRY (simp[result_prev_bb_equiv_def] >> NO_TAC) >>
    (* OK-OK case *)
    rename1 `step_inst fuel ctx inst s1 = OK r1` >>
    rename1 `step_inst _ _ (update_phi_bypass _ _ _) s2 = OK r2` >>
    Cases_on `is_terminator inst.inst_opcode` >>
    simp[simplifyCfgWfTheory.update_phi_bypass_opcode]
    >- (
      `r1.vs_halted = r2.vs_halted` by
        fs[prev_bb_equiv_def,
           venomStateTheory.venom_state_component_equality] >>
      Cases_on `r1.vs_halted` >> simp[] >>
      fs[prev_bb_equiv_def])
    >>
    (* Non-terminator: step_inst preserves prev_bb *)
    `r1.vs_prev_bb = s1.vs_prev_bb` by
      metis_tac[venomExecProofsTheory.step_inst_preserves_prev_bb] >>
    `r2.vs_prev_bb = s2.vs_prev_bb` by (
      `~is_terminator (update_phi_bypass a_lbl b_lbl inst).inst_opcode` by
        simp[simplifyCfgWfTheory.update_phi_bypass_opcode] >>
      metis_tac[venomExecProofsTheory.step_inst_preserves_prev_bb]) >>
    `prev_bb_equiv (r1 with vs_inst_idx := SUC s1.vs_inst_idx)
                   (r2 with vs_inst_idx := SUC s1.vs_inst_idx)` by (
      irule simplifyCfgPrevBBTheory.prev_bb_equiv_update_idx >> simp[]) >>
    simp[simplifyCfgWfTheory.update_phi_bypass_opcode] >>
    qpat_x_assum `!m'. m' < _ ==> _`
      (qspec_then `LENGTH target.bb_instructions - (s1.vs_inst_idx + 1)` mp_tac) >>
    impl_tac >- simp[] >>
    disch_then (qspecl_then [`fuel`, `ctx`, `target`,
      `r1 with vs_inst_idx := SUC s1.vs_inst_idx`,
      `r2 with vs_inst_idx := SUC s1.vs_inst_idx`,
      `a_lbl`, `b_lbl`, `func`] mp_tac) >>
    simp[])
  >>
  simp[result_prev_bb_equiv_def]
QED

(* Wrapper: run_block version *)
Triviality run_block_phi_bypass_prev_bb_equiv:
  !fuel ctx target s1 s2 a_lbl b_lbl func.
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME b_lbl /\ s2.vs_prev_bb = SOME a_lbl /\
    a_lbl <> b_lbl /\
    bb_well_formed target /\ EVERY inst_wf target.bb_instructions /\
    MEM target func.fn_blocks /\
    fn_phi_preds_wf func /\ fn_phi_resolve_complete func /\
    MEM b_lbl (pred_labels func target.bb_label) /\
    phi_values_agree a_lbl b_lbl target.bb_instructions ==>
    result_prev_bb_equiv
      (run_block fuel ctx target s1)
      (run_block fuel ctx
        (target with bb_instructions :=
          MAP (update_phi_bypass a_lbl b_lbl) target.bb_instructions) s2)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_def] >>
  irule (REWRITE_RULE[PULL_FORALL, AND_IMP_INTRO]
    run_block_phi_bypass_prev_bb_equiv_helper) >>
  simp[] >> conj_tac
  >- (qexists_tac `func` >> simp[]) >>
  gvs[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
QED

(* D1 block-level: run_block on target = run_block on target' when prev_bb ≠ SOME b.
   update_phi_bypass doesn't change PHI resolution when prev_bb isn't b. *)
Triviality run_block_update_phi_bypass_eq_D1:
  !m fuel ctx target s a_lbl b_lbl func.
    m = LENGTH target.bb_instructions - s.vs_inst_idx /\
    s.vs_prev_bb <> SOME b_lbl /\
    (∀lbl. s.vs_prev_bb = SOME lbl ==>
       MEM lbl (pred_labels func target.bb_label)) /\
    a_lbl <> b_lbl /\
    bb_well_formed target /\ EVERY inst_wf target.bb_instructions /\
    MEM target func.fn_blocks /\
    fn_phi_preds_wf func /\ fn_phi_preds_complete func /\
    fn_phi_resolve_complete func /\
    phi_values_agree a_lbl b_lbl target.bb_instructions ==>
    run_block fuel ctx target s =
    run_block fuel ctx (target with bb_instructions :=
      MAP (update_phi_bypass a_lbl b_lbl) target.bb_instructions) s
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_def] >>
  `run_block_non_phis fuel ctx
     (target with bb_instructions :=
       MAP (update_phi_bypass a_lbl b_lbl) target.bb_instructions)
     (s with vs_inst_idx := 0) =
   run_block_non_phis fuel ctx target (s with vs_inst_idx := 0)` by (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `target`,
      `s with vs_inst_idx := 0`, `a_lbl`, `b_lbl`, `func`]
      run_block_non_phis_update_phi_bypass_eq_D1) >>
    simp[]) >>
  ASM_REWRITE_TAC[]
QED

(* --- WF preservation for update_phi_bypass --- *)

Triviality update_phi_bypass_opcode:
  !a b inst. (update_phi_bypass a b inst).inst_opcode = inst.inst_opcode
Proof
  rw[update_phi_bypass_def]
QED

Triviality bb_well_formed_update_phi_bypass:
  !a_lbl b_lbl bb. bb_well_formed bb ==>
    bb_well_formed (bb with bb_instructions :=
      MAP (update_phi_bypass a_lbl b_lbl) bb.bb_instructions)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[GSYM indexedListsTheory.MAPi_EQ_MAP] >>
  irule passSimulationPropsTheory.mapi_transform_bb_well_formed >>
  simp[update_phi_bypass_opcode]
QED

Triviality EVERY_inst_wf_update_phi_bypass:
  !a_lbl b_lbl insts. EVERY inst_wf insts ==>
    EVERY inst_wf (MAP (update_phi_bypass a_lbl b_lbl) insts)
Proof
  rw[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  metis_tac[simplifyCfgHelpersTheory.inst_wf_update_phi_bypass]
QED

(* --- at_target: current_bb = target_lbl --- *)

(* Helper: non-OK result on LHS, with result_prev_bb_equiv → result_equiv on run_blockss.
   Takes the non-OK result R1 directly so callers in case-split context don't need
   to reconstruct !v. run_block ... <> OK v. *)
Triviality nonOK_pair_sim:
  !n ctx func1 bb1 s1 func2 bb2 s2 R1.
    lookup_block s1.vs_current_bb func1.fn_blocks = SOME bb1 /\
    lookup_block s2.vs_current_bb func2.fn_blocks = SOME bb2 /\
    run_block n ctx bb1 s1 = R1 /\ (!v. R1 <> OK v) /\
    result_prev_bb_equiv R1 (run_block n ctx bb2 s2) /\
    s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
    s2.vs_inst_idx = 0 /\ ~s2.vs_halted ==>
    result_equiv {}
      (run_blocks (SUC n) ctx func1 s1)
      (run_blocks (SUC n) ctx func2 s2)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`n`,`ctx`,`func1`,`bb1`,`s1`, `R1`] rf_nonOK_match) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  `!v. run_block n ctx bb2 s2 <> OK v` by (
    strip_tac >> spose_not_then assume_tac >>
    fs[simplifyCfgPrevBBTheory.result_prev_bb_equiv_def] >>
    Cases_on `R1` >>
    fs[simplifyCfgPrevBBTheory.result_prev_bb_equiv_def]) >>
  mp_tac (Q.SPECL [`n`,`ctx`,`func2`,`bb2`,`s2`,
    `run_block n ctx bb2 s2`] rf_nonOK_match) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  irule simplifyCfgPrevBBTheory.result_prev_bb_equiv_terminal_implies_result_equiv >>
  simp[]
QED

(* nonOK_pair_sim with fuel witness: used by all simulation cases for non-OK branches *)
Triviality nonOK_pair_sim_fuel:
  !n ctx func1 bb1 s1 func2 bb2 s2 R1.
    lookup_block s1.vs_current_bb func1.fn_blocks = SOME bb1 /\
    lookup_block s2.vs_current_bb func2.fn_blocks = SOME bb2 /\
    run_block n ctx bb1 s1 = R1 /\ (!v. R1 <> OK v) /\
    result_prev_bb_equiv R1 (run_block n ctx bb2 s2) /\
    s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
    s2.vs_inst_idx = 0 /\ ~s2.vs_halted ==>
    ?fuel'.
      SUC n <= fuel' /\
      result_equiv {}
        (run_blocks fuel' ctx func1 s1)
        (run_blocks (SUC n) ctx func2 s2)
Proof
  rpt strip_tac >>
  qexists_tac `SUC n` >> conj_tac >- simp[] >>
  irule nonOK_pair_sim >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`R1`, `bb1`, `bb2`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Reusable: derive MEM bb.bb_label (pred_labels func lbl) from
   MEM bb func.fn_blocks and MEM lbl (bb_succs bb) *)
Triviality mem_pred_labels:
  !bb func lbl. MEM bb func.fn_blocks /\ MEM lbl (bb_succs bb) ==>
    MEM bb.bb_label (pred_labels func lbl)
Proof
  simp[cfgTransformTheory.pred_labels_def,
       cfgTransformTheory.block_preds_def,
       listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

(* D2 OK case: run_block returns OK on original, prev_bb_equiv gives equal post-states *)
Triviality at_target_sim_D2_OK:
  !func a b target_lbl target target' n ctx s1 s2 v1 v2 a' func2.
    wf_function func /\ fn_inst_wf func /\
    can_bypass_jump func a b /\ bb_succs b = [target_lbl] /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    MEM target func.fn_blocks /\
    target.bb_label = target_lbl /\
    lookup_block target_lbl func.fn_blocks = SOME target /\
    lookup_block a.bb_label func.fn_blocks = SOME a /\
    lookup_block b.bb_label func.fn_blocks = SOME b /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    a.bb_label <> b.bb_label /\
    a.bb_label <> target_lbl /\ b.bb_label <> target_lbl /\
    bb_well_formed target /\ EVERY inst_wf target.bb_instructions /\
    bb_well_formed target' /\ EVERY inst_wf target'.bb_instructions /\
    run_block n ctx target s1 = OK v1 /\
    run_block n ctx target' s2 = OK v2 /\
    prev_bb_equiv v1 v2 /\
    s1.vs_current_bb = target_lbl /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    ~s1.vs_halted /\ ~s2.vs_halted /\
    prev_bb_valid func s1 /\
    lookup_block target_lbl func2.fn_blocks = SOME target' /\
    (!m. m < SUC n ==>
      !ctx' s1' s2'.
        bypass_R a.bb_label b.bb_label target_lbl s1' s2' /\
        prev_bb_valid func s1' /\
        s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
        ~s1'.vs_halted /\ ~s2'.vs_halted /\
        s1'.vs_current_bb <> b.bb_label ==>
      ?fuel'.
        m <= fuel' /\
        result_equiv {} (run_blocks fuel' ctx' func s1')
          (run_blocks m ctx' func2 s2')) ==>
    ?fuel'.
      SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s1)
        (run_blocks (SUC n) ctx func2 s2)
Proof
  rpt strip_tac >> gvs[] >>
  `v1.vs_prev_bb = SOME s1.vs_current_bb` by
    metis_tac[simplifyCfgCollapseBaseTheory.run_block_ok_prev_bb_wf] >>
  `v2.vs_prev_bb = SOME s2.vs_current_bb` by
    metis_tac[simplifyCfgCollapseBaseTheory.run_block_ok_prev_bb_wf] >>
  `v1.vs_prev_bb = v2.vs_prev_bb` by ASM_REWRITE_TAC[] >>
  `v1 = v2` by (
    qpat_x_assum `prev_bb_equiv v1 v2` mp_tac >>
    simp[simplifyCfgPrevBBTheory.prev_bb_equiv_def,
         venomStateTheory.venom_state_component_equality]) >>
  gvs[] >>
  `~v1.vs_halted` by
    metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `v1.vs_inst_idx = 0` by
    metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  `v1.vs_current_bb <> b.bb_label` by (
    `MEM v1.vs_current_bb (bb_succs target)` by
      metis_tac[simplifyCfgCollapseBaseTheory.run_block_current_bb_in_succs_wf] >>
    `~MEM b.bb_label (bb_succs target)` by (
      MATCH_MP_TAC sole_pred_no_other_succ >>
      qexistsl_tac [`func`, `a`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum `can_bypass_jump _ _ _` mp_tac >>
      simp[simplifyCfgDefsTheory.can_bypass_jump_def]) >>
    metis_tac[listTheory.MEM]) >>
  `prev_bb_valid func v1` by (
    mp_tac prev_bb_valid_preserved >>
    disch_then (qspecl_then [`func`,`n`,`ctx`,`target`,`s1`,`v1`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_assum `s1.vs_current_bb = _` (fn th => REWRITE_TAC[th]) >>
      first_assum ACCEPT_TAC)) >>
    simp[prev_bb_valid_def]) >>
  qpat_x_assum `!m. m < SUC n ==> _` (qspec_then `n` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`ctx`, `v1`, `v1`] mp_tac) >>
  (impl_tac >- (
    simp[bypass_R_def] >> disj1_tac >> simp[] >>
    qpat_x_assum `v1.vs_prev_bb = _` (fn th => REWRITE_TAC[th]) >>
    metis_tac[])) >>
  strip_tac >>
  `run_block fuel' ctx target s1 = OK v1` by (
    mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
    disch_then (qspecl_then [`n`,`fuel'`,`ctx`,`target`,`s1`,`OK v1`]
      mp_tac) >> simp[]) >>
  `run_block fuel' ctx target' s2 = OK v1` by (
    mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
    disch_then (qspecl_then [`n`,`fuel'`,`ctx`,`target'`,`s2`,`OK v1`]
      mp_tac) >> simp[]) >>
  qexists_tac `SUC fuel'` >> conj_tac >- simp[] >>
  UNFOLD_RF_STEP_TAC (RATOR_CONV o RAND_CONV) >>
  UNFOLD_RF_STEP_TAC RAND_CONV
QED

(* D2 case extracted as standalone Triviality to avoid 30+ assumption timeouts *)
Triviality at_target_sim_D2:
  !func a b target_lbl target a' target' n ctx s1 s2.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\
    fn_phi_preds_complete func /\
    fn_phi_resolve_complete func /\
    fn_bypass_safe func /\
    MEM a func.fn_blocks /\
    MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    bb_succs b = [target_lbl] /\
    lookup_block target_lbl func.fn_blocks = SOME target /\
    lookup_block a.bb_label func.fn_blocks = SOME a /\
    lookup_block b.bb_label func.fn_blocks = SOME b /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
    a.bb_label <> b.bb_label /\
    a.bb_label <> target_lbl /\
    b.bb_label <> target_lbl /\
    a' = a with bb_instructions :=
      MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                  else subst_label_inst b.bb_label target_lbl inst)
        a.bb_instructions /\
    target' = target with bb_instructions :=
      MAP (update_phi_bypass a.bb_label b.bb_label) target.bb_instructions /\
    target.bb_label = target_lbl /\
    (* D2-specific hypotheses *)
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME b.bb_label /\
    s2.vs_prev_bb = SOME a.bb_label /\
    prev_bb_valid func s1 /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    ~s1.vs_halted /\ ~s2.vs_halted /\
    s1.vs_current_bb = target_lbl /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_current_bb <> b.bb_label /\
    bb_well_formed target /\
    EVERY inst_wf target.bb_instructions /\
    MEM target func.fn_blocks /\
    (!m. m < SUC n ==>
      !ctx' s1' s2'.
        bypass_R a.bb_label b.bb_label target_lbl s1' s2' /\
        prev_bb_valid func s1' /\
        s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
        ~s1'.vs_halted /\ ~s2'.vs_halted /\
        s1'.vs_current_bb <> b.bb_label ==>
      ?fuel'.
        m <= fuel' /\
        result_equiv {} (run_blocks fuel' ctx' func s1')
          (run_blocks m ctx'
            (func with fn_blocks :=
              replace_block a.bb_label a'
                (replace_block target_lbl target'
                  (remove_block b.bb_label func.fn_blocks))) s2')) ==>
    ?fuel'.
      SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s1)
        (run_blocks (SUC n) ctx
          (func with fn_blocks :=
            replace_block a.bb_label a'
              (replace_block target_lbl target'
                (remove_block b.bb_label func.fn_blocks))) s2)
Proof
  rpt strip_tac >>
  qpat_assum `bb_well_formed target`
    (fn th => ASSUME_TAC (MATCH_MP bb_well_formed_update_phi_bypass th)) >>
  qpat_assum `EVERY inst_wf target.bb_instructions`
    (fn th => ASSUME_TAC (MATCH_MP EVERY_inst_wf_update_phi_bypass th)) >>
  (* Derive bb_well_formed target' and EVERY inst_wf target'.bb_instructions
     by specializing the universals and rewriting with target' equation *)
  qpat_assum `!a_lbl b_lbl. bb_well_formed _` (fn wf_all =>
  qpat_assum `!a_lbl b_lbl. EVERY inst_wf _` (fn iw_all =>
  qpat_assum `target' = _` (fn t'eq =>
    let val wf_spec = REWRITE_RULE [GSYM t'eq]
          (SPECL [``a.bb_label``, ``b.bb_label``] wf_all)
        val iw_spec = SPECL [``a.bb_label``, ``b.bb_label``] iw_all
        (* Derive target'.bb_instructions = MAP ... from t'eq *)
        val insts_eq = AP_TERM ``basic_block_bb_instructions`` t'eq
        (* insts_eq : target'.bb_instructions = (target with ...).bb_instructions *)
        (* Reduce the RHS accessor *)
        val insts_eq' = CONV_RULE (RAND_CONV EVAL) insts_eq
        (* Now iw_spec : EVERY inst_wf (MAP ...) and
           insts_eq' : target'.bb_instructions = MAP ...
           Combine: EVERY inst_wf target'.bb_instructions *)
        val iw_target' = REWRITE_RULE [SYM insts_eq'] iw_spec
    in
      ASSUME_TAC wf_spec >>
      ASSUME_TAC iw_target' >>
      ASSUME_TAC wf_all >> ASSUME_TAC iw_all >> ASSUME_TAC t'eq
    end))) >>
  mp_tac (Q.SPECL [`b`, `func`, `target_lbl`] mem_pred_labels) >>
  (impl_tac >- (
    qpat_assum `bb_succs b = _` (fn th => REWRITE_TAC[th, listTheory.MEM]) >>
    first_assum ACCEPT_TAC)) >>
  disch_tac >>
  qpat_assum `s1.vs_inst_idx = 0` (fn idx1 =>
  qpat_assum `s2.vs_inst_idx = 0` (fn idx2 =>
    ASSUME_TAC idx1 >> ASSUME_TAC idx2 >>
    ASSUME_TAC (TRANS idx1 (SYM idx2)))) >>
  qpat_assum `target.bb_label = _` (fn lbl_eq =>
    mp_tac (REWRITE_RULE [lbl_eq] (Q.SPECL [
      `n`, `ctx`, `target`, `s1`, `s2`, `a.bb_label`, `b.bb_label`, `func`]
      run_block_phi_bypass_prev_bb_equiv)) >>
    ASSUME_TAC lbl_eq) >>
  (impl_tac >- (
    rpt conj_tac >> TRY REFL_TAC >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  mp_tac (Q.SPECL [`a.bb_label`, `target_lbl`, `b.bb_label`,
    `a'`, `target'`, `func.fn_blocks`] lookup_block_bypass_full) >>
  (impl_tac >- (
    qpat_assum `a' = _` (fn a'eq =>
    qpat_assum `target' = _` (fn t'eq =>
      REWRITE_TAC[a'eq, t'eq] >> ASSUME_TAC a'eq >> ASSUME_TAC t'eq)) >>
    simp_tac (srw_ss()) [] >>
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    TRY (qpat_assum `b.bb_label <> target_lbl`
      (ACCEPT_TAC o GSYM)) >>
    metis_tac[])) >>
  strip_tac >>
  (* Fold target' into result_prev_bb_equiv *)
  qpat_x_assum `result_prev_bb_equiv _ _` (fn th =>
    qpat_assum `target' = _` (fn eq =>
      ASSUME_TAC (REWRITE_RULE [GSYM eq] th))) >>
  qabbrev_tac `func2 = func with fn_blocks :=
    replace_block a.bb_label a'
      (replace_block target_lbl target'
        (remove_block b.bb_label func.fn_blocks))` >>
  qabbrev_tac `R1 = run_block n ctx target s1` >>
  Cases_on `R1`
  >- suspend "OK"
  >> ( (* Non-OK cases: Halt/Abort/IntRet/Error — handle uniformly *)
    qpat_x_assum `Abbrev (R1 = _)`
      (ASSUME_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    qpat_assum `run_block n ctx target s1 = _` (fn rb_eq =>
      let val R = rb_eq |> concl |> rhs in
      mp_tac (Q.SPECL [`n`, `ctx`, `func`, `target`, `s1`,
        `func2`, `target'`, `s2`, `^R`] nonOK_pair_sim_fuel)
      end) >>
    (* Expand func2 in goal only (NOT qunabbrev which is too slow) *)
    qpat_assum `Abbrev (func2 = _)` (fn abbr =>
      PURE_REWRITE_TAC[REWRITE_RULE [markerTheory.Abbrev_def] abbr,
                       fn_blocks_with] >>
      ASSUME_TAC abbr) >>
    (impl_tac >- (
      qpat_assum `s1.vs_current_bb = target_lbl` (fn cb =>
      qpat_assum `s1.vs_current_bb = s2.vs_current_bb` (fn eq =>
        REWRITE_TAC[cb, GSYM (REWRITE_RULE [cb] eq)] >>
        ASSUME_TAC cb >> ASSUME_TAC eq)) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp_tac (srw_ss()) [])) >>
    REWRITE_TAC[])
QED

Resume at_target_sim_D2[OK]:
  qpat_x_assum `Abbrev (OK _ = _)`
    (ASSUME_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule simplifyCfgCollapseBaseTheory.result_prev_bb_equiv_OK_left >>
  strip_tac >> rename1 `prev_bb_equiv v v2` >>
  (* Apply at_target_sim_D2_OK — bb_well_formed/EVERY inst_wf target' already
     derived in at_target_sim_D2 before the case split *)
  mp_tac (Q.SPECL
    [`func`,`a`,`b`,`target_lbl`,`target`,`target'`,`n`,`ctx`,`s1`,`s2`,
     `v`,`v2`,`a'`,`func2`] at_target_sim_D2_OK) >>
  (* Fold lookup result into func2 form via ML-level rewrite *)
  qpat_x_assum `lookup_block target_lbl
    (replace_block _ _ (replace_block _ _ (remove_block _ _))) = _`
    (fn lookup_th => qpat_assum `Abbrev (func2 = _)` (fn abbr =>
      let val abbr_eq = REWRITE_RULE [markerTheory.Abbrev_def] abbr
          val fn_blocks_eq = AP_TERM ``ir_function_fn_blocks`` abbr_eq
          val fn_blocks_eq' = CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [])) fn_blocks_eq
      in ASSUME_TAC (REWRITE_RULE [SYM fn_blocks_eq'] lookup_th) >>
         ASSUME_TAC abbr end)) >>
  (impl_tac >- (
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  REWRITE_TAC[]
QED

Finalise at_target_sim_D2;

(* Helper: at target block, the D1 case gives identical run_block,
   the D2 case collapses to D1 after one step *)
Triviality at_target_sim:
  !func a b target_lbl target a' target' n ctx s1 s2.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\
    fn_phi_preds_complete func /\
    fn_phi_resolve_complete func /\
    fn_bypass_safe func /\
    MEM a func.fn_blocks /\
    MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    bb_succs b = [target_lbl] /\
    lookup_block target_lbl func.fn_blocks = SOME target /\
    lookup_block a.bb_label func.fn_blocks = SOME a /\
    lookup_block b.bb_label func.fn_blocks = SOME b /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
    a.bb_label <> b.bb_label /\
    a.bb_label <> target_lbl /\
    b.bb_label <> target_lbl /\
    a' = a with bb_instructions :=
      MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                  else subst_label_inst b.bb_label target_lbl inst)
        a.bb_instructions /\
    target' = target with bb_instructions :=
      MAP (update_phi_bypass a.bb_label b.bb_label) target.bb_instructions /\
    target.bb_label = target_lbl /\
    bypass_R a.bb_label b.bb_label target_lbl s1 s2 /\
    prev_bb_valid func s1 /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    ~s1.vs_halted /\ ~s2.vs_halted /\
    s1.vs_current_bb = target_lbl /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_current_bb <> b.bb_label /\
    (!m. m < SUC n ==>
      !ctx' s1' s2'.
        bypass_R a.bb_label b.bb_label target_lbl s1' s2' /\
        prev_bb_valid func s1' /\
        s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
        ~s1'.vs_halted /\ ~s2'.vs_halted /\
        s1'.vs_current_bb <> b.bb_label ==>
      ?fuel'.
        m <= fuel' /\
        result_equiv {} (run_blocks fuel' ctx' func s1')
          (run_blocks m ctx'
            (func with fn_blocks :=
              replace_block a.bb_label a'
                (replace_block target_lbl target'
                  (remove_block b.bb_label func.fn_blocks))) s2')) ==>
    ?fuel'.
      SUC n <= fuel' /\
      result_equiv {} (run_blocks fuel' ctx func s1)
        (run_blocks (SUC n) ctx
          (func with fn_blocks :=
            replace_block a.bb_label a'
              (replace_block target_lbl target'
                (remove_block b.bb_label func.fn_blocks))) s2)
Proof
  rpt strip_tac >>
  (* Derive wf facts for target *)
  `bb_well_formed target /\ EVERY inst_wf target.bb_instructions` by
    metis_tac[lookup_block_wf_facts] >>
  (* Case split on bypass_R: D1 or D2 *)
  qpat_x_assum `bypass_R _ _ _ _ _` mp_tac >>
  REWRITE_TAC[bypass_R_def] >> strip_tac
  >- (
    (* D1: s1 = s2, s1.vs_prev_bb <> SOME b.bb_label *)
    gvs[] >>
    (* Derive shared facts *)
    `MEM target func.fn_blocks` by
      metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
    mp_tac (Q.SPECL [`LENGTH target.bb_instructions - s1.vs_inst_idx`,
      `n`, `ctx`, `target`, `s1`, `a.bb_label`, `b.bb_label`, `func`]
      run_block_update_phi_bypass_eq_D1) >>
    (impl_tac >- (
      ASM_REWRITE_TAC[] >>
      qpat_x_assum `prev_bb_valid _ _` mp_tac >>
      simp[prev_bb_valid_def])) >>
    disch_tac >>
    `lookup_block target.bb_label
       (replace_block a.bb_label
         (a with bb_instructions := MAP (\inst.
           if ~is_terminator inst.inst_opcode then inst
           else subst_label_inst b.bb_label target.bb_label inst) a.bb_instructions)
         (replace_block target.bb_label
           (target with bb_instructions :=
             MAP (update_phi_bypass a.bb_label b.bb_label) target.bb_instructions)
           (remove_block b.bb_label func.fn_blocks))) =
       SOME (target with bb_instructions :=
         MAP (update_phi_bypass a.bb_label b.bb_label) target.bb_instructions)` by (
      simp[cfgTransformPropsTheory.lookup_block_replace_neq] >>
      irule cfgTransformPropsTheory.lookup_block_replace_eq >>
      simp[] >>
      qexists_tac `target` >>
      simp[cfgTransformPropsTheory.lookup_block_remove_neq]) >>
    (* Case split on run_block n ctx target s1 *)
    Cases_on `run_block n ctx target s1`
    >- (
      rename1 `_ = OK v` >>
      `~v.vs_halted` by
        metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
      `v.vs_prev_bb = SOME s1.vs_current_bb` by
        metis_tac[run_block_ok_prev_bb_wf] >>
      `v.vs_current_bb <> b.bb_label` by (
        `MEM v.vs_current_bb (bb_succs target)` by
          metis_tac[run_block_current_bb_in_succs_wf] >>
        `~MEM b.bb_label (bb_succs target)` by (
          MATCH_MP_TAC sole_pred_no_other_succ >>
          qexistsl_tac [`func`, `a`] >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          qpat_x_assum `can_bypass_jump _ _ _` mp_tac >>
          simp[simplifyCfgDefsTheory.can_bypass_jump_def]) >>
        metis_tac[listTheory.MEM]) >>
      `v.vs_inst_idx = 0` by
        metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
      `prev_bb_valid func v` by (
        mp_tac prev_bb_valid_preserved >>
        disch_then (qspecl_then [`func`,`n`,`ctx`,`target`,`s1`,`v`] mp_tac) >>
        (impl_tac >- (
          qpat_x_assum `s1.vs_current_bb = _` (fn th => REWRITE_TAC[th]) >>
          rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        simp[prev_bb_valid_def]) >>
      (* Apply IH with m=n, instantiate with v directly *)
      qpat_x_assum `!m. m < SUC n ==> _` (qspec_then `n` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qspecl_then [`ctx`, `v`, `v`] mp_tac) >>
      (impl_tac >- (
        simp[bypass_R_def] >>
        disj1_tac >> simp[] >>
        qpat_x_assum `v.vs_prev_bb = _` (fn th => REWRITE_TAC[th]) >>
        qpat_x_assum `s1.vs_current_bb = _` (fn th => REWRITE_TAC[th]) >>
        metis_tac[])) >>
      strip_tac >>
      (* fuel_mono: run_block fuel' ctx target s1 = OK v *)
      `run_block fuel' ctx target s1 = OK v` by (
        mp_tac (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 venomExecPropsTheory.fuel_mono))) >>
        disch_then (qspecl_then [`n`,`fuel'`,`ctx`,`target`,`s1`,`OK v`]
          mp_tac) >> simp[]) >>
      qexists_tac `SUC fuel'` >> conj_tac >- simp[] >>
      (* Flip the D1 eq so ASM_REWRITE_TAC rewrites L→R correctly *)
      qpat_x_assum `OK _ = run_block n _ _ _` (ASSUME_TAC o SYM) >>
      UNFOLD_RF_STEP_TAC (RATOR_CONV o RAND_CONV) >>
      UNFOLD_RF_STEP_TAC RAND_CONV >>
      first_assum ACCEPT_TAC)
    >> ( (* Non-OK cases: Halt/Abort/IntRet/Error — both sides same result *)
      qexists_tac `SUC n` >> simp[] >>
      qpat_x_assum `_ = run_block n _ _ _` (ASSUME_TAC o SYM) >>
      UNFOLD_RF_STEP_TAC (RATOR_CONV o RAND_CONV) >>
      UNFOLD_RF_STEP_TAC RAND_CONV >>
      simp[stateEquivTheory.result_equiv_def,
           stateEquivPropsTheory.execution_equiv_refl])
  )
  >- (
    (* D2: delegate to standalone at_target_sim_D2 *)
    match_mp_tac at_target_sim_D2 >>
    qexists_tac `target` >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    metis_tac[venomExecPropsTheory.lookup_block_MEM, lookup_block_wf_facts])
QED

Resume do_merge_jump_equiv_strong[at_target]:
  match_mp_tac at_target_sim >>
  qexists_tac `target` >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `Abbrev (a' = _)` (ACCEPT_TAC o
    REWRITE_RULE [markerTheory.Abbrev_def])) >>
  TRY (qpat_assum `Abbrev (target' = _)` (ACCEPT_TAC o
    REWRITE_RULE [markerTheory.Abbrev_def]))
QED

Finalise do_merge_jump_equiv_strong

(* Entry-point wrapper: same state, prev_bb = NONE *)
Theorem do_merge_jump_correct[local]:
  !func a b label_map func' lm' target_lbl target.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\
    fn_phi_preds_complete func /\
    fn_phi_resolve_complete func /\
    fn_bypass_safe func /\
    MEM a func.fn_blocks /\
    MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    bb_succs b = [target_lbl] /\
    lookup_block target_lbl func.fn_blocks = SOME target /\
    phi_values_agree a.bb_label b.bb_label target.bb_instructions /\
    do_merge_jump func a b label_map = SOME (func', lm') /\
    a.bb_label <> b.bb_label /\
    a.bb_label <> target_lbl /\
    b.bb_label <> target_lbl ==>
    !fuel ctx s.
      fn_entry_label func = SOME s.vs_current_bb /\
      s.vs_inst_idx = 0 /\
      s.vs_prev_bb = NONE /\
      ~s.vs_halted ==>
    ?fuel'. fuel <= fuel' /\
      result_equiv {}
        (run_blocks fuel' ctx func s)
        (run_blocks fuel ctx func' s)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `a`, `b`, `label_map`, `func'`, `lm'`,
                    `target_lbl`, `target`] do_merge_jump_equiv_strong) >>
  ASM_REWRITE_TAC[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
  impl_tac
  >- (`prev_bb_valid func s` by
        (match_mp_tac prev_bb_valid_NONE >> first_assum ACCEPT_TAC) >>
      ASM_REWRITE_TAC[] >>
      simp[bypass_R_def] >>
      qpat_x_assum `can_bypass_jump _ _ _` mp_tac >>
      simp[can_bypass_jump_def] >>
      metis_tac[])
  >> strip_tac >> qexists_tac `fuel'` >> ASM_REWRITE_TAC[]
QED

(* Well-formedness: bypass candidates don't target their own source block.
   When a.bb_label = target_lbl, do_merge_jump's replace_block ordering
   loses the PHI update (outer replace overwrites inner). This is a
   formalization artifact — Python modifies in-place and doesn't have
   this issue. The condition is trivially satisfied by real compiler output. *)
Definition no_bypass_self_target_def:
  no_bypass_self_target func <=>
    !a b. MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
           can_bypass_jump func a b ==>
           !lbl. MEM lbl (bb_succs b) ==>
             a.bb_label <> lbl /\ ~MEM lbl (bb_succs a)
End

(* General: ALL_DISTINCT (MAP f l) + same image => same element *)
Triviality ALL_DISTINCT_MAP_INJ_MEM:
  !l (a:'a) (b:'a) (f:'a -> 'b).
    ALL_DISTINCT (MAP f l) /\ MEM a l /\ MEM b l /\ f a = f b ==> a = b
Proof
  Induct >> rw[] >> fs[] >> metis_tac[listTheory.MEM_MAP]
QED

(* Helper: derive the three label inequalities needed by do_merge_jump_correct.
   a.bb_label <> target_lbl comes from the try_bypass guard (was: no_bypass_self_target). *)
Triviality bypass_label_inequalities:
  !func a b target_lbl.
    wf_function func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    bb_succs b = [target_lbl] /\
    a.bb_label <> target_lbl ==>
    a.bb_label <> b.bb_label /\
    b.bb_label <> target_lbl /\
    a.bb_label <> target_lbl
Proof
  rpt gen_tac >> strip_tac >>
  fs[can_bypass_jump_def] >> rpt conj_tac
  (* a.bb_label <> b.bb_label *)
  >- (strip_tac >>
      mp_tac (ISPECL [``(func:ir_function).fn_blocks``, ``a:basic_block``,
        ``b:basic_block``, ``\bb:basic_block. bb.bb_label``]
        ALL_DISTINCT_MAP_INJ_MEM) >>
      impl_tac >- fs[wf_function_def, fn_labels_def] >>
      strip_tac >> gvs[cfgTransformTheory.num_succs_def])
  (* b.bb_label <> target_lbl *)
  >- (strip_tac >> gvs[] >>
      fs[cfgTransformTheory.num_preds_def,
         cfgTransformTheory.block_preds_def] >>
      `a <> b` by
        (strip_tac >> gvs[] >> fs[cfgTransformTheory.num_succs_def]) >>
      `MEM a (FILTER (\bb'. MEM b.bb_label (bb_succs bb')) func.fn_blocks)` by
        simp[listTheory.MEM_FILTER] >>
      `MEM b (FILTER (\bb'. MEM b.bb_label (bb_succs bb')) func.fn_blocks)` by
        simp[listTheory.MEM_FILTER] >>
      Cases_on `FILTER (\bb'. MEM b.bb_label (bb_succs bb')) func.fn_blocks` >>
      fs[] >> Cases_on `t` >> fs[])
QED

Theorem try_bypass_correct[local]:
  !func label_map bb succs func' lm' fuel ctx s.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\
    fn_phi_preds_complete func /\
    fn_phi_resolve_complete func /\
    fn_bypass_safe func /\
    MEM bb func.fn_blocks /\
    try_bypass func label_map bb succs = (func', lm', T) /\
    fn_entry_label func = SOME s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    ~s.vs_halted ==>
    ?fuel'. fuel <= fuel' /\
      result_equiv {}
        (run_blocks fuel' ctx func s)
        (run_blocks fuel ctx func' s)
Proof
  Induct_on `succs` >> rw[try_bypass_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  (* IH cases: try_bypass recursed on tail with same func *)
  TRY (last_x_assum irule >> simp[] >>
       qexistsl_tac [`bb`, `label_map`] >> simp[] >> NO_TAC) >>
  (* Success case: do_merge_jump directly produces func' *)
  irule do_merge_jump_correct >>
  `MEM x func.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb_succs x = [HD (bb_succs x)]` by (
    qpat_x_assum `can_bypass_jump _ _ _` mp_tac >>
    simp[can_bypass_jump_def, cfgTransformTheory.num_succs_def] >>
    Cases_on `bb_succs x` >> simp[] >>
    Cases_on `t` >> simp[]) >>
  (* Guard provides: bb.bb_label <> target_lbl, ~MEM target_lbl (bb_succs bb) *)
  mp_tac bypass_label_inequalities >>
  disch_then (qspecl_then [`func`, `bb`, `x`, `HD (bb_succs x)`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  simp[] >>
  qexistsl_tac [`bb`, `x`, `label_map`, `lm'`, `x'`, `HD (bb_succs x)`] >>
  simp[]
QED

(* ================================================================
   Section 3b: WF preservation through collapse_dfs
   ================================================================ *)

(* PHI operands have even length (proper Label::Value pairs, no trailing singletons).
   Needed because remove_phi_label doesn't handle singleton edge case. *)
Definition fn_phi_even_def:
  fn_phi_even func <=>
    !bb inst. MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI ==> EVEN (LENGTH inst.inst_operands)
End

(* Strict PHI operand structure: alternating Label-Var pairs.
   Stronger than phi_well_formed which allows non-Label at even positions.
   Trivially satisfied by compiler output. Implies phi_well_formed, EVEN,
   and ensures remove_phi_label fully removes matching labels. *)
Definition phi_strict_wf_def:
  phi_strict_wf [] = T /\
  phi_strict_wf (Label l :: Var v :: rest) = phi_strict_wf rest /\
  phi_strict_wf _ = F
End

Definition fn_phi_labels_wf_def:
  fn_phi_labels_wf func <=>
    !bb inst.
      MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI ==>
      phi_strict_wf inst.inst_operands
End

(* phi_strict_wf implies the properties we need *)
Triviality phi_strict_wf_phi_well_formed:
  !ops. phi_strict_wf ops ==> phi_well_formed ops
Proof
  ho_match_mp_tac (fetch "-" "phi_strict_wf_ind") >>
  rw[phi_strict_wf_def, phi_well_formed_def]
QED

Triviality phi_strict_wf_EVEN:
  !ops. phi_strict_wf ops ==> EVEN (LENGTH ops)
Proof
  ho_match_mp_tac (fetch "-" "phi_strict_wf_ind") >>
  rw[phi_strict_wf_def, arithmeticTheory.EVEN]
QED

Triviality phi_strict_wf_remove_phi_label:
  !ops b. phi_strict_wf ops ==> ~MEM (Label b) (remove_phi_label b ops)
Proof
  ho_match_mp_tac (fetch "-" "phi_strict_wf_ind") >>
  rw[phi_strict_wf_def, remove_phi_label_def] >> rw[]
QED

Triviality phi_strict_wf_remove_phi_label_preserved:
  !ops b. phi_strict_wf ops ==> phi_strict_wf (remove_phi_label b ops)
Proof
  ho_match_mp_tac (fetch "-" "phi_strict_wf_ind") >>
  rw[phi_strict_wf_def, remove_phi_label_def] >>
  IF_CASES_TAC >> rw[phi_strict_wf_def]
QED

(* phi_strict_wf preserved through update_phi_bypass MAP (not_has_a case) *)
Triviality phi_strict_wf_MAP_label_subst:
  !ops a_label b_label.
    phi_strict_wf ops ==>
    phi_strict_wf (MAP (\op. case op of
                           Label l => if l = b_label then Label a_label
                                      else Label l
                         | _ => op) ops)
Proof
  ho_match_mp_tac (fetch "-" "phi_strict_wf_ind") >>
  rw[phi_strict_wf_def] >> IF_CASES_TAC >> rw[phi_strict_wf_def]
QED

(* phi_strict_wf preserved through subst_label_op MAP (for update_succ_phi_labels) *)
Triviality phi_strict_wf_MAP_subst_label_op:
  !ops old new.
    phi_strict_wf ops ==>
    phi_strict_wf (MAP (subst_label_op old new) ops)
Proof
  ho_match_mp_tac (fetch "-" "phi_strict_wf_ind") >>
  rw[phi_strict_wf_def, cfgTransformTheory.subst_label_op_def] >>
  IF_CASES_TAC >> rw[phi_strict_wf_def]
QED

(* Bundle all WF predicates needed by do_merge_jump_correct / try_bypass_correct *)
Definition collapse_wf_def:
  collapse_wf func <=>
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\ fn_phi_preds_complete func /\
    fn_phi_resolve_complete func /\ fn_bypass_safe func /\
    fn_phi_even func /\ fn_phi_labels_wf func
End

(* ================================================================
   Section 3b.1: Helpers for WF preservation through do_merge_jump
   ================================================================ *)

(* -- Small operand/instruction helpers -- *)

Triviality MEM_remove_phi_label_mono[local]:
  !b ops x. MEM x (remove_phi_label b ops) ==> MEM x ops
Proof
  ho_match_mp_tac cfgTransformTheory.remove_phi_label_ind >>
  rw[remove_phi_label_def] >> gvs[]
QED

Triviality MEM_Label_remove_phi_label[local]:
  !b ops lbl.
    phi_well_formed ops /\ EVEN (LENGTH ops) /\ lbl <> b /\
    MEM (Label lbl) ops ==>
    MEM (Label lbl) (remove_phi_label b ops)
Proof
  ho_match_mp_tac cfgTransformTheory.remove_phi_label_ind >>
  rw[remove_phi_label_def] >>
  fs[arithmeticTheory.EVEN] >>
  TRY (
    qpat_x_assum `phi_well_formed (Label _ :: _ :: _)` mp_tac >>
    Cases_on `val_op` >> simp[phi_well_formed_def] >> strip_tac >>
    first_x_assum (qspec_then `lbl` mp_tac) >> simp[]) >>
  fs[phi_well_formed_def]
QED


Triviality MEM_Label_MAP_subst_label_op[local]:
  !lbl old new ops.
    MEM (Label lbl) (MAP (subst_label_op old new) ops) <=>
    (lbl = new /\ MEM (Label old) ops) \/
    (MEM (Label lbl) ops /\ lbl <> old)
Proof
  rw[listTheory.MEM_MAP] >> eq_tac >> rw[]
  >- (Cases_on `y` >> fs[subst_label_op_def] >>
      BasicProvers.every_case_tac >> fs[] >> rw[])
  >- (qexists_tac `Label old` >> simp[subst_label_op_def])
  >> (qexists_tac `Label lbl` >> simp[subst_label_op_def])
QED

Triviality EVEN_LENGTH_remove_phi_label[local]:
  !b ops. EVEN (LENGTH ops) ==>
    EVEN (LENGTH (remove_phi_label b ops))
Proof
  ho_match_mp_tac cfgTransformTheory.remove_phi_label_ind >>
  rw[remove_phi_label_def] >>
  fs[arithmeticTheory.EVEN]
QED

Triviality phi_wf_remove_phi_label[local]:
  !b ops. phi_well_formed ops ==>
    phi_well_formed (remove_phi_label b ops)
Proof
  ho_match_mp_tac cfgTransformTheory.remove_phi_label_ind >>
  rw[remove_phi_label_def, phi_well_formed_def] >>
  Cases_on `val_op` >> fs[phi_well_formed_def]
QED

Triviality not_is_terminator_PHI[local]:
  ~is_terminator PHI
Proof
  simp[is_terminator_def]
QED

Triviality EVEN_update_phi_bypass[local]:
  !a b inst. inst.inst_opcode = PHI /\ EVEN (LENGTH inst.inst_operands) ==>
    EVEN (LENGTH (update_phi_bypass a b inst).inst_operands)
Proof
  rw[update_phi_bypass_def] >>
  irule EVEN_LENGTH_remove_phi_label >> simp[]
QED

Triviality update_phi_bypass_PHI_inv[local]:
  !a b inst.
    (update_phi_bypass a b inst).inst_opcode = PHI ==>
    inst.inst_opcode = PHI
Proof
  rw[update_phi_bypass_def]
QED

Triviality cond_subst_PHI_inv[local]:
  !old new inst.
    (if ~is_terminator inst.inst_opcode then inst
     else subst_label_inst old new inst).inst_opcode = PHI ==>
    inst.inst_opcode = PHI /\
    (if ~is_terminator inst.inst_opcode then inst
     else subst_label_inst old new inst) = inst
Proof
  rw[] >> Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  gvs[cfgTransformProofsTheory.subst_label_inst_fields, is_terminator_def]
QED

(* Quick derivation of bb_well_formed from wf_function + MEM *)
Triviality wf_bb_well_formed[local]:
  !func bb. wf_function func /\ MEM bb func.fn_blocks ==> bb_well_formed bb
Proof
  rw[wf_function_def]
QED

(* Unique labels: wf_function + same label => same block *)
Triviality wf_same_label_eq[local]:
  !func a b. wf_function func /\ MEM a func.fn_blocks /\
    MEM b func.fn_blocks /\ a.bb_label = b.bb_label ==> a = b
Proof
  rw[wf_function_def, fn_labels_def] >>
  mp_tac (ISPECL [``func.fn_blocks``, ``a:basic_block``, ``b:basic_block``,
                   ``\(bb:basic_block). bb.bb_label``] ALL_DISTINCT_MAP_INJ_MEM) >>
  simp[]
QED

(* pred_labels biconditional *)
Triviality pred_labels_MEM[local]:
  MEM lbl (pred_labels func x) <=>
  ?bb. MEM bb func.fn_blocks /\ MEM x (bb_succs bb) /\ bb.bb_label = lbl
Proof
  simp[pred_labels_def, block_preds_def, listTheory.MEM_MAP,
       listTheory.MEM_FILTER] >> metis_tac[]
QED

(* pred_labels + lookup_block + ALL_DISTINCT → bb_succs directly *)
Triviality pred_labels_lookup_succs[local]:
  !func lbl x bb.
    MEM lbl (pred_labels func x) /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks) ==>
    MEM x (bb_succs bb)
Proof
  rpt strip_tac >>
  fs[pred_labels_MEM] >>
  `lookup_block lbl func.fn_blocks = SOME bb'` by
    metis_tac[venomExecProofsTheory.MEM_lookup_block] >>
  gvs[]
QED

(* -- Block case analysis -- *)

Triviality do_merge_jump_block_cases[local]:
  !func a b lm func' lm' bb.
    do_merge_jump func a b lm = SOME (func', lm') /\
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    MEM bb func'.fn_blocks ==>
    (?target_lbl target a_insts target_insts.
      bb_succs b = [target_lbl] /\
      lookup_block target_lbl func.fn_blocks = SOME target /\
      a_insts = MAP (update_phi_bypass a.bb_label b.bb_label)
                    (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                                 else subst_label_inst b.bb_label target_lbl inst)
                         a.bb_instructions) /\
      target_insts = MAP (update_phi_bypass a.bb_label b.bb_label)
                         target.bb_instructions /\
      (bb.bb_label = a.bb_label /\ bb = a with bb_instructions := a_insts \/
       bb.bb_label = target_lbl /\ a.bb_label <> target_lbl /\
         bb = target with bb_instructions := target_insts \/
       MEM bb func.fn_blocks /\ bb.bb_label <> a.bb_label /\
         bb.bb_label <> target_lbl /\ bb.bb_label <> b.bb_label))
Proof
  rw[] >>
  imp_res_tac do_merge_jump_SOME_cases >>
  imp_res_tac lookup_block_label >>
  qexistsl_tac [`target_lbl`, `target`] >> simp[] >>
  fs[MEM_replace_block_cases, MEM_remove_block_iff] >>
  gvs[]
QED

(* Simplified version: when fn_phi_preds_wf holds, the MAP upb on the a-block
   simplifies away (MAP_upb_cs_a_identity), giving the single-MAP form. *)
Triviality do_merge_jump_block_cases_wf[local]:
  !func a b lm func' lm' bb.
    do_merge_jump func a b lm = SOME (func', lm') /\
    wf_function func /\ fn_phi_preds_wf func /\
    a.bb_label <> HD (bb_succs b) /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    MEM bb func'.fn_blocks ==>
    (?target_lbl target a_insts target_insts.
      bb_succs b = [target_lbl] /\
      lookup_block target_lbl func.fn_blocks = SOME target /\
      a_insts = MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                            else subst_label_inst b.bb_label target_lbl inst)
                    a.bb_instructions /\
      target_insts = MAP (update_phi_bypass a.bb_label b.bb_label)
                         target.bb_instructions /\
      (bb.bb_label = a.bb_label /\ bb = a with bb_instructions := a_insts \/
       bb.bb_label = target_lbl /\ a.bb_label <> target_lbl /\
         bb = target with bb_instructions := target_insts \/
       MEM bb func.fn_blocks /\ bb.bb_label <> a.bb_label /\
         bb.bb_label <> target_lbl /\ bb.bb_label <> b.bb_label))
Proof
  rpt strip_tac >>
  `!target_lbl'.
     bb_succs b = [target_lbl'] /\ a.bb_label <> target_lbl' ==>
     MAP (update_phi_bypass a.bb_label b.bb_label)
       (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                    else subst_label_inst b.bb_label target_lbl' inst)
            a.bb_instructions) =
     MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                 else subst_label_inst b.bb_label target_lbl' inst)
         a.bb_instructions` by (
    rpt strip_tac >>
    match_mp_tac MAP_upb_cs_a_identity >>
    qexistsl [`func`, `target_lbl'`] >>
    simp[is_terminator_def, subst_label_inst_fields] >>
    rpt strip_tac >> IF_CASES_TAC >>
    simp[subst_label_inst_fields]) >>
  drule_all do_merge_jump_block_cases >> strip_tac >>
  (* bypass_label_inequalities needs a.bb_label <> target_lbl *)
  `bb_succs b = [target_lbl]` by simp[] >>
  `a.bb_label <> target_lbl` by (
    `HD (bb_succs b) = target_lbl` by simp[] >> fs[]) >>
  drule_all bypass_label_inequalities >> strip_tac >>
  qexistsl [`target_lbl`, `target`] >>
  first_x_assum (qspec_then `target_lbl` mp_tac) >> simp[]
QED

(* ---- MEM introduction lemmas for replace_block / remove_block ---- *)
(* These compose to handle the nested replace_block . replace_block . remove_block
   structure from do_merge_jump. Use match_mp_tac instead of rewrite_tac+disj_tac. *)

Triviality MEM_replace_block_new[local]:
  !lbl new_bb bbs.
    (?bb. MEM bb bbs /\ bb.bb_label = lbl) ==>
    MEM new_bb (replace_block lbl new_bb bbs)
Proof
  rpt strip_tac >>
  simp[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  qexists_tac `bb` >> simp[]
QED

Triviality MEM_replace_block_other[local]:
  !a lbl new_bb bbs.
    MEM a bbs /\ a.bb_label <> lbl ==>
    MEM a (replace_block lbl new_bb bbs)
Proof
  rpt strip_tac >>
  simp[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  qexists_tac `a` >> simp[]
QED

Triviality MEM_remove_block_intro[local]:
  !a nlbl bbs.
    MEM a bbs /\ a.bb_label <> nlbl ==>
    MEM a (remove_block nlbl bbs)
Proof
  rpt strip_tac >>
  simp[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER]
QED

(* -- Backward block membership: given bb' in func (not b), find corresponding in func' -- *)
(* This is the converse of do_merge_jump_block_cases: for any block in func
   that isn't b, there's a corresponding block in func' with same label.
   target_lbl = unique successor of b, provided as hypothesis. *)
Triviality do_merge_jump_block_backward[local]:
  !func a b lm func' lm' bb' target_lbl.
    do_merge_jump func a b lm = SOME (func', lm') /\
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\ a.bb_label <> target_lbl /\
    bb_succs b = [target_lbl] /\
    MEM bb' func.fn_blocks /\ bb'.bb_label <> b.bb_label ==>
    ?bb_new.
      MEM bb_new func'.fn_blocks /\
      bb_new.bb_label = bb'.bb_label /\
      (bb'.bb_label = a.bb_label ==>
        !x. MEM x (bb_succs bb_new) <=>
          (x = target_lbl /\ MEM b.bb_label (bb_succs bb')) \/
          (MEM x (bb_succs bb') /\ x <> b.bb_label)) /\
      (bb'.bb_label = target_lbl ==>
        bb_succs bb_new = bb_succs bb') /\
      (bb'.bb_label <> a.bb_label /\ bb'.bb_label <> target_lbl ==>
        bb_new = bb')
Proof
  rpt strip_tac >>
  qpat_x_assum `do_merge_jump _ _ _ _ = SOME _` mp_tac >>
  disch_then (strip_assume_tac o MATCH_MP do_merge_jump_SOME_cases) >>
  rename [`lookup_block target_lbl2 _ = SOME tgt_bb`] >>
  `target_lbl2 = target_lbl` by fs[] >> gvs[] >>
  imp_res_tac lookup_block_label >>
  mp_tac (Q.SPECL [`func`, `a`, `b`, `target_lbl`]
    bypass_label_inequalities) >>
  (impl_tac >- simp[]) >> strip_tac >>
  imp_res_tac lookup_block_MEM >>
  (* Rewrite goal to expose the replace_block structure *)
  qpat_assum `func'.fn_blocks = _` (fn eq =>
    PURE_REWRITE_TAC[eq]) >>
  Cases_on `bb'.bb_label = a.bb_label`
  >- suspend "case_a"
  >> Cases_on `bb'.bb_label = target_lbl`
  >- suspend "case_target"
  >> suspend "case_other"
QED

Resume do_merge_jump_block_backward[case_a]:
  mp_tac (Q.SPECL [`func`, `bb'`, `a`] wf_same_label_eq) >>
  (impl_tac >- simp[]) >> disch_tac >> gvs[] >>
  imp_res_tac wf_bb_well_formed >>
  qmatch_goalsub_abbrev_tac `replace_block _ a_mod _` >>
  qexists `a_mod` >>
  conj_tac >- (match_mp_tac MEM_replace_block_new >>
    qexists `a` >> simp[Abbr `a_mod`] >>
    match_mp_tac MEM_replace_block_other >> simp[] >>
    match_mp_tac MEM_remove_block_intro >> simp[]) >>
  simp[Abbr `a_mod`, bb_succs_a_block_bypass] >>
  gen_tac >> eq_tac
  >- (strip_tac >>
      imp_res_tac MEM_bb_succs_cond_subst_label >>
      gvs[can_bypass_jump_def] >> metis_tac[])
  >> (strip_tac >> gvs[] >>
      metis_tac[MEM_bb_succs_cond_subst_forward])
QED

Resume do_merge_jump_block_backward[case_target]:
  (* tgt_bb is the target block from do_merge_jump_SOME_cases *)
  qpat_assum `lookup_block target_lbl _ = SOME tgt_bb`
    (fn th => assume_tac (MATCH_MP
       venomExecProofsTheory.lookup_block_MEM th)) >>
  imp_res_tac wf_bb_well_formed >>
  mp_tac (Q.SPECL [`func`, `bb'`, `tgt_bb`] wf_same_label_eq) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  qexists `tgt_bb with bb_instructions :=
    MAP (update_phi_bypass a.bb_label b.bb_label)
      tgt_bb.bb_instructions` >>
  conj_tac
  >- (match_mp_tac MEM_replace_block_other >> simp[] >>
      match_mp_tac MEM_replace_block_new >>
      qexists `tgt_bb` >> conj_tac
      >- (match_mp_tac MEM_remove_block_intro >> simp[])
      >> simp[]) >>
  simp[bb_succs_update_phi_bypass]
QED

Resume do_merge_jump_block_backward[case_other]:
  qexists `bb'` >>
  conj_tac
  >- (match_mp_tac MEM_replace_block_other >> simp[] >>
      match_mp_tac MEM_replace_block_other >> simp[] >>
      match_mp_tac MEM_remove_block_intro >> simp[]) >>
  simp[]
QED

Finalise do_merge_jump_block_backward

(* ================================================================
   Section 3b.2: pred_labels after do_merge_jump
   ================================================================ *)

(* pred_labels for target_lbl after bypass.
   After a→b→target becomes a→target:
   - a gains target_lbl as successor (via subst b.bb_label→target_lbl)
   - b is removed
   - target' succs unchanged (update_phi_bypass only touches PHI)
   - unchanged blocks have unchanged succs *)
Triviality pred_labels_do_merge_jump_target[local]:
  !func a b lm func' lm' target_lbl lbl.
    do_merge_jump func a b lm = SOME (func', lm') /\
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    a.bb_label <> target_lbl /\
    bb_succs b = [target_lbl] ==>
    (MEM lbl (pred_labels func' target_lbl) <=>
      (lbl = a.bb_label) \/
      (MEM lbl (pred_labels func target_lbl) /\ lbl <> b.bb_label))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `a`, `b`, `target_lbl`]
    bypass_label_inequalities) >>
  (impl_tac >- simp[]) >> strip_tac >>
  imp_res_tac wf_bb_well_formed >>
  eq_tac
  >- ((* ==> : lbl is pred in func', show lbl = a.bb_label or old pred *)
      simp[pred_labels_MEM] >> strip_tac >>
      drule_all do_merge_jump_block_cases >> strip_tac >> gvs[]
      (* a-block: resolved by gvs (lbl = a.bb_label makes disjunction trivial).
         target/other remaining: show old pred via pred_labels_MEM witness *)
      >> (TRY (imp_res_tac lookup_block_MEM >>
               mp_tac (Q.SPECL [`a.bb_label`, `b.bb_label`, `target`]
                 bb_succs_update_phi_bypass) >>
               (impl_tac >- metis_tac[wf_bb_well_formed]) >>
               strip_tac >> gvs[]) >>
          simp[pred_labels_MEM] >> metis_tac[]))
  >> ((* <== : lbl = a.bb_label or (old pred, not b) => pred in func' *)
      strip_tac >> simp[pred_labels_MEM] >> gvs[]
      (* lbl = a.bb_label: need witness in func' with target_lbl in succs *)
      >- (drule_all do_merge_jump_block_backward >>
          disch_then strip_assume_tac >>
          qexists `bb_new` >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac
          >- (gvs[] >> fs[can_bypass_jump_def]) >>
          first_assum ACCEPT_TAC)
      (* old pred, not b *)
      >> (gvs[pred_labels_MEM] >>
          `bb.bb_label <> b.bb_label` by metis_tac[] >>
          drule_all do_merge_jump_block_backward >>
          disch_then strip_assume_tac >>
          qexists `bb_new` >> simp[] >>
          Cases_on `bb.bb_label = a.bb_label` >> gvs[] >>
          Cases_on `bb.bb_label = target_lbl` >> gvs[]))
QED

(* pred_labels for other labels x <> target_lbl, x <> b.bb_label after bypass *)
Triviality pred_labels_do_merge_jump_other[local]:
  !func a b lm func' lm' x target_lbl lbl.
    do_merge_jump func a b lm = SOME (func', lm') /\
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    a.bb_label <> target_lbl /\
    bb_succs b = [target_lbl] /\
    x <> target_lbl /\ x <> b.bb_label ==>
    (MEM lbl (pred_labels func' x) <=>
      MEM lbl (pred_labels func x) /\ lbl <> b.bb_label)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `a`, `b`, `target_lbl`]
    bypass_label_inequalities) >>
  (impl_tac >- simp[]) >> strip_tac >>
  imp_res_tac wf_bb_well_formed >>
  eq_tac
  >- ((* ==> : lbl is pred of x in func', show old pred and not b *)
      simp[pred_labels_MEM] >> strip_tac >>
      drule_all do_merge_jump_block_cases >> strip_tac >> gvs[]
      >- ((* a-block *)
          gvs[bb_succs_a_block_bypass] >>
          imp_res_tac MEM_bb_succs_cond_subst_label >> gvs[] >>
          qexists `a` >> simp[])
      >- ((* target-block: update_phi_bypass preserves succs *)
          imp_res_tac lookup_block_MEM >>
          imp_res_tac wf_bb_well_formed >>
          gvs[bb_succs_update_phi_bypass] >>
          qexists `target` >> simp[])
      >> ((* other block: unchanged *)
          qexists `bb` >> simp[]))
  >> ((* <== : old pred, not b => pred in func' *)
      strip_tac >> gvs[pred_labels_MEM] >>
      drule_all do_merge_jump_block_backward >>
      disch_then strip_assume_tac >>
      simp[pred_labels_MEM] >>
      qexists `bb_new` >> simp[] >>
      Cases_on `bb.bb_label = a.bb_label` >> gvs[] >>
      Cases_on `bb.bb_label = target_lbl` >> gvs[])
QED

(* ================================================================
   Section 3b.3: Per-predicate preservation through do_merge_jump
   ================================================================ *)

Triviality fn_phi_even_do_merge_jump[local]:
  !func a b lm func' lm'.
    fn_phi_even func /\ wf_function func /\ fn_inst_wf func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    do_merge_jump func a b lm = SOME (func', lm') ==>
    fn_phi_even func'
Proof
  rw[fn_phi_even_def] >>
  drule_all do_merge_jump_block_cases >> strip_tac >> gvs[]
  >- (gvs[listTheory.MEM_MAP] >>
      imp_res_tac update_phi_bypass_PHI_inv >>
      imp_res_tac cond_subst_PHI_inv >> gvs[] >>
      irule EVEN_update_phi_bypass >> gvs[] >> metis_tac[])
  >- (gvs[listTheory.MEM_MAP] >> imp_res_tac update_phi_bypass_PHI_inv >>
      imp_res_tac lookup_block_MEM >>
      irule EVEN_update_phi_bypass >> gvs[] >> metis_tac[])
  >> (first_x_assum (qspecl_then [`bb`, `inst`] mp_tac) >> simp[])
QED

Triviality fn_bypass_safe_do_merge_jump[local]:
  !func a b lm func' lm'.
    fn_bypass_safe func /\ wf_function func /\ fn_inst_wf func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    ~MEM (HD (bb_succs b)) (bb_succs a) /\ a.bb_label <> HD (bb_succs b) /\
    do_merge_jump func a b lm = SOME (func', lm') ==>
    fn_bypass_safe func'
Proof
  rpt gen_tac >> strip_tac >>
  simp[fn_bypass_safe_def] >> rpt gen_tac >> strip_tac >>
  drule_all do_merge_jump_block_cases >> strip_tac >> gvs[]
  (* Case 1: bb is the modified a-block *)
  >- suspend "case_a"
  (* Case 2: bb is the modified target block *)
  >- suspend "case_target"
  (* Case 3: unchanged block from func *)
  >> suspend "case_other"
QED

Resume fn_bypass_safe_do_merge_jump[case_a]:
  (* Step 1: setup *)
  `bb_well_formed a` by (fs[wf_function_def] >> res_tac) >>
  `num_succs a = 2` by fs[can_bypass_jump_def] >>
  (* Step 2: JNZ opcode from fn_bypass_safe + num_succs = 2 *)
  `(LAST a.bb_instructions).inst_opcode = JNZ` by (
    qpat_assum `fn_bypass_safe func`
      (mp_tac o REWRITE_RULE [fn_bypass_safe_def]) >>
    disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  `~MEM target_lbl (bb_succs a)` by (
    `HD (bb_succs b) = target_lbl` by simp[] >> fs[]) >>
  simp[is_terminator_def, cfgTransformProofsTheory.subst_label_inst_fields] >>
  conj_tac
  >- (
    (* num_succs (MAP upb (MAP cond_subst a)) = num_succs a = 2 ≠ 1 *)
    `num_succs (a with bb_instructions :=
       MAP (update_phi_bypass a.bb_label b.bb_label)
         (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                      else subst_label_inst b.bb_label target_lbl inst)
              a.bb_instructions)) =
     num_succs (a with bb_instructions :=
       MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                    else subst_label_inst b.bb_label target_lbl inst)
            a.bb_instructions)` by
      simp[cfgTransformTheory.num_succs_def, bb_succs_a_block_bypass] >>
    simp[num_succs_cond_subst])
  >>
  (* ∀c l1 l2. upb(subst_label_inst ...) operands ⇒ c ≠ Label *)
  rpt gen_tac >> strip_tac >>
  (* upb is identity on non-PHI terminator (JNZ) *)
  `update_phi_bypass a.bb_label b.bb_label
     (subst_label_inst b.bb_label target_lbl (LAST a.bb_instructions)) =
   subst_label_inst b.bb_label target_lbl (LAST a.bb_instructions)` by
    simp[update_phi_bypass_non_phi,
         cfgTransformProofsTheory.subst_label_inst_fields] >>
  (* Expand subst_label_inst: operands = MAP subst_label_op over original *)
  gvs[cfgTransformTheory.subst_label_inst_def] >>
  (* Case split original operands to extract 3-element [h;h2;h3] structure *)
  Cases_on `(LAST a.bb_instructions).inst_operands` >> gvs[] >>
  qpat_x_assum `MAP _ _ = [_; _]` mp_tac >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  strip_tac >> gvs[] >>
  (* h' and h'' must be Labels (only Labels map to Labels under subst_label_op) *)
  Cases_on `h'` >> gvs[cfgTransformTheory.subst_label_op_def] >>
  Cases_on `h''` >> gvs[cfgTransformTheory.subst_label_op_def] >>
  (* Original operands: [h; Label _; Label _] — use fn_bypass_safe *)
  qpat_assum `fn_bypass_safe func`
    (mp_tac o REWRITE_RULE [fn_bypass_safe_def]) >>
  disch_then (qspec_then `a` mp_tac) >> simp[] >>
  strip_tac >>
  (* h is not a Label, so subst_label_op is identity on h *)
  Cases_on `h` >> gvs[cfgTransformTheory.subst_label_op_def]
QED

Resume fn_bypass_safe_do_merge_jump[case_target]:
  (* MAP update_phi_bypass preserves bb_succs/num_succs on wf blocks.
     LAST is non-PHI (terminator) so upb is identity on LAST.
     Properties transfer from fn_bypass_safe func. *)
  imp_res_tac lookup_block_MEM >>
  `bb_well_formed target` by (fs[wf_function_def] >> res_tac) >>
  `num_succs (target with bb_instructions :=
     MAP (update_phi_bypass a.bb_label b.bb_label) target.bb_instructions) =
   num_succs target` by
    simp[cfgTransformTheory.num_succs_def, bb_succs_update_phi_bypass] >>
  `(LAST target.bb_instructions).inst_opcode <> PHI` by
    (fs[bb_well_formed_def] >> metis_tac[not_is_terminator_PHI]) >>
  simp[update_phi_bypass_non_phi] >>
  qpat_assum `fn_bypass_safe func`
    (mp_tac o REWRITE_RULE [fn_bypass_safe_def]) >>
  disch_then (qspec_then `target` mp_tac) >> simp[]
QED

Resume fn_bypass_safe_do_merge_jump[case_other]:
  (* unchanged block: properties carry directly from fn_bypass_safe func *)
  qpat_assum `fn_bypass_safe func`
    (mp_tac o REWRITE_RULE [fn_bypass_safe_def]) >>
  disch_then (qspec_then `bb` mp_tac) >> simp[]
QED

Finalise fn_bypass_safe_do_merge_jump

(* b.bb_label cannot be a predecessor of any block x <> target_lbl:
   because bb_succs b = [target_lbl], so b only points to target_lbl. *)
Triviality b_not_pred_of_non_target[local]:
  !func a b x target_lbl.
    wf_function func /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    bb_succs b = [target_lbl] /\ x <> target_lbl ==>
    ~MEM b.bb_label (pred_labels func x)
Proof
  rw[pred_labels_MEM] >>
  spose_not_then strip_assume_tac >>
  `bb = b` by metis_tac[wf_same_label_eq] >>
  gvs[]
QED

(* KEY helper: characterize labels after update_phi_bypass.
   If MEM (Label lbl) in the result and opcode=PHI, then either
   lbl = a_label (from substitution) or lbl was already there and lbl <> b_label. *)
Triviality MEM_Label_update_phi_bypass:
  !a_label b_label inst lbl.
    inst.inst_opcode = PHI /\
    phi_strict_wf inst.inst_operands /\
    MEM (Label lbl) (update_phi_bypass a_label b_label inst).inst_operands ==>
    lbl = a_label \/ (MEM (Label lbl) inst.inst_operands /\ lbl <> b_label)
Proof
  rw[update_phi_bypass_def] >>
  Cases_on `MEM (Label a_label) inst.inst_operands`
  >- ((* has_a = T: remove_phi_label *)
      gvs[] >>
      disj2_tac >>
      imp_res_tac MEM_remove_phi_label_mono >>
      conj_tac >- first_assum ACCEPT_TAC >>
      strip_tac >> gvs[] >>
      metis_tac[phi_strict_wf_remove_phi_label])
  >> ((* has_a = F: MAP substitution *)
      gvs[listTheory.MEM_MAP] >>
      rename1 `MEM src_op inst.inst_operands` >>
      Cases_on `src_op` >> gvs[]
      >> (rename1 `MEM (Label orig_lbl) inst.inst_operands` >>
          Cases_on `orig_lbl = b_label` >> gvs[]))
QED

(* Reverse direction: labels present in original are preserved by update_phi_bypass.
   For lbl <> b_label: the label is preserved (not removed/changed).
   For lbl = a_label: also preserved (either already there, or b->a subst introduces it). *)
Triviality MEM_Label_update_phi_bypass_preserve:
  !a_label b_label inst lbl.
    inst.inst_opcode = PHI /\
    phi_strict_wf inst.inst_operands /\
    EVEN (LENGTH inst.inst_operands) /\
    MEM (Label lbl) inst.inst_operands /\
    lbl <> b_label ==>
    MEM (Label lbl) (update_phi_bypass a_label b_label inst).inst_operands
Proof
  rw[update_phi_bypass_def] >>
  Cases_on `MEM (Label a_label) inst.inst_operands`
  >- ((* has_a = T: remove_phi_label *)
      gvs[] >>
      irule MEM_Label_remove_phi_label >>
      simp[phi_strict_wf_phi_well_formed])
  >> ((* has_a = F: MAP substitution *)
      gvs[] >>
      simp[listTheory.MEM_MAP] >>
      qexists `Label lbl` >> simp[])
QED

(* When b_label is in original PHI ops, a_label appears in the result.
   Needs phi_strict_wf/EVEN for the has_a=T case (remove_phi_label preserves a<>b). *)
Triviality MEM_Label_a_update_phi_bypass:
  !a_label b_label inst.
    inst.inst_opcode = PHI /\
    phi_strict_wf inst.inst_operands /\
    EVEN (LENGTH inst.inst_operands) /\
    a_label <> b_label /\
    MEM (Label b_label) inst.inst_operands ==>
    MEM (Label a_label) (update_phi_bypass a_label b_label inst).inst_operands
Proof
  rw[update_phi_bypass_def] >>
  Cases_on `MEM (Label a_label) inst.inst_operands`
  >- ((* has_a = T: remove_phi_label preserves Label a since a<>b *)
      gvs[] >>
      irule MEM_Label_remove_phi_label >>
      simp[phi_strict_wf_phi_well_formed])
  >> ((* has_a = F: MAP turns Label b into Label a *)
      gvs[listTheory.MEM_MAP] >>
      qexists `Label b_label` >> simp[])
QED

Triviality fn_phi_preds_wf_do_merge_jump[local]:
  !func a b lm func' lm'.
    fn_phi_preds_wf func /\ fn_phi_even func /\ fn_phi_labels_wf func /\
    wf_function func /\ fn_inst_wf func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\ a.bb_label <> HD (bb_succs b) /\
    do_merge_jump func a b lm = SOME (func', lm') ==>
    fn_phi_preds_wf func'
Proof
  rpt gen_tac >> strip_tac >>
  rw[fn_phi_preds_wf_def] >>
  drule_all do_merge_jump_block_cases_wf >> strip_tac >> gvs[]
  >- ((* Case 1: a-block — cond_subst is identity on PHI *)
      drule_all bypass_label_inequalities >> strip_tac >>
      gvs[listTheory.MEM_MAP] >>
      rename1 `MEM orig_inst a.bb_instructions` >>
      imp_res_tac cond_subst_PHI_inv >> gvs[] >>
      (* Get MEM lbl (pred_labels func a.bb_label) from fn_phi_preds_wf *)
      qpat_assum `fn_phi_preds_wf func`
        (mp_tac o REWRITE_RULE[fn_phi_preds_wf_def]) >>
      disch_then (qspecl_then [`a`, `orig_inst`, `lbl`] mp_tac) >>
      simp[] >> strip_tac >>
      (* Get ¬MEM b.bb_label (pred_labels func a.bb_label) *)
      mp_tac b_not_pred_of_non_target >>
      disch_then (qspecl_then [`func`, `a`, `b`, `a.bb_label`, `target_lbl`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      (* Get the pred_labels biconditional for func' *)
      mp_tac pred_labels_do_merge_jump_other >>
      disch_then (qspecl_then [`func`, `a`, `b`, `lm`, `func'`, `lm'`,
        `a.bb_label`, `target_lbl`, `lbl`] mp_tac) >>
      (impl_tac >- simp[]) >>
      (* The biconditional: apply RL direction, prove both conjuncts *)
      disch_then (fn bic =>
        match_mp_tac (snd (EQ_IMP_RULE bic))) >>
      conj_asm1_tac >- first_assum ACCEPT_TAC >>
      strip_tac >> gvs[])
  >- ((* Case 2: target-block *)
      gvs[listTheory.MEM_MAP] >>
      rename1 `MEM orig_inst target.bb_instructions` >>
      imp_res_tac update_phi_bypass_PHI_inv >> gvs[] >>
      (* Get phi_strict_wf from fn_phi_labels_wf *)
      qpat_assum `fn_phi_labels_wf func`
        (mp_tac o REWRITE_RULE[fn_phi_labels_wf_def]) >>
      disch_then (qspecl_then [`target`, `orig_inst`] mp_tac) >>
      (impl_tac >- (imp_res_tac lookup_block_MEM >> simp[])) >>
      strip_tac >>
      (* Use MEM_Label_update_phi_bypass to decompose *)
      drule_all MEM_Label_update_phi_bypass >> strip_tac >> gvs[]
      >- ((* lbl = a.bb_label: left disjunct *)
          (* Use pred_labels_do_merge_jump_target RL direction *)
          mp_tac pred_labels_do_merge_jump_target >>
          disch_then (qspecl_then [`func`, `a`, `b`, `lm`, `func'`, `lm'`,
            `target.bb_label`, `a.bb_label`] mp_tac) >>
          (impl_tac >- simp[]) >>
          disch_then (fn bic => match_mp_tac (snd (EQ_IMP_RULE bic))) >>
          disj1_tac >> simp[])
      >> ((* MEM (Label lbl) orig operands, lbl <> b: use fn_phi_preds_wf + biconditional *)
          mp_tac pred_labels_do_merge_jump_target >>
          disch_then (qspecl_then [`func`, `a`, `b`, `lm`, `func'`, `lm'`,
            `target.bb_label`, `lbl`] mp_tac) >>
          (impl_tac >- simp[]) >>
          disch_then (fn bic => match_mp_tac (snd (EQ_IMP_RULE bic))) >>
          disj2_tac >>
          conj_tac
          >- (qpat_assum `fn_phi_preds_wf func`
                (mp_tac o REWRITE_RULE[fn_phi_preds_wf_def]) >>
              disch_then (qspecl_then [`target`, `orig_inst`, `lbl`] mp_tac) >>
              (impl_tac >- (imp_res_tac lookup_block_MEM >> simp[])) >>
              simp[])
          >> first_assum ACCEPT_TAC))
  >> ((* Case 3: other block — unchanged *)
      qpat_x_assum `fn_phi_preds_wf func`
        (mp_tac o REWRITE_RULE[fn_phi_preds_wf_def]) >>
      disch_then (qspecl_then [`bb`, `inst`, `lbl`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      mp_tac b_not_pred_of_non_target >>
      disch_then (qspecl_then [`func`, `a`, `b`, `bb.bb_label`, `target_lbl`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      mp_tac pred_labels_do_merge_jump_other >>
      disch_then (qspecl_then [`func`, `a`, `b`, `lm`, `func'`, `lm'`,
        `bb.bb_label`, `target_lbl`, `lbl`] mp_tac) >>
      (impl_tac >- simp[]) >>
      simp[] >> metis_tac[])
QED

Triviality fn_phi_preds_complete_do_merge_jump[local]:
  !func a b lm func' lm'.
    fn_phi_preds_complete func /\ fn_phi_preds_wf func /\ fn_phi_even func /\
    fn_phi_labels_wf func /\
    wf_function func /\ fn_inst_wf func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\ a.bb_label <> HD (bb_succs b) /\
    do_merge_jump func a b lm = SOME (func', lm') ==>
    fn_phi_preds_complete func'
Proof
  rpt gen_tac >> strip_tac >>
  simp[fn_phi_preds_complete_def] >> rpt gen_tac >> strip_tac >>
  drule_all do_merge_jump_block_cases_wf >> strip_tac >> gvs[]
  >- ((* Case 1: a-block — cond_subst on PHI is identity *)
      gvs[listTheory.MEM_MAP] >>
      imp_res_tac cond_subst_PHI_inv >> gvs[] >>
      drule_all bypass_label_inequalities >> strip_tac >>
      mp_tac pred_labels_do_merge_jump_other >>
      disch_then (qspecl_then [`func`, `a`, `b`, `lm`, `func'`, `lm'`,
        `a.bb_label`, `target_lbl`, `lbl`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[] >> strip_tac >>
      qpat_assum `fn_phi_preds_complete func`
        (mp_tac o REWRITE_RULE[fn_phi_preds_complete_def]) >>
      disch_then (qspecl_then [`a`, `inst'`, `lbl`] mp_tac) >>
      simp[])
  >- ((* Case 2: target-block *)
      gvs[listTheory.MEM_MAP] >>
      imp_res_tac update_phi_bypass_PHI_inv >> gvs[] >>
      rename1 `MEM orig_inst target.bb_instructions` >>
      qpat_assum `fn_phi_labels_wf func`
        (mp_tac o REWRITE_RULE[fn_phi_labels_wf_def]) >>
      disch_then (qspecl_then [`target`, `orig_inst`] mp_tac) >>
      (impl_tac >- (imp_res_tac lookup_block_MEM >> simp[])) >> strip_tac >>
      qpat_assum `fn_phi_even func`
        (mp_tac o REWRITE_RULE[fn_phi_even_def]) >>
      disch_then (qspecl_then [`target`, `orig_inst`] mp_tac) >>
      (impl_tac >- (imp_res_tac lookup_block_MEM >> simp[])) >> strip_tac >>
      mp_tac pred_labels_do_merge_jump_target >>
      disch_then (qspecl_then [`func`, `a`, `b`, `lm`, `func'`, `lm'`,
        `target.bb_label`, `lbl`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[] >> strip_tac >> gvs[]
      >- ((* lbl = a.bb_label — b was pred of target, a replaces b *)
          qpat_assum `fn_phi_preds_complete func`
            (mp_tac o REWRITE_RULE[fn_phi_preds_complete_def]) >>
          disch_then (qspecl_then [`target`, `orig_inst`, `b.bb_label`] mp_tac) >>
          (impl_tac >-
            (imp_res_tac lookup_block_MEM >>
             simp[pred_labels_MEM] >>
             qexists `b` >> gvs[can_bypass_jump_def])) >>
          strip_tac >>
          drule_all bypass_label_inequalities >> strip_tac >>
          irule MEM_Label_a_update_phi_bypass >> simp[])
      >> ((* lbl was old pred of target, lbl <> b — preserve label *)
          qpat_assum `fn_phi_preds_complete func`
            (mp_tac o REWRITE_RULE[fn_phi_preds_complete_def]) >>
          disch_then (qspecl_then [`target`, `orig_inst`, `lbl`] mp_tac) >>
          (impl_tac >- (imp_res_tac lookup_block_MEM >> simp[])) >> strip_tac >>
          irule MEM_Label_update_phi_bypass_preserve >> simp[]))
  >> ((* Case 3: other block — unchanged *)
      mp_tac pred_labels_do_merge_jump_other >>
      disch_then (qspecl_then [`func`, `a`, `b`, `lm`, `func'`, `lm'`,
        `bb.bb_label`, `target_lbl`, `lbl`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[] >> strip_tac >>
      qpat_assum `fn_phi_preds_complete func`
        (mp_tac o REWRITE_RULE[fn_phi_preds_complete_def]) >>
      disch_then (qspecl_then [`bb`, `inst`, `lbl`] mp_tac) >>
      simp[])
QED

Triviality fn_phi_resolve_complete_do_merge_jump[local]:
  !func a b lm func' lm'.
    fn_phi_resolve_complete func /\ fn_phi_preds_wf func /\
    fn_phi_preds_complete func /\ fn_phi_even func /\
    wf_function func /\ fn_inst_wf func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\ a.bb_label <> HD (bb_succs b) /\
    do_merge_jump func a b lm = SOME (func', lm') ==>
    fn_phi_resolve_complete func'
Proof
  rpt gen_tac >> strip_tac >>
  simp[fn_phi_resolve_complete_def] >> rpt gen_tac >> strip_tac >>
  drule_all do_merge_jump_block_cases_wf >> strip_tac >> gvs[]
  >- ((* Case 1: a-block — cond_subst is identity on PHI *)
      gvs[listTheory.MEM_MAP] >>
      imp_res_tac cond_subst_PHI_inv >> gvs[] >>
      drule_all bypass_label_inequalities >> strip_tac >>
      mp_tac pred_labels_do_merge_jump_other >>
      disch_then (qspecl_then [`func`, `a`, `b`, `lm`, `func'`, `lm'`,
        `a.bb_label`, `target_lbl`, `lbl`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[] >> strip_tac >>
      qpat_assum `fn_phi_resolve_complete func`
        (mp_tac o REWRITE_RULE[fn_phi_resolve_complete_def]) >>
      disch_then (qspecl_then [`a`, `inst'`, `lbl`] mp_tac) >>
      simp[])
  >- ((* Case 2: target-block — update_phi_bypass *)
      gvs[listTheory.MEM_MAP] >>
      imp_res_tac update_phi_bypass_PHI_inv >> gvs[] >>
      rename1 `MEM orig_inst target.bb_instructions` >>
      drule_all bypass_label_inequalities >> strip_tac >>
      imp_res_tac lookup_block_wf_facts >>
      `inst_wf orig_inst` by (imp_res_tac listTheory.EVERY_MEM >> res_tac) >>
      `phi_well_formed orig_inst.inst_operands` by
        (irule phi_operands_wf_implies_phi_well_formed >> gvs[inst_wf_def]) >>
      mp_tac pred_labels_do_merge_jump_target >>
      disch_then (qspecl_then [`func`, `a`, `b`, `lm`, `func'`, `lm'`,
        `target.bb_label`, `lbl`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[] >> strip_tac >> gvs[]
      >- ((* lbl = a.bb_label: resolve_phi a on update_phi_bypass *)
          simp[update_phi_bypass_def] >>
          Cases_on `MEM (Label a.bb_label) orig_inst.inst_operands` >> simp[]
          >- ((* has_a: resolve_phi a (remove b) = resolve_phi a orig *)
              mp_tac (Q.SPECL [`b.bb_label`, `a.bb_label`,
                `orig_inst.inst_operands`]
                cfgTransformProofsTheory.resolve_phi_remove_other) >>
              simp[] >> disch_then (fn th => simp[th]) >>
              (* a is a pred of target since MEM (Label a) in PHI operands *)
              qpat_assum `fn_phi_preds_wf func`
                (mp_tac o REWRITE_RULE[fn_phi_preds_wf_def]) >>
              disch_then (qspecl_then [`target`, `orig_inst`, `a.bb_label`]
                mp_tac) >> simp[] >> strip_tac >>
              qpat_assum `fn_phi_resolve_complete func`
                (mp_tac o REWRITE_RULE[fn_phi_resolve_complete_def]) >>
              disch_then (qspecl_then [`target`, `orig_inst`, `a.bb_label`]
                mp_tac) >> simp[])
          >> ((* ~has_a: resolve_phi a (MAP subst) = resolve_phi b orig *)
              mp_tac (Q.SPECL [`orig_inst.inst_operands`, `a.bb_label`,
                `b.bb_label`] resolve_phi_relabel_b_to_a) >>
              simp[] >> disch_then (fn th => simp[th]) >>
              (* b is a pred of target since bb_succs b = [target.bb_label] *)
              qpat_assum `fn_phi_resolve_complete func`
                (mp_tac o REWRITE_RULE[fn_phi_resolve_complete_def]) >>
              disch_then (qspecl_then [`target`, `orig_inst`, `b.bb_label`]
                mp_tac) >>
              simp[pred_labels_MEM] >>
              disch_then irule >>
              qexists `b` >> gvs[can_bypass_jump_def]))
      >> ((* lbl <> b, old pred of target *)
          Cases_on `lbl = a.bb_label`
          >- ((* lbl = a: same as Case 2A — just rewrite and repeat *)
              gvs[] >>
              simp[update_phi_bypass_def] >>
              Cases_on `MEM (Label a.bb_label) orig_inst.inst_operands` >> simp[]
              >- (mp_tac (Q.SPECL [`b.bb_label`, `a.bb_label`,
                    `orig_inst.inst_operands`]
                    cfgTransformProofsTheory.resolve_phi_remove_other) >>
                  simp[] >> disch_then (fn th => simp[th]) >>
                  qpat_assum `fn_phi_resolve_complete func`
                    (mp_tac o REWRITE_RULE[fn_phi_resolve_complete_def]) >>
                  disch_then (qspecl_then [`target`, `orig_inst`, `a.bb_label`]
                    mp_tac) >> simp[])
              >> (mp_tac (Q.SPECL [`orig_inst.inst_operands`, `a.bb_label`,
                    `b.bb_label`] resolve_phi_relabel_b_to_a) >>
                  simp[] >> disch_then (fn th => simp[th]) >>
                  qpat_assum `fn_phi_resolve_complete func`
                    (mp_tac o REWRITE_RULE[fn_phi_resolve_complete_def]) >>
                  disch_then (qspecl_then [`target`, `orig_inst`, `b.bb_label`]
                    mp_tac) >>
                  simp[pred_labels_MEM] >>
                  disch_then irule >>
                  qexists `b` >> gvs[can_bypass_jump_def]))
          >> ((* lbl <> a, lbl <> b: resolve_phi lbl preserved *)
              mp_tac (Q.SPECL [`a.bb_label`, `b.bb_label`, `lbl`, `orig_inst`]
                resolve_phi_update_bypass_other) >>
              simp[] >> disch_then (fn th => simp[th]) >>
              qpat_assum `fn_phi_resolve_complete func`
                (mp_tac o REWRITE_RULE[fn_phi_resolve_complete_def]) >>
              disch_then (qspecl_then [`target`, `orig_inst`, `lbl`] mp_tac) >>
              simp[])))
  >> ((* Case 3: other block — unchanged *)
      mp_tac pred_labels_do_merge_jump_other >>
      disch_then (qspecl_then [`func`, `a`, `b`, `lm`, `func'`, `lm'`,
        `bb.bb_label`, `target_lbl`, `lbl`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[] >> strip_tac >>
      qpat_assum `fn_phi_resolve_complete func`
        (mp_tac o REWRITE_RULE[fn_phi_resolve_complete_def]) >>
      disch_then (qspecl_then [`bb`, `inst`, `lbl`] mp_tac) >>
      simp[])
QED



Triviality fn_phi_labels_wf_do_merge_jump[local]:
  !func a b lm func' lm'.
    fn_phi_labels_wf func /\ wf_function func /\ fn_inst_wf func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\ a.bb_label <> HD (bb_succs b) /\
    do_merge_jump func a b lm = SOME (func', lm') ==>
    fn_phi_labels_wf func'
Proof
  rpt gen_tac >> strip_tac >>
  rw[fn_phi_labels_wf_def] >>
  drule_all do_merge_jump_block_cases >> strip_tac >> gvs[]
  >- ((* Case 1: a-block — double MAP: upb(cond_subst(inst)) *)
      gvs[listTheory.MEM_MAP] >>
      imp_res_tac cond_subst_PHI_inv >> gvs[] >>
      imp_res_tac update_phi_bypass_PHI_inv >> gvs[] >>
      rename1 `MEM orig_inst a.bb_instructions` >>
      qpat_x_assum `fn_phi_labels_wf func`
        (mp_tac o REWRITE_RULE[fn_phi_labels_wf_def]) >>
      disch_then (qspecl_then [`a`, `orig_inst`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      fs[update_phi_bypass_def] >>
      Cases_on `MEM (Label a.bb_label) orig_inst.inst_operands` >> fs[]
      >- (irule phi_strict_wf_remove_phi_label_preserved >> first_assum ACCEPT_TAC)
      >> irule phi_strict_wf_MAP_label_subst >> first_assum ACCEPT_TAC)
  >- ((* Case 2: target-block — update_phi_bypass *)
      gvs[listTheory.MEM_MAP] >>
      imp_res_tac update_phi_bypass_PHI_inv >> gvs[] >>
      rename1 `MEM orig_inst target.bb_instructions` >>
      qpat_x_assum `fn_phi_labels_wf func`
        (mp_tac o REWRITE_RULE[fn_phi_labels_wf_def]) >>
      disch_then (qspecl_then [`target`, `orig_inst`] mp_tac) >>
      (impl_tac >- (imp_res_tac lookup_block_MEM >>
                    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >>
      fs[update_phi_bypass_def] >>
      Cases_on `MEM (Label a.bb_label) orig_inst.inst_operands` >> fs[]
      >- (irule phi_strict_wf_remove_phi_label_preserved >> first_assum ACCEPT_TAC)
      >> irule phi_strict_wf_MAP_label_subst >> first_assum ACCEPT_TAC)
  >> ((* Case 3: other block — unchanged *)
      qpat_x_assum `fn_phi_labels_wf func`
        (mp_tac o REWRITE_RULE[fn_phi_labels_wf_def]) >>
      disch_then match_mp_tac >> metis_tac[])
QED

(* ================================================================
   Section 3b.4: collapse_wf preservation through merge_step
   ================================================================ *)

(* subst_label_op / subst_label_inst are idempotent *)
Triviality subst_label_op_idem[local]:
  !old new op.
    subst_label_op old new (subst_label_op old new op) =
    subst_label_op old new op
Proof
  Cases_on `op` >> rw[cfgTransformTheory.subst_label_op_def]
QED

Triviality subst_label_inst_idem[local]:
  !old new inst.
    subst_label_inst old new (subst_label_inst old new inst) =
    subst_label_inst old new inst
Proof
  simp[cfgTransformTheory.subst_label_inst_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF,
       subst_label_op_idem, SF ETA_ss]
QED

(* Stronger inverse: PHI instructions in output blocks whose labels
   are in succs are always substituted versions of originals.
   Combines with uspl_phi_inst_inverse: when bb'.bb_label ∈ succs,
   forces in_succ = T. *)
Triviality uspl_phi_in_succ_subst[local]:
  !succs old new bbs bb' inst.
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
    MEM bb' (update_succ_phi_labels old new bbs succs) /\
    MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI /\
    MEM bb'.bb_label succs ==>
    ?bb0 inst0.
      MEM bb0 bbs /\ MEM inst0 bb0.bb_instructions /\
      inst0.inst_opcode = PHI /\ bb0.bb_label = bb'.bb_label /\
      inst = subst_label_inst old new inst0
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM _ (update_succ_phi_labels _ _ _ (h::_))` mp_tac >>
  simp_tac std_ss [update_succ_phi_labels_cons] >>
  Cases_on `lookup_block h bbs` >> simp_tac (srw_ss()) []
  >- (
    strip_tac >>
    suspend "case_none")
  >>
  strip_tac >>
  rename1 `lookup_block h bbs = SOME sbb` >>
  Cases_on `MEM bb'.bb_label succs`
  >- suspend "case_some_mem"
  >> suspend "case_some_eq"
QED

Resume uspl_phi_in_succ_subst[case_none]:
  (* NONE: step is no-op, bb' ∈ uspl(bbs, succs). Need MEM bb'.bb_label succs.
     If bb'.bb_label = h, contradiction: bb' ∈ output means h ∈ MAP label bbs,
     but lookup_block h bbs = NONE. *)
  Cases_on `MEM bb'.bb_label succs`
  >- (last_assum (qspecl_then [`old`, `new`, `bbs`, `bb'`, `inst`] mp_tac) >>
      simp[])
  >>
  (* bb'.bb_label = h: contradiction *)
  `bb'.bb_label = h` by
    (qpat_x_assum `MEM bb'.bb_label (h::_)` mp_tac >> gvs[listTheory.MEM]) >>
  `MEM h (MAP (\b. b.bb_label) bbs)` by (
    `MEM h (MAP (\b. b.bb_label)
       (update_succ_phi_labels old new bbs succs))` by
      (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
    gvs[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels]) >>
  gvs[listTheory.MEM_MAP] >>
  rename1 `MEM b0 bbs` >>
  `lookup_block b0.bb_label bbs = SOME b0` by
    (irule venomExecProofsTheory.MEM_lookup_block >> simp[]) >>
  gvs[]
QED

Resume uspl_phi_in_succ_subst[case_some_mem]:
  (* SOME sbb, MEM bb'.bb_label succs: apply IH on bbs'.
     bbs' = replace_block h sbb' bbs where sbb' has PHIs substituted. *)
  `sbb.bb_label = h` by (imp_res_tac lookup_block_label >> simp[]) >>
  qmatch_asmsub_abbrev_tac `update_succ_phi_labels _ _ bbs' succs` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs')` by (
    simp[Abbr `bbs'`] >>
    irule ALL_DISTINCT_replace_block >> simp[]) >>
  last_assum (qspecl_then [`old`, `new`, `bbs'`, `bb'`, `inst`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* Trace bb0 from bbs' back to bbs *)
  simp[Abbr `bbs'`] >>
  qpat_x_assum `MEM bb0 _` mp_tac >>
  simp_tac (srw_ss()) [MEM_replace_block_cases] >> strip_tac >> gvs[]
  >- (
    (* bb0 = substituted sbb: trace inst0 through MAP *)
    qpat_x_assum `MEM inst0 _` mp_tac >>
    simp[listTheory.MEM_MAP] >> strip_tac >>
    rename1 `MEM orig sbb.bb_instructions` >>
    Cases_on `orig.inst_opcode = PHI` >> gvs[]
    >- (qexistsl [`sbb`, `orig`] >>
        imp_res_tac lookup_block_MEM >> simp[subst_label_inst_idem])
    >> gvs[])
  >> (qexistsl [`bb0`, `inst0`] >> simp[])
QED

Resume uspl_phi_in_succ_subst[case_some_eq]:
  (* SOME sbb, ~MEM bb'.bb_label succs: forced bb'.bb_label = h.
     Block h was modified in this step. uspl(succs, bbs') doesn't touch it
     since h ∉ succs. So bb' is the modified block sbb'. *)
  `sbb.bb_label = h` by (imp_res_tac lookup_block_label >> simp[]) >>
  `bb'.bb_label = h` by (
    qpat_x_assum `MEM bb'.bb_label (h::_)` mp_tac >> simp[]) >>
  qmatch_asmsub_abbrev_tac `update_succ_phi_labels _ _ bbs' succs` >>
  `~MEM h succs` by gvs[] >>
  (* Establish ALL_DISTINCT for bbs' early *)
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs')` by (
    qunabbrev_tac `bbs'` >>
    irule ALL_DISTINCT_replace_block >> simp[]) >>
  (* uspl doesn't change block at h since h ∉ succs *)
  `lookup_block h bbs' = SOME bb'` by (
    `lookup_block h (update_succ_phi_labels old new bbs' succs) =
     lookup_block h bbs'` by
      simp[lookup_block_update_succ_phi_not_in_succs] >>
    `lookup_block h (update_succ_phi_labels old new bbs' succs) = SOME bb'` by (
      irule venomExecProofsTheory.MEM_lookup_block >>
      simp[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels]) >>
    gvs[]) >>
  (* Abbreviate the modified block and derive lookup *)
  qabbrev_tac `sbb' = sbb with bb_instructions :=
    MAP (\i. if i.inst_opcode <> PHI then i
             else subst_label_inst old new i) sbb.bb_instructions` >>
  `lookup_block h bbs' = SOME sbb'` by (
    qpat_x_assum `Abbrev (bbs' = _)` (SUBST1_TAC o
      REWRITE_RULE [markerTheory.Abbrev_def]) >>
    irule cfgTransformProofsTheory.lookup_block_replace_eq >>
    simp[Abbr `sbb'`] >> metis_tac[]) >>
  (* bb' = sbb' by uniqueness of lookup *)
  `bb' = sbb'` by (
    qpat_x_assum `lookup_block h bbs' = SOME bb'` mp_tac >>
    qpat_x_assum `lookup_block h bbs' = SOME sbb'` mp_tac >>
    simp[]) >>
  gvs[Abbr `sbb'`] >>
  (* inst ∈ MAP(...) sbb.bb_instructions, decompose *)
  qpat_x_assum `MEM inst _` mp_tac >>
  simp[listTheory.MEM_MAP] >> strip_tac >>
  rename1 `MEM orig sbb.bb_instructions` >>
  Cases_on `orig.inst_opcode = PHI` >> gvs[]
  >- (qexistsl [`sbb`, `orig`] >>
      imp_res_tac venomExecPropsTheory.lookup_block_MEM >> simp[])
QED

Finalise uspl_phi_in_succ_subst

Triviality uspl_phi_inst_inverse[local]:
  !succs old new bbs bb' inst.
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
    MEM bb' (update_succ_phi_labels old new bbs succs) /\
    MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI ==>
    ?bb0 inst0 in_succ.
      MEM bb0 bbs /\ MEM inst0 bb0.bb_instructions /\
      inst0.inst_opcode = PHI /\ bb0.bb_label = bb'.bb_label /\
      (if in_succ then inst = subst_label_inst old new inst0
       else inst = inst0)
Proof
  Induct
  >- (rw[simplifyCfgDefsTheory.update_succ_phi_labels_def] >>
      qexistsl [`bb'`, `inst`, `F`] >> simp[])
  >> rpt gen_tac >> strip_tac >>
  (* Rewrite only the MEM assumption, not the IH *)
  qpat_x_assum `MEM _ (update_succ_phi_labels _ _ _ (h::_))` mp_tac >>
  simp_tac std_ss [update_succ_phi_labels_cons] >>
  Cases_on `lookup_block h bbs` >> simp_tac (srw_ss()) []
  >- (
    (* h not in bbs — IH applies directly *)
    strip_tac >>
    last_assum (qspecl_then [`old`, `new`, `bbs`, `bb'`, `inst`] mp_tac) >>
    simp[])
  >> strip_tac >>
  rename1 `lookup_block h bbs = SOME sbb` >>
  qabbrev_tac `sbb' = sbb with bb_instructions :=
    MAP (\i. if i.inst_opcode <> PHI then i
             else subst_label_inst old new i)
        sbb.bb_instructions` >>
  qabbrev_tac `bbs' = replace_block h sbb' bbs` >>
  (* ALL_DISTINCT for bbs' *)
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs')` by (
    qunabbrev_tac `bbs'` >> qunabbrev_tac `sbb'` >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
    simp[] >>
    imp_res_tac venomExecProofsTheory.lookup_block_label >> simp[]) >>
  last_x_assum (qspecl_then [`old`, `new`, `bbs'`, `bb'`, `inst`] mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >>
  (* bb0 is in bbs' = replace_block h sbb' bbs *)
  qunabbrev_tac `bbs'` >>
  gvs[MEM_replace_block_cases]
  >- suspend "sbb_case"
  >> (
    (* bb0 is an original block from bbs (not sbb') *)
    qexistsl [`bb0`, `inst0`, `in_succ`] >> simp[])
QED

Resume uspl_phi_inst_inverse[sbb_case]:
  (* bb0 (=sbb') has instructions MAP (subst if PHI) sbb.bb_instructions.
     inst0 is in those instructions. Decompose via MEM_MAP. *)
  simp[Abbr `bb0`] >>
  qpat_x_assum `MEM inst0 _` mp_tac >>
  simp[listTheory.MEM_MAP] >> strip_tac >>
  rename1 `MEM orig sbb.bb_instructions` >>
  (* Case split: if orig not PHI, contradiction (inst0 = orig but inst0.opcode = PHI) *)
  Cases_on `orig.inst_opcode = PHI` >> gvs[] >>
  (* orig is PHI: inst0 = subst(orig). Witness (sbb, orig, T). *)
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  qexistsl [`sbb`, `orig`, `T`] >> simp[] >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >> simp[] >>
  Cases_on `in_succ` >> gvs[] >> simp[subst_label_inst_idem]
QED

Finalise uspl_phi_inst_inverse

(* Generic: PHI property preserved through update_succ_phi_labels
   when the property is closed under subst_label_inst *)
Triviality phi_property_update_succ_phi_labels[local]:
  !succs P old new bbs.
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions /\
               inst.inst_opcode = PHI ==> P inst) /\
    (!inst. inst.inst_opcode = PHI /\ P inst ==>
            P (subst_label_inst old new inst)) ==>
    !bb inst. MEM bb (update_succ_phi_labels old new bbs succs) /\
              MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
              P inst
Proof
  Induct
  >- (rw[simplifyCfgDefsTheory.update_succ_phi_labels_def] >> res_tac)
  >> rpt gen_tac >> strip_tac >>
  simp_tac std_ss [update_succ_phi_labels_cons] >>
  Cases_on `lookup_block h bbs`
  >- (simp_tac (srw_ss()) [] >> rpt strip_tac >>
      first_x_assum (qspecl_then [`P`, `old`, `new`, `bbs`] mp_tac) >>
      (impl_tac >- (rpt strip_tac >> res_tac)) >> disch_tac >> res_tac)
  >> simp_tac (srw_ss()) [] >>
  rename1 `lookup_block h bbs = SOME sbb` >>
  qabbrev_tac `bbs' = replace_block h
    (sbb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst old new inst)
          sbb.bb_instructions) bbs` >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`P`, `old`, `new`, `bbs'`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- (rpt strip_tac >> qunabbrev_tac `bbs'` >>
          gvs[MEM_replace_block_cases]
          >- (gvs[listTheory.MEM_MAP] >>
              IF_CASES_TAC >> gvs[]
              >- (imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
                  metis_tac[])
              >> imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
              metis_tac[])
          >> metis_tac[])
      >> metis_tac[]) >>
  disch_tac >> res_tac
QED

(* Generic: PHI property preserved through merge_step *)
Triviality phi_property_merge_step[local]:
  !P func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    (!bb inst. MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions /\
               inst.inst_opcode = PHI ==> P inst) /\
    (!inst. inst.inst_opcode = PHI /\ P inst ==>
            P (subst_label_inst next_lbl lbl inst)) ==>
    !bb' inst. MEM bb' (update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))) /\
      MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI ==>
      P inst
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qsuff_tac `!bb'' inst'. MEM bb'' (replace_block lbl (merge_blocks bb next_bb)
       (remove_block next_lbl func.fn_blocks)) /\
     MEM inst' bb''.bb_instructions /\ inst'.inst_opcode = PHI ==>
     P inst'`
  >- suspend "USE_USPL"
  >> suspend "MEM_MID"
QED

Resume phi_property_merge_step[USE_USPL]:
  strip_tac >>
  qspecl_then [`bb_succs (merge_blocks bb next_bb)`, `P`, `next_lbl`, `lbl`,
       `replace_block lbl (merge_blocks bb next_bb)
          (remove_block next_lbl func.fn_blocks)`]
       mp_tac phi_property_update_succ_phi_labels >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`bb'`, `inst`] mp_tac) >>
  simp_tac std_ss [] >> metis_tac[]
QED

Resume phi_property_merge_step[MEM_MID]:
  rpt strip_tac >>
  gvs[MEM_replace_block_cases, cfgTransformProofsTheory.MEM_remove_block_iff]
  (* merged block case: inst' is PHI in FRONT bb ++ next_bb *)
  >- (gvs[merge_blocks_def, listTheory.MEM_APPEND,
          can_merge_blocks_def, no_phis_def, listTheory.EVERY_MEM] >>
      imp_res_tac lookup_block_MEM >>
      Cases_on `bb.bb_instructions` >> gvs[] >>
      imp_res_tac rich_listTheory.MEM_FRONT >>
      metis_tac[listTheory.MEM])
  (* original block case: inst' is PHI in unchanged block *)
  >> res_tac
QED

Finalise phi_property_merge_step

(* Block-contextual variant: PHI property indexed by block label,
   preserved through update_succ_phi_labels *)
Triviality phi_property_uspl_ctx[local]:
  !succs Q old new bbs.
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions /\
               inst.inst_opcode = PHI ==> Q bb.bb_label inst) /\
    (!L inst. inst.inst_opcode = PHI /\ Q L inst ==>
              Q L (subst_label_inst old new inst)) ==>
    !bb inst. MEM bb (update_succ_phi_labels old new bbs succs) /\
              MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
              Q bb.bb_label inst
Proof
  Induct
  >- (rw[simplifyCfgDefsTheory.update_succ_phi_labels_def] >> res_tac)
  >> rpt gen_tac >> strip_tac >>
  simp_tac std_ss [update_succ_phi_labels_cons] >>
  Cases_on `lookup_block h bbs`
  >- (simp_tac (srw_ss()) [] >> rpt strip_tac >>
      first_x_assum (qspecl_then [`Q`, `old`, `new`, `bbs`] mp_tac) >>
      (impl_tac >- (rpt strip_tac >> res_tac)) >> disch_tac >> res_tac)
  >> simp_tac (srw_ss()) [] >>
  rename1 `lookup_block h bbs = SOME sbb` >>
  qabbrev_tac `bbs' = replace_block h
    (sbb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst old new inst)
          sbb.bb_instructions) bbs` >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`Q`, `old`, `new`, `bbs'`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> qunabbrev_tac `bbs'` >>
          gvs[MEM_replace_block_cases]
          >- (gvs[listTheory.MEM_MAP] >>
              IF_CASES_TAC >> gvs[]
              >- (imp_res_tac venomExecProofsTheory.lookup_block_label >>
                  imp_res_tac venomExecProofsTheory.lookup_block_MEM >> gvs[] >>
                  metis_tac[])
              >> imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
              imp_res_tac venomExecProofsTheory.lookup_block_label >> gvs[] >>
              metis_tac[])
          >> metis_tac[])
      >> metis_tac[]) >>
  disch_tac >> res_tac
QED

(* Block-contextual variant: PHI property indexed by block label,
   preserved through full merge_step *)
Triviality phi_property_merge_step_ctx[local]:
  !Q func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    (!bb inst. MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions /\
               inst.inst_opcode = PHI ==> Q bb.bb_label inst) /\
    (!L inst. inst.inst_opcode = PHI /\ Q L inst ==>
              Q L (subst_label_inst next_lbl lbl inst)) ==>
    !bb' inst. MEM bb' (update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))) /\
      MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI ==>
      Q bb'.bb_label inst
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac phi_property_uspl_ctx >>
  conj_tac
  >- ((* base: Q bb0.bb_label inst for mid-layer blocks *)
      rpt strip_tac >>
      gvs[MEM_replace_block_cases, cfgTransformProofsTheory.MEM_remove_block_iff]
      (* merged block case: inst from FRONT bb ++ next_bb *)
      >- (gvs[merge_blocks_def, listTheory.MEM_APPEND,
              can_merge_blocks_def, no_phis_def, listTheory.EVERY_MEM] >>
          imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
          imp_res_tac venomExecProofsTheory.lookup_block_label >> gvs[] >>
          Cases_on `bb.bb_instructions` >> gvs[] >>
          imp_res_tac rich_listTheory.MEM_FRONT >>
          metis_tac[listTheory.MEM])
      (* original block case *)
      >> metis_tac[])
  >> metis_tac[]
QED

(* fn_phi_even through merge_step *)
Triviality fn_phi_even_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    fn_phi_even func /\ wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    fn_phi_even (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt gen_tac >> strip_tac >>
  `!bb' inst. MEM bb' (update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))) /\
      MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI ==>
      EVEN (LENGTH inst.inst_operands)` suffices_by simp[fn_phi_even_def] >>
  ho_match_mp_tac phi_property_merge_step >>
  gvs[fn_phi_even_def] >> rpt strip_tac >> res_tac >>
  gvs[cfgTransformTheory.subst_label_inst_def, listTheory.LENGTH_MAP]
QED

(* fn_phi_labels_wf through merge_step *)
Triviality fn_phi_labels_wf_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    fn_phi_labels_wf func /\ wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    fn_phi_labels_wf (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt gen_tac >> strip_tac >>
  `!bb' inst. MEM bb' (update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))) /\
      MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI ==>
      phi_strict_wf inst.inst_operands` suffices_by
    simp[fn_phi_labels_wf_def] >>
  ho_match_mp_tac phi_property_merge_step >>
  gvs[fn_phi_labels_wf_def] >> rpt strip_tac >> res_tac >>
  gvs[cfgTransformTheory.subst_label_inst_def] >>
  irule phi_strict_wf_MAP_subst_label_op >> first_assum ACCEPT_TAC
QED

(* ================================================================
   Infrastructure lemmas for merge_step (bbs_mid)
   ================================================================ *)

(* ALL_DISTINCT labels after replace+remove in merge_step *)
Triviality ALL_DISTINCT_merge_step_mid[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb ==>
    ALL_DISTINCT (MAP (\b. b.bb_label)
      (replace_block lbl (merge_blocks bb next_bb)
         (remove_block next_lbl func.fn_blocks)))
Proof
  rpt strip_tac >>
  irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
  simp[merge_blocks_def] >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >> simp[] >>
  irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >>
  fs[wf_function_def, fn_labels_def]
QED

(* bb_well_formed for all blocks in bbs_mid *)
Triviality bb_well_formed_merge_step_mid[local]:
  !func lbl next_lbl bb next_bb b.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    MEM b (replace_block lbl (merge_blocks bb next_bb)
             (remove_block next_lbl func.fn_blocks)) ==>
    bb_well_formed b
Proof
  rpt strip_tac >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  gvs[MEM_replace_block_cases]
  >- (irule simplifyCfgHelpersTheory.bb_well_formed_merge_blocks >>
      gvs[can_merge_blocks_def] >> fs[wf_function_def])
  >> gvs[cfgTransformProofsTheory.MEM_remove_block_iff] >>
  fs[wf_function_def]
QED


(* fn_bypass_safe preserved through merge_step — standalone to avoid
   large-context 'by' failures inside collapse_wf_merge_step.
   Why: fn_bypass_safe is about LAST instruction properties (opcode, num_succs).
   LAST is preserved through uspl (above), and for bbs_mid blocks,
   merged block has LAST = LAST(next_bb), others are unchanged from func. *)
Triviality fn_bypass_safe_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    fn_bypass_safe func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    fn_bypass_safe (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt strip_tac >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  `ALL_DISTINCT (MAP (\b. b.bb_label)
     (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks)))` by (
    irule ALL_DISTINCT_merge_step_mid >> metis_tac[]) >>
  `!b. MEM b (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks)) ==> bb_well_formed b` by (
    rpt strip_tac >> irule bb_well_formed_merge_step_mid >> metis_tac[]) >>
  (* Use LAST_update_succ_phi_labels to relate blocks in result to bbs_mid *)
  simp[fn_bypass_safe_def] >> rpt gen_tac >> strip_tac >>
  drule_all LAST_update_succ_phi_labels >> strip_tac >>
  (* bb0 is in bbs_mid with same LAST as bb' *)
  (* Case split: bb0 is the merged block or an original block *)
  qpat_x_assum `MEM bb0 _` mp_tac >>
  simp[MEM_replace_block_cases,
       cfgTransformProofsTheory.MEM_remove_block_iff] >>
  strip_tac >> gvs[]
  >- ((* bb0 = merge_blocks bb next_bb *)
      (* Establish LAST chain: bb' → merge_blocks → next_bb *)
      `bb_well_formed next_bb` by fs[wf_function_def] >>
      `next_bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
      `LAST (merge_blocks bb next_bb).bb_instructions =
       LAST next_bb.bb_instructions` by
        (Cases_on `next_bb.bb_instructions` >> gvs[] >>
         simp[merge_blocks_def, LAST_APPEND_CONS]) >>
      fs[] >>
      (* Transfer fn_bypass_safe from next_bb *)
      qpat_x_assum `fn_bypass_safe func`
        (mp_tac o REWRITE_RULE[fn_bypass_safe_def]) >>
      disch_then (qspec_then `next_bb` mp_tac) >> simp[] >>
      strip_tac >>
      `num_succs bb' = num_succs next_bb` by
        (irule num_succs_LAST_eq >> metis_tac[]) >>
      fs[])
  >> ((* bb0 is an original block — transfer directly *)
      qpat_x_assum `fn_bypass_safe func`
        (mp_tac o REWRITE_RULE[fn_bypass_safe_def]) >>
      disch_then (qspec_then `bb0` mp_tac) >> simp[] >>
      strip_tac >>
      `num_succs bb' = num_succs bb0` by
        (irule num_succs_LAST_eq >> metis_tac[]) >>
      fs[])
QED



(* ================================================================
   Section 3c: pred_labels and PHI properties through merge_step
   ================================================================ *)

(* Abbreviation for intermediate block list before uspl *)
val bbs_mid_tm = ``replace_block lbl (merge_blocks bb next_bb)
                     (remove_block next_lbl func.fn_blocks)``;

(* pred_labels through update_succ_phi_labels — uspl preserves pred_labels
   because it preserves both bb_labels and bb_succs.
   We use pred_labels_MEM to reduce to MEM reasoning about labels and succs. *)
Triviality pred_labels_update_succ_phi_labels[local]:
  !func old new bbs succs p x.
    (!b. MEM b bbs ==> bb_well_formed b) /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    (MEM p (pred_labels (func with fn_blocks :=
       update_succ_phi_labels old new bbs succs) x) <=>
     MEM p (pred_labels (func with fn_blocks := bbs) x))
Proof
  rpt strip_tac >>
  simp[pred_labels_MEM] >>
  `MAP (\b. b.bb_label) (update_succ_phi_labels old new bbs succs) =
   MAP (\b. b.bb_label) bbs` by
    simp[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels] >>
  `MAP bb_succs (update_succ_phi_labels old new bbs succs) =
   MAP bb_succs bbs` by (
    irule MAP_bb_succs_update_succ_phi_labels >> simp[]) >>
  `LENGTH (update_succ_phi_labels old new bbs succs) = LENGTH bbs` by
    metis_tac[listTheory.LENGTH_MAP] >>
  eq_tac >> strip_tac
  >- ((* ==> : bb in uspl, find corresponding bb in bbs *)
      `?i. i < LENGTH bbs /\
           EL i (update_succ_phi_labels old new bbs succs) = bb` by
        metis_tac[listTheory.MEM_EL] >>
      qexists `EL i bbs` >>
      `bb_succs (EL i (update_succ_phi_labels old new bbs succs)) =
       bb_succs (EL i bbs)` by
        metis_tac[listTheory.EL_MAP] >>
      `(EL i (update_succ_phi_labels old new bbs succs)).bb_label =
       (EL i bbs).bb_label` by
        metis_tac[listTheory.EL_MAP] >>
      gvs[] >> metis_tac[listTheory.MEM_EL])
  >> ((* <== : bb in bbs, find corresponding bb in uspl *)
      `?i. i < LENGTH bbs /\ EL i bbs = bb` by
        metis_tac[listTheory.MEM_EL] >>
      qexists `EL i (update_succ_phi_labels old new bbs succs)` >>
      `bb_succs (EL i (update_succ_phi_labels old new bbs succs)) =
       bb_succs (EL i bbs)` by
        metis_tac[listTheory.EL_MAP] >>
      `(EL i (update_succ_phi_labels old new bbs succs)).bb_label =
       (EL i bbs).bb_label` by
        metis_tac[listTheory.EL_MAP] >>
      gvs[] >> metis_tac[listTheory.MEM_EL])
QED

(* pred_labels through replace_block + remove_block for merge_step.
   Key insight: blocks in replace_block lbl merged (remove_block next_lbl bbs) are:
   - merged block (label = lbl, succs = bb_succs next_bb)
   - original blocks with label ≠ lbl and ≠ next_lbl (unchanged)
   And lbl's only old successor was next_lbl (from single_succ_jmp). *)
Triviality pred_labels_merge_step_mid[local]:
  !func lbl next_lbl bb next_bb p x.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_lbl ==>
    (MEM p (pred_labels (func with fn_blocks :=
       replace_block lbl (merge_blocks bb next_bb)
         (remove_block next_lbl func.fn_blocks)) x) <=>
     (p = lbl /\ MEM x (bb_succs next_bb)) \/
     (p <> next_lbl /\ p <> lbl /\ MEM p (pred_labels func x)))
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `bb_well_formed bb /\ bb_well_formed next_bb` by
    (fs[wf_function_def] >> res_tac) >>
  `bb_succs bb = [next_lbl]` by fs[can_merge_blocks_def] >>
  `bb_succs (merge_blocks bb next_bb) = bb_succs next_bb` by
    metis_tac[bb_succs_merge_blocks] >>
  `(merge_blocks bb next_bb).bb_label = lbl` by
    (simp[merge_blocks_def]) >>
  simp[pred_labels_MEM] >> eq_tac
  >- ((* ==> : bb' in replace_block lbl merged (remove_block next_lbl bbs) *)
      strip_tac >>
      gvs[MEM_replace_block_cases, cfgTransformProofsTheory.MEM_remove_block_iff] >>
      (* merged block case auto-closed by gvs; remaining: original block *)
      metis_tac[])
  >> ((* <== : reconstruct witness in replace+remove *)
      strip_tac >> gvs[]
      >- (qexists `merge_blocks bb next_bb` >> simp[] >>
          match_mp_tac MEM_replace_block_new >>
          qexists `bb` >> simp[] >>
          match_mp_tac MEM_remove_block_intro >> simp[])
      >> (gvs[pred_labels_MEM] >>
          qexists `bb'` >> simp[] >>
          match_mp_tac MEM_replace_block_other >> simp[] >>
          match_mp_tac MEM_remove_block_intro >> simp[]))
QED

(* Main: pred_labels through full merge_step *)
Triviality pred_labels_merge_step[local]:
  !func lbl next_lbl bb next_bb p x.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_lbl ==>
    (MEM p (pred_labels (func with fn_blocks :=
       update_succ_phi_labels next_lbl lbl
         (replace_block lbl (merge_blocks bb next_bb)
            (remove_block next_lbl func.fn_blocks))
         (bb_succs (merge_blocks bb next_bb))) x) <=>
     (p = lbl /\ MEM x (bb_succs next_bb)) \/
     (p <> next_lbl /\ p <> lbl /\ MEM p (pred_labels func x)))
Proof
  rpt strip_tac >>
  qabbrev_tac `bbs_mid = replace_block lbl (merge_blocks bb next_bb)
    (remove_block next_lbl func.fn_blocks)` >>
  qabbrev_tac `msuccs = bb_succs (merge_blocks bb next_bb)` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs_mid)` by (
    simp[Abbr `bbs_mid`] >>
    irule ALL_DISTINCT_merge_step_mid >> metis_tac[]) >>
  `!b. MEM b bbs_mid ==> bb_well_formed b` by (
    simp[Abbr `bbs_mid`] >> rpt strip_tac >>
    irule bb_well_formed_merge_step_mid >> metis_tac[]) >>
  `MEM p (pred_labels (func with fn_blocks :=
     update_succ_phi_labels next_lbl lbl bbs_mid msuccs) x) <=>
   MEM p (pred_labels (func with fn_blocks := bbs_mid) x)` by (
    irule pred_labels_update_succ_phi_labels >> simp[]) >>
  simp[Abbr `bbs_mid`] >>
  irule pred_labels_merge_step_mid >> metis_tac[]
QED



(* MEM Label through subst_label_inst *)
Triviality MEM_Label_subst_label_inst[local]:
  !old new inst lbl'.
    MEM (Label lbl') (subst_label_inst old new inst).inst_operands ==>
    lbl' = new \/ (lbl' <> old /\ MEM (Label lbl') inst.inst_operands)
Proof
  rw[cfgTransformTheory.subst_label_inst_def, listTheory.MEM_MAP] >>
  Cases_on `y` >> gvs[cfgTransformTheory.subst_label_op_def] >>
  IF_CASES_TAC >> gvs[]
QED

(* Converse: MEM Label through subst_label_inst, backward *)
Triviality MEM_Label_subst_label_inst_intro[local]:
  !old new inst lbl'.
    MEM (Label lbl') inst.inst_operands /\ lbl' <> old ==>
    MEM (Label lbl') (subst_label_inst old new inst).inst_operands
Proof
  rw[cfgTransformTheory.subst_label_inst_def, listTheory.MEM_MAP] >>
  qexists `Label lbl'` >> simp[cfgTransformTheory.subst_label_op_def]
QED

Triviality MEM_Label_subst_intro_new[local]:
  !old new inst.
    MEM (Label old) inst.inst_operands ==>
    MEM (Label new) (subst_label_inst old new inst).inst_operands
Proof
  rw[cfgTransformTheory.subst_label_inst_def, listTheory.MEM_MAP] >>
  qexists `Label old` >> simp[cfgTransformTheory.subst_label_op_def]
QED

(* Precise iff characterization of Label membership through subst_label_inst *)
Triviality MEM_Label_subst_label_inst_iff[local]:
  !old new inst l.
    MEM (Label l) (subst_label_inst old new inst).inst_operands <=>
    (MEM (Label l) inst.inst_operands /\ l <> old) \/
    (l = new /\ MEM (Label old) inst.inst_operands)
Proof
  rw[cfgTransformTheory.subst_label_inst_def, listTheory.MEM_MAP] >>
  eq_tac >> strip_tac
  >- (Cases_on `y` >>
      gvs[cfgTransformTheory.subst_label_op_def] >>
      IF_CASES_TAC >> gvs[] >>
      metis_tac[])
  >- (qexists `Label l` >> simp[cfgTransformTheory.subst_label_op_def])
  >> (qexists `Label old` >> simp[cfgTransformTheory.subst_label_op_def])
QED

(* lookup_block_unique: ALL_DISTINCT labels + lookup + MEM + same label => same block *)
Triviality lookup_block_unique[local]:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==>
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    !bb'. MEM bb' bbs /\ bb'.bb_label = lbl ==> bb' = bb
Proof
  rpt strip_tac >>
  `lookup_block lbl bbs = SOME bb'` by
    metis_tac[venomExecProofsTheory.MEM_lookup_block] >>
  gvs[]
QED

(* Helper: no block in func' has label next_lbl (it was removed) *)
Triviality no_next_lbl_in_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_lbl ==>
    !bb'. MEM bb' (update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))) ==>
      bb'.bb_label <> next_lbl
Proof
  rpt strip_tac >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  `(merge_blocks bb next_bb).bb_label = lbl` by
    simp[merge_blocks_def] >>
  `MEM bb'.bb_label (MAP (\b. b.bb_label)
     (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks)))` by
    (metis_tac[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels,
               listTheory.MEM_MAP]) >>
  gvs[cfgTransformPropsTheory.fn_labels_replace_block,
      cfgTransformPropsTheory.fn_labels_remove_block,
      listTheory.MEM_FILTER]
QED

(* Helper: bb'.bb_label = next_lbl is impossible for blocks in func' *)
Triviality bb_label_neq_next_lbl_merge[local]:
  !func lbl next_lbl bb next_bb lbl'.
    wf_function func /\ fn_phi_preds_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_lbl /\
    MEM lbl' (pred_labels func x) /\
    x <> next_lbl ==>
    (lbl' = next_lbl ==> MEM x (bb_succs next_bb))
Proof
  rpt strip_tac >> gvs[] >>
  gvs[pred_labels_MEM] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    (fs[wf_function_def, fn_labels_def]) >>
  metis_tac[lookup_block_unique]
QED

(* Hybrid Q: trace Label membership through merge_step.
   Each Label l in a PHI operand either was a predecessor in func,
   or is lbl when the containing block is a successor of next_bb. *)
Triviality phi_labels_hybrid_Q_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    fn_phi_preds_wf func /\ wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\ lbl <> next_lbl ==>
    !bb1 inst1. MEM bb1 (update_succ_phi_labels next_lbl lbl
         (replace_block lbl (merge_blocks bb next_bb)
            (remove_block next_lbl func.fn_blocks))
         (bb_succs (merge_blocks bb next_bb))) /\
         MEM inst1 bb1.bb_instructions /\ inst1.inst_opcode = PHI ==>
         !l. MEM (Label l) inst1.inst_operands ==>
             MEM l (pred_labels func bb1.bb_label) \/
             (l = lbl /\ MEM bb1.bb_label (bb_succs next_bb))
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac phi_property_merge_step_ctx >>
  BETA_TAC >> rpt strip_tac >> TRY (first_assum ACCEPT_TAC)
  (* Base: blocks in func.fn_blocks — fn_phi_preds_wf gives first disjunct *)
  >- (disj1_tac >>
      qpat_x_assum `fn_phi_preds_wf func`
        (mp_tac o REWRITE_RULE [fn_phi_preds_wf_def]) >>
      disch_then drule_all >> simp[])
  (* Closure: MEM (Label l) (subst next_lbl lbl inst1).operands *)
  >> (qpat_x_assum `MEM (Label _) (subst_label_inst _ _ _).inst_operands`
        (strip_assume_tac o REWRITE_RULE [MEM_Label_subst_label_inst_iff])
      >- ((* l preserved from original (l ≠ next_lbl) *)
          res_tac >> gvs[])
      >> ((* l = lbl from subst of Label next_lbl *)
          gvs[] >>
          first_x_assum (qspec_then `next_lbl` mp_tac) >> simp[] >>
          strip_tac >> gvs[] >>
          gvs[pred_labels_MEM] >>
          `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
            fs[wf_function_def, fn_labels_def] >>
          disj2_tac >> metis_tac[lookup_block_unique]))
QED

(* After merge_step, Label next_lbl never appears in any PHI in func'.
   Proof: hybrid Q says Label next_lbl → next_lbl ∈ pred_labels func bb'.label
   → bb'.label ∈ bb_succs next_bb → update_succ_phi_labels substituted that
   block → subst_label_inst removes Label next_lbl → contradiction. *)
Triviality no_Label_next_lbl_merge_step[local]:
  !func lbl next_lbl bb next_bb bb' inst.
    fn_phi_preds_wf func /\ wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\ lbl <> next_lbl /\
    MEM bb' (update_succ_phi_labels next_lbl lbl
      (replace_block lbl (merge_blocks bb next_bb)
         (remove_block next_lbl func.fn_blocks))
      (bb_succs (merge_blocks bb next_bb))) /\
    MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI ==>
    ~MEM (Label next_lbl) inst.inst_operands
Proof
  rpt strip_tac >>
  suspend "main"
QED

Resume no_Label_next_lbl_merge_step[main]:
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) (replace_block lbl (merge_blocks bb next_bb)
       (remove_block next_lbl func.fn_blocks)))` by
    (irule ALL_DISTINCT_merge_step_mid >> metis_tac[]) >>
  `bb_succs (merge_blocks bb next_bb) = bb_succs next_bb` by
    (irule simplifyCfgCollapseBaseTheory.bb_succs_merge_blocks >>
     fs[wf_function_def] >>
     metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
  (* Hybrid Q → bb'.label ∈ bb_succs next_bb *)
  suspend "bb_succs"
QED

Resume no_Label_next_lbl_merge_step[bb_succs]:
  (* Step A: hybrid Q already fully instantiated by drule_all *)
  drule_all phi_labels_hybrid_Q_merge_step >>
  (* Goal: (MEM next_lbl (pred_labels func bb'.label) ∨
            (next_lbl = lbl ∧ ...)) ⇒ F *)
  strip_tac >> gvs[] >>
  (* lbl ≠ next_lbl kills second disjunct, so:
     MEM next_lbl (pred_labels func bb'.bb_label) *)
  (* Step D: MEM next_lbl (pred_labels func bb'.label) → bb'.label ∈ bb_succs next_bb *)
  `MEM bb'.bb_label (bb_succs next_bb)` by
    (fs[pred_labels_MEM] >>
     `MEM next_bb func.fn_blocks` by
       metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
     `next_bb.bb_label = next_lbl` by
       metis_tac[venomExecProofsTheory.lookup_block_label] >>
     metis_tac[simplifyCfgCollapseBaseTheory.wf_blocks_unique]) >>
  (* Step E: bb' is in the substituted layer *)
  qabbrev_tac `mid = replace_block lbl (merge_blocks bb next_bb)
    (remove_block next_lbl func.fn_blocks)` >>
  `MEM bb'.bb_label (MAP (\b. b.bb_label) mid)` by
    (`MAP (\b. b.bb_label)
       (update_succ_phi_labels next_lbl lbl mid (bb_succs next_bb)) =
     MAP (\b. b.bb_label) mid` by
      simp[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels] >>
     metis_tac[listTheory.MEM_MAP]) >>
  `?orig_bb. lookup_block bb'.bb_label mid = SOME orig_bb` by
    (gvs[listTheory.MEM_MAP] >>
     metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  `lookup_block bb'.bb_label
     (update_succ_phi_labels next_lbl lbl mid (bb_succs next_bb)) =
   SOME (orig_bb with bb_instructions :=
     MAP (\i. if i.inst_opcode <> PHI then i
              else subst_label_inst next_lbl lbl i)
     orig_bb.bb_instructions)` by
    (irule lookup_block_uspl_in_succs >> gvs[]) >>
  `bb' = orig_bb with bb_instructions :=
     MAP (\i. if i.inst_opcode <> PHI then i
              else subst_label_inst next_lbl lbl i)
     orig_bb.bb_instructions` by
    (`ALL_DISTINCT (MAP (\b. b.bb_label)
       (update_succ_phi_labels next_lbl lbl mid (bb_succs next_bb)))` by
      metis_tac[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels] >>
     `lookup_block bb'.bb_label
       (update_succ_phi_labels next_lbl lbl mid (bb_succs next_bb)) =
      SOME bb'` by
      metis_tac[venomExecPropsTheory.MEM_lookup_block] >>
     gvs[]) >>
  (* Step F: inst is substituted → contradiction *)
  gvs[listTheory.MEM_MAP] >>
  Cases_on `i.inst_opcode <> PHI` >> gvs[MEM_Label_subst_label_inst_iff]
QED

Finalise no_Label_next_lbl_merge_step;

(* pred_labels through remove_block: precise iff *)
Triviality pred_labels_remove_block_iff[local]:
  !func lbl lbl' x.
    MEM lbl' (pred_labels (func with fn_blocks :=
      remove_block lbl func.fn_blocks) x) <=>
    MEM lbl' (pred_labels func x) /\ lbl' <> lbl
Proof
  rw[pred_labels_def, block_preds_def,
     cfgTransformTheory.remove_block_def,
     listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

(* Self-merge: no remaining PHI references lbl.
   Because bb_succs bb = [lbl], so lbl is a pred only of blocks
   with label lbl; but those were removed. *)
Triviality self_merge_no_phi_ref[local]:
  !func lbl bb b inst.
    wf_function func /\ fn_phi_preds_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    can_merge_blocks func bb bb /\
    MEM b func.fn_blocks /\ b.bb_label <> lbl /\
    MEM inst b.bb_instructions /\ inst.inst_opcode = PHI ==>
    ~MEM (Label lbl) inst.inst_operands
Proof
  rpt strip_tac >>
  `MEM lbl (pred_labels func b.bb_label)` by (
    fs[fn_phi_preds_wf_def] >> metis_tac[]) >>
  fs[pred_labels_MEM] >>
  rename1 `MEM wit func.fn_blocks` >>
  `MEM bb func.fn_blocks` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `bb.bb_label = lbl` by
    metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `wit = bb` by
    metis_tac[simplifyCfgCollapseBaseTheory.wf_blocks_unique] >>
  gvs[can_merge_blocks_def]
QED

(* In self-merge (lbl = next_lbl), the merge_step output simplifies to
   remove_block lbl func.fn_blocks. *)
Triviality merge_step_self_merge[local]:
  !func lbl bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb ==>
    update_succ_phi_labels lbl lbl
      (replace_block lbl (merge_blocks bb bb)
         (remove_block lbl func.fn_blocks))
      (bb_succs (merge_blocks bb bb)) =
    remove_block lbl func.fn_blocks
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `~MEM lbl (MAP (\b. b.bb_label) (remove_block lbl func.fn_blocks))` by
    simp[cfgTransformPropsTheory.fn_labels_remove_block,
         listTheory.MEM_FILTER] >>
  `replace_block lbl (merge_blocks bb bb)
     (remove_block lbl func.fn_blocks) =
   remove_block lbl func.fn_blocks` by
    (rw[cfgTransformTheory.replace_block_def] >>
     irule simplifyCfgCollapseBaseTheory.MAP_ID_ON >> rw[] >>
     rpt strip_tac >> fs[listTheory.MEM_MAP] >>
     first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label)
     (remove_block lbl func.fn_blocks))` by
    (simp[cfgTransformPropsTheory.fn_labels_remove_block] >>
     irule listTheory.FILTER_ALL_DISTINCT >> simp[]) >>
  simp[update_succ_phi_labels_same]
QED

(* fn_phi_preds_wf through merge_step *)
Triviality fn_phi_preds_wf_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    fn_phi_preds_wf func /\ fn_phi_even func /\ fn_phi_labels_wf func /\
    wf_function func /\ fn_inst_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    fn_phi_preds_wf (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `lbl = next_lbl`
  >- ((* self-merge: lbl = next_lbl, so bb = next_bb *)
      gvs[] >>
      drule_all merge_step_self_merge >> disch_then (fn th => simp[th]) >>
      simp[fn_phi_preds_wf_def, cfgTransformTheory.remove_block_def,
           listTheory.MEM_FILTER] >>
      rpt strip_tac >>
      (* Show MEM lbl' (pred_labels func' bb'.label) via remove_block_iff *)
      simp[GSYM cfgTransformTheory.remove_block_def,
           pred_labels_remove_block_iff] >>
      (* lbl' ≠ lbl from self_merge_no_phi_ref + fn_phi_preds_wf *)
      conj_tac
      >- (qpat_x_assum `fn_phi_preds_wf _`
            (mp_tac o REWRITE_RULE [fn_phi_preds_wf_def]) >>
          disch_then drule_all >> simp[])
      >> spose_not_then assume_tac >> gvs[] >>
         metis_tac[self_merge_no_phi_ref])
  >> (* Establish hybrid Q + ALL_DISTINCT BEFORE expanding fn_phi_preds_wf *)
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    (fs[wf_function_def, fn_labels_def]) >>
  `!bb1 inst1. MEM bb1 (update_succ_phi_labels next_lbl lbl
       (replace_block lbl (merge_blocks bb next_bb)
          (remove_block next_lbl func.fn_blocks))
       (bb_succs (merge_blocks bb next_bb))) /\
       MEM inst1 bb1.bb_instructions /\ inst1.inst_opcode = PHI ==>
       !l. MEM (Label l) inst1.inst_operands ==>
           MEM l (pred_labels func bb1.bb_label) \/
           (l = lbl /\ MEM bb1.bb_label (bb_succs next_bb))` by
    suspend "hybQ" >>
  simp[fn_phi_preds_wf_def] >> rpt gen_tac >> strip_tac >>
  suspend "main"
QED

Resume fn_phi_preds_wf_merge_step[hybQ]:
  match_mp_tac phi_labels_hybrid_Q_merge_step >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume fn_phi_preds_wf_merge_step[main]:
  drule_all no_next_lbl_in_merge_step >> strip_tac >>
  qspecl_then [`func`,`lbl`,`next_lbl`,`bb`,`next_bb`,`lbl'`,`bb'.bb_label`]
    mp_tac pred_labels_merge_step >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn th => rewrite_tac[th]) >>
  (* Apply hybrid Q to bb', inst, lbl' *)
  first_x_assum (qspecl_then [`bb'`, `inst`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspec_then `lbl'` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac
  (* Case 1 (first subgoal): MEM lbl' (pred_labels func bb'.bb_label) *)
  >- suspend "case_pred"
  (* Case 2 (second subgoal): lbl' = lbl ∧ MEM bb'.bb_label (bb_succs next_bb) *)
  >> (disj1_tac >> conj_tac >> first_assum ACCEPT_TAC)
QED

Resume fn_phi_preds_wf_merge_step[case_pred]:
  disj2_tac >> rpt conj_tac
  >- suspend "neq_next_lbl"
  >- suspend "neq_lbl"
  >> first_assum ACCEPT_TAC
QED

Resume fn_phi_preds_wf_merge_step[neq_next_lbl]:
  (* lbl' ≠ next_lbl: contradiction via no_Label_next_lbl_merge_step *)
  CCONTR_TAC >> gvs[] >>
  drule_all pred_labels_lookup_succs >> strip_tac >>
  imp_res_tac no_Label_next_lbl_merge_step
QED

Resume fn_phi_preds_wf_merge_step[neq_lbl]:
  (* lbl' ≠ lbl: bb_succs bb = [next_lbl] so bb'.label = next_lbl,
     but bb'.label ≠ next_lbl from assumption — contradiction *)
  CCONTR_TAC >> gvs[] >>
  drule_all pred_labels_lookup_succs >> strip_tac >>
  gvs[can_merge_blocks_def, single_succ_jmp_def] >>
  metis_tac[venomExecProofsTheory.lookup_block_label]
QED

Finalise fn_phi_preds_wf_merge_step;

(* Helper: PHI instruction in mid-layer block → find original block in func *)
Triviality mid_layer_phi_in_func[local]:
  !func lbl next_lbl bb next_bb bb0 inst0.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    MEM bb0 (replace_block lbl (merge_blocks bb next_bb)
               (remove_block next_lbl func.fn_blocks)) /\
    MEM inst0 bb0.bb_instructions /\ inst0.inst_opcode = PHI ==>
    ?bb_f. MEM bb_f func.fn_blocks /\ MEM inst0 bb_f.bb_instructions /\
           bb_f.bb_label = bb0.bb_label
Proof
  rpt strip_tac >>
  gvs[MEM_replace_block_cases, cfgTransformProofsTheory.MEM_remove_block_iff]
  >- (
    (* bb0 = merge_blocks bb next_bb: PHIs come from bb (next_bb has no_phis) *)
    qexists `bb` >>
    imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
    imp_res_tac venomExecProofsTheory.lookup_block_label >> gvs[] >>
    gvs[merge_blocks_def, listTheory.MEM_APPEND,
        can_merge_blocks_def, no_phis_def, listTheory.EVERY_MEM] >>
    Cases_on `bb.bb_instructions` >> gvs[] >>
    imp_res_tac rich_listTheory.MEM_FRONT >> gvs[listTheory.MEM])
  >> (qexists `bb0` >> simp[])
QED

(* fn_phi_preds_complete through merge_step *)
Triviality fn_phi_preds_complete_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    fn_phi_preds_complete func /\ fn_phi_preds_wf func /\
    fn_phi_even func /\ fn_phi_labels_wf func /\
    wf_function func /\ fn_inst_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    fn_phi_preds_complete (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `lbl = next_lbl`
  >- (
    (* Self-merge: func' = remove_block lbl func *)
    gvs[] >>
    drule_all merge_step_self_merge >> disch_then (fn th => simp[th]) >>
    simp[fn_phi_preds_complete_def, cfgTransformTheory.remove_block_def,
         listTheory.MEM_FILTER] >>
    rpt strip_tac >>
    (* Fold FILTER back to remove_block, then apply iff *)
    qpat_x_assum `MEM lbl' (pred_labels _ _)` mp_tac >>
    simp[GSYM cfgTransformTheory.remove_block_def,
         pred_labels_remove_block_iff] >>
    strip_tac >>
    qpat_x_assum `fn_phi_preds_complete _`
      (mp_tac o REWRITE_RULE [fn_phi_preds_complete_def]) >>
    disch_then drule_all >> simp[])
  >> (simp[fn_phi_preds_complete_def] >> rpt gen_tac >> strip_tac >>
      suspend "preds_complete_main")
QED

Resume fn_phi_preds_complete_merge_step[preds_complete_main]:
  (* Main case: lbl ≠ next_lbl.
     Given: MEM bb' func'.fn_blocks, MEM inst bb'.bb_instructions,
            inst.opcode = PHI, MEM lbl' (pred_labels func' bb'.label)
     Show: MEM (Label lbl') inst.inst_operands

     Strategy:
       1. ALL_DISTINCT + uspl_phi_inst_inverse → get bb0, inst0, in_succ
       2. pred_labels_merge_step → case-split on lbl'
       3. fn_phi_preds_complete on func + MEM_Label_subst_label_inst_iff *)
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  (* ALL_DISTINCT for mid-layer *)
  `ALL_DISTINCT (MAP (\b. b.bb_label)
     (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks)))` by (
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
    simp[cfgTransformProofsTheory.ALL_DISTINCT_remove_block] >>
    imp_res_tac venomExecProofsTheory.lookup_block_label >>
    simp[merge_blocks_def]) >>
  (* Step 1: uspl_phi_inst_inverse *)
  drule_all uspl_phi_inst_inverse >> strip_tac >>
  (* Step 2: pred_labels case-split *)
  qspecl_then [`func`,`lbl`,`next_lbl`,`bb`,`next_bb`,`lbl'`,`bb'.bb_label`]
    mp_tac pred_labels_merge_step >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> gvs[]
  >- suspend "case_lbl_eq_lbl"
  >> suspend "case_lbl_ordinary"
QED

Resume fn_phi_preds_complete_merge_step[case_lbl_eq_lbl]:
  (* lbl' = lbl ∧ MEM bb'.bb_label (bb_succs next_bb).
     Need: MEM (Label lbl) inst.inst_operands.
     Use uspl_phi_in_succ_subst directly (no in_succ case split needed):
     bb'.label ∈ bb_succs next_bb = succs list of uspl, so inst = subst(inst0'). *)
  `bb_succs (merge_blocks bb next_bb) = bb_succs next_bb` by (
    irule bb_succs_merge_blocks >>
    imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
    qpat_x_assum `wf_function _` mp_tac >>
    simp[wf_function_def] >> strip_tac >> res_tac) >>
  (* uspl_phi_in_succ_subst gives inst = subst_label_inst next_lbl lbl inst0' *)
  `?bb0' inst0'. MEM bb0' (replace_block lbl (merge_blocks bb next_bb)
       (remove_block next_lbl func.fn_blocks)) /\
     MEM inst0' bb0'.bb_instructions /\ inst0'.inst_opcode = PHI /\
     bb0'.bb_label = bb'.bb_label /\
     inst = subst_label_inst next_lbl lbl inst0'` by (
    qpat_x_assum `MEM bb'.bb_label (bb_succs next_bb)` mp_tac >>
    qpat_x_assum `bb_succs _ = _` (fn th => rewrite_tac [GSYM th]) >>
    strip_tac >>
    drule_all uspl_phi_in_succ_subst >> simp[]) >>
  simp[MEM_Label_subst_label_inst_iff] >> DISJ2_TAC >>
  (* next_lbl ∈ pred_labels func bb0'.bb_label *)
  `MEM next_lbl (pred_labels func bb0'.bb_label)` by (
    simp[pred_labels_MEM] >>
    qexists `next_bb` >> simp[] >>
    imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
    imp_res_tac venomExecProofsTheory.lookup_block_label >> simp[]) >>
  (* Find bb_f in func with inst0' via mid_layer_phi_in_func *)
  `?bb_f. MEM bb_f func.fn_blocks /\ MEM inst0' bb_f.bb_instructions /\
          bb_f.bb_label = bb0'.bb_label` by (
    qspecl_then [`func`,`lbl`,`next_lbl`,`bb`,`next_bb`,`bb0'`,`inst0'`]
      mp_tac mid_layer_phi_in_func >> simp[]) >>
  (* fn_phi_preds_complete gives MEM (Label next_lbl) inst0'.ops *)
  qpat_x_assum `fn_phi_preds_complete _`
    (mp_tac o REWRITE_RULE [fn_phi_preds_complete_def]) >>
  disch_then (qspecl_then [`bb_f`, `inst0'`, `next_lbl`] mp_tac) >>
  (impl_tac >- gvs[]) >> simp[]
QED

Resume fn_phi_preds_complete_merge_step[case_lbl_ordinary]:
  (* lbl' ≠ next_lbl ∧ lbl' ≠ lbl ∧ MEM lbl' (pred_labels func bb'.bb_label).
     Reduce to: MEM (Label lbl') inst0.inst_operands (via subst if in_succ). *)
  (* Step 1: Suffices to show MEM (Label lbl') inst0.inst_operands *)
  `MEM (Label lbl') inst0.inst_operands ==> MEM (Label lbl') inst.inst_operands`
    by (Cases_on `in_succ` >> gvs[] >>
        simp[MEM_Label_subst_label_inst_iff]) >>
  (* Step 2: bb0 in mid-layer → original block in func via mid_layer_phi_in_func *)
  `?bb_f. MEM bb_f func.fn_blocks /\ MEM inst0 bb_f.bb_instructions /\
          bb_f.bb_label = bb0.bb_label` by (
    qspecl_then [`func`,`lbl`,`next_lbl`,`bb`,`next_bb`,`bb0`,`inst0`]
      mp_tac mid_layer_phi_in_func >> simp[]) >>
  (* Step 3: Apply fn_phi_preds_complete to get MEM (Label lbl') inst0.ops *)
  first_x_assum match_mp_tac >>
  qpat_x_assum `fn_phi_preds_complete _`
    (mp_tac o REWRITE_RULE [fn_phi_preds_complete_def]) >>
  disch_then (qspecl_then [`bb_f`, `inst0`, `lbl'`] mp_tac) >>
  simp[]
QED

Finalise fn_phi_preds_complete_merge_step;

(* Helper: Label lbl doesn't appear in PHIs of blocks other than next_lbl,
   because can_merge_blocks means bb_succs bb = [next_lbl] so lbl only
   appears as a predecessor of next_lbl. *)
Triviality phi_no_Label_lbl_other_block[local]:
  !func lbl next_lbl bb next_bb bb_f inst0.
    fn_phi_preds_wf func /\ wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    MEM bb_f func.fn_blocks /\
    MEM inst0 bb_f.bb_instructions /\
    inst0.inst_opcode = PHI /\
    bb_f.bb_label <> next_lbl ==>
    ~MEM (Label lbl) inst0.inst_operands
Proof
  rpt strip_tac >>
  CCONTR_TAC >> fs[] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  (* fn_phi_preds_wf: Label lbl in PHI of bb_f → lbl is a pred of bb_f *)
  qpat_x_assum `fn_phi_preds_wf _`
    (mp_tac o REWRITE_RULE [fn_phi_preds_wf_def]) >>
  disch_then (qspecl_then [`bb_f`, `inst0`, `lbl`] mp_tac) >>
  simp[] >> strip_tac >>
  (* pred_labels_lookup_succs: → bb_f.label ∈ bb_succs bb *)
  drule_all pred_labels_lookup_succs >> strip_tac >>
  (* can_merge_blocks: bb_succs bb = [next_bb.bb_label] *)
  `bb_succs bb = [next_bb.bb_label]` by
    fs[can_merge_blocks_def] >>
  (* So bb_f.bb_label = next_bb.bb_label = next_lbl *)
  `next_bb.bb_label = next_lbl` by
    metis_tac[venomExecProofsTheory.lookup_block_label] >>
  fs[]
QED

(* fn_phi_resolve_complete through merge_step *)
Triviality fn_phi_resolve_complete_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    fn_phi_resolve_complete func /\ fn_phi_preds_wf func /\
    fn_phi_preds_complete func /\ fn_phi_even func /\
    fn_phi_labels_wf func /\
    wf_function func /\ fn_inst_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    fn_phi_resolve_complete (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `lbl = next_lbl`
  >- (
    (* Self-merge: func' = remove_block lbl func *)
    gvs[] >>
    drule_all merge_step_self_merge >> disch_then (fn th => simp[th]) >>
    simp[fn_phi_resolve_complete_def, cfgTransformTheory.remove_block_def,
         listTheory.MEM_FILTER] >>
    rpt strip_tac >>
    qpat_x_assum `MEM lbl' (pred_labels _ _)` mp_tac >>
    simp[GSYM cfgTransformTheory.remove_block_def,
         pred_labels_remove_block_iff] >>
    strip_tac >>
    qpat_x_assum `fn_phi_resolve_complete _`
      (mp_tac o REWRITE_RULE [fn_phi_resolve_complete_def]) >>
    disch_then drule_all >> simp[])
  >> (simp[fn_phi_resolve_complete_def] >> rpt gen_tac >> strip_tac >>
      suspend "resolve_complete_main")
QED

Resume fn_phi_resolve_complete_merge_step[resolve_complete_main]:
  (* Parallel to preds_complete_main.
     Given: MEM bb' func'.fn_blocks, MEM inst bb'.bb_instructions,
            inst.opcode = PHI, MEM lbl' (pred_labels func' bb'.label)
     Show: ∃v. resolve_phi lbl' inst.inst_operands = SOME v *)
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label)
     (replace_block lbl (merge_blocks bb next_bb)
        (remove_block next_lbl func.fn_blocks)))` by (
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
    simp[cfgTransformProofsTheory.ALL_DISTINCT_remove_block] >>
    imp_res_tac venomExecProofsTheory.lookup_block_label >>
    simp[merge_blocks_def]) >>
  drule_all uspl_phi_inst_inverse >> strip_tac >>
  qspecl_then [`func`,`lbl`,`next_lbl`,`bb`,`next_bb`,`lbl'`,`bb'.bb_label`]
    mp_tac pred_labels_merge_step >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> gvs[]
  >- suspend "rc_case_lbl_eq_lbl"
  >> suspend "rc_case_lbl_ordinary"
QED

Resume fn_phi_resolve_complete_merge_step[rc_case_lbl_eq_lbl]:
  (* case lbl' = lbl: use resolve_phi_subst_label *)
  `bb_succs (merge_blocks bb next_bb) = bb_succs next_bb` by (
    irule bb_succs_merge_blocks >>
    imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
    qpat_x_assum `wf_function _` mp_tac >>
    simp[wf_function_def] >> strip_tac >> res_tac) >>
  `?bb0' inst0'. MEM bb0' (replace_block lbl (merge_blocks bb next_bb)
       (remove_block next_lbl func.fn_blocks)) /\
     MEM inst0' bb0'.bb_instructions /\ inst0'.inst_opcode = PHI /\
     bb0'.bb_label = bb'.bb_label /\
     inst = subst_label_inst next_lbl lbl inst0'` by (
    qpat_x_assum `MEM bb'.bb_label (bb_succs next_bb)` mp_tac >>
    qpat_x_assum `bb_succs _ = _` (fn th => rewrite_tac [GSYM th]) >>
    strip_tac >>
    drule_all uspl_phi_in_succ_subst >> simp[]) >>
  simp[cfgTransformTheory.subst_label_inst_def] >>
  (* Find bb_f in func *)
  `?bb_f. MEM bb_f func.fn_blocks /\ MEM inst0' bb_f.bb_instructions /\
          bb_f.bb_label = bb0'.bb_label` by (
    qspecl_then [`func`,`lbl`,`next_lbl`,`bb`,`next_bb`,`bb0'`,`inst0'`]
      mp_tac mid_layer_phi_in_func >> simp[]) >>
  (* bb_f.bb_label ≠ next_lbl *)
  `bb_f.bb_label <> next_lbl` by (
    gvs[] >> CCONTR_TAC >> gvs[] >>
    qpat_x_assum `MEM bb0' (replace_block _ _ _)` mp_tac >>
    simp[MEM_replace_block_cases,
         cfgTransformProofsTheory.MEM_remove_block_iff] >>
    strip_tac >> gvs[] >>
    imp_res_tac venomExecProofsTheory.lookup_block_label >>
    gvs[merge_blocks_def]) >>
  (* ¬MEM (Label lbl) inst0'.ops *)
  `~MEM (Label lbl) inst0'.inst_operands` by (
    qspecl_then [`func`,`lbl`,`next_lbl`,`bb`,`next_bb`,`bb_f`,`inst0'`]
      mp_tac phi_no_Label_lbl_other_block >> simp[]) >>
  simp[cfgTransformPropsTheory.resolve_phi_subst_label] >>
  `MEM next_lbl (pred_labels func bb0'.bb_label)` by (
    simp[pred_labels_MEM] >>
    qexists `next_bb` >> simp[] >>
    imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
    imp_res_tac venomExecProofsTheory.lookup_block_label >> simp[]) >>
  qpat_x_assum `fn_phi_resolve_complete _`
    (mp_tac o REWRITE_RULE [fn_phi_resolve_complete_def]) >>
  disch_then (qspecl_then [`bb_f`, `inst0'`, `next_lbl`] mp_tac) >>
  (impl_tac >- gvs[]) >>
  strip_tac >> simp[]
QED

Resume fn_phi_resolve_complete_merge_step[rc_case_lbl_ordinary]:
  (* case lbl' ordinary: lbl' ≠ next_lbl ∧ lbl' ≠ lbl *)
  `?bb_f. MEM bb_f func.fn_blocks /\ MEM inst0 bb_f.bb_instructions /\
          bb_f.bb_label = bb0.bb_label` by (
    qspecl_then [`func`,`lbl`,`next_lbl`,`bb`,`next_bb`,`bb0`,`inst0`]
      mp_tac mid_layer_phi_in_func >> simp[]) >>
  (* Both cases: resolve_phi lbl' inst0.operands exists via fn_phi_resolve_complete *)
  `?v. resolve_phi lbl' inst0.inst_operands = SOME v` by (
    qpat_x_assum `fn_phi_resolve_complete _`
      (mp_tac o REWRITE_RULE [fn_phi_resolve_complete_def]) >>
    disch_then (qspecl_then [`bb_f`, `inst0`, `lbl'`] mp_tac) >>
    (impl_tac >- gvs[]) >> simp[]) >>
  Cases_on `in_succ` >> gvs[] >>
  (* in_succ=T: inst = subst(inst0), resolve_phi_subst_other handles it *)
  simp[cfgTransformTheory.subst_label_inst_def,
       cfgTransformPropsTheory.resolve_phi_subst_other]
QED

Finalise fn_phi_resolve_complete_merge_step;

Triviality collapse_wf_merge_step[local]:
  !func lbl next_lbl bb next_bb.
    collapse_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    collapse_wf (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rw[collapse_wf_def] >> rpt conj_tac
  (* wf_function *)
  >- (irule simplifyCfgWfTheory.wf_function_merge_step >> metis_tac[])
  (* fn_inst_wf *)
  >- (irule simplifyCfgHelpersTheory.fn_inst_wf_merge_step >> metis_tac[])
  (* fn_phi_preds_wf *)
  >- (irule fn_phi_preds_wf_merge_step >> metis_tac[])
  (* fn_phi_preds_complete *)
  >- (irule fn_phi_preds_complete_merge_step >> metis_tac[])
  (* fn_phi_resolve_complete *)
  >- (irule fn_phi_resolve_complete_merge_step >> metis_tac[])
  (* fn_bypass_safe *)
  >- (irule fn_bypass_safe_merge_step >> metis_tac[])
  (* fn_phi_even *)
  >- (irule fn_phi_even_merge_step >> metis_tac[])
  (* fn_phi_labels_wf *)
  >> (irule fn_phi_labels_wf_merge_step >> metis_tac[])
QED

Triviality collapse_wf_do_merge_jump[local]:
  !func a b label_map func' lm'.
    collapse_wf func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    can_bypass_jump func a b /\
    ~MEM (HD (bb_succs b)) (bb_succs a) /\ a.bb_label <> HD (bb_succs b) /\
    do_merge_jump func a b label_map = SOME (func', lm') ==>
    collapse_wf func'
Proof
  rw[collapse_wf_def] >> rpt conj_tac
  (* wf_function *)
  >- (irule simplifyCfgWfTheory.wf_function_do_merge_jump >>
      metis_tac[can_bypass_jump_def])
  (* fn_inst_wf *)
  >- (irule simplifyCfgHelpersTheory.fn_inst_wf_do_merge_jump >>
      metis_tac[])
  (* fn_phi_preds_wf *)
  >- (irule fn_phi_preds_wf_do_merge_jump >> metis_tac[])
  (* fn_phi_preds_complete *)
  >- (irule fn_phi_preds_complete_do_merge_jump >> metis_tac[])
  (* fn_phi_resolve_complete *)
  >- (irule fn_phi_resolve_complete_do_merge_jump >> metis_tac[])
  (* fn_bypass_safe *)
  >- (irule fn_bypass_safe_do_merge_jump >> metis_tac[])
  (* fn_phi_even *)
  >- (irule fn_phi_even_do_merge_jump >> metis_tac[])
  (* fn_phi_labels_wf *)
  >> (irule fn_phi_labels_wf_do_merge_jump >> metis_tac[])
QED

Triviality collapse_wf_try_bypass[local]:
  !func label_map bb succs func' lm' flag.
    collapse_wf func /\
    MEM bb func.fn_blocks /\
    try_bypass func label_map bb succs = (func', lm', flag) ==>
    collapse_wf func'
Proof
  ntac 3 gen_tac >> Induct_on `succs` >>
  rw[try_bypass_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  irule collapse_wf_do_merge_jump >> metis_tac[]
QED

Theorem collapse_wf_collapse_dfs:
  !func label_map visited wl func' lm' vis'.
    collapse_dfs func label_map visited wl = (func', lm', vis') /\
    collapse_wf func ==>
    collapse_wf func'
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (ISPEC ``collapse_wf`` simplifyCfgHelpersTheory.collapse_dfs_preserves) >>
  (impl_tac >- (
    rpt conj_tac
    >- (rpt strip_tac >> irule collapse_wf_merge_step >> metis_tac[])
    >> rpt strip_tac >> irule collapse_wf_try_bypass >> metis_tac[])) >>
  disch_then (qspecl_then [`func`, `label_map`, `visited`, `wl`,
                            `func'`, `lm'`, `vis'`] mp_tac) >>
  simp[]
QED

(* ================================================================
   Section 4: collapse_dfs preserves semantics (induction)
   ================================================================ *)

(* Inner lemma: unreachable block removal under invariant vs_current_bb ≠ lbl.
   Strengthened for induction — only requires vs_current_bb ≠ lbl,
   not the entry/prev_bb conditions needed by the caller. *)
Triviality self_merge_inner[local]:
  !fuel func lbl bb ctx s.
    wf_function func /\ fn_inst_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    num_preds func lbl = 1 /\ MEM lbl (bb_succs bb) /\
    s.vs_current_bb <> lbl /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    result_equiv {}
      (run_blocks fuel ctx func s)
      (run_blocks fuel ctx
        (func with fn_blocks := remove_block lbl func.fn_blocks) s)
Proof
  Induct_on `fuel`
  (* fuel = 0 *)
  >- (once_rewrite_tac[run_blocks_def] >> simp[result_equiv_def, GSYM run_block_def])
  >> rpt strip_tac >>
  once_rewrite_tac[run_blocks_def] >> simp[GSYM run_block_def] >>
  (* lookup current block — same in both functions since vs_current_bb ≠ lbl *)
  simp[cfgTransformPropsTheory.lookup_block_remove_neq] >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks`
  >- simp[result_equiv_def]
  >> rename1 `SOME cur_bb` >> simp[] >>
  (* run_block gives same result (same block, same state) *)
  Cases_on `run_block fuel ctx cur_bb s` >>
  simp[result_equiv_def, state_equiv_refl, execution_equiv_refl]
  (* OK s' — only remaining case after simp closes non-OK *)
  >> rename1 `OK s'` >>
  `s'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
  `~s'.vs_halted` by metis_tac[run_block_OK_not_halted] >>
  simp[] >>
  (* Show s'.vs_current_bb ≠ lbl *)
  `MEM cur_bb func.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `cur_bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `bb_well_formed cur_bb` by (fs[wf_function_def] >> res_tac) >>
  `EVERY inst_wf cur_bb.bb_instructions` by
    (fs[fn_inst_wf_def] >> rw[listTheory.EVERY_MEM] >> res_tac) >>
  `MEM s'.vs_current_bb (bb_succs cur_bb)` by
    metis_tac[run_block_current_bb_in_succs_wf] >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  (* cur_bb ≠ bb since cur_bb.bb_label = s.vs_current_bb ≠ lbl = bb.bb_label *)
  `cur_bb <> bb` by (strip_tac >> gvs[]) >>
  `~MEM lbl (bb_succs cur_bb)` by
    (strip_tac >>
     `cur_bb = bb` by metis_tac[num_preds_1_unique_pred, lookup_block_MEM] >>
     gvs[]) >>
  `s'.vs_current_bb <> lbl` by metis_tac[listTheory.MEM] >>
  first_x_assum (qspecl_then [`func`, `lbl`, `bb`, `ctx`, `s'`] mp_tac) >>
  simp[]
QED

(* Self-merge correctness: derived from inner lemma *)
Triviality self_merge_correct[local]:
  !func lbl bb fuel ctx s.
    wf_function func /\ fn_inst_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    can_merge_blocks func bb bb /\
    fn_entry_label func = SOME s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    ~s.vs_halted ==>
    result_equiv {}
      (run_blocks fuel ctx func s)
      (run_blocks fuel ctx
        (func with fn_blocks := remove_block lbl func.fn_blocks) s)
Proof
  rpt strip_tac >>
  irule self_merge_inner >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  fs[can_merge_blocks_def]
QED

Triviality fn_entry_label_HD[local]:
  !func. func.fn_blocks <> [] ==>
  fn_entry_label func = SOME (HD func.fn_blocks).bb_label
Proof
  rpt strip_tac >>
  Cases_on `func.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]
QED

(* fn_entry_label only depends on fn_blocks *)
Triviality fn_entry_label_fn_blocks[local]:
  fn_entry_label (func with fn_blocks := bbs) =
  fn_entry_label <|fn_blocks := bbs|>
Proof
  simp[fn_entry_label_def, entry_block_def]
QED

(* Combined: fn_entry_label preserved through full merge_step *)
Triviality fn_entry_label_merge_step_full[local]:
  !func lbl next_lbl merged succs.
    func.fn_blocks <> [] /\
    (HD func.fn_blocks).bb_label <> next_lbl /\
    merged.bb_label = lbl ==>
    fn_entry_label
      (func with fn_blocks :=
        update_succ_phi_labels next_lbl lbl
          (replace_block lbl merged
             (remove_block next_lbl func.fn_blocks))
          succs) =
    fn_entry_label func
Proof
  rpt strip_tac >>
  once_rewrite_tac[fn_entry_label_fn_blocks] >>
  rewrite_tac[fn_entry_label_update_succ_phi_labels] >>
  once_rewrite_tac[GSYM fn_entry_label_fn_blocks] >>
  irule (REWRITE_RULE [AND_IMP_INTRO] fn_entry_label_merge_step) >>
  simp[]
QED

(*
 * collapse_dfs_correct: induction over collapse_dfs.
 *
 * Strategy: once_rewrite_tac to unfold without consuming IH.
 * Trivial cases (func unchanged): disch_tac >> res_tac >> metis_tac[].
 * Merge case: apply IH (explicit SPECL), then merge_step_correct or
 *   self_merge_correct, compose via result_equiv_empty_trans.
 * Bypass case: apply IH, then try_bypass_correct, compose.
 *)
Theorem collapse_dfs_correct[local]:
  !func label_map visited wl func' lm' vis' fuel ctx s.
    collapse_dfs func label_map visited wl = (func', lm', vis') /\
    collapse_wf func /\
    fn_entry_label func = SOME s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    ~s.vs_halted ==>
    ?fuel'. fuel <= fuel' /\
      result_equiv {}
        (run_blocks fuel' ctx func s)
        (run_blocks fuel ctx func' s)
Proof
  recInduct collapse_dfs_ind >>
  conj_tac
  (* Base case: empty worklist *)
  >- (
    rw[Once collapse_dfs_def] >>
    qexists `fuel` >> simp[] >> irule result_equiv_empty_refl
  )
  >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `collapse_dfs _ _ _ _ = _` mp_tac >>
  (* Use once_rewrite_tac to avoid IH consumption by simp *)
  once_rewrite_tac[collapse_dfs_def] >>
  (* Case: MEM lbl visited *)
  IF_CASES_TAC >- (disch_tac >> res_tac >> metis_tac[]) >>
  (* Case: lookup_block lbl *)
  Cases_on `lookup_block lbl func.fn_blocks`
  >- (simp[] >> disch_tac >> res_tac >> metis_tac[]) >>
  rename1 `SOME bb` >> simp[] >>
  `func.fn_blocks <> []` by
    (imp_res_tac lookup_block_MEM >> Cases_on `func.fn_blocks` >> fs[]) >>
  Cases_on `bb_succs bb`
  (* Zero succs *)
  >- (simp[LET_THM, try_bypass_def] >> disch_tac >> res_tac >> metis_tac[])
  >> rename1 `h::t` >> Cases_on `t`
  (* ===== Single successor: [h] ===== *)
  >- (
    simp[] >>
    Cases_on `lookup_block h func.fn_blocks`
    >- (simp[] >> disch_tac >> res_tac >> metis_tac[]) >>
    rename1 `SOME next_bb` >> simp[] >>
    IF_CASES_TAC
    (* --- can_merge_blocks: the interesting case --- *)
    >- (
      pure_rewrite_tac[LET_THM] >> BETA_TAC >>
      strip_tac >>
      (* Abbreviate the merged function *)
      qmatch_asmsub_abbrev_tac `collapse_dfs func_mid _ _ _` >>
      (* Entry label ≠ next_bb.bb_label *)
      `fn_entry_label func <> SOME h` by (
        `next_bb.bb_label = h` by
          (imp_res_tac lookup_block_label >> simp[]) >>
        qpat_x_assum `can_merge_blocks _ _ _` mp_tac >>
        simp[can_merge_blocks_def]) >>
      `(HD func.fn_blocks).bb_label <> h` by
        metis_tac[fn_entry_label_HD] >>
      (* fn_entry_label preserved through merge *)
      `fn_entry_label func_mid = fn_entry_label func` by (
        qunabbrev_tac `func_mid` >>
        irule fn_entry_label_merge_step_full >>
        imp_res_tac lookup_block_label >> simp[merge_blocks_def]) >>
      (* collapse_wf preserved *)
      `collapse_wf func_mid` by (
        qunabbrev_tac `func_mid` >>
        irule collapse_wf_merge_step >> metis_tac[]) >>
      (* Apply IH for merge case *)
      qpat_x_assum
        `!bb' next_lbl v3 next_bb' merged bbs' bbs'' funcx lmx.
         _ /\ _ /\ _ /\ _ /\ _ /\ can_merge_blocks _ _ _ /\ _ ==> _`
        (mp_tac o Q.SPECL [`bb`, `h`, `[]`, `next_bb`,
          `merge_blocks bb next_bb`,
          `replace_block lbl (merge_blocks bb next_bb)
             (remove_block h func.fn_blocks)`,
          `update_succ_phi_labels h lbl
             (replace_block lbl (merge_blocks bb next_bb)
                (remove_block h func.fn_blocks))
             (bb_succs (merge_blocks bb next_bb))`,
          `func_mid`,
          `(next_bb.bb_label,lbl)::label_map`]) >>
      (impl_tac >- (qunabbrev_tac `func_mid` >> simp[])) >>
      disch_then (qspecl_then [`func'`, `lm'`, `vis'`, `fuel`, `ctx`, `s`]
        mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qx_choose_then `fuel2` strip_assume_tac) >>
      KILL_FORALLS >>
      (* Single-step: func → func_mid *)
      Cases_on `lbl = h`
      >- (
        (* Self-merge: lbl = h, so bb = next_bb.
           Use SUBST_ALL_TAC to replace h→lbl everywhere, keeping Abbr consistent *)
        pop_assum (SUBST_ALL_TAC o GSYM) >>
        `next_bb = bb` by
          (qpat_assum `lookup_block lbl _ = SOME next_bb` mp_tac >>
           qpat_assum `lookup_block lbl _ = SOME bb` mp_tac >> simp[]) >>
        `wf_function func` by
          (qpat_assum `collapse_wf func` mp_tac >>
           rewrite_tac[collapse_wf_def] >> strip_tac >> simp[]) >>
        (* Show func_mid = remove_block result *)
        `func_mid = func with fn_blocks :=
           remove_block lbl func.fn_blocks` by (
          qunabbrev_tac `func_mid` >>
          gvs[venomInstTheory.ir_function_component_equality] >>
          mp_tac (Q.SPECL [`func`, `lbl`, `bb`]
            merge_step_self_merge) >>
          simp[]) >>
        (* self_merge_correct on func → func_mid *)
        mp_tac (Q.SPECL [`func`, `lbl`, `bb`, `fuel2`, `ctx`, `s`]
          self_merge_correct) >>
        (impl_tac >- (
          qpat_assum `collapse_wf func` mp_tac >>
          rewrite_tac[collapse_wf_def] >> strip_tac >>
          simp[] >> gvs[can_merge_blocks_def])) >>
        strip_tac >>
        qexists `fuel2` >> simp[] >>
        irule result_equiv_empty_trans >>
        qexists `run_blocks fuel2 ctx func_mid s` >>
        conj_tac
        >- (gvs[] >> first_assum ACCEPT_TAC)
        >> first_assum ACCEPT_TAC
      ) >>
      (* Normal merge: lbl ≠ h *)
      mp_tac merge_step_correct >>
      disch_then (qspecl_then [`func`, `lbl`, `h`, `bb`, `next_bb`]
        mp_tac) >>
      (impl_tac >- (
        qpat_assum `collapse_wf func` mp_tac >>
        rewrite_tac[collapse_wf_def] >> strip_tac >> simp[])) >>
      simp[LET_THM] >>
      disch_then (qspecl_then [`fuel2`, `ctx`, `s`] mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qx_choose_then `fuel1` strip_assume_tac) >>
      qexists `fuel1` >> conj_tac >- simp[] >>
      irule result_equiv_empty_trans >>
      qexists `run_blocks fuel2 ctx func_mid s` >>
      conj_tac
      >- (qunabbrev_tac `func_mid` >> first_assum ACCEPT_TAC)
      >> first_assum ACCEPT_TAC
    )
    (* --- ~can_merge_blocks: trivial --- *)
    >> (simp[] >> disch_tac >> res_tac >> metis_tac[])
  )
  (* ===== Multi-successor: h::h'::t' ===== *)
  >> (
    rename1 `h'::t'` >> simp[LET_THM] >>
    pairarg_tac >> simp[] >>
    IF_CASES_TAC
    (* try_bypass succeeded *)
    >- (
      pure_rewrite_tac[combinTheory.o_THM] >> strip_tac >>
      (* fn_entry_label preserved *)
      `fn_entry_label func'' = fn_entry_label func` by (
        mp_tac (Q.SPECL [`h::h'::t'`, `func`, `label_map`, `bb`,
          `func''`, `lm''`, `T`] fn_entry_label_try_bypass) >>
        impl_tac >- (
          simp[] >> rpt strip_tac >>
          qpat_x_assum `can_bypass_jump _ _ _` mp_tac >>
          rewrite_tac[can_bypass_jump_def] >> strip_tac >>
          metis_tac[fn_entry_label_HD]) >>
        simp[]) >>
      (* collapse_wf preserved *)
      `collapse_wf func''` by (
        mp_tac (Q.SPECL [`func`, `label_map`, `bb`, `h::h'::t'`,
          `func''`, `lm''`, `bypassed`] collapse_wf_try_bypass) >>
        simp[] >> metis_tac[lookup_block_MEM]) >>
      (* Apply IH for try_bypass case (bypassed=T).
         Kill the ¬bypassed IH first to avoid pattern ambiguity. *)
      qpat_x_assum
        `!bb' next_lbl v3 v6 v7 func'x lm'x bypassed'.
         _ /\ _ /\ _ /\ _ /\ _ /\ ~bypassed' ==> _` kall_tac >>
      qpat_x_assum
        `!bb' next_lbl v3 v6 v7 func'x lm'x bypassed'.
         _ /\ _ /\ _ /\ _ /\ (_, _, _) = try_bypass _ _ _ _ /\ _ ==> _`
        (mp_tac o Q.SPECL [`bb`, `h`, `h'::t'`, `h'`, `t'`,
          `func''`, `lm''`, `bypassed`]) >>
      (impl_tac >- simp[]) >>
      disch_then (qspecl_then [`func'`, `lm'`, `vis'`, `fuel`, `ctx`, `s`]
        mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qx_choose_then `fuel2` strip_assume_tac) >>
      KILL_FORALLS >>
      mp_tac try_bypass_correct >>
      disch_then (qspecl_then [`func`, `label_map`, `bb`, `h::h'::t'`,
        `func''`, `lm''`, `fuel2`, `ctx`, `s`] mp_tac) >>
      (impl_tac >- (
        qpat_assum `collapse_wf func` mp_tac >>
        rewrite_tac[collapse_wf_def] >> strip_tac >>
        simp[] >> metis_tac[lookup_block_MEM])) >>
      disch_then (qx_choose_then `fuel1` strip_assume_tac) >>
      qexists `fuel1` >> conj_tac >- simp[] >>
      irule result_equiv_empty_trans >>
      qexists `run_blocks fuel2 ctx func'' s` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      first_assum ACCEPT_TAC
    )
    (* try_bypass failed: func unchanged *)
    >> (
      simp[] >>
      imp_res_tac simplifyCfgDefsTheory.try_bypass_F_unchanged >> gvs[] >>
      disch_tac >> res_tac >> metis_tac[]
    )
  )
QED

(* ================================================================
   Section 5: Main theorem -- collapse_dfs_subst_correct
   ================================================================ *)

Theorem collapse_dfs_subst_correct:
  !func func2 (label_map:(string#string) list) vis entry fuel ctx s.
    collapse_wf func /\
    fn_entry_label func = SOME entry /\
    fn_entry_label func = SOME s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    ~s.vs_halted /\
    collapse_dfs func [] [] [entry] = (func2, label_map, vis) ==>
    ?fuel'. fuel <= fuel' /\ result_equiv {}
      (run_blocks fuel' ctx func s)
      (run_blocks fuel ctx
        (if label_map = [] then func2
         else subst_block_labels_fn label_map func2) s)
Proof
  rpt strip_tac >>
  Cases_on `label_map = []`
  >- (
    (* label_map = [] : direct from collapse_dfs_correct *)
    simp[] >>
    mp_tac collapse_dfs_correct >>
    disch_then (qspecl_then [`func`, `[]:(string#string) list`, `[]`, `[entry]`,
      `func2`, `[]:(string#string) list`, `vis`, `fuel`, `ctx`, `s`] mp_tac) >>
    simp[]
  ) >>
  (* label_map ≠ [] : show subst is identity *)
  (* Establish wf props of func2 *)
  `wf_function func` by fs[collapse_wf_def] >>
  `collapse_wf func2` by (
    mp_tac (Q.SPECL [`func`, `[]:(string#string) list`, `[]`, `[entry]`,
      `func2`, `label_map`, `vis`] collapse_wf_collapse_dfs) >>
    simp[]) >>
  `wf_function func2 /\ fn_phi_preds_wf func2` by fs[collapse_wf_def] >>
  `!old. MEM old (MAP FST label_map) ==> ~MEM old (fn_labels func2)` by (
    mp_tac lm_keys_not_in_fn_labels_collapse_dfs >>
    disch_then (qspecl_then [`func`, `[]:(string#string) list`, `[]`, `[entry]`,
      `func2`, `label_map`, `vis`] mp_tac) >>
    simp[]) >>
  `subst_block_labels_fn label_map func2 = func2` by (
    irule subst_block_labels_fn_identity >>
    simp[labels_absent_fn_def] >> rpt strip_tac >>
    irule not_in_fn_labels_label_absent >> simp[] >>
    first_x_assum irule >>
    simp[listTheory.MEM_MAP] >> qexists `(old, new)` >> simp[]
  ) >>
  simp[] >>
  mp_tac collapse_dfs_correct >>
  disch_then (qspecl_then [`func`, `[]:(string#string) list`, `[]`, `[entry]`,
    `func2`, `label_map`, `vis`, `fuel`, `ctx`, `s`] mp_tac) >>
  simp[]
QED

(* Bridge: lift run_blocks result to run_function.
   fn_entry_label = SOME s.vs_current_bb + s.vs_inst_idx = 0
   means run_function just calls run_blocks on the same state. *)
Theorem collapse_dfs_subst_correct_rf:
  !func func2 (label_map:(string#string) list) vis entry fuel ctx s.
    collapse_wf func /\
    fn_entry_label func = SOME entry /\
    fn_entry_label func = SOME s.vs_current_bb /\
    fn_entry_label (if label_map = [] then func2
                    else subst_block_labels_fn label_map func2) =
      SOME s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    ~s.vs_halted /\
    collapse_dfs func [] [] [entry] = (func2, label_map, vis) ==>
    ?fuel'. fuel <= fuel' /\ result_equiv {}
      (run_function fuel' ctx func s)
      (run_function fuel ctx
        (if label_map = [] then func2
         else subst_block_labels_fn label_map func2) s)
Proof
  rpt strip_tac >>
  simp[venomExecSemanticsTheory.run_function_def] >>
  gvs[venom_state_accessors] >>
  irule collapse_dfs_subst_correct >>
  simp[]
QED

val _ = export_theory();
