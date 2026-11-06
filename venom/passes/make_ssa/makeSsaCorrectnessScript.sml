(*
 * Make SSA Pass — Correctness & Obligations
 *
 * Helper lemmas in proofs/makeSsaProofScript.sml and proofs/makeSsaSsaFormScript.sml.
 *
 * Obligations:
 *   make_ssa_establishes_ssa_form     — output is in SSA form (wf_ssa: see note)
 *   make_ssa_preserves_wf_function    — output is still wf_function
 *)

Theory makeSsaCorrectness
Ancestors
  makeSsaProof
  makeSsaHelper
  makeSsaSsaForm
  ssaPipelineProps
  makeSsaDefs dominatorDefs cfgTransform venomInst venomWf venomExecProofs cfgTransformProofs cfgTransformProps list rich_list alist arithmetic sorting pred_set ssaPipeline

(* Clean top-level correctness theorem — no pipeline-derivable assumptions *)
Theorem make_ssa_pass_correct:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in
   func s fuel ctx.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func /\
    fn_inst_wf func /\
    valid_liveness_flow live_in func /\
    valid_liveness_uses live_in func /\
    s.vs_vars = FEMPTY /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    fn_entry_label func = SOME s.vs_current_bb /\
    live_in_scope live_in s /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI /\
              EVERY colon_free inst.inst_outputs /\
              ALL_DISTINCT inst.inst_outputs /\
              (~opcode_has_output inst.inst_opcode ==>
               inst.inst_outputs = [])) ==>
    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    ?fresh fuel'.
      result_equiv fresh
        (run_blocks fuel ctx func s)
        (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  mp_tac (SIMP_RULE std_ss [LET_THM] make_ssa_fn_correct) >>
  simp_tac std_ss [LET_THM] >>
  disch_then irule >>
  rpt conj_tac
  >> TRY (first_assum ACCEPT_TAC)
  >> TRY (
    mp_tac (SIMP_RULE std_ss [LET_THM] ssaPipelinePropsTheory.phi_coverage) >>
    disch_then irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> res_tac >> simp[])
  >> TRY (
    mp_tac (SIMP_RULE std_ss [LET_THM] ssaPipelinePropsTheory.phi_operands) >>
    disch_then irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> res_tac >> simp[])
  >> TRY (
    mp_tac (SIMP_RULE std_ss [LET_THM] ssaPipelinePropsTheory.phi_bases_live) >>
    disch_then irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> res_tac >> simp[])
  >>
  mp_tac (Q.SPECL [`dom_frontiers`, `dtree`, `dom_post_order`, `pred_map`, `succ_map`, `live_in`, `func`, `s.vs_current_bb`,
    `compute_defs (MAP THE (FILTER IS_SOME (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)))`] entry_no_phis_in_bbs1) >>
(impl_tac >- (rpt strip_tac >> gvs[] >> metis_tac[])) >>
simp[LET_DEF] >> strip_tac >>
mp_tac (Q.SPECL [`dom_frontiers`, `pred_map`, `live_in`, `func.fn_blocks`,
  `compute_defs (MAP THE (FILTER IS_SOME (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)))`] phi_outputs_all_distinct) >>
(impl_tac >- (
  conj_tac >- simp[makeSsaDefsTheory.compute_defs_all_distinct] >>
  metis_tac[]
)) >>
simp[LET_DEF]
QED

(* MEM in labels implies lookup exists *)
Triviality mem_labels_lookup_exists[local]:
  !lbl bbs.
    MEM lbl (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl bbs <> NONE
Proof
  Induct_on `bbs` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `lbl` mp_tac) >>
  simp[lookup_block_def]
QED

(* ===== Obligations ===== *)

(*
 * NOTE: there is no make_ssa_establishes_wf_ssa; only ssa_form is established.
 * wf_ssa = ssa_form ∧ def_dominates_uses. def_dominates_uses requires
 * that for every MEM (Var v) inst.inst_operands, the defining block
 * fn_dominates the use block. This is FALSE for PHI instructions in
 * standard SSA: a PHI at block B uses Var v defined in predecessor P,
 * but P does NOT necessarily dominate B (e.g., in diamond CFGs).
 * The correct property for PHI-containing SSA would require
 * domination of the *predecessor* rather than the use block.
 * The downstream consumer (codegen_ready_fn) uses def_dominates_uses
 * AFTER PHI lowering, where no PHIs remain — so the existing
 * definition is correct for its actual use case.
 *)
Theorem make_ssa_establishes_ssa_form:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              EVERY colon_free inst.inst_outputs) ==>
    ssa_form (make_ssa_fn dom_frontiers dtree dom_post_order
                pred_map succ_map live_in func)
Proof
  rpt gen_tac >> strip_tac >>
  simp[make_ssa_fn_def] >>
  (* valid_dom_tree gives fn_entry_label = SOME entry *)
  `?entry children. dtree = DNode entry children /\
                    fn_entry_label func = SOME entry` by
    (gvs[valid_dom_tree_def] >> metis_tac[]) >>
  gvs[] >> simp[LET_THM] >>
  (* Name intermediate results *)
  qabbrev_tac `defs = compute_defs
    (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)))` >>
  qabbrev_tac `bbs1 = add_phi_nodes dom_frontiers pred_map live_in
                         func.fn_blocks defs` >>
  qabbrev_tac `rs0 = init_rename_state defs` >>
  Cases_on `rename_blocks rs0 bbs1 succ_map (DNode entry children)` >>
  rename1 `rename_blocks _ _ _ _ = (ctrs', bbs2)` >>
  simp[] >>
  (* === Phase A: Establish reusable intermediate facts === *)
  (* A1: label chain bbs2 = bbs1 = fn_blocks *)
  `MAP (\bb. bb.bb_label) bbs2 = MAP (\bb. bb.bb_label) bbs1` by
    (`bbs2 = SND (rename_blocks rs0 bbs1 succ_map (DNode entry children))` by
       simp[] >>
     metis_tac[rename_blocks_preserves_labels]) >>
  `MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) func.fn_blocks` by
    metis_tac[add_phi_nodes_preserves_labels] >>
  (* A2: ALL_DISTINCT labels *)
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs2)` by
    gvs[wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
    gvs[wf_function_def, fn_labels_def] >>
  (* A3: dtree facts from valid_dom_tree (forward, non-destructive) *)
  `ALL_DISTINCT (dom_tree_labels (DNode entry children))` by
    (qpat_x_assum `valid_dom_tree _ _ _ _` mp_tac >>
     simp[valid_dom_tree_def]) >>
  `set (dom_tree_labels (DNode entry children)) = set (fn_labels func)` by
    (qpat_x_assum `valid_dom_tree _ _ _ _` mp_tac >>
     simp[valid_dom_tree_def]) >>
  (* A4: PERM dtree_labels ~ MAP bb_label bbs2 *)
  `PERM (dom_tree_labels (DNode entry children))
        (MAP (\bb. bb.bb_label) bbs2)` by
    (irule PERM_ALL_DISTINCT >> simp[] >>
     gvs[fn_labels_def, EXTENSION] >> metis_tac[]) >>
  (* A5: colon_free for bbs1 *)
  `EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs)
           bb.bb_instructions) func.fn_blocks` by
    (simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[EVERY_MEM]) >>
  `EVERY (\p. colon_free (FST p)) defs` by
    (qunabbrev_tac `defs` >> irule compute_defs_colon_free >>
     gvs[EVERY_MEM, MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
     rpt strip_tac >>
     Cases_on `lookup_block lbl func.fn_blocks` >> gvs[] >>
     imp_res_tac lookup_block_MEM >>
     gvs[EVERY_MEM] >> res_tac >> gvs[EVERY_MEM]) >>
  `EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs)
           bb.bb_instructions) bbs1` by
    (qunabbrev_tac `bbs1` >>
     irule add_phi_nodes_colon_free >> simp[]) >>
  (* A6: lookup exists for dtree labels in bbs1 *)
  `!lbl. MEM lbl (dom_tree_labels (DNode entry children)) ==>
         lookup_block lbl bbs1 <> NONE` by
    (rpt gen_tac >> disch_tac >>
     irule mem_labels_lookup_exists >>
     `MEM lbl (fn_labels func)` by
       (qpat_x_assum `set _ = set (fn_labels _)` mp_tac >>
        simp[EXTENSION] >> metis_tac[]) >>
     gvs[fn_labels_def]) >>
  (* === Phase B: Apply the chain === *)
  irule all_distinct_outputs_ssa_form >>
  `collect_outputs bbs2 (MAP (\bb. bb.bb_label) bbs2) =
   FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs2))` by
    (irule collect_outputs_eq_fn_insts_outputs >> simp[]) >>
  ASM_REWRITE_TAC[] >>
  (* A7: colon_free for bbs1 blocks via lookup *)
  `!lbl bb. lookup_block lbl bbs1 = SOME bb ==>
            EVERY (\i. EVERY colon_free i.inst_outputs)
              bb.bb_instructions` by
    metis_tac[every_lookup_block] >>
  (* B1: rename_blocks_cross_distinct *)
  qspecl_then [`DNode entry children`, `rs0`, `bbs1`, `succ_map`,
     `ctrs'`, `bbs2`]
     mp_tac (CONJUNCT1 rename_blocks_cross_distinct) >>
  simp[] >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >>
  (* B2: PERM transfer *)
  `PERM (collect_outputs bbs2 (dom_tree_labels (DNode entry children)))
        (collect_outputs bbs2 (MAP (\bb. bb.bb_label) bbs2))` by
    (irule collect_outputs_perm >> simp[]) >>
  `ALL_DISTINCT (collect_outputs bbs2 (MAP (\bb. bb.bb_label) bbs2))`
    by metis_tac[ALL_DISTINCT_PERM] >>
  gvs[fn_insts_def]
QED

Theorem make_ssa_preserves_wf_function:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func ==>
    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    ALL_DISTINCT (fn_labels func') /\
    fn_has_entry func' /\
    (!bb. MEM bb func'.fn_blocks ==> bb_well_formed bb) /\
    fn_succs_closed func'
Proof
  ACCEPT_TAC makeSsaHelperTheory.make_ssa_preserves_wf_function
QED
