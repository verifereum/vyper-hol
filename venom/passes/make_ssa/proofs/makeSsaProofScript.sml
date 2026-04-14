(*
 * Make SSA Pass — Top-level Correctness Theorem
 *
 * Uses helpers from makeSsaHelper for structural properties
 * (label preservation, non_phi_refines, bbs_outputs_agree, etc.)
 * and ssaSimDefs/ssaRenamedSim for per-instruction simulation.
 *)

Theory makeSsaProof
Ancestors
  makeSsaSim makeSsaHelper ssaSimDefs ssaRenamedSim ssaPipeline makeSsaDefs stateEquiv
  venomExecSemantics venomExecProofs venomWf venomState venomInst
  cfgTransform cfgTransformProps passSimulationDefs passSimulationProps
  execEquivParamDefs execEquivParamProofs
  list rich_list alist finite_map pred_set string arithmetic

(* ===== Definitions and main theorem ===== *)

(* Freshness: push_version produces a name distinct from all existing
   latest_version entries for other variables *)
Triviality push_version_fresh[local]:
  !rs base x ver rs'.
    push_version rs base = (rs', ver) /\
    colon_free base /\ colon_free x /\ x <> base ==>
    latest_version rs x <> version_var base ver
Proof
  rpt gen_tac >> PairCases_on `rs` >> strip_tac >>
  fs[latest_version_def] >>
  rename1 `ALOOKUP rs1 x` >>
  (* Helper: x <> version_var base ver when colon_free x, colon_free base, x <> base *)
  `colon_free x ==> x <> version_var base' ver` by (
    strip_tac >>
    Cases_on `ver` >- simp[version_var_def] >>
    spose_not_then (ASSUME_TAC o GSYM) >>
    `SUC n > 0` by DECIDE_TAC >>
    imp_res_tac version_var_has_colon >> gvs[]) >>
  Cases_on `ALOOKUP rs1 x` >> fs[] >>
  rename1 `SOME stk` >> Cases_on `stk` >> fs[] >>
  strip_tac >> imp_res_tac version_var_inj
QED

(* latest_version after push_version: only base changes *)
Triviality latest_version_push_version[local]:
  !rs base ver rs'.
    push_version rs base = (rs', ver) ==>
    !x. latest_version rs' x =
        if x = base then version_var base ver
        else latest_version rs x
Proof
  rpt gen_tac >> PairCases_on `rs` >>
  simp[push_version_def] >> strip_tac >> gvs[] >>
  gen_tac >> simp[latest_version_def] >>
  Cases_on `x = base'` >> simp[] >- (
    (* x = base: ALOOKUP finds base at the head *)
    Cases_on `ALOOKUP rs1 base'` >> simp[]
  ) >>
  (* x <> base: ALOOKUP skips base entry *)
  Cases_on `ALOOKUP rs1 base'` >> simp[] >>
  simp[ALOOKUP_FILTER]
QED

(* ssa_sim preservation through update_var with fresh output *)
Triviality ssa_sim_update_fresh[local]:
  !sigma s1 s2 base out w.
    ssa_sim sigma s1 s2 /\
    lookup_var base s1 = SOME w /\
    (!x. x <> base ==> sigma x <> out) ==>
    ssa_sim ((base =+ out) sigma) s1 (update_var out w s2)
Proof
  rw[ssa_sim_def, update_var_def, lookup_var_def, combinTheory.UPDATE_def,
     FLOOKUP_UPDATE] >>
  metis_tac[optionTheory.SOME_11]
QED

(* Single PHI step: execute one PHI instruction, updating ssa_sim.
   The PHI reads via resolve_phi, evaluates in s2, writes to fresh output.
   After: ssa_sim sigma' s1 s2' where sigma'(bv) = out, rest unchanged. *)
Triviality phi_step_sim[local]:
  !bb' fuel ctx s1 s2 sigma bv out w prev_bb.
    s2.vs_inst_idx < LENGTH bb'.bb_instructions /\
    s2.vs_prev_bb = SOME prev_bb /\
    ssa_sim sigma s1 s2 /\
    (EL s2.vs_inst_idx bb'.bb_instructions).inst_opcode = PHI /\
    (EL s2.vs_inst_idx bb'.bb_instructions).inst_outputs = [out] /\
    resolve_phi prev_bb
      (EL s2.vs_inst_idx bb'.bb_instructions).inst_operands =
      SOME (Var (sigma bv)) /\
    lookup_var bv s1 = SOME w /\
    lookup_var (sigma bv) s2 = SOME w /\
    (!x. x <> bv ==> sigma x <> out) ==>
    let s2' = update_var out w s2 in
    ssa_sim ((bv =+ out) sigma) s1 s2' /\
    (s2'.vs_halted <=> s2.vs_halted) /\
    s2'.vs_current_bb = s2.vs_current_bb /\
    s2'.vs_prev_bb = s2.vs_prev_bb /\
    exec_block fuel ctx bb' s2 =
      exec_block fuel ctx bb'
        (s2' with vs_inst_idx := SUC s2.vs_inst_idx)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  conj_tac >- suspend "ssa_upd" >>
  suspend "rest"
QED

Resume phi_step_sim[ssa_upd]:
  irule ssa_sim_update_fresh >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume phi_step_sim[rest]:
  (conj_tac >- (simp[update_var_def])) >>
  (conj_tac >- (simp[update_var_def])) >>
  (conj_tac >- (simp[update_var_def])) >>
  mp_tac (SIMP_RULE std_ss [] exec_block_step_non_term) >>
  disch_then (qspecl_then [`bb'`, `fuel`, `ctx`, `s2`,
    `update_var out w s2`] mp_tac) >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (simp[is_terminator_def])
    >- (simp[])
    >> simp[step_inst_base_def, eval_operand_def])) >>
  simp[]
QED

Finalise phi_step_sim;

(* The root of the dom tree maps to the initial rename state *)
Triviality block_rename_states_root:
  !rs bbs succ_map lbl children.
    ALL_DISTINCT (dom_tree_labels (DNode lbl children)) ==>
    ALOOKUP (block_rename_states rs bbs succ_map (DNode lbl children))
      lbl = SOME rs
Proof
  rpt strip_tac >>
  simp[block_rename_states_def] >>
  Cases_on `lookup_block lbl bbs` >> simp[] >>
  Cases_on `rename_block_insts rs x.bb_instructions` >> simp[]
QED

Theorem make_ssa_fn_correct:
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
    (* Per-instruction well-formedness for original func (pre-SSA) *)
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI /\
              EVERY colon_free inst.inst_outputs /\
              ALL_DISTINCT inst.inst_outputs /\
              (~opcode_has_output inst.inst_opcode ==>
               inst.inst_outputs = [])) /\
    (* PHI structural correctness — pipeline-derivable *)
    (let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                   pred_map succ_map live_in func in
     let ordered_bbs = MAP THE (FILTER IS_SOME
           (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)) in
     let defs = compute_defs ordered_bbs in
     let bbs1 = add_phi_nodes dom_frontiers pred_map live_in
                  func.fn_blocks defs in
     let rs0 = init_rename_state defs in
     valid_phi_coverage bbs1 dtree succ_map rs0 live_in /\
     valid_phi_operands bbs1 (SND (rename_blocks rs0 bbs1 succ_map dtree))
                        dtree succ_map rs0 /\
     phi_bases_live_in live_in func' /\
     (* Entry block has no PHIs — derivable from fn_entry_no_preds + valid_dom_tree *)
     (!bb_entry. lookup_block s.vs_current_bb bbs1 = SOME bb_entry ==>
       EVERY (\i. i.inst_opcode <> PHI) bb_entry.bb_instructions) /\
     (* Distinct PHI outputs per block — derivable from add_phi_nodes MEM check *)
     (!lbl bb_mid. lookup_block lbl bbs1 = SOME bb_mid ==>
       ALL_DISTINCT
         (FLAT (MAP (\i. i.inst_outputs)
           (FILTER (\i. i.inst_opcode = PHI) bb_mid.bb_instructions))))) ==>


    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    ?fresh fuel'.
      result_equiv fresh
        (run_blocks fuel ctx func s)
        (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> rpt disch_tac >>
  qabbrev_tac `func' = make_ssa_fn dom_frontiers dtree dom_post_order
    pred_map succ_map live_in func` >>
  qabbrev_tac `ordered_bbs = MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order))` >>
  qabbrev_tac `defs = compute_defs ordered_bbs` >>
  qabbrev_tac `bbs1 = add_phi_nodes dom_frontiers pred_map live_in
    func.fn_blocks defs` >>
  qabbrev_tac `rs0 = init_rename_state defs` >>
  (* Case split: does func have an entry block? *)
  (* fn_entry_label is SOME from precondition *)
  `?entry. fn_entry_label func = SOME entry` by (
    Cases_on `fn_entry_label func` >> gvs[]) >>
  (* Case split on Error vs non-Error *)
  Cases_on `?e. run_blocks fuel ctx func s = Error e`
  >- (
    qexistsl_tac [`UNIV`, `0`] >>
    gvs[] >> simp[run_blocks_def, result_equiv_def])
  >>
  gvs[] >>
  (* Non-Error: apply run_blocks_ssa_sim *)
  qexistsl_tac [`UNIV`, `fuel`] >>
  qabbrev_tac `bbs2 = SND (rename_blocks rs0 bbs1 succ_map dtree)` >>
  mp_tac (SIMP_RULE std_ss [LET_THM] run_blocks_ssa_sim) >>
  disch_then (qspecl_then [`fuel`, `dom_frontiers`, `dtree`,
    `dom_post_order`, `pred_map`, `succ_map`, `live_in`,
    `func`, `\x. x`, `bbs1`, `rs0`,
    `ctx`, `s`, `s`] mp_tac) >>
  simp_tac std_ss [Abbr `func'`] >>
  `SND (rename_blocks rs0 bbs1 succ_map dtree) = bbs2`
    by simp[Abbr `bbs2`] >>
  pop_assum (fn eq => PURE_REWRITE_TAC [eq]) >>
  (* Establish per-instruction fact without opcode <> PHI *)
  `!bb inst. MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions ==>
     EVERY colon_free inst.inst_outputs /\
     ALL_DISTINCT inst.inst_outputs /\
     (~opcode_has_output inst.inst_opcode ==> inst.inst_outputs = [])` by
    metis_tac[] >>
  (impl_tac >- (
    rpt conj_tac
    >| [
      (* wf_function *) first_assum ACCEPT_TAC,
      (* valid_dom_tree *) first_assum ACCEPT_TAC,
      (* valid_cfg_maps *) first_assum ACCEPT_TAC,
      (* valid_liveness *) first_assum ACCEPT_TAC,
      (* fn_entry_no_preds *) first_assum ACCEPT_TAC,
      (* fn_inst_wf *) first_assum ACCEPT_TAC,
      (* ssa_sim identity *) simp[ssa_sim_def, lookup_var_def, FLOOKUP_DEF],
      (* version_var for identity sigma *)
      rpt strip_tac >> qexists_tac `0` >> simp[version_var_def],
      (* s.vs_inst_idx = 0 *) first_assum ACCEPT_TAC,
      (* s.vs_inst_idx = 0 (dup) *) first_assum ACCEPT_TAC,
      (* vars_colon_free *) simp[vars_colon_free_def, lookup_var_def, FLOOKUP_DEF],
      (* live_in_scope *) first_assum ACCEPT_TAC,
      (* phi_bases_live_in *) first_assum ACCEPT_TAC,
      (* valid_liveness_flow *) first_assum ACCEPT_TAC,
      (* valid_liveness_uses *) first_assum ACCEPT_TAC,
      (* phi_extends *) simp[Abbr `bbs1`] >> metis_tac[add_phi_nodes_phi_extends],
      (* PHI singleton outputs in bbs1: any PHI was added by add_phi_nodes *)
      rpt strip_tac >>
      imp_res_tac lookup_block_MEM >>
      `phi_extends func.fn_blocks bbs1` by (
        simp[Abbr `bbs1`] >> metis_tac[add_phi_nodes_phi_extends]) >>
      `?j. j < LENGTH bbs1 /\ EL j bbs1 = bb_mid` by metis_tac[MEM_EL] >>
      `j < LENGTH func.fn_blocks` by gvs[phi_extends_def] >>
      (* inst is in PHI prefix (original has no PHIs) *)
      `~MEM inst (EL j func.fn_blocks).bb_instructions` by (
        spose_not_then strip_assume_tac >>
        `MEM (EL j func.fn_blocks) func.fn_blocks` by metis_tac[MEM_EL] >>
        metis_tac[]) >>
      mp_tac (SIMP_RULE std_ss [LET_THM] add_phi_nodes_phi_outputs) >>
      disch_then (qspecl_then [`dom_frontiers`, `pred_map`, `live_in`,
        `func.fn_blocks`, `defs`] mp_tac) >>
      simp[Abbr `bbs1`] >>
      disch_then (qspec_then `j` mp_tac) >> simp[] >>
      disch_then (qspec_then `inst` mp_tac) >> simp[] >> strip_tac >>
      qexists_tac `var` >> simp[] >>
      (* colon_free from compute_defs_colon_free *)
      `EVERY (\p. colon_free (FST p)) defs` by (
        simp[Abbr `defs`] >> irule compute_defs_colon_free >>
        simp[Abbr `ordered_bbs`, EVERY_MAP, EVERY_FILTER, EVERY_MEM] >>
        rpt strip_tac >>
        Cases_on `IS_SOME (lookup_block lbl' func.fn_blocks)` >> simp[] >>
        gvs[optionTheory.IS_SOME_EXISTS] >> imp_res_tac lookup_block_MEM >>
        gvs[EVERY_MEM] >> res_tac >> res_tac >> simp[]) >>
      gvs[EVERY_MEM, MEM_MAP] >> metis_tac[pairTheory.FST],
      (* func'.fn_blocks = bbs2 *)
      simp[make_ssa_fn_def, LET_THM, Abbr `bbs2`] >>
      Cases_on `rename_blocks rs0 bbs1 succ_map dtree` >> simp[],
      (* valid_phi_operands *) first_assum ACCEPT_TAC,
      (* valid_phi_coverage *) first_assum ACCEPT_TAC,
      (* phi_resolve — vacuously true since s.vs_prev_bb = NONE *)
      rpt strip_tac >> gvs[],
      (* coverage: at entry block, rs_b = rs0, latest_version rs0 x = x = I x *)
      rpt strip_tac >>
      `?entry children. dtree = DNode entry children /\
        fn_entry_label func = SOME entry` by (
        gvs[valid_dom_tree_def] >> qexistsl_tac [`x'`, `l`] >> simp[]) >>
      `s.vs_current_bb = entry` by gvs[] >>
      `ALL_DISTINCT (dom_tree_labels (DNode entry children))` by (
        gvs[valid_dom_tree_def]) >>
      `ALOOKUP (block_rename_states rs0 bbs1 succ_map (DNode entry children))
         entry = SOME rs0` by (
        irule block_rename_states_root >> first_assum ACCEPT_TAC) >>
      `rs_b = rs0` by (gvs[]) >>
      gvs[Abbr `rs0`, latest_version_init_rename_state],
      (* distinct PHI bases: from precondition *)
      first_assum ACCEPT_TAC,
      (* prev_bb: at entry, no PHIs → EXISTS PHI = F → vacuous *)
      rpt strip_tac >>
      `EVERY (\i. i.inst_opcode <> PHI) bb_mid.bb_instructions` by (
        first_x_assum irule >> first_assum ACCEPT_TAC) >>
      gvs[listTheory.EXISTS_MEM, listTheory.EVERY_MEM],
      (* no-error *) first_assum ACCEPT_TAC,
      (* per-instruction *) first_assum ACCEPT_TAC
    ]
  )) >>
  simp[]
QED
