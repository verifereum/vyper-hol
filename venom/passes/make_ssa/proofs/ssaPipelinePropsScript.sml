(*
 * SSA Pipeline Obligations
 *
 * Proves the 5 structural properties of the make_ssa pipeline
 * that were previously hypotheses in make_ssa_fn_correct:
 *
 *   1. entry_no_phis         — entry block has no PHIs after add_phi_nodes
 *   2. phi_outputs_distinct  — PHI outputs are ALL_DISTINCT per block
 *   3. phi_bases_live        — PHI base variables are live-in
 *   4. phi_coverage          — valid_phi_coverage holds
 *   5. phi_operands          — valid_phi_operands holds
 *)

Theory ssaPipelineProps
Ancestors
  ssaPipeline makeSsaHelper makeSsaDefs ssaSimDefs
  cfgTransformProps venomWf venomExecProofs venomInst
  list rich_list alist string pred_set arithmetic

(* ===== Obligation 4: Entry block has no PHIs ===== *)

(* Entry is not in any dominance frontier when it has no predecessors *)
Theorem entry_not_in_frontiers:
  !dom_frontiers dtree dom_post_order func entry b fs.
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    fn_entry_no_preds func /\
    fn_entry_label func = SOME entry /\
    ALOOKUP dom_frontiers b = SOME fs ==>
    ~MEM entry fs
Proof
  rpt strip_tac >>
  gvs[valid_dom_tree_def] >>
  first_x_assum (qspecl_then [`b`, `entry`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  imp_res_tac lookup_block_MEM >>
  gvs[fn_entry_no_preds_def]
QED

(* lookup_block on conditional MAP preserves result for non-matching labels *)
Triviality lookup_block_map_cond:
  !bbs lbl f_lbl phi.
    lbl <> f_lbl ==>
    lookup_block lbl
      (MAP (\bb. if bb.bb_label = f_lbl
                 then insert_phi_at_block phi bb else bb) bbs) =
    lookup_block lbl bbs
Proof
  Induct >> simp[lookup_block_def, FIND_thm, insert_phi_at_block_def] >>
  rw[] >> gvs[] >>
  first_x_assum (qspecl_then [`lbl`, `f_lbl`, `phi`] mp_tac) >>
  simp[lookup_block_def, insert_phi_at_block_def]
QED

(* process_frontiers only modifies blocks whose label is in fs *)
Triviality process_frontiers_preserves_other:
  !fs var pm li bbs rest hp bbs' rest' hp' lbl.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') /\
    ~MEM lbl fs ==>
    lookup_block lbl bbs' = lookup_block lbl bbs
Proof
  Induct >> rw[process_frontiers_def] >> gvs[]
  >- metis_tac[]
  >- metis_tac[]
  >> (* live case *)
  first_x_assum drule >> disch_then drule >>
  simp[lookup_block_map_cond]
QED

(* insert_phis_for_var preserves blocks not in any frontier *)
Triviality insert_phis_for_var_preserves_other:
  !var dom_frontiers pred_map live_in bbs wl hp lbl.
    (!b fs. ALOOKUP dom_frontiers b = SOME fs ==> ~MEM lbl fs) ==>
    lookup_block lbl
      (insert_phis_for_var var dom_frontiers pred_map live_in bbs wl hp) =
    lookup_block lbl bbs
Proof
  ho_match_mp_tac insert_phis_for_var_ind >>
  rw[insert_phis_for_var_def] >>
  pairarg_tac >> gvs[] >>
  (* Goal: lookup_block lbl (insert_phis_for_var ... bbs' ...) = lookup_block lbl bbs
     IH:   lookup_block lbl (insert_phis_for_var ... bbs' ...) = lookup_block lbl bbs'
     Need: lookup_block lbl bbs' = lookup_block lbl bbs *)
  qsuff_tac `lookup_block lbl bbs' = lookup_block lbl bbs`
  >- (strip_tac >> metis_tac[]) >>
  qpat_x_assum `process_frontiers _ _ _ _ _ _ _ = _` mp_tac >>
  DISCH_TAC >>
  drule process_frontiers_preserves_other >>
  disch_then (qspec_then `lbl` mp_tac) >>
  impl_tac >- (
    Cases_on `ALOOKUP dom_frontiers d` >> simp[] >> metis_tac[]) >>
  simp[]
QED

(* add_phi_nodes preserves blocks not in any frontier *)
Triviality add_phi_nodes_preserves_other:
  !dom_frontiers pred_map live_in bbs defs lbl.
    (!b fs. ALOOKUP dom_frontiers b = SOME fs ==> ~MEM lbl fs) ==>
    lookup_block lbl
      (add_phi_nodes dom_frontiers pred_map live_in bbs defs) =
    lookup_block lbl bbs
Proof
  rpt gen_tac >> strip_tac >>
  simp[add_phi_nodes_def] >>
  qspec_tac (`bbs`, `acc`) >>
  Induct_on `defs` >> simp[FOLDL] >>
  rpt strip_tac >> PairCases_on `h` >> simp[] >>
  first_x_assum (qspec_then
    `insert_phis_for_var h0 dom_frontiers pred_map live_in acc h1 []`
    mp_tac) >> simp[] >>
  `lookup_block lbl
    (insert_phis_for_var h0 dom_frontiers pred_map live_in acc h1 []) =
   lookup_block lbl acc` suffices_by simp[] >>
  irule insert_phis_for_var_preserves_other >> first_assum ACCEPT_TAC
QED

Theorem entry_no_phis_in_bbs1:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in
   func entry defs.
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    fn_entry_no_preds func /\
    fn_entry_label func = SOME entry /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI) ==>
    let bbs1 = add_phi_nodes dom_frontiers pred_map live_in
                 func.fn_blocks defs in
    !bb_entry. lookup_block entry bbs1 = SOME bb_entry ==>
      EVERY (\i. i.inst_opcode <> PHI) bb_entry.bb_instructions
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  (* Entry is not in any dominance frontier *)
  `!b fs. ALOOKUP dom_frontiers b = SOME fs ==> ~MEM entry fs` by
    metis_tac[entry_not_in_frontiers] >>
  (* So add_phi_nodes doesn't modify the entry block *)
  `lookup_block entry
    (add_phi_nodes dom_frontiers pred_map live_in func.fn_blocks defs) =
   lookup_block entry func.fn_blocks` by
    (irule add_phi_nodes_preserves_other >> first_assum ACCEPT_TAC) >>
  (* Entry block is unchanged from original *)
  gvs[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  imp_res_tac lookup_block_MEM >> metis_tac[]
QED

(* phi_extends preserves block labels *)
Triviality phi_extends_label:
  !bbs bbs' j.
    phi_extends bbs bbs' /\ j < LENGTH bbs ==>
    (EL j bbs').bb_label = (EL j bbs).bb_label
Proof
  rw[phi_extends_def] >>
  `MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs` by
    first_assum ACCEPT_TAC >>
  `EL j (MAP (\bb. bb.bb_label) bbs') = EL j (MAP (\bb. bb.bb_label) bbs)`
    by simp[] >>
  gvs[EL_MAP]
QED

(* ===== Helpers: PHIs only inserted when live-in ===== *)

(* process_frontiers: added PHIs are for live-in variables.
   Proof mirrors process_frontiers_phi_outputs in ssaPipeline. *)
Triviality process_frontiers_phi_live_in:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    !j. j < LENGTH bbs ==>
      !inst. MEM inst (EL j bbs').bb_instructions /\
             ~MEM inst (EL j bbs).bb_instructions ==>
        ?vs. ALOOKUP li (EL j bbs).bb_label = SOME vs /\ MEM var vs
Proof
  Induct >> rw[process_frontiers_def]
  >- metis_tac[] >- metis_tac[]
  >> (
    qmatch_asmsub_abbrev_tac
      `process_frontiers _ _ _ bbs_map _ _ _` >>
    Cases_on `MEM inst (EL j bbs_map).bb_instructions`
    >- (
      (* inst in bbs_map but not in bbs: inserted by MAP at block h *)
      `(EL j bbs).bb_label = h` by (
        spose_not_then ASSUME_TAC >>
        `EL j bbs_map = EL j bbs` by simp[Abbr `bbs_map`, EL_MAP] >>
        gvs[]) >>
      Cases_on `ALOOKUP li h` >> gvs[])
    >- (
      (* inst not in bbs_map: IH applies *)
      first_x_assum drule >> disch_then (qspec_then `j` mp_tac) >>
      simp[Abbr `bbs_map`] >> disch_then drule >> strip_tac >>
      `(EL j (MAP (\bb. if bb.bb_label = h
         then insert_phi_at_block
           (build_phi_inst var
             (case ALOOKUP pm h of SOME ps => ps | NONE => []))
           bb else bb) bbs)).bb_label = (EL j bbs).bb_label` by (
        simp[EL_MAP] >> rw[insert_phi_at_block_def]) >>
      gvs[]))
QED

(* insert_phis_for_var: combined output + live-in property *)
Triviality insert_phis_for_var_phi_live_in:
  !var dom_frontiers pred_map live_in bbs wl hp.
    !j. j < LENGTH bbs ==>
      !inst. MEM inst (EL j
        (insert_phis_for_var var dom_frontiers pred_map
           live_in bbs wl hp)).bb_instructions /\
             ~MEM inst (EL j bbs).bb_instructions ==>
        inst.inst_outputs = [var] /\ inst.inst_opcode = PHI /\
        ?vs. ALOOKUP live_in (EL j bbs).bb_label = SOME vs /\
             MEM var vs
Proof
  (* Same pattern as insert_phis_for_var_phi_outputs in ssaPipeline,
     using process_frontiers_phi_outputs + process_frontiers_phi_live_in
     for the MEM case, and IH for the not-MEM case. *)
  ho_match_mp_tac insert_phis_for_var_ind >>
  simp[insert_phis_for_var_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >>
  `phi_extends bbs bbs'` by
    metis_tac[process_frontiers_phi_extends, phi_extends_refl] >>
  `j < LENGTH bbs'` by gvs[phi_extends_def] >>
  `(EL j bbs').bb_label = (EL j bbs).bb_label`
    by metis_tac[phi_extends_label] >>
  Cases_on `MEM inst (EL j bbs').bb_instructions` >> gvs[]
  >- (
    drule process_frontiers_phi_outputs >>
    disch_then (qspec_then `j` mp_tac) >> simp[] >>
    disch_then drule >> strip_tac >> gvs[] >>
    drule process_frontiers_phi_live_in >>
    disch_then (qspec_then `j` mp_tac) >> simp[] >>
    disch_then drule >> gvs[])
  >- (
    first_x_assum drule >> disch_then drule >> gvs[])
QED

(* ===== Obligation 5: PHI outputs ALL_DISTINCT per block ===== *)

(* Blocks whose label is in has_phi are not modified by process_frontiers *)
Triviality process_frontiers_has_phi_preserves:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    !j. j < LENGTH bbs ==>
      MEM (EL j bbs).bb_label hp ==>
      (EL j bbs').bb_instructions = (EL j bbs).bb_instructions
Proof
  Induct >- simp[process_frontiers_def] >>
  rw[process_frontiers_def]
  >- metis_tac[]  (* MEM h hp: skip *)
  >- ( (* not live: add h to hp *)
    `MEM (EL j bbs).bb_label (h::hp)` by simp[] >>
    metis_tac[])
  >> ( (* live case *)
    qmatch_asmsub_abbrev_tac `process_frontiers _ _ _ bbs_map _ _ _` >>
    `(EL j bbs).bb_label <> h` by metis_tac[] >>
    `EL j bbs_map = EL j bbs` by simp[Abbr `bbs_map`, EL_MAP] >>
    `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
    `MEM (EL j bbs_map).bb_label (h::hp)` by simp[] >>
    res_tac >> gvs[])
QED

(* process_frontiers preserves labels *)
Triviality process_frontiers_labels:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  Induct >> rw[process_frontiers_def] >> gvs[] >>
  rpt CASE_TAC >> gvs[] >>
  first_x_assum drule >> rw[MAP_MAP_o, insert_phi_at_block_def] >>
  irule MAP_CONG >> rw[]
QED

(* process_frontiers extends has_phi *)
Triviality process_frontiers_hp_mono:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    !x. MEM x hp ==> MEM x hp'
Proof
  Induct >> rw[process_frontiers_def] >> metis_tac[MEM]
QED

(* insert_phis_for_var preserves blocks whose label is in has_phi *)
Triviality insert_phis_for_var_has_phi_preserves:
  !var dom_frontiers pred_map live_in bbs wl hp.
    !j. j < LENGTH bbs ==>
      MEM (EL j bbs).bb_label hp ==>
      (EL j (insert_phis_for_var var dom_frontiers
        pred_map live_in bbs wl hp)).bb_instructions =
      (EL j bbs).bb_instructions
Proof
  ho_match_mp_tac insert_phis_for_var_ind >>
  rw[insert_phis_for_var_def] >>
  pairarg_tac >> gvs[] >>
  (* bbs' from process_frontiers preserves block j *)
  `(EL j bbs').bb_instructions = (EL j bbs).bb_instructions` by
    (drule process_frontiers_has_phi_preserves >> simp[]) >>
  (* hp' extends hp, so label is still in hp' *)
  `MEM (EL j bbs).bb_label has_phi'` by
    (drule process_frontiers_hp_mono >> simp[]) >>
  (* Labels preserved by process_frontiers *)
  imp_res_tac process_frontiers_labels >>
  `j < LENGTH bbs'` by
    (qpat_x_assum `MAP _ bbs' = _` mp_tac >> simp[MAP_EQ_EVERY2, LIST_REL_EL_EQN]) >>
  `(EL j bbs').bb_label = (EL j bbs).bb_label` by (
    `EL j (MAP (\bb. bb.bb_label) bbs') =
     EL j (MAP (\bb. bb.bb_label) bbs)` by simp[] >>
    gvs[EL_MAP]) >>
  metis_tac[]
QED

(* If process_frontiers modifies block j, then j's label is in output has_phi *)
Triviality process_frontiers_modified_in_hp:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    !j. j < LENGTH bbs ==>
      !inst. MEM inst (EL j bbs').bb_instructions /\
             ~MEM inst (EL j bbs).bb_instructions ==>
             MEM (EL j bbs).bb_label hp'
Proof
  Induct >> rw[process_frontiers_def]
  >- metis_tac[] >- metis_tac[]
  >> (
    qmatch_asmsub_abbrev_tac `process_frontiers _ _ _ bbs_map _ _ _` >>
    `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
    Cases_on `MEM inst (EL j bbs_map).bb_instructions`
    >- ( (* inst in bbs_map but not bbs: modified at this step *)
      `(EL j bbs).bb_label = h` by (
        spose_not_then ASSUME_TAC >>
        `EL j bbs_map = EL j bbs` by simp[Abbr `bbs_map`, EL_MAP] >>
        gvs[]) >>
      drule process_frontiers_hp_mono >>
      disch_then (qspec_then `h` mp_tac) >> simp[])
    >- ( (* inst not in bbs_map: modified in recursion, use IH *)
      first_x_assum drule >> disch_then (qspec_then `j` mp_tac) >>
      simp[] >> disch_then drule >> strip_tac >>
      `(EL j bbs_map).bb_label = (EL j bbs).bb_label` by (
        simp[Abbr `bbs_map`, EL_MAP] >>
        rw[insert_phi_at_block_def]) >>
      gvs[]))
QED

(* process_frontiers adds at most one new instruction per block *)
Triviality process_frontiers_new_unique:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    !j. j < LENGTH bbs ==>
      !(inst1 : instruction) inst2.
        MEM inst1 (EL j bbs').bb_instructions /\
        ~MEM inst1 (EL j bbs).bb_instructions /\
        MEM inst2 (EL j bbs').bb_instructions /\
        ~MEM inst2 (EL j bbs).bb_instructions ==>
        inst1 = inst2
Proof
  Induct >> rw[process_frontiers_def]
  >- metis_tac[] >- metis_tac[]
  >> (
    qmatch_asmsub_abbrev_tac `process_frontiers _ _ _ bbs_map _ _ _` >>
    `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
    Cases_on `MEM inst1 (EL j bbs_map).bb_instructions` >>
    Cases_on `MEM inst2 (EL j bbs_map).bb_instructions`
    >- ( (* both in bbs_map but not bbs: both from MAP, must be same *)
      qsuff_tac `!inst. MEM inst (EL j bbs_map).bb_instructions /\
                        ~MEM inst (EL j bbs).bb_instructions ==>
                        inst = build_phi_inst var
                          (case ALOOKUP pm h of SOME ps => ps | NONE => [])`
      >- metis_tac[] >>
      rpt strip_tac >>
      `EL j bbs_map = (if (EL j bbs).bb_label = h
         then insert_phi_at_block
           (build_phi_inst var
             (case ALOOKUP pm h of SOME ps => ps | NONE => []))
           (EL j bbs) else EL j bbs)` by
        simp[Abbr `bbs_map`, EL_MAP] >>
      Cases_on `(EL j bbs).bb_label = h` >>
      gvs[insert_phi_at_block_def])
    >- ( (* inst1 in bbs_map, inst2 not: impossible *)
      (* inst1 new vs bbs => (EL j bbs).bb_label = h *)
      `(EL j bbs).bb_label = h` by (
        spose_not_then ASSUME_TAC >>
        `EL j bbs_map = EL j bbs` by simp[Abbr `bbs_map`, EL_MAP] >>
        gvs[]) >>
      (* After MAP, label preserved, so (EL j bbs_map).bb_label = h *)
      `(EL j bbs_map).bb_label = h` by
        simp[Abbr `bbs_map`, EL_MAP, insert_phi_at_block_def] >>
      (* h is in h::hp, so has_phi_preserves says no changes at block j *)
      `(EL j bbs').bb_instructions = (EL j bbs_map).bb_instructions` by (
        drule process_frontiers_has_phi_preserves >>
        disch_then (qspec_then `j` mp_tac) >> simp[]) >>
      (* inst2 is in bbs' but not bbs_map: contradiction *)
      metis_tac[])
    >- ( (* symmetric: inst2 in bbs_map, inst1 not *)
      `(EL j bbs).bb_label = h` by (
        spose_not_then ASSUME_TAC >>
        `EL j bbs_map = EL j bbs` by simp[Abbr `bbs_map`, EL_MAP] >>
        gvs[]) >>
      `(EL j bbs_map).bb_label = h` by
        simp[Abbr `bbs_map`, EL_MAP, insert_phi_at_block_def] >>
      `(EL j bbs').bb_instructions = (EL j bbs_map).bb_instructions` by (
        drule process_frontiers_has_phi_preserves >>
        disch_then (qspec_then `j` mp_tac) >> simp[]) >>
      metis_tac[])
    >- (* neither in bbs_map: both from recursive call, IH *)
       metis_tac[])
QED

(* insert_phis_for_var adds at most one new instruction per block *)
Triviality insert_phis_for_var_new_unique:
  !var dom_frontiers pred_map live_in bbs wl hp.
    !j. j < LENGTH bbs ==>
      !(inst1 : instruction) inst2.
        MEM inst1 (EL j (insert_phis_for_var var dom_frontiers
          pred_map live_in bbs wl hp)).bb_instructions /\
        ~MEM inst1 (EL j bbs).bb_instructions /\
        MEM inst2 (EL j (insert_phis_for_var var dom_frontiers
          pred_map live_in bbs wl hp)).bb_instructions /\
        ~MEM inst2 (EL j bbs).bb_instructions ==>
        inst1 = inst2
Proof
  ho_match_mp_tac insert_phis_for_var_ind >>
  rw[insert_phis_for_var_def] >>
  pairarg_tac >> gvs[] >>
  (* bbs' is from process_frontiers, result is insert_phis_for_var on bbs' *)
  `phi_extends bbs bbs'` by
    metis_tac[process_frontiers_phi_extends, phi_extends_refl] >>
  `j < LENGTH bbs'` by gvs[phi_extends_def] >>
  Cases_on `MEM inst1 (EL j bbs').bb_instructions` >>
  Cases_on `MEM inst2 (EL j bbs').bb_instructions`
  >- ( (* both in bbs' but not bbs: from process_frontiers *)
    drule process_frontiers_new_unique >>
    disch_then (qspec_then `j` mp_tac) >> simp[] >>
    metis_tac[])
  >- ( (* inst1 in bbs', inst2 not: contradiction via has_phi *)
    (* process_frontiers modified block j, so label is in has_phi' *)
    drule process_frontiers_modified_in_hp >>
    disch_then (qspec_then `j` mp_tac) >> simp[] >>
    disch_then (qspec_then `inst1` mp_tac) >> simp[] >> strip_tac >>
    (* labels preserved by process_frontiers *)
    imp_res_tac process_frontiers_labels >>
    `(EL j bbs').bb_label = (EL j bbs).bb_label` by (
      `EL j (MAP (\bb. bb.bb_label) bbs') =
       EL j (MAP (\bb. bb.bb_label) bbs)` by simp[] >>
      gvs[EL_MAP]) >>
    (* insert_phis_for_var doesn't modify block j since label in has_phi' *)
    `(EL j (insert_phis_for_var var dom_frontiers pred_map live_in
        bbs' rest' has_phi')).bb_instructions =
     (EL j bbs').bb_instructions` by (
      irule insert_phis_for_var_has_phi_preserves >> gvs[]) >>
    (* inst2 in result means inst2 in bbs': contradiction *)
    metis_tac[])
  >- ( (* symmetric: inst2 in bbs', inst1 not *)
    drule process_frontiers_modified_in_hp >>
    disch_then (qspec_then `j` mp_tac) >> simp[] >>
    disch_then (qspec_then `inst2` mp_tac) >> simp[] >> strip_tac >>
    imp_res_tac process_frontiers_labels >>
    `(EL j bbs').bb_label = (EL j bbs).bb_label` by (
      `EL j (MAP (\bb. bb.bb_label) bbs') =
       EL j (MAP (\bb. bb.bb_label) bbs)` by simp[] >>
      gvs[EL_MAP]) >>
    `(EL j (insert_phis_for_var var dom_frontiers pred_map live_in
        bbs' rest' has_phi')).bb_instructions =
     (EL j bbs').bb_instructions` by (
      irule insert_phis_for_var_has_phi_preserves >> gvs[]) >>
    metis_tac[])
  >- ( (* neither in bbs': both from later recursion, IH *)
    metis_tac[])
QED

(* Step lemma: insert_phis_for_var preserves PHI injectivity *)
Triviality insert_phis_inv1_step:
  !h0 dom_frontiers pred_map live_in bbs h1.
    phi_extends bbs
      (insert_phis_for_var h0 dom_frontiers pred_map live_in bbs h1 []) /\
    (!j inst. j < LENGTH bbs /\
      MEM inst (EL j bbs).bb_instructions /\ inst.inst_opcode = PHI ==>
      !v. MEM v inst.inst_outputs ==> v <> h0 /\ ~MEM v (MAP FST defs)) /\
    ALL_DISTINCT (MAP FST defs) /\
    ~MEM h0 (MAP FST defs) ==>
    let acc = insert_phis_for_var h0 dom_frontiers pred_map live_in
               bbs h1 [] in
    !j inst. j < LENGTH bbs /\
      MEM inst (EL j acc).bb_instructions /\ inst.inst_opcode = PHI ==>
      !v. MEM v inst.inst_outputs ==> ~MEM v (MAP FST defs)
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  Cases_on `MEM inst (EL j bbs).bb_instructions`
  >- metis_tac[]
  >- (
    drule_all_then strip_assume_tac
      (Q.SPECL [`h0`,`dom_frontiers`,`pred_map`,`live_in`,
        `bbs`,`h1`,`[]`] insert_phis_for_var_phi_live_in) >>
    gvs[])
QED

Triviality insert_phis_inv2_step:
  !h0 dom_frontiers pred_map live_in bbs h1.
    phi_extends bbs
      (insert_phis_for_var h0 dom_frontiers pred_map live_in bbs h1 []) /\
    (!j inst. j < LENGTH bbs /\
      MEM inst (EL j bbs).bb_instructions /\ inst.inst_opcode = PHI ==>
      !v. MEM v inst.inst_outputs ==> v <> h0 /\ ~MEM v (MAP FST defs)) /\
    (!j inst1 inst2. j < LENGTH bbs /\
      MEM inst1 (EL j bbs).bb_instructions /\
      MEM inst2 (EL j bbs).bb_instructions /\
      inst1.inst_opcode = PHI /\ inst2.inst_opcode = PHI /\
      inst1.inst_outputs = inst2.inst_outputs ==> inst1 = inst2) ==>
    let acc = insert_phis_for_var h0 dom_frontiers pred_map live_in
               bbs h1 [] in
    !j inst1 inst2. j < LENGTH bbs /\
      MEM inst1 (EL j acc).bb_instructions /\
      MEM inst2 (EL j acc).bb_instructions /\
      inst1.inst_opcode = PHI /\ inst2.inst_opcode = PHI /\
      inst1.inst_outputs = inst2.inst_outputs ==> inst1 = inst2
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  Cases_on `MEM inst1 (EL j bbs).bb_instructions` >>
  Cases_on `MEM inst2 (EL j bbs).bb_instructions`
  >- metis_tac[]
  >- ( (* inst1 old, inst2 new *)
    mp_tac (Q.SPECL [`h0`,`dom_frontiers`,`pred_map`,`live_in`,
      `bbs`,`h1`,`[]`] insert_phis_for_var_phi_live_in) >>
    disch_then (qspec_then `j` mp_tac) >> simp[] >>
    disch_then (qspec_then `inst2` mp_tac) >> simp[] >>
    strip_tac >> (* inst2.inst_outputs = [h0] *)
    `MEM h0 inst1.inst_outputs` by gvs[] >>
    metis_tac[])
  >- ( (* inst1 new, inst2 old *)
    mp_tac (Q.SPECL [`h0`,`dom_frontiers`,`pred_map`,`live_in`,
      `bbs`,`h1`,`[]`] insert_phis_for_var_phi_live_in) >>
    disch_then (qspec_then `j` mp_tac) >> simp[] >>
    disch_then (qspec_then `inst1` mp_tac) >> simp[] >>
    strip_tac >> (* inst1.inst_outputs = [h0] *)
    `MEM h0 inst2.inst_outputs` by gvs[] >>
    metis_tac[])
  >- ( (* both new *)
    mp_tac (Q.SPECL [`h0`,`dom_frontiers`,`pred_map`,`live_in`,
      `bbs`,`h1`,`[]`] insert_phis_for_var_new_unique) >>
    disch_then (qspec_then `j` mp_tac) >> simp[])
QED

(* FOLDL induction: PHIs with same output at same block are equal *)
Triviality add_phi_nodes_phi_inj_aux:
  !defs dom_frontiers pred_map live_in bbs.
    ALL_DISTINCT (MAP FST defs) /\
    (* Inv1: existing PHI outputs disjoint from MAP FST defs *)
    (!j inst. j < LENGTH bbs /\
      MEM inst (EL j bbs).bb_instructions /\
      inst.inst_opcode = PHI ==>
      !v. MEM v inst.inst_outputs ==> ~MEM v (MAP FST defs)) /\
    (* Inv2: PHIs at same block with same output are equal *)
    (!j inst1 inst2. j < LENGTH bbs /\
      MEM inst1 (EL j bbs).bb_instructions /\
      MEM inst2 (EL j bbs).bb_instructions /\
      inst1.inst_opcode = PHI /\ inst2.inst_opcode = PHI /\
      inst1.inst_outputs = inst2.inst_outputs ==>
      inst1 = inst2) ==>
    let bbs1 = FOLDL (\acc (var,wl).
      insert_phis_for_var var dom_frontiers pred_map live_in acc wl [])
      bbs defs in
    !j inst1 inst2. j < LENGTH bbs /\
      MEM inst1 (EL j bbs1).bb_instructions /\
      MEM inst2 (EL j bbs1).bb_instructions /\
      inst1.inst_opcode = PHI /\ inst2.inst_opcode = PHI /\
      inst1.inst_outputs = inst2.inst_outputs ==>
      inst1 = inst2
Proof
  simp_tac std_ss [LET_THM] >>
  Induct >- simp[FOLDL] >>
  rpt gen_tac >> PairCases_on `h` >> simp[FOLDL] >> rpt strip_tac >>
  `phi_extends bbs
    (insert_phis_for_var h0 dom_frontiers pred_map live_in bbs h1 [])` by
    (irule insert_phis_for_var_phi_extends >> simp[phi_extends_refl]) >>
  `LENGTH (insert_phis_for_var h0 dom_frontiers pred_map live_in bbs h1
     []) = LENGTH bbs` by gvs[phi_extends_def] >>
  (* Inv1 + Inv2 via step lemmas *)
  mp_tac (Q.SPECL [`h0`,`dom_frontiers`,`pred_map`,`live_in`,`bbs`,`h1`]
    (INST_TYPE [``:'a`` |-> ``:string list``]
      (SIMP_RULE std_ss [LET_THM] insert_phis_inv1_step))) >>
  impl_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  mp_tac (Q.SPECL [`h0`,`dom_frontiers`,`pred_map`,`live_in`,`bbs`,`h1`]
    (INST_TYPE [``:'a`` |-> ``:string list``]
      (SIMP_RULE std_ss [LET_THM] insert_phis_inv2_step))) >>
  impl_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  (* Apply IH — rewrite LENGTH bbs to LENGTH acc for matching *)
  first_x_assum (qspecl_then
    [`dom_frontiers`,`pred_map`,`live_in`,
     `insert_phis_for_var h0 dom_frontiers pred_map live_in bbs h1 []`]
    mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
      (gvs[] >> first_assum ACCEPT_TAC))) >>
  strip_tac >> metis_tac[]
QED

(* process_frontiers: at each block, either unchanged or one PHI prepended *)
Triviality process_frontiers_at_most_one:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    !j. j < LENGTH bbs ==>
      (EL j bbs').bb_instructions = (EL j bbs).bb_instructions \/
      ((EL j bbs').bb_instructions =
        build_phi_inst var
          (case ALOOKUP pm (EL j bbs).bb_label of
             SOME ps => ps | NONE => []) ::
        (EL j bbs).bb_instructions /\
       MEM (EL j bbs).bb_label hp')
Proof
  Induct >> rw[process_frontiers_def]
  >- metis_tac[] >- metis_tac[]
  >> (
    qmatch_asmsub_abbrev_tac `process_frontiers _ _ _ bbs_map _ _ _` >>
    `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
    Cases_on `(EL j bbs).bb_label = h`
    >- ( (* j's label = h: modified by MAP, then preserved *)
      `EL j bbs_map = insert_phi_at_block
        (build_phi_inst var
          (case ALOOKUP pm h of SOME ps => ps | NONE => []))
        (EL j bbs)` by simp[Abbr `bbs_map`, EL_MAP] >>
      `(EL j bbs_map).bb_label = h` by
        simp[insert_phi_at_block_def] >>
      `MEM (EL j bbs_map).bb_label (h :: hp)` by simp[] >>
      imp_res_tac process_frontiers_hp_mono >>
      drule process_frontiers_has_phi_preserves >>
      disch_then drule >> disch_then drule >> strip_tac >>
      DISJ2_TAC >> gvs[insert_phi_at_block_def])
    >- ( (* j's label ≠ h: not modified by MAP, IH on recursion *)
      `EL j bbs_map = EL j bbs` by simp[Abbr `bbs_map`, EL_MAP] >>
      `(EL j bbs_map).bb_label = (EL j bbs).bb_label` by simp[] >>
      first_x_assum drule >> disch_then (qspec_then `j` mp_tac) >>
      simp[]))
QED

(* insert_phis_for_var: at each block, either unchanged or one PHI prepended *)
Triviality insert_phis_for_var_at_most_one:
  !var dom_frontiers pred_map live_in bbs wl hp.
    !j. j < LENGTH bbs ==>
      (EL j (insert_phis_for_var var dom_frontiers pred_map
        live_in bbs wl hp)).bb_instructions =
      (EL j bbs).bb_instructions \/
      ((EL j (insert_phis_for_var var dom_frontiers pred_map
        live_in bbs wl hp)).bb_instructions =
        build_phi_inst var
          (case ALOOKUP pred_map (EL j bbs).bb_label of
             SOME ps => ps | NONE => []) ::
        (EL j bbs).bb_instructions)
Proof
  ho_match_mp_tac insert_phis_for_var_ind >>
  rw[insert_phis_for_var_def] >>
  pairarg_tac >> gvs[] >>
  `j < LENGTH bbs'` by (
    imp_res_tac process_frontiers_labels >>
    qpat_x_assum `MAP _ bbs' = _` mp_tac >>
    simp[MAP_EQ_EVERY2, LIST_REL_EL_EQN]) >>
  `(EL j bbs').bb_label = (EL j bbs).bb_label` by (
    imp_res_tac process_frontiers_labels >>
    `EL j (MAP (\bb. bb.bb_label) bbs') =
     EL j (MAP (\bb. bb.bb_label) bbs)` by simp[] >>
    gvs[EL_MAP]) >>
  drule process_frontiers_at_most_one >>
  disch_then (qspec_then `j` mp_tac) >> simp[] >> strip_tac
  >- ( (* process_frontiers didn't modify j: IH *)
    first_x_assum (qspec_then `j` mp_tac) >> simp[])
  >- ( (* process_frontiers modified j: has_phi preserves *)
    `MEM (EL j bbs').bb_label has_phi'` by simp[] >>
    `(EL j (insert_phis_for_var var dom_frontiers pred_map
        live_in bbs' rest' has_phi')).bb_instructions =
     (EL j bbs').bb_instructions` by
      (irule insert_phis_for_var_has_phi_preserves >> simp[]) >>
    simp[])
QED

(* FOLDL invariant: PHI outputs are ALL_DISTINCT after add_phi_nodes *)
Triviality add_phi_nodes_phi_outputs_distinct_aux:
  !defs dom_frontiers pred_map live_in bbs.
    ALL_DISTINCT (MAP FST defs) /\
    (!j inst. j < LENGTH bbs /\
      MEM inst (EL j bbs).bb_instructions /\
      inst.inst_opcode = PHI ==>
      !v. MEM v inst.inst_outputs ==> ~MEM v (MAP FST defs)) /\
    (!j. j < LENGTH bbs ==>
      ALL_DISTINCT
        (FLAT (MAP (\i. i.inst_outputs)
          (FILTER (\i. i.inst_opcode = PHI)
            (EL j bbs).bb_instructions)))) ==>
    let bbs1 = FOLDL (\acc (var,wl).
      insert_phis_for_var var dom_frontiers pred_map live_in acc wl [])
      bbs defs in
    !j. j < LENGTH bbs ==>
      ALL_DISTINCT
        (FLAT (MAP (\i. i.inst_outputs)
          (FILTER (\i. i.inst_opcode = PHI)
            (EL j bbs1).bb_instructions)))
Proof
  simp_tac std_ss [LET_THM] >>
  Induct >- simp[FOLDL] >>
  rpt gen_tac >> PairCases_on `h` >> simp[FOLDL] >> rpt strip_tac >>
  `phi_extends bbs
    (insert_phis_for_var h0 dom_frontiers pred_map live_in bbs h1 [])` by
    (irule insert_phis_for_var_phi_extends >> simp[phi_extends_refl]) >>
  `LENGTH (insert_phis_for_var h0 dom_frontiers pred_map live_in bbs h1
     []) = LENGTH bbs` by gvs[phi_extends_def] >>
  (* Establish Inv1 for acc via step lemma *)
  mp_tac (Q.SPECL [`h0`,`dom_frontiers`,`pred_map`,`live_in`,`bbs`,`h1`]
    (INST_TYPE [``:'a`` |-> ``:string list``]
      (SIMP_RULE std_ss [LET_THM] insert_phis_inv1_step))) >>
  impl_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  (* Apply IH *)
  first_x_assum (qspecl_then
    [`dom_frontiers`,`pred_map`,`live_in`,
     `insert_phis_for_var h0 dom_frontiers pred_map live_in bbs h1 []`]
    mp_tac) >>
  impl_tac
  >- (
    CONJ_TAC >- gvs[] >>
    CONJ_TAC >- (gvs[] >> first_assum ACCEPT_TAC) >>
    gvs[] >> rpt strip_tac >>
    rename1 `jj < LENGTH bbs` >>
    (* Use at_most_one: acc_j = bbs_j or phi::bbs_j *)
    mp_tac (Q.SPECL [`h0`,`dom_frontiers`,`pred_map`,`live_in`,
      `bbs`,`h1`,`[]`] insert_phis_for_var_at_most_one) >>
    disch_then (qspec_then `jj` mp_tac) >> simp[] >> strip_tac
    >- simp[] (* unchanged: same as IH *)
    >- ( (* one PHI prepended with output [h0] *)
      simp[build_phi_inst_def, ALL_DISTINCT_APPEND,
        MEM_FLAT, MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
      rpt strip_tac >> metis_tac[]))
  >> strip_tac >> metis_tac[]
QED

Theorem phi_outputs_all_distinct:
  !dom_frontiers pred_map live_in bbs defs.
    ALL_DISTINCT (MAP FST defs) /\
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI) ==>
    let bbs1 = add_phi_nodes dom_frontiers pred_map live_in bbs defs in
    !lbl bb_mid.
      lookup_block lbl bbs1 = SOME bb_mid ==>
      ALL_DISTINCT
        (FLAT (MAP (\i. i.inst_outputs)
          (FILTER (\i. i.inst_opcode = PHI) bb_mid.bb_instructions)))
Proof
  simp_tac std_ss [LET_THM]
  \\ rpt strip_tac
  \\ gvs[lookup_block_def]
  \\ imp_res_tac FIND_MEM
  \\ imp_res_tac FIND_P >> gvs[]
  \\ `phi_extends bbs (add_phi_nodes dom_frontiers pred_map live_in bbs defs)`
       by simp[add_phi_nodes_phi_extends]
  \\ `LENGTH (add_phi_nodes dom_frontiers pred_map live_in bbs defs) =
       LENGTH bbs` by gvs[phi_extends_def]
  \\ `?j. j < LENGTH bbs /\
          EL j (add_phi_nodes dom_frontiers pred_map live_in bbs defs) = bb_mid`
       by metis_tac[MEM_EL]
  \\ mp_tac add_phi_nodes_phi_outputs_distinct_aux
  \\ disch_then (qspecl_then
       [`defs`,`dom_frontiers`,`pred_map`,`live_in`,`bbs`] mp_tac)
  \\ simp[add_phi_nodes_def]
  \\ impl_tac
  >- (
    CONJ_TAC
    >- (rpt strip_tac >> imp_res_tac EL_MEM >> res_tac)
    \\ rpt strip_tac
    \\ `FILTER (\i. i.inst_opcode = PHI) (EL j' bbs).bb_instructions = []`
         by (simp[FILTER_EQ_NIL, EVERY_MEM] >>
             rpt strip_tac >> imp_res_tac EL_MEM >> res_tac)
    \\ simp[])
  \\ disch_then (qspec_then `j` mp_tac) >> gvs[add_phi_nodes_def]
QED

(* ===== Obligation 3: PHI bases are live-in ===== *)

(* add_phi_nodes: every added PHI has var live-in at the block *)
Theorem add_phi_nodes_phi_live_in:
  !dom_frontiers pred_map live_in bbs defs.
    let bbs1 = add_phi_nodes dom_frontiers pred_map live_in bbs defs in
    !j. j < LENGTH bbs ==>
      !inst. MEM inst (EL j bbs1).bb_instructions /\
             ~MEM inst (EL j bbs).bb_instructions ==>
        inst.inst_opcode = PHI /\
        ?var vs. inst.inst_outputs = [var] /\
                 MEM var (MAP FST defs) /\
                 ALOOKUP live_in (EL j bbs).bb_label = SOME vs /\
                 MEM var vs
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >>
  qspec_tac (`bbs`, `acc`) >>
  Induct_on `defs` >> simp[add_phi_nodes_def, FOLDL] >>
  rpt gen_tac >> PairCases_on `h` >> simp[] >>
  rpt strip_tac >>
  qabbrev_tac `acc' =
    insert_phis_for_var h0 dom_frontiers pred_map live_in acc h1 []` >>
  `phi_extends acc acc'` by (
    simp[Abbr `acc'`] >>
    irule insert_phis_for_var_phi_extends >> simp[phi_extends_refl]) >>
  `j < LENGTH acc'` by gvs[phi_extends_def] >>
  `(EL j acc').bb_label = (EL j acc).bb_label`
    by metis_tac[phi_extends_label] >>
  Cases_on `MEM inst (EL j acc').bb_instructions` >>
  TRY (
    (* ~MEM case: inst from later FOLDL steps, use IH *)
    first_x_assum (qspec_then `acc'` mp_tac) >>
    simp[add_phi_nodes_def] >>
    disch_then drule >> strip_tac >> gvs[] >>
    qexists_tac `var` >> qexists_tac `vs` >> simp[] >> NO_TAC) >>
  (* MEM case: inst added by insert_phis_for_var h0 *)
  Cases_on `MEM inst (EL j acc).bb_instructions` >>
  TRY (gvs[] >> NO_TAC) >>  (* close MEM+~MEM contradiction goals *)
  mp_tac insert_phis_for_var_phi_live_in >>
  disch_then (qspecl_then
    [`h0`,`dom_frontiers`,`pred_map`,`live_in`,`acc`,`h1`,`[]`]
    mp_tac) >> simp[] >>
  disch_then (qspec_then `j` mp_tac) >> simp[] >>
  disch_then drule >> simp[Abbr `acc'`]
QED

(* rename_inst of PHI preserves output structure *)
Triviality rename_inst_phi_outputs_version_var:
  !rs inst var.
    inst.inst_opcode = PHI /\ inst.inst_outputs = [var] ==>
    ?ver. (SND (rename_inst rs inst)).inst_outputs = [version_var var ver]
Proof
  rw[rename_inst_def, rename_outputs_def, LET_THM] >>
  Cases_on `push_version rs var` >> gvs[] >>
  qexists_tac `r` >> simp[]
QED

(* For blocks inside the dom tree, instruction outputs in bbs2 come from
   rename_inst applied to the corresponding instruction in bbs1 *)
Triviality rename_blocks_inst_outputs:
  !dtree rs bbs succ_map.
    ALL_DISTINCT (dom_tree_labels dtree) /\
    (!l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs = SOME b) ==>
    !lbl bb2 k.
      lookup_block lbl (SND (rename_blocks rs bbs succ_map dtree)) = SOME bb2 /\
      MEM lbl (dom_tree_labels dtree) /\
      k < LENGTH bb2.bb_instructions ==>
      ?bb1 rs_k.
        lookup_block lbl bbs = SOME bb1 /\
        k < LENGTH bb1.bb_instructions /\
        (EL k bb2.bb_instructions).inst_outputs =
          (SND (rename_inst rs_k (EL k bb1.bb_instructions))).inst_outputs
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  (* Get rs_entry from block_rename_states *)
  `?rs_entry. ALOOKUP (block_rename_states rs bbs succ_map dtree) lbl =
     SOME rs_entry` by (
    `MAP FST (block_rename_states rs bbs succ_map dtree) =
       dom_tree_labels dtree` by
      (irule (CONJUNCT1 block_rename_states_keys) >> first_assum ACCEPT_TAC) >>
    Cases_on `ALOOKUP (block_rename_states rs bbs succ_map dtree) lbl` >>
    gvs[ALOOKUP_NONE]) >>
  `?bb1. lookup_block lbl bbs = SOME bb1` by metis_tac[] >>
  (* Apply rename_blocks_body_match *)
  drule_all (CONJUNCT1 rename_blocks_body_match) >> strip_tac >>
  `bb2 = bb'` by gvs[] >> gvs[] >>
  (* phi_refines gives output + length equality *)
  gvs[phi_refines_def, non_phi_refines_def] >>
  `k < LENGTH bb1.bb_instructions` by
    metis_tac[rename_block_insts_length] >>
  qexists_tac
    `FST (rename_block_insts rs_entry (TAKE k bb1.bb_instructions))` >>
  simp[] >>
  simp[rename_block_insts_el]
QED

(* Every dom_tree label has a block in bbs1 *)
Triviality dom_labels_have_blocks:
  !dom_frontiers dtree dom_post_order func bbs1.
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    wf_function func /\
    MAP (\bb. bb.bb_label) bbs1 = fn_labels func ==>
    !l. MEM l (dom_tree_labels dtree) ==>
        ?b. lookup_block l bbs1 = SOME b
Proof
  rpt strip_tac >>
  `MEM l (fn_labels func)` by (
    `set (dom_tree_labels dtree) = set (fn_labels func)` by
      gvs[valid_dom_tree_def] >> gvs[EXTENSION]) >>
  `MEM l (MAP (\bb. bb.bb_label) bbs1)` by
    gvs[fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
    gvs[wf_function_def, fn_labels_def] >>
  gvs[MEM_MAP] >>
  metis_tac[MEM_lookup_block]
QED

(* bbs1 labels = fn_labels func *)
Triviality bbs1_labels_eq:
  !dom_frontiers pred_map live_in func defs.
    MAP (\bb. bb.bb_label)
      (add_phi_nodes dom_frontiers pred_map live_in func.fn_blocks defs) =
    fn_labels func
Proof
  rpt strip_tac >> simp[fn_labels_def] >>
  `phi_extends func.fn_blocks
    (add_phi_nodes dom_frontiers pred_map live_in func.fn_blocks defs)` by
    simp[add_phi_nodes_phi_extends] >>
  gvs[phi_extends_def]
QED

(* bbs2 label in dom_tree_labels *)
Triviality bbs2_label_in_dtree:
  !dtree dom_frontiers dom_post_order func rs0 bbs1 succ_map lbl bb2.
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    wf_function func /\
    MAP (\bb. bb.bb_label) bbs1 = fn_labels func /\
    lookup_block lbl (SND (rename_blocks rs0 bbs1 succ_map dtree)) =
      SOME bb2 ==>
    MEM lbl (dom_tree_labels dtree)
Proof
  rpt strip_tac >>
  imp_res_tac lookup_block_MEM >>
  `bb2.bb_label = lbl` by (
    gvs[lookup_block_def] >> imp_res_tac FIND_P >> gvs[]) >>
  `MAP (\bb. bb.bb_label) (SND (rename_blocks rs0 bbs1 succ_map dtree)) =
   fn_labels func` by
    metis_tac[rename_blocks_preserves_labels] >>
  `MEM lbl (fn_labels func)` by (
    `MEM lbl (MAP (\bb. bb.bb_label)
      (SND (rename_blocks rs0 bbs1 succ_map dtree)))` suffices_by
      metis_tac[] >>
    simp[MEM_MAP] >> metis_tac[]) >>
  gvs[valid_dom_tree_def, EXTENSION]
QED

(* Helper: any PHI in bbs1 was added by add_phi_nodes (not original) *)
Triviality bbs1_phi_not_original:
  !func defs dom_frontiers pred_map live_in.
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI) ==>
    let bbs1 = add_phi_nodes dom_frontiers pred_map live_in
                 func.fn_blocks defs in
    !j inst. j < LENGTH func.fn_blocks /\
      MEM inst (EL j bbs1).bb_instructions /\
      inst.inst_opcode = PHI ==>
      ~MEM inst (EL j func.fn_blocks).bb_instructions
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  imp_res_tac EL_MEM >> res_tac
QED

Triviality ordered_bbs_colon_free:
  (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    EVERY colon_free inst.inst_outputs) ==>
  EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs)
         bb.bb_instructions)
    (MAP THE (FILTER IS_SOME
      (MAP (\l. lookup_block l bbs) post_order)))
Proof
  strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  gvs[MEM_MAP, MEM_FILTER, optionTheory.IS_SOME_EXISTS] >>
  imp_res_tac lookup_block_MEM >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  res_tac >> gvs[EVERY_MEM]
QED

Theorem phi_bases_live:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI /\
              EVERY colon_free inst.inst_outputs) ==>
    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    phi_bases_live_in live_in func'
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  (* Destructure dom tree for make_ssa_fn case split *)
  `?entry children. dtree = DNode entry children /\
    fn_entry_label func = SOME entry` by gvs[valid_dom_tree_def] >>
  (* Unfold make_ssa_fn, split the pair, unfold phi_bases_live_in *)
  gvs[make_ssa_fn_def] >>
  qabbrev_tac `ordered_bbs = MAP THE (FILTER IS_SOME
    (MAP (\l. lookup_block l func.fn_blocks) dom_post_order))` >>
  qabbrev_tac `defs = compute_defs ordered_bbs` >>
  qabbrev_tac `bbs1 = add_phi_nodes dom_frontiers pred_map live_in
    func.fn_blocks defs` >>
  qabbrev_tac `rs0 = init_rename_state defs` >>
  Cases_on `rename_blocks rs0 bbs1 succ_map (DNode entry children)` >>
  gvs[phi_bases_live_in_def] >> rpt strip_tac >>
  (* r = SND (rename_blocks ...) = bbs2 *)
  `r = SND (rename_blocks rs0 bbs1 succ_map (DNode entry children))`
    by gvs[] >>
  (* Use opcodes_preserved to get bbs1 block with same opcodes *)
  `opcodes_preserved bbs1 r` by
    metis_tac[rename_blocks_opcodes_preserved] >>
  gvs[opcodes_preserved_def] >>
  first_x_assum drule >> strip_tac >>
  rename1 `lookup_block lbl bbs1 = SOME bb1` >>
  (* Get MEM_EL index for bbs2 instruction *)
  `?k. k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst` by
    metis_tac[MEM_EL] >>
  (* bbs1 instruction at same position has same opcode *)
  `k < LENGTH bb1.bb_instructions` by gvs[] >>
  `(EL k bb1.bb_instructions).inst_opcode = PHI` by metis_tac[] >>
  (* bbs1 labels = fn_labels *)
  `MAP (\bb. bb.bb_label) bbs1 = fn_labels func` by
    simp[Abbr `bbs1`, bbs1_labels_eq] >>
  (* dom_tree labels have blocks in bbs1 *)
  `!l. MEM l (dom_tree_labels (DNode entry children)) ==>
       ?b. lookup_block l bbs1 = SOME b` by (
    rpt strip_tac >>
    `MEM l (fn_labels func)` by (
      `set (dom_tree_labels (DNode entry children)) =
       set (fn_labels func)` by gvs[valid_dom_tree_def] >>
      gvs[EXTENSION]) >>
    `MEM l (MAP (\bb. bb.bb_label) bbs1)` by gvs[fn_labels_def] >>
    `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
      gvs[wf_function_def, fn_labels_def] >>
    gvs[MEM_MAP] >> metis_tac[MEM_lookup_block]) >>
  (* lbl is in dom_tree_labels *)
  `MEM lbl (dom_tree_labels (DNode entry children))` by
    metis_tac[bbs2_label_in_dtree] >>
  `ALL_DISTINCT (dom_tree_labels (DNode entry children))` by
    gvs[valid_dom_tree_def] >>
  (* rename_blocks_inst_outputs: get bbs1 instruction outputs *)
  mp_tac rename_blocks_inst_outputs >>
  disch_then (qspecl_then
    [`DNode entry children`, `rs0`, `bbs1`, `succ_map`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`lbl`, `bb`, `k`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `rename_inst rs_k (EL k bb1.bb_instructions)` >>
  (* bbs1 PHI instruction was added by add_phi_nodes *)
  `phi_extends func.fn_blocks bbs1` by
    simp[Abbr `bbs1`, add_phi_nodes_phi_extends] >>
  `LENGTH bbs1 = LENGTH func.fn_blocks` by gvs[phi_extends_def] >>
  imp_res_tac lookup_block_MEM >>
  `?j. j < LENGTH bbs1 /\ EL j bbs1 = bb1` by metis_tac[MEM_EL] >>
  `j < LENGTH func.fn_blocks` by gvs[] >>
  (* The bbs1 PHI is not from original blocks *)
  `~MEM (EL k bb1.bb_instructions)
       (EL j func.fn_blocks).bb_instructions` by (
    spose_not_then ASSUME_TAC >>
    `MEM (EL j func.fn_blocks) func.fn_blocks` by
      metis_tac[EL_MEM] >>
    res_tac >> gvs[]) >>
  (* Use add_phi_nodes_phi_live_in to get var live-in *)
  mp_tac add_phi_nodes_phi_live_in >>
  disch_then (qspecl_then
    [`dom_frontiers`, `pred_map`, `live_in`,
     `func.fn_blocks`, `defs`] mp_tac) >>
  simp[LET_THM] >>
  disch_then (qspec_then `j` mp_tac) >> simp[] >>
  disch_then (qspec_then `EL k bb1.bb_instructions` mp_tac) >>
  impl_tac >- simp[EL_MEM] >> strip_tac >>
  (* Connect labels: (EL j func.fn_blocks).bb_label = lbl *)
  `(EL j bbs1).bb_label = (EL j func.fn_blocks).bb_label` by (
    `EL j (MAP (\bb. bb.bb_label) bbs1) =
     EL j (MAP (\bb. bb.bb_label) func.fn_blocks)` by
      gvs[fn_labels_def] >>
    gvs[EL_MAP]) >>
  `(EL j bbs1).bb_label = lbl` by (
    gvs[lookup_block_def] >> imp_res_tac FIND_P >> gvs[]) >>
  (* rename_inst_phi_outputs_version_var *)
  `?ver'. (SND (rename_inst rs_k (EL k bb1.bb_instructions))).inst_outputs =
    [version_var var ver']` by (
    irule rename_inst_phi_outputs_version_var >> simp[]) >>
  (* inst.inst_outputs = [version_var var ver'] *)
  `inst.inst_outputs = [version_var var ver']` by metis_tac[] >>
  (* Prove EVERY colon_free for ordered_bbs via lookup_block *)
  `EVERY (\bb. EVERY (\i. EVERY colon_free i.inst_outputs)
         bb.bb_instructions) ordered_bbs` by (
    gvs[Abbr `ordered_bbs`] >>
    irule ordered_bbs_colon_free >>
    rpt strip_tac >> res_tac >> gvs[]) >>
  `EVERY (\p. colon_free (FST p)) (compute_defs ordered_bbs)` by
    metis_tac[compute_defs_colon_free] >>
  `colon_free var` by (
    gvs[Abbr `defs`] >>
    fs[EVERY_MEM, MEM_MAP] >> res_tac >> gvs[]) >>
  `base' = var` by (
    `version_var base' ver = version_var var ver'` by gvs[] >>
    metis_tac[version_var_inj]) >>
  gvs[]
QED

(* ===== Helpers for phi_coverage and phi_operands ===== *)

(* General form: resolve_phi after update_phi_for_pred for the SAME label *)
Triviality resolve_phi_update_same_gen:
  !rs lbl ops.
    resolve_phi lbl (update_phi_for_pred rs lbl ops) =
    OPTION_MAP (renamed_operand (latest_version rs)) (resolve_phi lbl ops)
Proof
  ho_match_mp_tac update_phi_for_pred_ind >>
  rw[venomExecSemanticsTheory.resolve_phi_def,
     update_phi_for_pred_def, renamed_operand_def] >>
  Cases_on `x` >>
  rw[venomExecSemanticsTheory.resolve_phi_def, renamed_operand_def]
QED

(* Specialized: when resolve_phi gives Var v, update gives Var (latest_version rs v) *)
Triviality resolve_phi_update_same:
  !rs lbl ops v.
    resolve_phi lbl ops = SOME (Var v) ==>
    resolve_phi lbl (update_phi_for_pred rs lbl ops) =
      SOME (Var (latest_version rs v))
Proof
  rpt strip_tac >> simp[resolve_phi_update_same_gen, renamed_operand_def]
QED

(* resolve_phi after update_phi_for_pred for a DIFFERENT label *)
Triviality resolve_phi_update_other:
  !rs lbl ops lbl'.
    lbl' <> lbl ==>
    resolve_phi lbl' (update_phi_for_pred rs lbl ops) =
    resolve_phi lbl' ops
Proof
  ho_match_mp_tac update_phi_for_pred_ind >>
  rw[venomExecSemanticsTheory.resolve_phi_def,
     update_phi_for_pred_def] >>
  Cases_on `x` >>
  rw[venomExecSemanticsTheory.resolve_phi_def]
QED

(* ===== Helpers for phi_operands ===== *)

(* resolve_phi on build_phi_inst operands *)
Triviality resolve_phi_build_phi_inst:
  !pred_labels lbl var.
    MEM lbl pred_labels ==>
    resolve_phi lbl
      (FLAT (MAP (\l. [Label l; Var var]) pred_labels)) = SOME (Var var)
Proof
  Induct >> simp[venomExecSemanticsTheory.resolve_phi_def] >>
  rpt strip_tac >> gvs[]
QED

(* One step of update_succ_phis: resolve_phi for lbl' <> lbl is preserved.
   The one-step either leaves the block unchanged (h not found or lbl_s <> h)
   or applies update_phi_for_pred which preserves resolve_phi for other labels. *)
Triviality update_succ_phis_one_step_resolve_other:
  !rs lbl bbs h lbl_s bb lbl'.
    lbl' <> lbl /\
    lookup_block lbl_s bbs = SOME bb ==>
    ?bb1. lookup_block lbl_s
            (case lookup_block h bbs of
               NONE => bbs
             | SOME sbb => replace_block h
                 (sbb with bb_instructions :=
                   MAP (\inst. if inst.inst_opcode <> PHI then inst
                               else inst with inst_operands :=
                                 update_phi_for_pred rs lbl inst.inst_operands)
                   sbb.bb_instructions) bbs) = SOME bb1 /\
          LENGTH bb1.bb_instructions = LENGTH bb.bb_instructions /\
          (!j. j < LENGTH bb.bb_instructions ==>
               (EL j bb1.bb_instructions).inst_opcode =
               (EL j bb.bb_instructions).inst_opcode) /\
          (!j. j < LENGTH bb.bb_instructions /\
               (EL j bb.bb_instructions).inst_opcode = PHI ==>
               resolve_phi lbl' (EL j bb1.bb_instructions).inst_operands =
               resolve_phi lbl' (EL j bb.bb_instructions).inst_operands)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block h bbs`
  >- (qexists_tac `bb` >> simp[]) >>
  rename1 `lookup_block h bbs = SOME sbb` >>
  imp_res_tac lookup_block_label >>
  Cases_on `lbl_s = h`
  >- (
    gvs[] >>
    qexists_tac `bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else inst with inst_operands :=
                    update_phi_for_pred rs lbl inst.inst_operands)
      bb.bb_instructions` >>
    simp[lookup_block_replace_eq, EL_MAP] >>
    rpt strip_tac
    >- (COND_CASES_TAC >> simp[])
    >- gvs[resolve_phi_update_other])
  >>
  qexists_tac `bb` >> simp[lookup_block_replace_neq]
QED

(* update_succ_phis preserves resolve_phi for different labels *)
Triviality update_succ_phis_resolve_other:
  !succs rs lbl bbs lbl' lbl_s bb.
    lbl' <> lbl /\
    lookup_block lbl_s bbs = SOME bb ==>
    ?bb'. lookup_block lbl_s (update_succ_phis rs lbl bbs succs) = SOME bb' /\
          LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
          (!j. j < LENGTH bb.bb_instructions ==>
               (EL j bb'.bb_instructions).inst_opcode =
               (EL j bb.bb_instructions).inst_opcode) /\
          (!j. j < LENGTH bb.bb_instructions /\
               (EL j bb.bb_instructions).inst_opcode = PHI ==>
               resolve_phi lbl' (EL j bb'.bb_instructions).inst_operands =
               resolve_phi lbl' (EL j bb.bb_instructions).inst_operands)
Proof
  Induct_on `succs`
  >- simp[update_succ_phis_def, FOLDL]
  >>
  rpt gen_tac >> strip_tac >>
  simp[update_succ_phis_def, FOLDL, LET_THM] >>
  drule_all update_succ_phis_one_step_resolve_other >>
  disch_then (qspecl_then [`rs`, `h`] strip_assume_tac) >>
  rename1 `lookup_block lbl_s _ = SOME bb1` >>
  qmatch_asmsub_abbrev_tac `lookup_block lbl_s bbs1 = SOME bb1` >>
  first_x_assum (qspecl_then [`rs`, `lbl`, `bbs1`, `lbl'`, `lbl_s`, `bb1`]
    mp_tac) >>
  simp[Abbr `bbs1`, update_succ_phis_def] >> strip_tac >>
  qexists_tac `bb'` >> simp[]
QED

(* ===== Helpers for phi_operands: resolve_phi through rename_blocks ===== *)

(* PHI operands are preserved by rename_inst *)
Triviality rename_inst_phi_operands:
  !rs inst.
    inst.inst_opcode = PHI ==>
    (SND (rename_inst rs inst)).inst_operands = inst.inst_operands
Proof
  rw[rename_inst_def, LET_THM] >> pairarg_tac >> simp[]
QED

(* Block unchanged by update_succ_phis when not in succs *)
Triviality update_succ_phis_unchanged_block:
  !succs rs lbl bbs lbl_s bb.
    ~MEM lbl_s succs /\ lookup_block lbl_s bbs = SOME bb ==>
    lookup_block lbl_s (update_succ_phis rs lbl bbs succs) = SOME bb
Proof
  Induct_on `succs` >- simp[update_succ_phis_def, FOLDL] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC[update_succ_phis_def] >>
  PURE_REWRITE_TAC[FOLDL] >>
  ONCE_REWRITE_TAC[GSYM update_succ_phis_def] >>
  first_x_assum irule >> simp[LET_THM] >>
  Cases_on `lookup_block h bbs` >> simp[LET_THM] >>
  imp_res_tac lookup_block_label >>
  simp[lookup_block_replace_neq]
QED

(* Successor lists from bb_succs are ALL_DISTINCT (via nub) *)
Triviality bb_succs_all_distinct:
  !bb. ALL_DISTINCT (bb_succs bb)
Proof
  rw[bb_succs_def] >> CASE_TAC >> simp[all_distinct_nub]
QED

(* OPTION_MAP with idempotent function is idempotent *)
Triviality option_map_idempotent:
  !f (x : operand option).
    (!y. f (f y) = f y) ==>
    OPTION_MAP f (OPTION_MAP f x) = OPTION_MAP f x
Proof
  rpt strip_tac >> Cases_on `x` >> simp[]
QED

(* One-step: update at h for resolve_phi lbl (same label) *)
Triviality update_succ_phis_one_step_resolve_same:
  !rs lbl bbs h bb.
    lookup_block h bbs = SOME bb ==>
    ?bb1. lookup_block h
            (case lookup_block h bbs of
               NONE => bbs
             | SOME sbb => replace_block h
                 (sbb with bb_instructions :=
                   MAP (\inst. if inst.inst_opcode <> PHI then inst
                               else inst with inst_operands :=
                                 update_phi_for_pred rs lbl inst.inst_operands)
                   sbb.bb_instructions) bbs) = SOME bb1 /\
          LENGTH bb1.bb_instructions = LENGTH bb.bb_instructions /\
          (!j. j < LENGTH bb.bb_instructions ==>
               (EL j bb1.bb_instructions).inst_opcode =
               (EL j bb.bb_instructions).inst_opcode) /\
          (!j. j < LENGTH bb.bb_instructions /\
               (EL j bb.bb_instructions).inst_opcode = PHI ==>
               resolve_phi lbl (EL j bb1.bb_instructions).inst_operands =
                 OPTION_MAP (renamed_operand (latest_version rs))
                   (resolve_phi lbl (EL j bb.bb_instructions).inst_operands))
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  qexists_tac `bb with bb_instructions :=
    MAP (\inst. if inst.inst_opcode <> PHI then inst
                else inst with inst_operands :=
                  update_phi_for_pred rs lbl inst.inst_operands)
    bb.bb_instructions` >>
  imp_res_tac lookup_block_label >>
  simp[lookup_block_replace_eq, EL_MAP] >>
  rpt strip_tac
  >- (COND_CASES_TAC >> simp[])
  >- simp[resolve_phi_update_same_gen]
QED

(* Helper: FOLDL cons step for update_succ_phis *)
Triviality update_succ_phis_cons:
  !h succs rs lbl bbs.
    update_succ_phis rs lbl bbs (h::succs) =
    update_succ_phis rs lbl
      (case lookup_block h bbs of
         NONE => bbs
       | SOME sbb =>
           replace_block h
             (sbb with bb_instructions :=
               MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else inst with inst_operands :=
                      update_phi_for_pred rs lbl inst.inst_operands)
               sbb.bb_instructions) bbs)
      succs
Proof
  rpt gen_tac >>
  ONCE_REWRITE_TAC[update_succ_phis_def] >>
  PURE_REWRITE_TAC[FOLDL] >>
  ONCE_REWRITE_TAC[GSYM update_succ_phis_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> simp[LET_THM]
QED

(* update_succ_phis correctly sets resolve_phi for lbl when lbl_s in succs *)
Triviality update_succ_phis_resolve_same:
  !succs rs lbl bbs lbl_s bb.
    ALL_DISTINCT succs /\
    MEM lbl_s succs /\ lookup_block lbl_s bbs = SOME bb ==>
    ?bb'. lookup_block lbl_s (update_succ_phis rs lbl bbs succs) = SOME bb' /\
          LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
          (!j. j < LENGTH bb.bb_instructions ==>
               (EL j bb'.bb_instructions).inst_opcode =
               (EL j bb.bb_instructions).inst_opcode) /\
          (!j. j < LENGTH bb.bb_instructions /\
               (EL j bb.bb_instructions).inst_opcode = PHI ==>
               resolve_phi lbl (EL j bb'.bb_instructions).inst_operands =
                 OPTION_MAP (renamed_operand (latest_version rs))
                   (resolve_phi lbl (EL j bb.bb_instructions).inst_operands))
Proof
  Induct_on `succs` >- simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC[update_succ_phis_cons] >|
  [(* lbl_s = h: gvs[] substituted lbl_s := h *)
   imp_res_tac lookup_block_label >>
   qexists_tac `bb with bb_instructions :=
     MAP (\inst. if inst.inst_opcode <> PHI then inst
                 else inst with inst_operands :=
                   update_phi_for_pred rs lbl inst.inst_operands)
     bb.bb_instructions` >>
   conj_tac >- (
     irule update_succ_phis_unchanged_block >> simp[] >>
     simp[lookup_block_replace_eq]) >>
   simp[EL_MAP, resolve_phi_update_same_gen] >>
   rpt strip_tac >> COND_CASES_TAC >> simp[],
   (* MEM lbl_s succs *)
   first_x_assum irule >> simp[] >>
   Cases_on `lookup_block h bbs` >> simp[] >>
   imp_res_tac lookup_block_label >>
   `lbl_s <> h` by (strip_tac >> gvs[]) >>
   simp[lookup_block_replace_neq]]
QED

(* ===== rename_blocks preserves resolve_phi for external labels ===== *)

(* Key lemma: if lbl_a is NOT in the dom tree subtree being processed,
   then resolve_phi lbl_a at any block is preserved by rename_blocks. *)

(* Helper: if two block lists have the same labels, lookup existence is preserved *)
Triviality labels_eq_lookup_exists:
  !bbs1 bbs2 l b.
    MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) bbs2 /\
    lookup_block l bbs1 = SOME b ==>
    ?b'. lookup_block l bbs2 = SOME b'
Proof
  Induct >- simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `bbs2` >> gvs[] >>
  reverse (Cases_on `h.bb_label = l`)
  >- (gvs[lookup_block_def, FIND_thm] >>
      first_x_assum irule >> metis_tac[])
  >>
  gvs[] >> qexists_tac `h'` >> simp[lookup_block_def, FIND_thm]
QED

(* Extracted from rename_blocks_preserves_resolve_phi DNode case by block *)
Triviality replace_block_preserves_resolve_phi:
  !rs bbs s bb_s lbl_b bb_b lbl_a j rs1 insts'.
    rename_block_insts rs bb_s.bb_instructions = (rs1, insts') /\
    lookup_block s bbs = SOME bb_s /\
    lookup_block lbl_b bbs = SOME bb_b /\
    bb_s.bb_label = s /\ bb_b.bb_label = lbl_b /\
    j < LENGTH bb_b.bb_instructions /\
    (EL j bb_b.bb_instructions).inst_opcode = PHI ==>
    ?bb_b1.
      lookup_block lbl_b
        (replace_block s (bb_s with bb_instructions := insts') bbs) = SOME bb_b1 /\
      j < LENGTH bb_b1.bb_instructions /\
      (EL j bb_b1.bb_instructions).inst_opcode = PHI /\
      resolve_phi lbl_a (EL j bb_b1.bb_instructions).inst_operands =
        resolve_phi lbl_a (EL j bb_b.bb_instructions).inst_operands
Proof
  rpt strip_tac >>
  Cases_on `lbl_b = s`
  >- (
    gvs[] >>
    qexists_tac `bb_b with bb_instructions := insts'` >>
    `insts' = SND (rename_block_insts rs bb_b.bb_instructions)` by gvs[] >>
    pop_assum SUBST_ALL_TAC >>
    simp[lookup_block_replace_eq, rename_block_insts_length,
         rename_block_insts_opcodes] >>
    simp[Once rename_block_insts_el, rename_inst_phi_operands])
  >>
  qexists_tac `bb_b` >>
  simp[lookup_block_replace_neq]
QED

(* Step 3 helper: children labels have blocks after replace+update *)
Triviality children_blocks_after_update:
  !s children bbs rs1 insts' succs bb_s.
    lookup_block s bbs = SOME bb_s /\
    bb_s.bb_label = s /\
    (!l. MEM l (s :: FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs = SOME b) ==>
    !l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
        ?b. lookup_block l
              (update_succ_phis rs1 s
                (replace_block s (bb_s with bb_instructions := insts') bbs)
                succs) = SOME b
Proof
  rpt strip_tac >>
  irule labels_eq_lookup_exists >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac `replace_block s (bb_s with bb_instructions := insts') bbs` >>
  simp[update_succ_phis_preserves_labels] >>
  Cases_on `l = s` >> gvs[]
  >- simp[lookup_block_replace_eq]
  >- (simp[lookup_block_replace_neq] >>
      first_x_assum match_mp_tac >>
      simp[Once dom_tree_labels_def, ETA_THM])
QED

Triviality rename_blocks_lookup_exists:
  !rs bbs succ_map dtree l b.
    lookup_block l bbs = SOME b ==>
    ?b'. lookup_block l (SND (rename_blocks rs bbs succ_map dtree)) = SOME b'
Proof
  rpt strip_tac >>
  irule labels_eq_lookup_exists >>
  qexists_tac `b` >> qexists_tac `bbs` >>
  simp[rename_blocks_preserves_labels]
QED

Triviality rename_blocks_lookup_exists_pair:
  !rs bbs succ_map dtree l b ctrs' bbs'.
    lookup_block l bbs = SOME b /\
    rename_blocks rs bbs succ_map dtree = (ctrs', bbs') ==>
    ?b'. lookup_block l bbs' = SOME b'
Proof
  rpt strip_tac >>
  drule rename_blocks_lookup_exists >>
  disch_then (qspecl_then [`rs`, `succ_map`, `dtree`] mp_tac) >>
  simp[]
QED

Triviality rename_blocks_all_lookup_exists:
  !rs bbs succ_map dtree labels ctrs' bbs'.
    (!l. MEM l labels ==> ?b. lookup_block l bbs = SOME b) /\
    rename_blocks rs bbs succ_map dtree = (ctrs', bbs') ==>
    (!l. MEM l labels ==> ?b. lookup_block l bbs' = SOME b)
Proof
  rpt strip_tac >>
  `?b. lookup_block l bbs = SOME b` by metis_tac[] >>
  metis_tac[rename_blocks_lookup_exists_pair]
QED

Triviality rename_blocks_preserves_resolve_phi:
  (!dtree rs bbs succ_map lbl_a lbl_b bb_b j.
    ~MEM lbl_a (dom_tree_labels dtree) /\
    ALL_DISTINCT (dom_tree_labels dtree) /\
    (!l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs = SOME b) /\
    lookup_block lbl_b bbs = SOME bb_b /\
    j < LENGTH bb_b.bb_instructions /\
    (EL j bb_b.bb_instructions).inst_opcode = PHI ==>
    ?bb'. lookup_block lbl_b (SND (rename_blocks rs bbs succ_map dtree)) = SOME bb' /\
          j < LENGTH bb'.bb_instructions /\
          (EL j bb'.bb_instructions).inst_opcode = PHI /\
          resolve_phi lbl_a (EL j bb'.bb_instructions).inst_operands =
            resolve_phi lbl_a (EL j bb_b.bb_instructions).inst_operands) /\
  (!children ctrs stacks bbs succ_map lbl_a lbl_b bb_b j.
    ~MEM lbl_a (FLAT (MAP dom_tree_labels children)) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs = SOME b) /\
    lookup_block lbl_b bbs = SOME bb_b /\
    j < LENGTH bb_b.bb_instructions /\
    (EL j bb_b.bb_instructions).inst_opcode = PHI ==>
    ?bb'. lookup_block lbl_b
            (SND (rename_children ctrs stacks bbs succ_map children)) = SOME bb' /\
          j < LENGTH bb'.bb_instructions /\
          (EL j bb'.bb_instructions).inst_opcode = PHI /\
          resolve_phi lbl_a (EL j bb'.bb_instructions).inst_operands =
            resolve_phi lbl_a (EL j bb_b.bb_instructions).inst_operands)
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac
  (* DNode s children *)
  >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qpat_x_assum `~MEM lbl_a _` mp_tac >>
    simp[Once dom_tree_labels_def, ETA_THM] >> strip_tac >>
    simp[Once rename_blocks_def, LET_THM] >>
    Cases_on `lookup_block s bbs` >- (
      (* NONE: bbs unchanged *)
      first_x_assum (qspecl_then [`(FST rs)`, `(SND rs)`, `bbs`, `succ_map`,
        `lbl_a`, `lbl_b`, `bb_b`, `j`] mp_tac) >>
      simp[]) >>
    rename1 `lookup_block s bbs = SOME bb_s` >>
    Cases_on `rename_block_insts rs bb_s.bb_instructions` >>
    rename1 `rename_block_insts rs _ = (rs1, insts')` >> simp[] >>
    imp_res_tac lookup_block_label >>
    qabbrev_tac `succs = case ALOOKUP succ_map s of NONE => [] | SOME ss => ss` >>
    (* Step 1: replace_block preserves resolve_phi *)
    mp_tac (Q.SPECL [`rs`, `bbs`, `s`, `bb_s`, `lbl_b`, `bb_b`, `lbl_a`,
                      `j`, `rs1`, `insts'`]
            replace_block_preserves_resolve_phi) >>
    simp[] >> strip_tac >>
    rename1 `lookup_block lbl_b _ = SOME bb_b1` >>
    (* Step 2: update_succ_phis preserves resolve_phi for lbl_a ≠ s *)
    drule_all update_succ_phis_resolve_other >>
    disch_then (qspecl_then [`succs`, `rs1`] strip_assume_tac) >>
    rename1 `lookup_block lbl_b _ = SOME bb_b2` >>
    (* Step 3: all children labels have blocks in updated bbs *)
    `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l
               (update_succ_phis rs1 s
                 (replace_block s (bb_s with bb_instructions := insts') bbs)
                 succs) = SOME b` by (
      rpt strip_tac >>
      irule labels_eq_lookup_exists >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac `replace_block s (bb_s with bb_instructions := insts') bbs` >>
      simp[update_succ_phis_preserves_labels] >>
      Cases_on `l = s` >> gvs[]
      >- simp[lookup_block_replace_eq]
      >- (simp[lookup_block_replace_neq] >>
          first_x_assum match_mp_tac >>
          simp[Once dom_tree_labels_def, ETA_THM])) >>
    (* Step 4: apply children IH *)
    first_x_assum (qspecl_then [`(FST rs1)`, `(SND rs1)`,
      `update_succ_phis rs1 s
         (replace_block s (bb_s with bb_instructions := insts') bbs)
         succs`,
      `succ_map`, `lbl_a`, `lbl_b`, `bb_b2`, `j`] mp_tac) >>
    `ALL_DISTINCT (FLAT (MAP dom_tree_labels children))` by (
      qpat_x_assum `ALL_DISTINCT (dom_tree_labels _)` mp_tac >>
      simp[Once dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND]) >>
    simp[] >> strip_tac >>
    qexists_tac `bb'` >> simp[] >> gvs[])
  (* nil *)
  >- simp[Once rename_blocks_def]
  (* cons *)
  >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    simp[Once rename_blocks_def, LET_THM] >>
    Cases_on `rename_blocks (ctrs,stacks) bbs succ_map dtree` >>
    rename1 `rename_blocks _ bbs _ dtree = (ctrs', bbs')` >> simp[] >>
    (* Side conditions for DNode IH *)
    `~MEM lbl_a (dom_tree_labels dtree)` by (
      qpat_x_assum `~MEM lbl_a _` mp_tac >> simp[ETA_THM]) >>
    `ALL_DISTINCT (dom_tree_labels dtree)` by (
      qpat_x_assum `ALL_DISTINCT _` mp_tac >>
      simp[ALL_DISTINCT_APPEND, ETA_THM]) >>
    `!l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs = SOME b` by (
      rpt strip_tac >> first_x_assum match_mp_tac >> simp[ETA_THM]) >>
    (* Apply DNode IH *)
    first_x_assum (qspecl_then [`(ctrs,stacks)`, `bbs`, `succ_map`,
      `lbl_a`, `lbl_b`, `bb_b`, `j`] mp_tac) >>
    simp[] >> disch_then strip_assume_tac >>
    rename1 `lookup_block lbl_b bbs' = SOME bb_mid` >>
    (* Side conditions for children IH *)
    `~MEM lbl_a (FLAT (MAP dom_tree_labels children))` by (
      qpat_x_assum `~MEM lbl_a (FLAT (MAP dom_tree_labels (_ :: _)))` mp_tac >>
      simp[ETA_THM]) >>
    `ALL_DISTINCT (FLAT (MAP dom_tree_labels children))` by (
      qpat_x_assum `ALL_DISTINCT (FLAT (MAP dom_tree_labels (_ :: _)))` mp_tac >>
      simp[ALL_DISTINCT_APPEND, ETA_THM]) >>
    `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs' = SOME b` by (
      rpt strip_tac >>
      `?b. lookup_block l bbs = SOME b` by (
        qpat_x_assum `!l. MEM l (FLAT (MAP dom_tree_labels (_ :: _))) ==> _`
          (fn th => irule th) >> simp[ETA_THM]) >>
      pop_assum strip_assume_tac >>
      drule rename_blocks_lookup_exists >>
      disch_then (qspecl_then [`(ctrs,stacks)`, `succ_map`, `dtree`] mp_tac) >>
      simp[]) >>
    (* Apply children IH — simp resolves antecedent + transitivity *)
    last_x_assum (qspecl_then [`ctrs'`, `stacks`, `bbs'`, `succ_map`,
      `lbl_a`, `lbl_b`, `bb_mid`, `j`] mp_tac) >>
    simp[])
QED

(* ALOOKUP block_rename_states at root always returns the initial rs *)
Triviality block_rename_states_root_alookup:
  !rs bbs succ_map lbl children.
    ALOOKUP (block_rename_states rs bbs succ_map (DNode lbl children)) lbl =
    SOME rs
Proof
  rpt gen_tac >> ONCE_REWRITE_TAC[block_rename_states_def] >>
  Cases_on `lookup_block lbl bbs` >> simp[pairTheory.UNCURRY]
QED

Triviality bbs_outputs_agree_rename_blocks:
  !dtree rs bbs succ_map labels.
    (!l. MEM l labels ==> ~MEM l (dom_tree_labels dtree)) /\
    (!l. MEM l labels ==> ?b. lookup_block l bbs = SOME b) ==>
    bbs_outputs_agree labels bbs (SND (rename_blocks rs bbs succ_map dtree))
Proof
  rpt strip_tac >> simp[bbs_outputs_agree_def] >>
  rpt conj_tac >> rpt strip_tac
  >- metis_tac[rename_blocks_lookup_exists]
  >> (`~MEM l (dom_tree_labels dtree)` by res_tac >>
      mp_tac (CONJUNCT1 rename_blocks_preserves_outside) >>
      disch_then (qspecl_then [`dtree`, `rs`, `bbs`, `succ_map`, `l`, `b1`]
        mp_tac) >>
      simp[])
QED

(* ===== Helper: rename_blocks UPDATES resolve_phi for blocks IN the tree ===== *)
(* Complementary to rename_blocks_preserves_resolve_phi (which handles NOT IN) *)
Triviality rename_blocks_updates_resolve_phi:
  (!dtree rs bbs succ_map lbl_a bb_a lbl_b bb_b j rs_a_entry.
    MEM lbl_a (dom_tree_labels dtree) /\
    ALL_DISTINCT (dom_tree_labels dtree) /\
    (!l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs = SOME b) /\
    lookup_block lbl_a bbs = SOME bb_a /\
    ALOOKUP (block_rename_states rs bbs succ_map dtree) lbl_a = SOME rs_a_entry /\
    MEM lbl_b (case ALOOKUP succ_map lbl_a of NONE => [] | SOME ss => ss) /\
    ALL_DISTINCT (case ALOOKUP succ_map lbl_a of NONE => [] | SOME ss => ss) /\
    lookup_block lbl_b bbs = SOME bb_b /\
    j < LENGTH bb_b.bb_instructions /\
    (EL j bb_b.bb_instructions).inst_opcode = PHI ==>
    ?bb'.
      lookup_block lbl_b (SND (rename_blocks rs bbs succ_map dtree)) = SOME bb' /\
      j < LENGTH bb'.bb_instructions /\
      (EL j bb'.bb_instructions).inst_opcode = PHI /\
      resolve_phi lbl_a (EL j bb'.bb_instructions).inst_operands =
        OPTION_MAP (renamed_operand (latest_version
          (FST (rename_block_insts rs_a_entry bb_a.bb_instructions))))
          (resolve_phi lbl_a (EL j bb_b.bb_instructions).inst_operands)) /\
  (!children ctrs stacks bbs succ_map lbl_a bb_a lbl_b bb_b j rs_a_entry.
    MEM lbl_a (FLAT (MAP dom_tree_labels children)) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs = SOME b) /\
    lookup_block lbl_a bbs = SOME bb_a /\
    ALOOKUP (children_rename_states ctrs stacks bbs succ_map children)
      lbl_a = SOME rs_a_entry /\
    MEM lbl_b (case ALOOKUP succ_map lbl_a of NONE => [] | SOME ss => ss) /\
    ALL_DISTINCT (case ALOOKUP succ_map lbl_a of NONE => [] | SOME ss => ss) /\
    lookup_block lbl_b bbs = SOME bb_b /\
    j < LENGTH bb_b.bb_instructions /\
    (EL j bb_b.bb_instructions).inst_opcode = PHI ==>
    ?bb'.
      lookup_block lbl_b
        (SND (rename_children ctrs stacks bbs succ_map children)) = SOME bb' /\
      j < LENGTH bb'.bb_instructions /\
      (EL j bb'.bb_instructions).inst_opcode = PHI /\
      resolve_phi lbl_a (EL j bb'.bb_instructions).inst_operands =
        OPTION_MAP (renamed_operand (latest_version
          (FST (rename_block_insts rs_a_entry bb_a.bb_instructions))))
          (resolve_phi lbl_a (EL j bb_b.bb_instructions).inst_operands))
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac
  (* DNode s children *)
  >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qpat_x_assum `MEM lbl_a _` mp_tac >>
    simp[Once dom_tree_labels_def, ETA_THM] >> strip_tac
    (* Sub-case: lbl_a = s *)
    >- (
      pop_assum SUBST_ALL_TAC >>
      imp_res_tac lookup_block_label >>
      (* Unfold rename_blocks *)
      simp[Once rename_blocks_def, LET_THM] >>
      Cases_on `rename_block_insts rs bb_a.bb_instructions` >>
      rename1 `rename_block_insts rs bb_a.bb_instructions = (rs1, insts')` >>
      simp[] >>
      qabbrev_tac `succs = case ALOOKUP succ_map s of NONE => [] | SOME ss => ss` >>
      (* Step 1: replace_block preserves resolve_phi *)
      mp_tac (Q.SPECL [`rs`, `bbs`, `s`, `bb_a`, `lbl_b`, `bb_b`, `s`,
                        `j`, `rs1`, `insts'`]
              replace_block_preserves_resolve_phi) >>
      simp[] >> strip_tac >>
      rename1 `lookup_block lbl_b _ = SOME bb_b1` >>
      (* Step 2: update_succ_phis updates operands for pred s *)
      drule_all update_succ_phis_resolve_same >>
      disch_then (qspecl_then [`rs1`, `s`] strip_assume_tac) >>
      rename1 `lookup_block lbl_b (update_succ_phis _ _ _ _) = SOME bb_b2` >>
      (* Step 3: rename_children preserves (s NOT in children) *)
      qpat_x_assum `ALL_DISTINCT (dom_tree_labels _)` mp_tac >>
      simp[Once dom_tree_labels_def, ETA_THM] >> strip_tac >>
      `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
           ?b. lookup_block l
                 (update_succ_phis rs1 s
                   (replace_block s (bb_a with bb_instructions := insts') bbs)
                   succs) = SOME b` by (
        rpt strip_tac >>
        `?b. lookup_block l bbs = SOME b` by (
          first_x_assum match_mp_tac >>
          simp[Once dom_tree_labels_def, ETA_THM]) >>
        irule labels_eq_lookup_exists >>
        qexists_tac `b` >> qexists_tac `bbs` >>
        simp[update_succ_phis_preserves_labels,
             replace_block_preserves_labels]) >>
      (* rename_children preserves resolve_phi since s NOT in children *)
      mp_tac (CONJUNCT2 rename_blocks_preserves_resolve_phi) >>
      disch_then (qspecl_then [`children`, `FST rs1`, `SND rs1`,
        `update_succ_phis rs1 s
           (replace_block s (bb_a with bb_instructions := insts') bbs)
           succs`,
        `succ_map`, `s`, `lbl_b`, `bb_b2`, `j`] mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac `bb'` >> simp[] >>
      (* Resolve rs_a_entry = rs *)
      gvs[block_rename_states_root_alookup])
    (* Sub-case: MEM lbl_a (FLAT (MAP dom_tree_labels children)) *)
    >- (
      (* Get lookup_block s bbs *)
      `?bb_s. lookup_block s bbs = SOME bb_s` by (
        first_x_assum match_mp_tac >>
        simp[Once dom_tree_labels_def, ETA_THM]) >>
      imp_res_tac lookup_block_label >>
      simp[Once rename_blocks_def, LET_THM] >>
      Cases_on `rename_block_insts rs bb_s.bb_instructions` >>
      rename1 `rename_block_insts rs _ = (rs1, insts')` >> simp[] >>
      qabbrev_tac `succs = case ALOOKUP succ_map s of NONE => [] | SOME ss => ss` >>
      (* lbl_a <> s (ALL_DISTINCT) *)
      `lbl_a <> s` by (
        qpat_x_assum `ALL_DISTINCT (dom_tree_labels _)` mp_tac >>
        simp[Once dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND] >>
        metis_tac[]) >>
      (* Step 1: replace_block preserves resolve_phi *)
      mp_tac (Q.SPECL [`rs`, `bbs`, `s`, `bb_s`, `lbl_b`, `bb_b`, `lbl_a`,
                        `j`, `rs1`, `insts'`]
              replace_block_preserves_resolve_phi) >>
      simp[] >> strip_tac >>
      rename1 `lookup_block lbl_b _ = SOME bb_b1` >>
      (* Step 2: update_succ_phis preserves for lbl_a <> s *)
      drule_all update_succ_phis_resolve_other >>
      disch_then (qspecl_then [`succs`, `rs1`] strip_assume_tac) >>
      rename1 `lookup_block lbl_b (update_succ_phis _ _ _ _) = SOME bb_b2` >>
      (* ALOOKUP children_rename_states = rs_a_entry *)
      qpat_x_assum `ALOOKUP _ lbl_a = SOME rs_a_entry` mp_tac >>
      simp[Once block_rename_states_def, LET_THM] >>
      strip_tac >>
      (* Bridge: bbs_outputs_agree for children_rename_states *)
      `ALL_DISTINCT (FLAT (MAP dom_tree_labels children))` by (
        qpat_x_assum `ALL_DISTINCT (dom_tree_labels _)` mp_tac >>
        simp[Once dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND]) >>
      `~MEM s (FLAT (MAP dom_tree_labels children))` by (
        qpat_x_assum `ALL_DISTINCT (dom_tree_labels _)` mp_tac >>
        simp[Once dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND]) >>
      qabbrev_tac `bbs2 = update_succ_phis rs1 s
        (replace_block s (bb_s with bb_instructions := insts') bbs) succs` >>
      `bbs_outputs_agree (FLAT (MAP dom_tree_labels children)) bbs bbs2` by (
        simp[Abbr `bbs2`] >>
        irule bbs_outputs_agree_replace_update_refl >> simp[]) >>
      `children_rename_states (FST rs1) (SND rs1) bbs succ_map children =
       children_rename_states (FST rs1) (SND rs1) bbs2 succ_map children` by (
        irule (CONJUNCT2 block_rename_states_outputs_agree) >> simp[]) >>
      (* lookup_block lbl_a in bbs2 *)
      `?bb_a2. lookup_block lbl_a bbs2 = SOME bb_a2` by (
        `?b. lookup_block lbl_a bbs = SOME b` by (
          first_x_assum match_mp_tac >>
          simp[Once dom_tree_labels_def, ETA_THM]) >>
        irule labels_eq_lookup_exists >>
        qexists_tac `b` >> qexists_tac `bbs` >>
        simp[Abbr `bbs2`, update_succ_phis_preserves_labels,
             replace_block_preserves_labels]) >>
      (* blocks exist in bbs2 for children *)
      `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
           ?b. lookup_block l bbs2 = SOME b` by (
        rpt strip_tac >>
        simp[Abbr `bbs2`] >>
        irule (SPEC_ALL children_blocks_after_update) >>
        simp[] >> qexists_tac `children` >> simp[] >>
        simp[Once dom_tree_labels_def, ETA_THM]) >>
      (* Apply children IH with bbs2 *)
      first_x_assum (qspecl_then [`(FST rs1)`, `(SND rs1)`, `bbs2`,
        `succ_map`, `lbl_a`, `bb_a2`, `lbl_b`, `bb_b2`, `j`,
        `rs_a_entry`] mp_tac) >>
      simp[] >>
      impl_tac >- gvs[] >>
      strip_tac >>
      qexists_tac `bb'` >> simp[] >>
      (* Bridge: FST(rename_block_insts) uses outputs only *)
      `FST (rename_block_insts rs_a_entry bb_a2.bb_instructions) =
       FST (rename_block_insts rs_a_entry bb_a.bb_instructions)` by (
        irule rename_block_insts_fst_outputs_only >>
        fs[bbs_outputs_agree_def] >>
        first_x_assum (qspecl_then [`lbl_a`, `bb_a`, `bb_a2`] mp_tac) >>
        simp[]) >>
      gvs[]))
  (* nil *)
  >- simp[Once rename_blocks_def]
  (* cons *)
  >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    simp[Once (CONJUNCT2 (CONJUNCT2 rename_blocks_def)), LET_THM] >>
    Cases_on `rename_blocks (ctrs,stacks) bbs succ_map dtree` >>
    rename1 `rename_blocks _ bbs _ dtree = (ctrs', bbs')` >> simp[] >>
    qpat_x_assum `MEM lbl_a _` mp_tac >>
    simp[ETA_THM] >> strip_tac >| [
    (* dtree case: apply IH then preserve through rename_children *)
    `ALL_DISTINCT (dom_tree_labels dtree)` by (
      qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >>
      simp[ALL_DISTINCT_APPEND, ETA_THM]) >>
    `ALL_DISTINCT (FLAT (MAP dom_tree_labels children))` by (
      qpat_x_assum `ALL_DISTINCT (FLAT (MAP dom_tree_labels (_ :: _)))` mp_tac >>
      simp[ALL_DISTINCT_APPEND, ETA_THM]) >>
    `~MEM lbl_a (FLAT (MAP dom_tree_labels children))` by (
      qpat_x_assum `ALL_DISTINCT (FLAT (MAP dom_tree_labels (_ :: _)))` mp_tac >>
      simp[ALL_DISTINCT_APPEND, ETA_THM] >> metis_tac[]) >>
    `!l. MEM l (dom_tree_labels dtree) ==>
         ?b. lookup_block l bbs = SOME b` by (
      rpt strip_tac >> first_x_assum match_mp_tac >>
      simp[ETA_THM]) >>
    qpat_x_assum `ALOOKUP _ lbl_a = SOME rs_a_entry` mp_tac >>
    simp[Once (CONJUNCT2 (CONJUNCT2 block_rename_states_def)), LET_THM] >>
    `MAP FST (children_rename_states ctrs' stacks bbs succ_map children)
       = FLAT (MAP dom_tree_labels children)` by (
      irule (CONJUNCT2 block_rename_states_keys) >>
      rpt gen_tac >> strip_tac >>
      last_x_assum match_mp_tac >> simp[ETA_THM]) >>
    `ALOOKUP (children_rename_states ctrs' stacks bbs succ_map children)
       lbl_a = NONE` by metis_tac[ALOOKUP_NONE] >>
    simp[ALOOKUP_APPEND] >>
    Cases_on `ALOOKUP (block_rename_states (ctrs,stacks) bbs succ_map dtree) lbl_a` >> simp[] >>
    strip_tac >>
    (* Apply dtree IH *)
    first_x_assum (qspecl_then [`(ctrs,stacks)`, `bbs`, `succ_map`,
      `lbl_a`, `bb_a`, `lbl_b`, `bb_b`, `j`, `rs_a_entry`] mp_tac) >>
    simp[] >> disch_then strip_assume_tac >>
    (* rename_children preserves since lbl_a NOT in children *)
    `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs' = SOME b` by (
      rpt strip_tac >>
      `?b0. lookup_block l bbs = SOME b0` by (
        last_assum (qspec_then `l` mp_tac) >>
        simp[ETA_THM]) >>
      drule rename_blocks_lookup_exists >>
      disch_then (qspecl_then [`(ctrs,stacks)`, `succ_map`, `dtree`]
        mp_tac) >> simp[]) >>
    mp_tac (CONJUNCT2 rename_blocks_preserves_resolve_phi) >>
    disch_then (qspecl_then [`children`, `ctrs'`, `stacks`, `bbs'`,
      `succ_map`, `lbl_a`, `lbl_b`, `bb'`, `j`] mp_tac) >>
    simp[] >> disch_then strip_assume_tac >>
    qexists_tac `bb''` >> gvs[],
    (* children case: MEM lbl_a (FLAT (MAP dom_tree_labels children)) *)
    `ALL_DISTINCT (dom_tree_labels dtree)` by (
      qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >>
      simp[ALL_DISTINCT_APPEND, ETA_THM]) >>
    `~MEM lbl_a (dom_tree_labels dtree)` by (
      qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >>
      simp[ALL_DISTINCT_APPEND, ETA_THM] >> metis_tac[]) >>
    `ALL_DISTINCT (FLAT (MAP dom_tree_labels children))` by (
      qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >>
      simp[ALL_DISTINCT_APPEND, ETA_THM]) >>
    `!l. MEM l (dom_tree_labels dtree) ==>
         ?b. lookup_block l bbs = SOME b` by (
      rpt strip_tac >>
      qpat_assum `!l. MEM l (FLAT (MAP dom_tree_labels (_ :: _))) ==> _`
        match_mp_tac >> simp[ETA_THM]) >>
    `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs = SOME b` by (
      rpt strip_tac >>
      qpat_assum `!l. MEM l (FLAT (MAP dom_tree_labels (_ :: _))) ==> _`
        match_mp_tac >> simp[ETA_THM]) >>
    (* rename_blocks preserves resolve_phi for lbl_a NOT in dtree *)
    mp_tac (CONJUNCT1 rename_blocks_preserves_resolve_phi) >>
    disch_then (qspecl_then [`dtree`, `(ctrs,stacks)`, `bbs`,
      `succ_map`, `lbl_a`, `lbl_b`, `bb_b`, `j`] mp_tac) >>
    simp[] >> strip_tac >>
    (* ALOOKUP: unfold cons, skip dtree part, get from children *)
    qpat_x_assum `ALOOKUP _ lbl_a = SOME rs_a_entry` mp_tac >>
    simp[Once (CONJUNCT2 (CONJUNCT2 block_rename_states_def)), LET_THM] >>
    `ALOOKUP (block_rename_states (ctrs,stacks) bbs succ_map dtree)
       lbl_a = NONE` by (
      `MAP FST (block_rename_states (ctrs,stacks) bbs succ_map dtree)
       = dom_tree_labels dtree` by (
        irule (CONJUNCT1 block_rename_states_keys) >>
        rpt strip_tac >>
        qpat_assum `!l. MEM l (dom_tree_labels dtree) ==> _`
          match_mp_tac >> first_assum ACCEPT_TAC) >>
      metis_tac[ALOOKUP_NONE]) >>
    simp[ALOOKUP_APPEND] >> strip_tac >>
    (* Bridge: bbs_outputs_agree + children_rename_states bbs = bbs' *)
    mp_tac (Q.SPECL [`dtree`, `(ctrs,stacks)`, `bbs`, `succ_map`,
      `FLAT (MAP dom_tree_labels children)`] bbs_outputs_agree_rename_blocks) >>
    impl_tac >- (
      conj_tac >> rpt strip_tac
      >- (qpat_x_assum `ALL_DISTINCT (FLAT (MAP dom_tree_labels (_ :: _)))` mp_tac >>
          simp[ALL_DISTINCT_APPEND, ETA_THM] >> metis_tac[])
      >- metis_tac[]) >>
    simp[] >> strip_tac >>
    `children_rename_states ctrs' stacks bbs succ_map children =
     children_rename_states ctrs' stacks bbs' succ_map children` by (
      irule (CONJUNCT2 block_rename_states_outputs_agree) >> simp[]) >>
    `ALOOKUP (children_rename_states ctrs' stacks bbs' succ_map children)
       lbl_a = SOME rs_a_entry` by (
      qpat_x_assum `children_rename_states _ _ bbs _ _ = _`
        (fn th => REWRITE_TAC[GSYM th]) >>
      first_assum ACCEPT_TAC) >>
    `?bb_a'. lookup_block lbl_a bbs' = SOME bb_a'` by (
      mp_tac (Q.SPECL [`(ctrs,stacks)`, `bbs`, `succ_map`, `dtree`,
        `lbl_a`, `bb_a`] rename_blocks_lookup_exists) >> simp[]) >>
    `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs' = SOME b` by (
      rpt strip_tac >>
      `?b0. lookup_block l bbs = SOME b0` by (
        first_assum match_mp_tac >> first_assum ACCEPT_TAC) >>
      drule rename_blocks_lookup_exists >>
      disch_then (qspecl_then [`(ctrs,stacks)`, `succ_map`, `dtree`]
        mp_tac) >> simp[]) >>
    (* Apply children IH with bbs' *)
    last_x_assum (qspecl_then [`ctrs'`, `stacks`, `bbs'`, `succ_map`,
      `lbl_a`, `bb_a'`, `lbl_b`, `bb'`, `j`,
      `rs_a_entry`] mp_tac) >>
    simp[] >> disch_then strip_assume_tac >>
    qexists_tac `bb''` >> gvs[] >>
    (* Bridge: bb_a' outputs agree with bb_a, so rename state is same *)
    `FST (rename_block_insts rs_a_entry bb_a'.bb_instructions) =
     FST (rename_block_insts rs_a_entry bb_a.bb_instructions)` by (
      irule rename_block_insts_fst_outputs_only >>
      qpat_x_assum `bbs_outputs_agree _ _ _`
        (mp_tac o REWRITE_RULE [bbs_outputs_agree_def]) >>
      strip_tac >>
      pop_assum (qspecl_then [`lbl_a`, `bb_a`, `bb_a'`] mp_tac) >>
      simp[] >> strip_tac >> gvs[]) >>
    gvs[]
  ])
QED

(* ===== Helpers: PHIs in bbs1 are build_phi_inst ===== *)

(* process_frontiers only adds build_phi_inst — stronger than phi_outputs *)
Triviality process_frontiers_phi_is_build_phi:
  !fs var pred_map live_in bbs rest has_phi bbs' rest' has_phi'.
    process_frontiers var pred_map live_in bbs rest has_phi fs =
      (bbs', rest', has_phi') ==>
    !j. j < LENGTH bbs ==>
      !inst. MEM inst (EL j bbs').bb_instructions /\
             ~MEM inst (EL j bbs).bb_instructions ==>
        inst = build_phi_inst var
          (case ALOOKUP pred_map (EL j bbs).bb_label
           of NONE => [] | SOME ps => ps)
Proof
  Induct >> rw[process_frontiers_def] >> (
    qabbrev_tac `bbs_map = MAP (\bb. if bb.bb_label = h
       then insert_phi_at_block
         (build_phi_inst var
           (case ALOOKUP pred_map h of SOME ps => ps | NONE => []))
         bb else bb) bbs` >>
    `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
    Cases_on `MEM inst (EL j bbs_map).bb_instructions`
    >- (
      `EL j bbs_map = (
         if (EL j bbs).bb_label = h
         then insert_phi_at_block
           (build_phi_inst var
             (case ALOOKUP pred_map h of SOME ps => ps | NONE => []))
           (EL j bbs)
         else EL j bbs)` by
        simp[Abbr `bbs_map`, EL_MAP] >>
      Cases_on `(EL j bbs).bb_label = h` >> gvs[insert_phi_at_block_def])
    >- (
      first_x_assum drule >> disch_then drule >>
      disch_then drule >>
      `(EL j bbs_map).bb_label = (EL j bbs).bb_label` by (
        simp[Abbr `bbs_map`, EL_MAP] >>
        Cases_on `(EL j bbs).bb_label = h` >>
        simp[insert_phi_at_block_def]) >>
      simp[]))
QED

(* insert_phis_for_var only adds build_phi_inst *)
Triviality insert_phis_for_var_phi_is_build_phi:
  !var dom_frontiers pred_map live_in bbs wl hp.
    !j. j < LENGTH bbs ==>
      !inst. MEM inst
        (insert_phis_for_var var dom_frontiers pred_map live_in bbs wl hp)
          ❲j❳.bb_instructions /\
             ~MEM inst (EL j bbs).bb_instructions ==>
        inst = build_phi_inst var
          (case ALOOKUP pred_map (EL j bbs).bb_label
           of NONE => [] | SOME ps => ps)
Proof
  ho_match_mp_tac (fetch "makeSsaDefs" "insert_phis_for_var_ind") >>
  rw[insert_phis_for_var_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `process_frontiers _ _ _ bbs1 _ _ _ = (bbs2, _, _)` >>
  `j < LENGTH bbs2` by (
    drule process_frontiers_phi_extends >>
    disch_then (qspec_then `bbs1` mp_tac) >>
    (impl_tac >- simp[phi_extends_refl]) >>
    simp[phi_extends_def]) >>
  `(EL j bbs2).bb_label = (EL j bbs1).bb_label` by (
    drule process_frontiers_phi_extends >>
    disch_then (qspec_then `bbs1` mp_tac) >>
    (impl_tac >- simp[phi_extends_refl]) >>
    simp[phi_extends_def] >> metis_tac[EL_MAP]) >>
  Cases_on `MEM inst (EL j bbs2).bb_instructions`
  >- (
    drule process_frontiers_phi_is_build_phi >>
    disch_then (qspec_then `j` mp_tac) >> simp[] >>
    disch_then drule >> simp[])
  >- (
    first_x_assum drule >> disch_then drule >>
    disch_then drule >> simp[])
QED

(* add_phi_nodes: new instructions are build_phi_inst *)
Triviality add_phi_nodes_new_is_build_phi:
  !dom_frontiers pred_map live_in bbs defs.
    let bbs1 = add_phi_nodes dom_frontiers pred_map live_in bbs defs in
    !j inst.
      j < LENGTH bbs /\
      MEM inst (EL j bbs1).bb_instructions /\
      ~MEM inst (EL j bbs).bb_instructions ==>
      ?var. inst = build_phi_inst var
        (case ALOOKUP pred_map (EL j bbs).bb_label
         of NONE => [] | SOME ps => ps)
Proof
  simp_tac std_ss [LET_THM, add_phi_nodes_def] >>
  ntac 3 gen_tac >>
  Induct_on `defs` >> rw[FOLDL] >>
  PairCases_on `h` >> FULL_SIMP_TAC std_ss [] >> BETA_TAC >>
  qabbrev_tac `bbs_mid = insert_phis_for_var h0 dom_frontiers pred_map
    live_in bbs h1 []` >>
  `LENGTH bbs_mid = LENGTH bbs` by (
    `phi_extends bbs bbs_mid` by (
      simp[Abbr `bbs_mid`] >>
      irule insert_phis_for_var_phi_extends >> simp[phi_extends_refl]) >>
    gvs[phi_extends_def]) >>
  `(EL j bbs_mid).bb_label = (EL j bbs).bb_label` by (
    `phi_extends bbs bbs_mid` by (
      simp[Abbr `bbs_mid`] >>
      irule insert_phis_for_var_phi_extends >> simp[phi_extends_refl]) >>
    gvs[phi_extends_def] >> metis_tac[EL_MAP]) >>
  Cases_on `MEM inst (EL j bbs_mid).bb_instructions`
  >- (
    mp_tac (Q.SPECL [`h0`, `dom_frontiers`, `pred_map`, `live_in`,
      `bbs`, `h1`, `[]:(string list)`]
      insert_phis_for_var_phi_is_build_phi) >>
    disch_then (qspec_then `j` mp_tac) >> simp[Abbr `bbs_mid`] >>
    disch_then (qspec_then `inst` mp_tac) >> simp[] >>
    strip_tac >> qexists_tac `h0` >> simp[])
  >- (
    first_x_assum (qspecl_then [`bbs_mid`, `j`, `inst`] mp_tac) >>
    (impl_tac >- simp[]) >> simp[])
QED

(* Wrapper: all PHIs in bbs1 are build_phi_inst (when original has no PHIs) *)
Triviality add_phi_nodes_phi_is_build_phi:
  !dom_frontiers pred_map live_in bbs defs.
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI) ==>
    let bbs1 = add_phi_nodes dom_frontiers pred_map live_in bbs defs in
    !j inst.
      j < LENGTH bbs /\
      MEM inst (EL j bbs1).bb_instructions /\
      inst.inst_opcode = PHI ==>
      ?var. inst = build_phi_inst var
        (case ALOOKUP pred_map (EL j bbs).bb_label
         of NONE => [] | SOME ps => ps)
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  rpt strip_tac >>
  mp_tac add_phi_nodes_new_is_build_phi >>
  simp_tac std_ss [LET_THM] >>
  disch_then (qspecl_then [`dom_frontiers`, `pred_map`, `live_in`,
    `bbs`, `defs`, `j`, `inst`] mp_tac) >> simp[] >>
  impl_tac >- (
    spose_not_then ASSUME_TAC >>
    `MEM (EL j bbs) bbs` by metis_tac[MEM_EL] >>
    metis_tac[]) >>
  simp[]
QED

(* ===== Helpers for phi_coverage ===== *)

(* latest_version only depends on stacks, not counters *)
Triviality latest_version_stacks_eq:
  !c1 c2 s v. latest_version (c1, s) v = latest_version (c2, s) v
Proof
  rw[latest_version_def]
QED

(* process_frontiers: rest is a subset of rest' *)
Triviality process_frontiers_rest_mono:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    !x. MEM x rest ==> MEM x rest'
Proof
  Induct >> rw[process_frontiers_def] >> metis_tac[MEM]
QED

(* process_frontiers: if f in fs, f not in hp, var live at f,
   then PHI for var is inserted at block f *)
Triviality process_frontiers_inserts_phi:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    !f j.
      MEM f fs /\ ~MEM f hp /\
      j < LENGTH bbs /\ (EL j bbs).bb_label = f /\
      (?vs. ALOOKUP li f = SOME vs /\ MEM var vs) ==>
      ?inst. MEM inst (EL j bbs').bb_instructions /\
             inst.inst_opcode = PHI /\ inst.inst_outputs = [var]
Proof
  Induct >- simp[process_frontiers_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `process_frontiers _ _ _ _ _ _ (_::_) = _` mp_tac >>
  simp[Once process_frontiers_def] >>
  Cases_on `MEM h hp` >> simp[]
  >- ( (* h in hp: skip h, recurse *)
    strip_tac >>
    `f <> h` by (strip_tac >> gvs[]) >>
    `MEM f fs` by gvs[] >>
    first_x_assum drule >>
    disch_then (qspecl_then [`f`, `j`] mp_tac) >> simp[])
  >- (
    Cases_on `case ALOOKUP li h of NONE => F | SOME vars => MEM var vars` >>
    simp[]
    >- ( (* h is live: insert PHI at h, then recurse *)
      strip_tac >>
      Cases_on `f = h`
      >- ( (* f = h: PHI was just inserted here *)
        pop_assum SUBST_ALL_TAC >>
        qmatch_asmsub_abbrev_tac `process_frontiers _ _ _ bbs_map _ _ _` >>
        `(EL j bbs_map).bb_instructions =
           build_phi_inst var (case ALOOKUP pm h of NONE => [] | SOME ps => ps)
           :: (EL j bbs).bb_instructions` by
          simp[Abbr `bbs_map`, EL_MAP, insert_phi_at_block_def] >>
        `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
        `phi_extends bbs_map bbs'` by (
          drule process_frontiers_phi_extends >>
          disch_then match_mp_tac >>
          simp[phi_extends_refl]) >>
        qpat_x_assum `bbs❲j❳.bb_label = h` (fn _ => ALL_TAC) >>
        gvs[phi_extends_def] >>
        first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
        qexists_tac `build_phi_inst var
          (case ALOOKUP pm h of NONE => [] | SOME ps => ps)` >>
        simp[build_phi_inst_def, MEM_APPEND])
      >- ( (* f <> h: block j unchanged, recurse *)
        `MEM f fs` by gvs[] >>
        qmatch_asmsub_abbrev_tac `process_frontiers _ _ _ bbs_map _ _ _` >>
        `EL j bbs_map = EL j bbs` by simp[Abbr `bbs_map`, EL_MAP] >>
        `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
        first_x_assum drule >>
        disch_then (qspecl_then [`f`, `j`] mp_tac) >> simp[]))
    >- ( (* h not live: bbs unchanged, add h to hp, recurse *)
      strip_tac >>
      `f <> h` by (
        strip_tac >> gvs[] >> Cases_on `ALOOKUP li h` >> gvs[]) >>
      `MEM f fs` by gvs[] >>
      first_x_assum drule >>
      disch_then (qspecl_then [`f`, `j`] mp_tac) >> simp[]))
QED

(* process_frontiers: if f is in hp' but not hp, and var is live at f,
   then a PHI was inserted at f *)
Triviality process_frontiers_hp_live_phi:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    !f j.
      MEM f hp' /\ ~MEM f hp /\
      j < LENGTH bbs /\ (EL j bbs).bb_label = f /\
      (?vs. ALOOKUP li f = SOME vs /\ MEM var vs) ==>
      ?inst. MEM inst (EL j bbs').bb_instructions /\
             inst.inst_opcode = PHI /\ inst.inst_outputs = [var]
Proof
  Induct >- (rpt strip_tac >> gvs[process_frontiers_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `process_frontiers _ _ _ _ _ _ (_::_) = _` mp_tac >>
  simp[Once process_frontiers_def] >>
  Cases_on `MEM h hp` >> simp[]
  >- ( (* h in hp: skip *)
    strip_tac >>
    first_x_assum drule >>
    disch_then (qspecl_then [`f`, `j`] mp_tac) >> simp[])
  >- (
    Cases_on `case ALOOKUP li h of NONE => F | SOME vars => MEM var vars` >>
    simp[]
    >- ( (* h live: insert PHI *)
      strip_tac >>
      Cases_on `f = h`
      >- ( (* f = h: PHI was inserted here *)
        pop_assum SUBST_ALL_TAC >>
        qmatch_asmsub_abbrev_tac `process_frontiers _ _ _ bbs_map _ _ _` >>
        `(EL j bbs_map).bb_instructions =
           build_phi_inst var (case ALOOKUP pm h of NONE => [] | SOME ps => ps)
           :: (EL j bbs).bb_instructions` by
          simp[Abbr `bbs_map`, EL_MAP, insert_phi_at_block_def] >>
        `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
        `phi_extends bbs_map bbs'` by (
          drule process_frontiers_phi_extends >>
          disch_then match_mp_tac >>
          simp[phi_extends_refl]) >>
        qpat_x_assum `bbs❲j❳.bb_label = h` (fn _ => ALL_TAC) >>
        gvs[phi_extends_def] >>
        first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
        qexists_tac `build_phi_inst var
          (case ALOOKUP pm h of NONE => [] | SOME ps => ps)` >>
        simp[build_phi_inst_def, MEM_APPEND])
      >- ( (* f <> h: recurse *)
        qmatch_asmsub_abbrev_tac `process_frontiers _ _ _ bbs_map _ _ _` >>
        `EL j bbs_map = EL j bbs` by simp[Abbr `bbs_map`, EL_MAP] >>
        `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
        `MEM f hp' /\ ~MEM f (h::hp)` by (
          qpat_x_assum `MEM f hp'` mp_tac >> simp[]) >>
        first_x_assum drule >>
        disch_then (qspecl_then [`f`, `j`] mp_tac) >> simp[]))
    >- ( (* h not live: hp unchanged, recurse *)
      strip_tac >>
      Cases_on `f = h`
      >- (gvs[] >> Cases_on `ALOOKUP li h` >> gvs[])
      >- (
        `MEM f hp' /\ ~MEM f (h::hp)` by simp[] >>
        first_x_assum drule >>
        disch_then (qspecl_then [`f`, `j`] mp_tac) >> simp[])))
QED

(* insert_phis_for_var covers all worklist entries:
   if d is in the worklist, f in dom_frontiers[d],
   f not in has_phi, and var live at f,
   then PHI for var at f in the output *)
Triviality insert_phis_for_var_covers_wl:
  !var df pm li bbs wl hp.
    !d f j.
      MEM d wl /\
      MEM f (case ALOOKUP df d of SOME x => x | NONE => []) /\
      j < LENGTH bbs /\ (EL j bbs).bb_label = f /\
      ~MEM f hp /\
      (?vs. ALOOKUP li f = SOME vs /\ MEM var vs) ==>
      ?inst. MEM inst (EL j
        (insert_phis_for_var var df pm li bbs wl hp)).bb_instructions /\
             inst.inst_opcode = PHI /\ inst.inst_outputs = [var]
Proof
  ho_match_mp_tac insert_phis_for_var_ind >>
  simp[insert_phis_for_var_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* strip_tac splits MEM into d'=d | MEM d' rest, giving 2 goals *)
  (* After pairarg_tac >> gvs[], goal1 has d' eliminated (merged with d) *)
  pairarg_tac >> gvs[] >>
  `MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs` by
    (irule process_frontiers_labels >> metis_tac[]) >>
  `LENGTH bbs' = LENGTH bbs` by
    (qpat_x_assum `MAP _ bbs' = _` mp_tac >> simp[MAP_EQ_EVERY2, LIST_REL_EL_EQN]) >>
  `(EL j bbs').bb_label = (EL j bbs).bb_label` by (
    `EL j (MAP (\bb. bb.bb_label) bbs') =
     EL j (MAP (\bb. bb.bb_label) bbs)` by simp[] >>
    gvs[EL_MAP]) >>
  `phi_extends bbs bbs'` by
    metis_tac[process_frontiers_phi_extends, phi_extends_refl] >>
  `phi_extends bbs'
     (insert_phis_for_var var df pm li bbs' rest' has_phi')` by
    (irule insert_phis_for_var_phi_extends >> simp[phi_extends_refl])
  (* Now handle 2 goals from MEM split *)
  >- ( (* Goal 1: d' = d (target is worklist head, d' eliminated by gvs) *)
    drule process_frontiers_inserts_phi >>
    disch_then (qspecl_then [`bbs❲j❳.bb_label`, `j`] mp_tac) >>
    simp[] >> strip_tac >>
    qpat_x_assum `phi_extends bbs' _` mp_tac >>
    simp[phi_extends_def] >> strip_tac >>
    first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
    qexists_tac `inst` >> simp[MEM_APPEND])
  >- ( (* Goal 2: MEM d' rest (target in worklist tail) *)
    `MEM d' rest'` by (
      drule process_frontiers_rest_mono >>
      disch_then (qspec_then `d'` mp_tac) >> simp[]) >>
    Cases_on `MEM (bbs❲j❳.bb_label) has_phi'`
    >- ( (* f in has_phi': PHI was inserted during current step *)
      `∃inst. MEM inst (EL j bbs').bb_instructions /\
              inst.inst_opcode = PHI /\ inst.inst_outputs = [var]` by (
        drule process_frontiers_hp_live_phi >>
        disch_then (qspecl_then [`bbs❲j❳.bb_label`, `j`] mp_tac) >>
        simp[]) >>
      qpat_x_assum `phi_extends bbs' _` mp_tac >>
      simp[phi_extends_def] >> strip_tac >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
      qexists_tac `inst` >> simp[MEM_APPEND])
    >- ( (* f not in has_phi': use IH *)
      first_x_assum (qspecl_then [`d'`, `j`] mp_tac) >> simp[]))
QED

(* ALOOKUP on alist_update_or_prepend: same key *)
Triviality alist_update_or_prepend_alookup_same:
  !alist k f d.
    ALOOKUP (alist_update_or_prepend k f d alist) k =
    SOME (case ALOOKUP alist k of SOME v => f v | NONE => d)
Proof
  Induct >> simp[alist_update_or_prepend_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[alist_update_or_prepend_def] >>
  Cases_on `h0 = k` >> simp[]
QED

(* ALOOKUP on alist_update_or_prepend: different key *)
Triviality alist_update_or_prepend_alookup_other:
  !alist k k' f d.
    k' <> k ==>
    ALOOKUP (alist_update_or_prepend k f d alist) k' = ALOOKUP alist k'
Proof
  Induct >> simp[alist_update_or_prepend_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[alist_update_or_prepend_def] >>
  Cases_on `h0 = k` >> simp[]
QED

(* FOLDR alist_update_or_prepend: if var is in the list, result has lbl *)
Triviality foldr_update_mem_result:
  !vars var lbl acc.
    MEM var vars ==>
    ?dbs. ALOOKUP (FOLDR (\v a. alist_update_or_prepend v (CONS lbl) [lbl] a)
                         acc vars) var = SOME dbs /\
          MEM lbl dbs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[]
  >- ( (* var = h: alist_update_or_prepend at same key *)
    simp[alist_update_or_prepend_alookup_same] >>
    Cases_on `ALOOKUP (FOLDR (\v a. alist_update_or_prepend v (CONS lbl)
      [lbl] a) acc vars) h` >> simp[])
  >- ( (* MEM var vars: IH gives result in FOLDR, then alist_update preserves *)
    first_x_assum (qspecl_then [`var`, `lbl`, `acc`] mp_tac) >> simp[] >>
    strip_tac >>
    Cases_on `h = var`
    >- (simp[alist_update_or_prepend_alookup_same] >> metis_tac[MEM])
    >- (simp[alist_update_or_prepend_alookup_other] >> metis_tac[]))
QED

(* FOLDR alist_update_or_prepend preserves existing ALOOKUP results *)
Triviality foldr_update_preserves:
  !vars var lbl acc dbs.
    ALOOKUP acc var = SOME dbs ==>
    ?dbs'. ALOOKUP (FOLDR (\v a. alist_update_or_prepend v (CONS lbl) [lbl] a)
                          acc vars) var = SOME dbs' /\
           !x. MEM x dbs ==> MEM x dbs'
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  Cases_on `h = var`
  >- (gvs[] >> simp[alist_update_or_prepend_alookup_same] >>
      first_x_assum (qspec_then `lbl` strip_assume_tac) >> gvs[] >>
      qexists_tac `lbl :: dbs'` >> simp[] >> metis_tac[MEM])
  >- (simp[alist_update_or_prepend_alookup_other] >>
      first_x_assum (qspec_then `lbl` strip_assume_tac) >> metis_tac[])
QED

(* compute_defs: if var is in block_assignments of a block in the list,
   then ALOOKUP compute_defs gives SOME dbs with the block's label in dbs *)
Triviality compute_defs_complete:
  !bbs var bb.
    MEM bb bbs /\ MEM var (block_assignments bb) ==>
    ?dbs. ALOOKUP (compute_defs bbs) var = SOME dbs /\
          MEM bb.bb_label dbs
Proof
  Induct >> simp[compute_defs_def] >> rpt gen_tac >> strip_tac
  >- ( (* bb is the head *)
    gvs[] >>
    irule foldr_update_mem_result >> simp[])
  >- ( (* bb in tail: IH + FOLDR preserves *)
    first_x_assum (drule_all_then strip_assume_tac) >>
    drule foldr_update_preserves >>
    disch_then (qspecl_then [`block_assignments h`, `h.bb_label`] strip_assume_tac) >>
    metis_tac[])
QED

Triviality phi_extends_trans:
  !bbs1 bbs2 bbs3.
    phi_extends bbs1 bbs2 /\ phi_extends bbs2 bbs3 ==>
    phi_extends bbs1 bbs3
Proof
  rw[phi_extends_def] >>
  `j < LENGTH bbs2` by DECIDE_TAC >>
  res_tac >> qexists_tac `phis ++ phis'` >> gvs[EVERY_APPEND]
QED

(* add_phi_nodes: if d defines var (in compute_defs),
   and f is in dom_frontiers[d], and var is live at f,
   then PHI for var at f in the output *)
(* add_phi_nodes: if d defines var (in defs),
   and f is in dom_frontiers[d], and var is live at f,
   then PHI for var at f in the output.
   No-PHI hypothesis removed: not maintainable through FOLDL steps. *)
Triviality add_phi_nodes_covers:
  !dom_frontiers pred_map live_in defs var dbs d f j bbs.
    ALOOKUP defs var = SOME dbs /\
    MEM d dbs /\
    MEM f (case ALOOKUP dom_frontiers d of SOME x => x | NONE => []) /\
    j < LENGTH bbs /\ (EL j bbs).bb_label = f /\
    (?vs. ALOOKUP live_in f = SOME vs /\ MEM var vs) ==>
    ?inst. MEM inst (EL j (add_phi_nodes dom_frontiers pred_map live_in
                             bbs defs)).bb_instructions /\
           inst.inst_opcode = PHI /\ inst.inst_outputs = [var]
Proof
  ntac 3 gen_tac >>
  Induct_on `defs` >- simp[add_phi_nodes_def] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  qabbrev_tac `bbs_mid = insert_phis_for_var h0 dom_frontiers pred_map
    live_in bbs h1 []` >>
  `phi_extends bbs bbs_mid` by (
    simp[Abbr `bbs_mid`] >>
    irule insert_phis_for_var_phi_extends >> simp[phi_extends_refl]) >>
  `LENGTH bbs_mid = LENGTH bbs` by gvs[phi_extends_def] >>
  `(EL j bbs_mid).bb_label = f` by (
    `EL j (MAP (\bb. bb.bb_label) bbs_mid) =
     EL j (MAP (\bb. bb.bb_label) bbs)` by gvs[phi_extends_def] >>
    gvs[EL_MAP]) >>
  Cases_on `h0 = var`
  >- ( (* h0 = var, dbs = h1 *)
    pop_assum SUBST_ALL_TAC >>  (* h0 -> var *)
    `h1 = dbs` by fs[] >> pop_assum SUBST_ALL_TAC >>  (* h1 -> dbs *)
    (* insert_phis_for_var_covers_wl gives PHI in bbs_mid *)
    `?inst. MEM inst (EL j bbs_mid).bb_instructions /\
            inst.inst_opcode = PHI /\ inst.inst_outputs = [var]` by (
      simp[Abbr `bbs_mid`] >>
      mp_tac insert_phis_for_var_covers_wl >>
      disch_then (qspecl_then [`var`, `dom_frontiers`, `pred_map`,
        `live_in`, `bbs`, `dbs`, `[]`, `d`, `f`, `j`] mp_tac) >>
      simp[]) >>
    (* PHI persists through remaining add_phi_nodes *)
    `phi_extends bbs_mid
       (add_phi_nodes dom_frontiers pred_map live_in bbs_mid defs)` by
      simp[add_phi_nodes_phi_extends] >>
    `add_phi_nodes dom_frontiers pred_map live_in bbs ((var,dbs)::defs) =
     add_phi_nodes dom_frontiers pred_map live_in bbs_mid defs` by
      simp[add_phi_nodes_def, Abbr `bbs_mid`] >>
    simp[] >> gvs[phi_extends_def] >>
    first_x_assum (qspec_then `j` mp_tac) >> simp[] >>
    strip_tac >> qexists_tac `inst` >> gvs[MEM_APPEND])
  >- ( (* h0 <> var: IH with bbs_mid *)
    `ALOOKUP defs var = SOME dbs` by gvs[] >>
    first_x_assum (qspecl_then [`var`, `dbs`, `d`, `f`, `j`, `bbs_mid`]
      mp_tac) >>
    simp[add_phi_nodes_def, Abbr `bbs_mid`])
QED

(* ===== CFG dominance basics ===== *)

Triviality cfg_dominates_refl:
  !bbs entry d. cfg_dominates bbs entry d d
Proof
  simp[cfg_dominates_def]
QED

Triviality cfg_dominates_trans:
  !bbs entry a b c.
    cfg_dominates bbs entry a b /\
    cfg_dominates bbs entry b c ==>
    cfg_dominates bbs entry a c
Proof
  simp[cfg_dominates_def]
QED

(* ===== dtree_parent infrastructure ===== *)

(* dtree_parent: result is in the tree *)
Triviality dtree_parent_in_tree:
  !t x p. dtree_parent t x = SOME p ==> MEM x (dom_tree_labels t)
Proof
  ho_match_mp_tac dtree_parent_ind >> rpt conj_tac
  >- simp[dtree_parent_def]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once dtree_parent_def, AllCaseEqs(),
          dom_tree_labels_def, ETA_THM, MEM_FLAT, MEM_MAP] >>
      metis_tac[])
QED

(* dtree_parent: result is in the children labels (not the root) *)
Triviality dtree_parent_in_children:
  !root children x p.
    dtree_parent (DNode root children) x = SOME p /\ x <> root ==>
    MEM x (FLAT (MAP dom_tree_labels children))
Proof
  rpt strip_tac >>
  `MEM x (dom_tree_labels (DNode root children))` by
    metis_tac[dtree_parent_in_tree] >>
  gvs[dom_tree_labels_def, ETA_THM]
QED

(* dtree_parent fails for labels not in the tree *)
Triviality dtree_parent_not_in_tree:
  !t x. ~MEM x (dom_tree_labels t) ==> dtree_parent t x = NONE
Proof
  rpt strip_tac >> CCONTR_TAC >>
  Cases_on `dtree_parent t x` >> gvs[] >>
  metis_tac[dtree_parent_in_tree]
QED

(* dtree_parent never returns the root (with ALL_DISTINCT) *)
Triviality dtree_parent_not_root:
  !t x p.
    ALL_DISTINCT (dom_tree_labels t) /\
    dtree_parent t x = SOME p ==>
    !r cs. t = DNode r cs ==> x <> r
Proof
  ho_match_mp_tac dtree_parent_ind >> rpt conj_tac
  >- simp[dtree_parent_def]
  >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> gvs[] >>
    qpat_x_assum `dtree_parent _ _ = SOME _` mp_tac >>
    simp[Once dtree_parent_def] >>
    Cases_on `c = x` >> simp[]
    >- ( (* c = x: SOME lbl = SOME p *)
      strip_tac >>
      fs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND])
    >- (
      Cases_on `dtree_parent (DNode c cs) x` >> simp[]
      >- ( (* NONE *)
        strip_tac >>
        qpat_x_assum `_ /\ _ = NONE ==> _` mp_tac >>
        impl_tac >- simp[] >>
        disch_then (qspec_then `p` mp_tac) >>
        impl_tac
        >- (conj_tac
          >- fs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND]
          >- simp[]) >>
        simp[])
      >- ( (* SOME *)
        strip_tac >>
        `MEM x (dom_tree_labels (DNode c cs))` by
          metis_tac[dtree_parent_in_tree] >>
        spose_not_then ASSUME_TAC >> gvs[] >>
        gvs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT, MEM_APPEND])))
QED

(* dtree_parent on a child subtree implies dtree_parent on the full tree *)
Triviality dtree_parent_child_subtree:
  !root children d x p.
    ALL_DISTINCT (dom_tree_labels (DNode root children)) /\
    MEM d children /\
    dtree_parent d x = SOME p ==>
    dtree_parent (DNode root children) x = SOME p
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `children` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `h::rest` >>
  Cases_on `h` >> rename1 `DNode c cs` >>
  simp[Once dtree_parent_def] >>
  (* x is in d's subtree, so x <> c when d <> DNode c cs *)
  `MEM x (dom_tree_labels d)` by metis_tac[dtree_parent_in_tree] >>
  Cases_on `d = DNode c cs`
  >- ( (* d = DNode c cs: use dtree_parent_not_root *)
    gvs[] >>
    `x <> c` by (
      `ALL_DISTINCT (dom_tree_labels (DNode c cs))` by
        gvs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND] >>
      metis_tac[dtree_parent_not_root]) >>
    simp[])
  >- ( (* d in rest *)
    strip_tac >> gvs[] >>
    `x <> c` by (
      CCONTR_TAC >> gvs[] >>
      fs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND,
         MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
    simp[] >>
    `dtree_parent (DNode c cs) x = NONE` by (
      irule dtree_parent_not_in_tree >>
      CCONTR_TAC >> gvs[] >>
      fs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND,
         MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
    simp[] >>
    first_x_assum match_mp_tac >>
    gvs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND])
QED

(* dtree_parent on DNode root rest extends to DNode root (DNode c cs :: rest) *)
Triviality dtree_parent_extend_head:
  !root c cs rest child parent.
    ALL_DISTINCT (dom_tree_labels (DNode root (DNode c cs :: rest))) /\
    dtree_parent (DNode root rest) child = SOME parent ==>
    dtree_parent (DNode root (DNode c cs :: rest)) child = SOME parent
Proof
  rpt strip_tac >>
  `MEM child (dom_tree_labels (DNode root rest))` by
    metis_tac[dtree_parent_in_tree] >>
  `child <> c` by (
    CCONTR_TAC >> gvs[] >>
    fs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND,
       MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `dtree_parent (DNode c cs) child = NONE` by (
    irule dtree_parent_not_in_tree >>
    CCONTR_TAC >> gvs[] >>
    fs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND,
       MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  simp[Once dtree_parent_def]
QED

(* If x is in the tree, x <> root, and labels are distinct, then x has a parent *)
Triviality non_root_has_parent:
  !t x root children.
    t = DNode root children /\
    MEM x (dom_tree_labels t) /\
    x <> root /\
    ALL_DISTINCT (dom_tree_labels t) ==>
    ?p. dtree_parent t x = SOME p
Proof
  qsuff_tac `∀t x. MEM x (dom_tree_labels t) ∧ ALL_DISTINCT (dom_tree_labels t) ∧ HD (dom_tree_labels t) ≠ x ⇒ ∃p. dtree_parent t x = SOME p` >- (rpt strip_tac >> first_x_assum irule >> gvs[dom_tree_labels_def]) >>
  ho_match_mp_tac dtree_parent_ind >> conj_tac >- simp[dom_tree_labels_def, dtree_parent_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once dtree_parent_def] >>
  IF_CASES_TAC >- (qexists_tac `lbl` >> simp[]) >>
  Cases_on `dtree_parent (DNode c cs) x` >> simp[]
  >- (fs[dom_tree_labels_def, MEM_FLAT, MEM_MAP] >>
      last_x_assum match_mp_tac >>
      gvs[ALL_DISTINCT, ALL_DISTINCT_APPEND,
          dom_tree_labels_def, MEM_FLAT, MEM_MAP] >>
      metis_tac[])
QED

(* Helper: ALL_DISTINCT of subtree from ALL_DISTINCT of full tree *)
Triviality subtree_all_distinct:
  ALL_DISTINCT (dom_tree_labels (DNode root (d :: rest))) ==>
  ALL_DISTINCT (dom_tree_labels d)
Proof
  simp[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND]
QED

(* Helper: dtree_parent dominance in subtree from dominance in full tree *)
Triviality subtree_dtree_parent_dominates:
  !root children d bbs entry child parent.
    ALL_DISTINCT (dom_tree_labels (DNode root children)) /\
    MEM d children /\
    (!child parent. dtree_parent (DNode root children) child = SOME parent ==>
       cfg_dominates bbs entry parent child) /\
    dtree_parent d child = SOME parent ==>
    cfg_dominates bbs entry parent child
Proof
  rpt strip_tac >> first_x_assum match_mp_tac >>
  irule dtree_parent_child_subtree >>
  simp[] >> qexists_tac `d` >> simp[]
QED

(* Helper: IH1 application — subtree root dominates node in subtree *)
Triviality ih1_dominates:
  c <> child_lbl /\
  (c <> child_lbl ==>
   !bbs' entry'.
     ALL_DISTINCT (dom_tree_labels (DNode c cs)) /\
     (!child parent.
        dtree_parent (DNode c cs) child = SOME parent ==>
        cfg_dominates bbs' entry' parent child) ==>
     cfg_dominates bbs' entry' c child_lbl) /\
  ALL_DISTINCT (dom_tree_labels (DNode root (DNode c cs :: rest))) /\
  (!child parent.
     dtree_parent (DNode root (DNode c cs :: rest)) child = SOME parent ==>
     cfg_dominates bbs entry parent child) ==>
  cfg_dominates bbs entry c child_lbl
Proof
  rpt strip_tac
  >> first_x_assum (fn ih => mp_tac ih >> impl_tac >- simp[] >> strip_tac)
  >> first_x_assum (qspecl_then [`bbs`, `entry`] mp_tac)
  >> impl_tac
  >- (
    conj_tac
    >- (fs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND])
    >> rpt strip_tac
    >> first_x_assum match_mp_tac
    >> irule dtree_parent_child_subtree
    >> simp[]
    >> qexists_tac `DNode c cs`
    >> simp[])
  >> simp[]
QED

(* Root of a domtree dominates all nodes in it *)
Triviality dom_tree_root_dominates:
  !t child_lbl bbs entry root children.
    ALL_DISTINCT (dom_tree_labels t) /\
    (!child parent. dtree_parent t child = SOME parent ==>
       cfg_dominates bbs entry parent child) /\
    MEM child_lbl (dom_tree_labels t) /\
    t = DNode root children ==>
    cfg_dominates bbs entry root child_lbl
Proof
  ho_match_mp_tac dtree_parent_ind >> rpt conj_tac
  >- ( (* Base: DNode lbl [] *)
    rpt gen_tac >> strip_tac >> gvs[dom_tree_labels_def, ETA_THM] >>
    simp[cfg_dominates_refl])
  >- ( (* Step: DNode lbl (DNode c cs :: rest) *)
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> gvs[] >>
    (* child_lbl = lbl, in DNode c cs subtree, or in rest *)
    Cases_on `child_lbl = lbl`
    >- simp[cfg_dominates_refl]
    >- (
      `MEM child_lbl (dom_tree_labels (DNode c cs)) \/
       MEM child_lbl (FLAT (MAP dom_tree_labels rest))` by (
        qpat_x_assum `MEM _ (dom_tree_labels _)` mp_tac >>
        simp[Once dom_tree_labels_def, ETA_THM, MEM_APPEND]) >>
      gvs[]
      >- ( (* MEM child_lbl (dom_tree_labels (DNode c cs)) *)
        Cases_on `child_lbl = c`
        >- ( (* child_lbl = c: direct child *)
          gvs[] >> first_x_assum match_mp_tac >>
          simp[Once dtree_parent_def])
        >- ( (* child_lbl in subtree of c: IH1 gives c dom child_lbl *)
          `cfg_dominates bbs entry c child_lbl` by
            metis_tac[ih1_dominates] >>
          irule cfg_dominates_trans >> qexists_tac `c` >> simp[] >>
          qpat_x_assum `!child parent. dtree_parent _ _ = _ ==> _` match_mp_tac >>
          simp[Once dtree_parent_def]))
      >- ( (* MEM child_lbl (FLAT (MAP dom_tree_labels rest)): IH2 *)
        `child_lbl <> c` by (
          CCONTR_TAC >> gvs[] >>
          fs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND,
             MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
        `dtree_parent (DNode c cs) child_lbl = NONE` by (
          irule dtree_parent_not_in_tree >>
          CCONTR_TAC >> gvs[] >>
          fs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND,
             MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
        qpat_x_assum `_ /\ _ = NONE ==> _` mp_tac >>
        impl_tac >- simp[] >>
        disch_then (qspecl_then [`bbs`, `entry`] mp_tac) >>
        impl_tac >- (
          rpt conj_tac
          >- fs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND]
          >- (rpt strip_tac >> first_x_assum match_mp_tac >>
              irule dtree_parent_extend_head >> simp[])
          >- simp[dom_tree_labels_def, ETA_THM]
          >> simp[]) >>
        simp[])))
QED

(* Helper: if P = idom(B) and P dom D and D ≠ P and D ≠ B, then ¬(D dom B).
   Proof: D dom B ∧ D ≠ B → (idom clause) D dom P ∨ D = P.
   D ≠ P → D dom P. But P dom D (given). dom_antisym → D = P. Contradiction. *)
Triviality descendant_not_dom:
  !dom_frontiers dtree dom_post_order func entry D B P.
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    fn_entry_label func = SOME entry /\
    dtree_parent dtree B = SOME P /\
    cfg_dominates func.fn_blocks entry P D /\
    D <> P /\ D <> B ==>
    ~cfg_dominates func.fn_blocks entry D B
Proof
  rpt strip_tac >>
  (* idom clause: D dom B ∧ D ≠ B → D dom P ∨ D = P *)
  `cfg_dominates func.fn_blocks entry D P \/ D = P` by (
    gvs[valid_dom_tree_def] >> metis_tac[]) >>
  gvs[] >>
  (* D dom P and P dom D → antisym → D = P, contradiction *)
  `D = P` by (fs[valid_dom_tree_def] >> metis_tac[])
QED

(* ===== cfg_path manipulation helpers ===== *)

(* Prefix of a cfg_path is a cfg_path *)
Triviality cfg_path_prefix:
  !p bbs q. cfg_path bbs (p ++ q) /\ p <> [] ==> cfg_path bbs p
Proof
  Induct_on `p` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `p` >> gvs[cfg_path_def]
  >- (Cases_on `q` >> gvs[cfg_path_def])
  >- metis_tac[]
QED

(* Extending cfg_path by one successor edge *)
Triviality cfg_path_snoc:
  !p bbs a b bb.
    cfg_path bbs (p ++ [a]) /\ lookup_block a bbs = SOME bb /\
    MEM b (bb_succs bb) /\ lookup_block b bbs <> NONE ==>
    cfg_path bbs (p ++ [a; b])
Proof
  Induct_on `p` >> simp[cfg_path_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `p` >> gvs[cfg_path_def]
QED

(* ===== idom_dominates_predecessor ===== *)

(* P = idom(B) and A→B edge ⟹ P dom A.
   Proof: extend any path to A by edge A→B. P dom B gives P on extended path.
   P ≠ B gives P on original path. *)
Triviality idom_dominates_predecessor:
  !dom_frontiers dtree dom_post_order func entry P A B bb_a.
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    fn_entry_label func = SOME entry /\
    dtree_parent dtree B = SOME P /\
    lookup_block A func.fn_blocks = SOME bb_a /\
    MEM B (bb_succs bb_a) /\
    lookup_block B func.fn_blocks <> NONE ==>
    cfg_dominates func.fn_blocks entry P A
Proof
  rpt strip_tac >> simp[cfg_dominates_def] >> rpt strip_tac >>
  (* P dom B from valid_dom_tree *)
  `cfg_dominates func.fn_blocks entry P B /\ P <> B` by
    (gvs[valid_dom_tree_def] >> metis_tac[]) >>
  (* Split path at A *)
  `?l1 l2. path = l1 ++ A :: l2` by metis_tac[MEM_SPLIT] >>
  gvs[] >>
  (* cfg_path of prefix l1 ++ [A] *)
  `l1 ++ A :: l2 = (l1 ++ [A]) ++ l2` by simp[] >>
  `cfg_path func.fn_blocks (l1 ++ [A])` by
    metis_tac[cfg_path_prefix, APPEND_NIL, NOT_NIL_CONS, APPEND_eq_NIL] >>
  (* Construct path to B: l1 ++ [A; B] *)
  `cfg_path func.fn_blocks (l1 ++ [A; B])` by
    metis_tac[cfg_path_snoc] >>
  (* P dom B applied to extended path *)
  `MEM P (l1 ++ [A; B])` by (
    qpat_x_assum `cfg_dominates _ _ P B` mp_tac >>
    simp[cfg_dominates_def] >> disch_then (qspec_then `l1 ++ [A; B]` mp_tac) >>
    simp[MEM_APPEND] >> disch_then irule >>
    Cases_on `l1` >> gvs[]) >>
  (* P ≠ B → P ∈ l1 ++ [A] → P ∈ path *)
  gvs[MEM_APPEND]
QED

(* ===== IDF closure helpers ===== *)

(* When process_frontiers modifies a block (adds new instruction),
   that block's label is in rest' *)
Triviality process_frontiers_modified_in_rest:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') ==>
    !j. j < LENGTH bbs ==>
      !inst. MEM inst (EL j bbs').bb_instructions /\
             ~MEM inst (EL j bbs).bb_instructions ==>
             MEM (EL j bbs).bb_label rest'
Proof
  Induct >> rw[process_frontiers_def]
  >- metis_tac[] >- metis_tac[]
  >> (
    qmatch_asmsub_abbrev_tac `process_frontiers _ _ _ bbs_map _ _ _` >>
    `j < LENGTH bbs_map` by simp[Abbr `bbs_map`] >>
    Cases_on `MEM inst (EL j bbs_map).bb_instructions`
    >- ( (* inst in bbs_map but not bbs: modified at this step *)
      `(EL j bbs).bb_label = h` by (
        spose_not_then ASSUME_TAC >>
        `EL j bbs_map = EL j bbs` by simp[Abbr `bbs_map`, EL_MAP] >>
        gvs[]) >>
      drule process_frontiers_rest_mono >>
      disch_then (qspec_then `h` mp_tac) >> simp[])
    >- ( (* inst not in bbs_map: modified in recursion, use IH *)
      first_x_assum drule >> disch_then (qspec_then `j` mp_tac) >>
      simp[] >> disch_then drule >> strip_tac >>
      `(EL j bbs_map).bb_label = (EL j bbs).bb_label` by (
        simp[Abbr `bbs_map`, EL_MAP] >>
        rw[insert_phi_at_block_def]) >>
      gvs[]))
QED

(* hp invariant maintenance through process_frontiers *)
Triviality process_frontiers_hp_inv_maintained:
  !fs var pm li bbs rest hp bbs' rest' hp'.
    process_frontiers var pm li bbs rest hp fs = (bbs', rest', hp') /\
    (!lbl j vs. MEM lbl hp /\ j < LENGTH bbs /\ (EL j bbs).bb_label = lbl /\
                ALOOKUP li lbl = SOME vs /\ MEM var vs ==>
                ?inst. MEM inst (EL j bbs).bb_instructions /\
                       inst.inst_opcode = PHI /\ inst.inst_outputs = [var]) /\
    phi_extends bbs bbs' /\
    LENGTH bbs' = LENGTH bbs /\
    (!k. k < LENGTH bbs ==> (EL k bbs').bb_label = (EL k bbs).bb_label) ==>
    !lbl j vs. MEM lbl hp' /\ j < LENGTH bbs' /\ (EL j bbs').bb_label = lbl /\
               ALOOKUP li lbl = SOME vs /\ MEM var vs ==>
               ?inst. MEM inst (EL j bbs').bb_instructions /\
                      inst.inst_opcode = PHI /\ inst.inst_outputs = [var]
Proof
  rpt strip_tac >>
  `j < LENGTH bbs` by simp[] >>
  `(EL j bbs).bb_label = lbl` by metis_tac[] >>
  Cases_on `MEM lbl hp`
  >- (
    res_tac >>
    qpat_x_assum `phi_extends _ _`
      (strip_assume_tac o REWRITE_RULE [phi_extends_def]) >>
    qpat_x_assum `!j. j < _ ==> ?phis. _`
      (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
    qexists_tac `inst` >> simp[MEM_APPEND])
  >- (
    qpat_x_assum `process_frontiers _ _ _ _ _ _ _ = _`
      (mp_tac o MATCH_MP process_frontiers_hp_live_phi) >>
    disch_then (qspecl_then [`lbl`, `j`] mp_tac) >>
    impl_tac >- simp[] >> simp[])
QED

(* IDF closure: if D has a NEW PHI in insert_phis_for_var output
   and f ∈ DF(D) with var live at f, then f also gets a PHI.
   hp_inv: blocks tracked in hp actually have PHIs in bbs. *)
Triviality insert_phis_for_var_idf_closure:
  !var dom_frontiers pred_map live_in bbs wl hp.
    (!lbl j vs. MEM lbl hp /\ j < LENGTH bbs /\ (EL j bbs).bb_label = lbl /\
                ALOOKUP live_in lbl = SOME vs /\ MEM var vs ==>
                ?inst. MEM inst (EL j bbs).bb_instructions /\
                       inst.inst_opcode = PHI /\ inst.inst_outputs = [var])
    ==>
    !d_lbl f j_d j_f inst.
      j_d < LENGTH bbs /\
      MEM inst (EL j_d (insert_phis_for_var var dom_frontiers pred_map
                          live_in bbs wl hp)).bb_instructions /\
      inst.inst_opcode = PHI /\ inst.inst_outputs = [var] /\
      ~MEM inst (EL j_d bbs).bb_instructions /\
      (EL j_d bbs).bb_label = d_lbl /\
      MEM f (case ALOOKUP dom_frontiers d_lbl of SOME x => x | NONE => []) /\
      j_f < LENGTH bbs /\ (EL j_f bbs).bb_label = f /\
      (?vs. ALOOKUP live_in f = SOME vs /\ MEM var vs) ==>
      ?inst2. MEM inst2 (EL j_f (insert_phis_for_var var dom_frontiers
                pred_map live_in bbs wl hp)).bb_instructions /\
              inst2.inst_opcode = PHI /\ inst2.inst_outputs = [var]
Proof
  ho_match_mp_tac insert_phis_for_var_ind >> rpt conj_tac
  >- (simp[insert_phis_for_var_def] >> metis_tac[])
  >> (
    simp[insert_phis_for_var_def] >> rpt gen_tac >> strip_tac >>
    strip_tac >> rpt gen_tac >> strip_tac >>
    pairarg_tac >> gvs[] >>
    (* After gvs: d_lbl -> bbs[j_d].bb_label, f -> bbs[j_f].bb_label *)
    `MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs` by
      (irule process_frontiers_labels >> metis_tac[]) >>
    `LENGTH bbs' = LENGTH bbs` by metis_tac[LENGTH_MAP] >>
    `!k. k < LENGTH bbs ==> (EL k bbs').bb_label = (EL k bbs).bb_label` by (
      rpt strip_tac >>
      `EL k (MAP (\bb. bb.bb_label) bbs') =
       EL k (MAP (\bb. bb.bb_label) bbs)` by simp[] >>
      gvs[EL_MAP]) >>
    `phi_extends bbs bbs'` by
      metis_tac[process_frontiers_phi_extends, phi_extends_refl] >>
    `phi_extends bbs'
       (insert_phis_for_var var dom_frontiers pred_map live_in bbs' rest'
          has_phi')` by
      (irule insert_phis_for_var_phi_extends >> simp[phi_extends_refl]) >>


    (* hp_inv maintenance: has_phi' invariant holds for bbs' *)
    `!lbl j' vs'. MEM lbl has_phi' /\ j' < LENGTH bbs' /\
                  (EL j' bbs').bb_label = lbl /\
                  ALOOKUP live_in lbl = SOME vs' /\ MEM var vs' ==>
                  ?inst'. MEM inst' (EL j' bbs').bb_instructions /\
                          inst'.inst_opcode = PHI /\
                          inst'.inst_outputs = [var]` by (
      mp_tac process_frontiers_hp_inv_maintained >>
      disch_then (qspecl_then [`case ALOOKUP dom_frontiers d of
          NONE => [] | SOME fs => fs`,
        `var`, `pred_map`, `live_in`, `bbs`, `rest`, `hp`,
        `bbs'`, `rest'`, `has_phi'`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
    (* modified blocks are in rest' *)
    `!j' inst'. j' < LENGTH bbs /\ MEM inst' (EL j' bbs').bb_instructions /\
               ~MEM inst' (EL j' bbs).bb_instructions ==>
               MEM (EL j' bbs).bb_label rest'` by
      metis_tac[process_frontiers_modified_in_rest] >>
    (* Main case split: was inst added by process_frontiers or recursive call? *)
    Cases_on `MEM inst (EL j_d bbs').bb_instructions`
    >- ( (* Case A *)
      `MEM bbs❲j_d❳.bb_label rest'` by metis_tac[] >>
      Cases_on `MEM bbs❲j_f❳.bb_label has_phi'`
      >- ( (* f tracked: hp_inv gives PHI in bbs', phi_extends to output *)
        `?i. MEM i bbs'❲j_f❳.bb_instructions /\
             i.inst_opcode = PHI /\ i.inst_outputs = [var]` by (
          mp_tac process_frontiers_hp_inv_maintained >>
          disch_then (qspecl_then [`case ALOOKUP dom_frontiers d of
              NONE => [] | SOME fs => fs`,
            `var`, `pred_map`, `live_in`, `bbs`, `rest`, `hp`,
            `bbs'`, `rest'`, `has_phi'`] mp_tac) >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          disch_then (qspecl_then [`bbs❲j_f❳.bb_label`, `j_f`, `vs`]
            mp_tac) >> simp[]) >>
        qpat_x_assum `phi_extends bbs' _`
          (strip_assume_tac o REWRITE_RULE [phi_extends_def]) >>
        qpat_x_assum `!j. j < _ ==> ?phis. _`
          (qspec_then `j_f` mp_tac) >> simp[] >> strip_tac >>
        qexists_tac `i` >> simp[MEM_APPEND])
      >- ( (* f not tracked *)
        mp_tac insert_phis_for_var_covers_wl >>
        disch_then (qspecl_then [`var`, `dom_frontiers`, `pred_map`,
          `live_in`, `bbs'`, `rest'`, `has_phi'`,
          `bbs❲j_d❳.bb_label`, `bbs❲j_f❳.bb_label`, `j_f`] mp_tac) >>
        impl_tac >- (simp[] >> metis_tac[]) >> simp[]))
    >- ( (* Case B: inst NOT in bbs' -> use IH for recursive call *)
      qpat_x_assum `_ ==> !_ _ _. _` mp_tac >>
      impl_tac >- metis_tac[] >>
      disch_then (qspecl_then [`j_d`, `j_f`, `inst`] mp_tac) >>
      disch_then irule >>
      fs[] >> metis_tac[]))
QED

(* ===== Combined coverage: original + PHI definitions ===== *)

Triviality build_phi_inst_outputs[simp]:
  !v ps. (build_phi_inst v ps).inst_outputs = [v]
Proof
  rw[build_phi_inst_def]
QED

Triviality build_phi_inst_opcode[simp]:
  !v ps. (build_phi_inst v ps).inst_opcode = PHI
Proof
  rw[build_phi_inst_def]
QED

(* IDF closure at FOLDL level: new PHI at D, f in DF(D) -> PHI at f *)
Triviality add_phi_nodes_idf_closure:
  !defs dom_frontiers pred_map live_in bbs j_d j_f var f inst.
    j_d < LENGTH bbs /\
    MEM inst (EL j_d (add_phi_nodes dom_frontiers pred_map live_in
                        bbs defs)).bb_instructions /\
    ~MEM inst (EL j_d bbs).bb_instructions /\
    inst = build_phi_inst var
      (case ALOOKUP pred_map (EL j_d bbs).bb_label of
         NONE => [] | SOME ps => ps) /\
    MEM f (case ALOOKUP dom_frontiers (EL j_d bbs).bb_label of
             SOME x => x | NONE => []) /\
    j_f < LENGTH bbs /\ (EL j_f bbs).bb_label = f /\
    (?vs. ALOOKUP live_in f = SOME vs /\ MEM var vs) ==>
    ?inst2. MEM inst2 (EL j_f (add_phi_nodes dom_frontiers pred_map live_in
                                 bbs defs)).bb_instructions /\
            inst2.inst_opcode = PHI /\ inst2.inst_outputs = [var]
Proof
  Induct_on `defs` >- rw[add_phi_nodes_def] >>
  gen_tac >> PairCases_on `h` >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inst = _` SUBST_ALL_TAC >>
  qabbrev_tac `bm = insert_phis_for_var h0 dom_frontiers pred_map
    live_in bbs h1 []` >>
  qabbrev_tac `bp = build_phi_inst var
    (case ALOOKUP pred_map bbs❲j_d❳.bb_label of
       NONE => [] | SOME ps => ps)` >>
  `add_phi_nodes dom_frontiers pred_map live_in bbs ((h0,h1)::defs) =
   add_phi_nodes dom_frontiers pred_map live_in bm defs` by
    simp[add_phi_nodes_def, Abbr `bm`] >>
  pop_assum (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq]) >> REWRITE_TAC [eq]) >>
  `phi_extends bbs bm` by
    (simp[Abbr `bm`] >> irule insert_phis_for_var_phi_extends >>
     simp[phi_extends_refl]) >>
  `LENGTH bm = LENGTH bbs /\
   !k. k < LENGTH bbs ==> (EL k bm).bb_label = (EL k bbs).bb_label` by (
    gvs[phi_extends_def] >> rpt strip_tac >>
    `EL k (MAP (\bb. bb.bb_label) bm) =
     EL k (MAP (\bb. bb.bb_label) bbs)` by simp[] >> gvs[EL_MAP]) >>
  Cases_on `MEM bp (EL j_d bm).bb_instructions`
  >- ( (* bp in bm: h0 = var, idf_closure -> PHI at f, phi_extends *)
    `h0 = var` by (
      mp_tac insert_phis_for_var_phi_is_build_phi >>
      disch_then (qspecl_then [`h0`, `dom_frontiers`, `pred_map`,
        `live_in`, `bbs`, `h1`, `[]`, `j_d`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `bp` mp_tac) >>
      simp[Abbr `bm`] >> strip_tac >>
      `[h0]:string list = [var]` suffices_by simp[] >>
      pop_assum (fn eq2 =>
        qpat_x_assum `Abbrev (bp = _)` (fn abbr =>
          let val eq = REWRITE_RULE [markerTheory.Abbrev_def] abbr
              val combined = TRANS (SYM eq2) eq
              val projected = BETA_RULE
                (AP_TERM ``\(i:instruction). i.inst_outputs`` combined)
          in ACCEPT_TAC (REWRITE_RULE [build_phi_inst_outputs] projected)
          end))) >>
    pop_assum SUBST_ALL_TAC >> (* h0 -> var *)
    `?i2. MEM i2 (EL j_f bm).bb_instructions /\
          i2.inst_opcode = PHI /\ i2.inst_outputs = [var]` by (
      mp_tac insert_phis_for_var_idf_closure >>
      disch_then (qspecl_then [`var`, `dom_frontiers`, `pred_map`,
        `live_in`, `bbs`, `h1`, `[]`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`bbs❲j_d❳.bb_label`, `f`,
        `j_d`, `j_f`, `bp`] mp_tac) >>
      impl_tac
      >- gvs[Abbr `bm`, markerTheory.Abbrev_def, build_phi_inst_opcode,
             build_phi_inst_outputs]
      >> gvs[Abbr `bm`]) >>
    `phi_extends bm (add_phi_nodes dom_frontiers pred_map live_in
                       bm defs)` by simp[add_phi_nodes_phi_extends] >>
    gvs[phi_extends_def] >>
    first_x_assum (qspec_then `j_f` mp_tac) >> simp[] >>
    strip_tac >> metis_tac[MEM_APPEND])
  >- ( (* bp NOT in bm -> IH with bbs:=bm *)
    last_x_assum (qspecl_then [`dom_frontiers`, `pred_map`, `live_in`,
      `bm`, `j_d`, `j_f`, `var`, `f`, `bp`] mp_tac) >>
    impl_tac
    >- (rpt conj_tac >> fs[markerTheory.Abbrev_def] >>
        qexists_tac `vs` >> fs[])
    >> simp[])
QED

(* If D has v as output in bbs1 (original OR PHI) and f in DF(D)
   and v live at f, then f has PHI for v.
   defs_cover: defs accounts for all original block assignments *)
Triviality add_phi_nodes_all_covered:
  !dom_frontiers pred_map live_in defs bbs d_lbl f j_f var j_d.
    j_d < LENGTH bbs /\
    (?inst. MEM inst (EL j_d (add_phi_nodes dom_frontiers pred_map live_in
                                bbs defs)).bb_instructions /\
            MEM var inst.inst_outputs) /\
    (EL j_d bbs).bb_label = d_lbl /\
    MEM f (case ALOOKUP dom_frontiers d_lbl of SOME x => x | NONE => []) /\
    j_f < LENGTH bbs /\ (EL j_f bbs).bb_label = f /\
    (?vs. ALOOKUP live_in f = SOME vs /\ MEM var vs) /\
    (!bb v. MEM bb bbs /\ MEM v (block_assignments bb) ==>
            ?dbs. ALOOKUP defs v = SOME dbs /\ MEM bb.bb_label dbs) ==>
    ?inst2. MEM inst2 (EL j_f (add_phi_nodes dom_frontiers pred_map live_in
                                 bbs defs)).bb_instructions /\
            inst2.inst_opcode = PHI /\ inst2.inst_outputs = [var]
Proof
  rpt strip_tac >>
  Cases_on `MEM inst (EL j_d bbs).bb_instructions`
  >- ( (* D has v output from ORIGINAL instruction *)
    `MEM var (block_assignments (EL j_d bbs))` by
      (simp[block_assignments_def, MEM_nub, MEM_FLAT, MEM_MAP] >>
       metis_tac[]) >>
    `MEM (EL j_d bbs) bbs` by metis_tac[MEM_EL] >>
    `?dbs. ALOOKUP defs var = SOME dbs /\ MEM d_lbl dbs` by
      metis_tac[] >>
    mp_tac add_phi_nodes_covers >>
    disch_then (qspecl_then [`dom_frontiers`, `pred_map`, `live_in`,
      `defs`, `var`, `dbs`, `d_lbl`, `f`, `j_f`, `bbs`] mp_tac) >>
    simp[] >> metis_tac[])
  >- ( (* D has v output from INSERTED PHI *)
    `inst = build_phi_inst var
      (case ALOOKUP pred_map bbs❲j_d❳.bb_label of
         NONE => [] | SOME ps => ps)` by (
      mp_tac (SIMP_RULE std_ss [LET_THM] add_phi_nodes_new_is_build_phi) >>
      disch_then (qspecl_then [`dom_frontiers`, `pred_map`, `live_in`,
        `bbs`, `defs`, `j_d`, `inst`] mp_tac) >>
      simp[] >> strip_tac >>
      gvs[MEM] >> gvs[build_phi_inst_outputs]) >>
    mp_tac add_phi_nodes_idf_closure >>
    disch_then (qspecl_then [`defs`, `dom_frontiers`, `pred_map`,
      `live_in`, `bbs`, `j_d`, `j_f`, `var`, `f`, `inst`] mp_tac) >>
    simp[])
QED

(* When x is the root of a child in children_rename_states, its entry
   stacks = the stacks parameter passed to children_rename_states. *)
Triviality children_rename_states_root_stacks:
  !children ctrs stacks bbs sm x rs_x xs.
    MEM (DNode x xs) children /\
    ALOOKUP (children_rename_states ctrs stacks bbs sm children) x =
      SOME rs_x /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs = SOME b) ==>
    SND rs_x = stacks
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `h` >> rename1 `DNode c cs :: children` >>
  simp[Once block_rename_states_def, ALOOKUP_APPEND] >>
  strip_tac
  >- gvs[block_rename_states_root_alookup]
  >>
  `MEM x (FLAT (MAP dom_tree_labels children))` by (
    simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
    qexists_tac `DNode x xs` >> simp[dom_tree_labels_def]) >>
  `~MEM x (dom_tree_labels (DNode c cs))` by
    (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `ALOOKUP (block_rename_states (ctrs,stacks) bbs sm (DNode c cs)) x = NONE` by (
    simp[ALOOKUP_NONE] >>
    `MAP FST (block_rename_states (ctrs,stacks) bbs sm (DNode c cs)) =
     dom_tree_labels (DNode c cs)` suffices_by simp[] >>
    irule (CONJUNCT1 block_rename_states_keys) >>
    rpt strip_tac >>
    first_x_assum (qspec_then `l` mp_tac) >> simp[]) >>
  gvs[] >>
  last_x_assum (qspecl_then
    [`case rename_blocks (ctrs,stacks) bbs sm (DNode c cs) of (c',v1) => c'`,
     `stacks`, `bbs`, `sm`, `x`, `rs_x`, `xs`] mp_tac) >>
  simp[] >>
  (impl_tac >- (
    fs[ALL_DISTINCT_APPEND] >>
    rpt strip_tac >>
    first_x_assum (qspec_then `l` mp_tac) >> simp[])) >>
  simp[]
QED

(* The parent returned by dtree_parent is also in the tree *)
Triviality dtree_parent_parent_in_tree:
  !t x p. dtree_parent t x = SOME p ==> MEM p (dom_tree_labels t)
Proof
  ho_match_mp_tac dtree_parent_ind >> rpt strip_tac >> gvs[dtree_parent_def, dom_tree_labels_def, AllCaseEqs()]
QED

(* If dtree_parent returns the root itself, then x is a direct child root *)
Triviality dtree_parent_returns_root:
  !s children x.
    dtree_parent (DNode s children) x = SOME s /\
    ALL_DISTINCT (dom_tree_labels (DNode s children)) ==>
    ?xs. MEM (DNode x xs) children
Proof
  rpt gen_tac >> strip_tac >> Induct_on `children` >- (gvs[dtree_parent_def]) >> rpt strip_tac >> Cases_on `h` >> rename1 `DNode c cs` >> gvs[Once dtree_parent_def] >> pop_assum mp_tac >> Cases_on `c = x` >- (rw[] >> qexists_tac `cs` >> simp[]) >> simp[] >> Cases_on `dtree_parent (DNode c cs) x` >> gvs[AllCaseEqs()] >- (strip_tac >> first_x_assum irule >> gvs[dom_tree_labels_def, ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS]) >> strip_tac >> imp_res_tac dtree_parent_parent_in_tree >> gvs[dom_tree_labels_def, ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

(* If dtree_parent returns p ≠ s, then it comes from a child subtree *)
Triviality dtree_parent_decompose_non_root:
  !s children x p.
    dtree_parent (DNode s children) x = SOME p /\
    p <> s /\
    ALL_DISTINCT (dom_tree_labels (DNode s children)) ==>
    ?dt_c. MEM dt_c children /\ dtree_parent dt_c x = SOME p
Proof
  Induct_on `children` >- simp[dtree_parent_def] >>
rpt gen_tac >>
Cases_on `h` >> rename1 `DNode c cs :: children` >>
simp[Once dtree_parent_def] >>
strip_tac >>
Cases_on `c = x` >- (
  gvs[]
) >>
Cases_on `dtree_parent (DNode c cs) x` >- (
  gvs[] >>
  first_x_assum (qspecl_then [`s`, `x`, `p`] mp_tac) >>
  (impl_tac >- (
    gvs[] >>
    fs[dom_tree_labels_def, ALL_DISTINCT_APPEND]
  )) >>
  strip_tac >>
  qexists `dt_c` >> simp[]
) >>
gvs[] >>
qexists `DNode c cs` >> simp[]
QED

(* INDEX_OF on append: if x not in prefix, INDEX_OF shifts by prefix length *)
Triviality INDEX_OF_APPEND_right:
  !pfx sfx x i.
    ~MEM x pfx /\ INDEX_OF x sfx = SOME i ==>
    INDEX_OF x (pfx ++ sfx) = SOME (LENGTH pfx + i)
Proof
  rpt strip_tac >> gvs[INDEX_OF_eq_SOME, EL_APPEND_EQN, LENGTH_APPEND] >> rpt strip_tac >> Cases_on `j < LENGTH pfx` >> gvs[] >> metis_tac[MEM_EL]
QED

Triviality INDEX_OF_APPEND_left:
  !pfx sfx x i.
    ~MEM x sfx /\ INDEX_OF x pfx = SOME i ==>
    INDEX_OF x (pfx ++ sfx) = SOME i
Proof
  rpt strip_tac >> gvs[INDEX_OF_eq_SOME, EL_APPEND_EQN, LENGTH_APPEND] >>
  rpt strip_tac >> Cases_on `j < LENGTH pfx` >> gvs[] >> metis_tac[MEM_EL]
QED

Triviality ALL_DISTINCT_FLAT_MEM:
  !ls x. ALL_DISTINCT (FLAT ls) /\ MEM x ls ==> ALL_DISTINCT x
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

(* Parent has smaller INDEX_OF than child in dom_tree_labels (preorder) *)
Triviality parent_index_lt:
  !dtree lbl q i_lbl i_q.
    ALL_DISTINCT (dom_tree_labels dtree) /\
    dtree_parent dtree lbl = SOME q /\
    INDEX_OF lbl (dom_tree_labels dtree) = SOME i_lbl /\
    INDEX_OF q (dom_tree_labels dtree) = SOME i_q ==>
    i_q < i_lbl
Proof
  ho_match_mp_tac dtree_parent_ind >> rpt conj_tac
  >- simp[dtree_parent_def]
  >> rpt strip_tac >>
  gvs[dtree_parent_def] >>
  Cases_on `c = lbl'` >> gvs[] >>
  Cases_on `dtree_parent (DNode c cs) lbl'` >> gvs[] >>
  fs[dom_tree_labels_def, ETA_THM] >>
  TRY (gvs[INDEX_OF_def, INDEX_FIND_def] >> NO_TAC)
  (* Goal 1: NONE case - lbl' in rest *)
  >- (
    `lbl' <> lbl` by (
  CCONTR_TAC >> gvs[] >>
  qpat_x_assum `dtree_parent (DNode lbl rest) lbl = SOME q` mp_tac >>
  mp_tac (Q.SPECL [`DNode lbl rest`, `lbl`, `q`] dtree_parent_not_root) >>
  simp[dom_tree_labels_def, ETA_THM] >>
  gvs[ALL_DISTINCT_APPEND]
) >>
  `~MEM lbl' (FLAT (MAP dom_tree_labels cs))` by (
  strip_tac >>
  `MEM lbl' (dom_tree_labels (DNode c cs))` by simp[dom_tree_labels_def, ETA_THM] >>
  `ALL_DISTINCT (dom_tree_labels (DNode c cs))` by (
    simp[dom_tree_labels_def, ETA_THM, ALL_DISTINCT] >>
    gvs[ALL_DISTINCT_APPEND]
  ) >>
  `lbl' <> c` by metis_tac[] >>
  mp_tac (Q.SPECL [`DNode c cs`, `lbl'`, `c`, `cs`] non_root_has_parent) >>
  simp[] >>
  metis_tac[optionTheory.NOT_NONE_SOME]
) >>
    `MEM lbl' (FLAT (MAP dom_tree_labels rest))` by
      (imp_res_tac dtree_parent_in_tree >>
       gvs[dom_tree_labels_def, ETA_THM]) >>
    `MEM q (dom_tree_labels (DNode lbl rest))` by
      (irule dtree_parent_parent_in_tree >> metis_tac[]) >>
    `MEM q (lbl::FLAT (MAP dom_tree_labels rest))` by
      gvs[dom_tree_labels_def, ETA_THM] >>
    `ALL_DISTINCT (FLAT (MAP dom_tree_labels rest))` by
      gvs[ALL_DISTINCT_APPEND] >>
    `?il. INDEX_OF lbl' (lbl::FLAT (MAP dom_tree_labels rest)) = SOME il` by
      (Cases_on `INDEX_OF lbl' (lbl::FLAT (MAP dom_tree_labels rest))` >>
       gvs[INDEX_OF_eq_NONE]) >>
    `?iq. INDEX_OF q (lbl::FLAT (MAP dom_tree_labels rest)) = SOME iq` by
      (Cases_on `INDEX_OF q (lbl::FLAT (MAP dom_tree_labels rest))` >>
       gvs[INDEX_OF_eq_NONE]) >>
    first_x_assum (qspecl_then [`il`, `iq`] mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on `q = lbl` >- (
  gvs[] >>
  qpat_x_assum `INDEX_OF lbl (lbl::c::_) = SOME i_q` mp_tac >>
  simp[INDEX_OF_eq_SOME] >> strip_tac >>
  qpat_x_assum `INDEX_OF lbl' (lbl::c::_) = SOME i_lbl` mp_tac >>
  simp[INDEX_OF_eq_SOME] >> strip_tac >>
  `i_q = 0` by (
    Cases_on `i_q` >> simp[] >>
    rename1 `SUC n < _` >>
    qpat_x_assum `!j. j < SUC n ==> _` (qspec_then `0` mp_tac) >>
    simp[]
  ) >>
  `0 < i_lbl` by (
    Cases_on `i_lbl` >> simp[] >>
    gvs[]
  ) >>
  gvs[]
) >>
  rpt strip_tac >>
 `MEM q (FLAT (MAP dom_tree_labels rest))` by (
   fs[MEM] >> gvs[]) >>
 `¬MEM q (FLAT (MAP dom_tree_labels cs))` by (
   fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
 `q ≠ c` by (
   strip_tac >> gvs[] >> fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
 `¬MEM lbl' (c::FLAT (MAP dom_tree_labels cs))` by simp[] >>
 `¬MEM q (c::FLAT (MAP dom_tree_labels cs))` by simp[] >>
 `∃iq'. INDEX_OF q (FLAT (MAP dom_tree_labels rest)) = SOME iq'` by (
   Cases_on `INDEX_OF q (FLAT (MAP dom_tree_labels rest))` >> fs[INDEX_OF_eq_NONE]) >>
 `∃il'. INDEX_OF lbl' (FLAT (MAP dom_tree_labels rest)) = SOME il'` by (
   Cases_on `INDEX_OF lbl' (FLAT (MAP dom_tree_labels rest))` >> fs[INDEX_OF_eq_NONE]) >>
 `INDEX_OF q (lbl::FLAT (MAP dom_tree_labels rest)) = SOME (1 + iq')` by (
   `¬MEM q [lbl]` by simp[] >>
   drule_all INDEX_OF_APPEND_right >>
   simp[]) >>
 `INDEX_OF lbl' (lbl::FLAT (MAP dom_tree_labels rest)) = SOME (1 + il')` by (
   `¬MEM lbl' [lbl]` by simp[] >>
   drule_all INDEX_OF_APPEND_right >>
   simp[]) >>
 `iq = 1 + iq'` by fs[] >>
 `il = 1 + il'` by fs[] >>
 `iq' < il'` by decide_tac >>
 `¬MEM q ([lbl] ++ c::FLAT (MAP dom_tree_labels cs))` by simp[] >>
 `¬MEM lbl' ([lbl] ++ c::FLAT (MAP dom_tree_labels cs))` by simp[] >>
 `INDEX_OF q ([lbl] ++ c::FLAT (MAP dom_tree_labels cs) ++ FLAT (MAP dom_tree_labels rest)) = SOME (LENGTH ([lbl] ++ c::FLAT (MAP dom_tree_labels cs)) + iq')` by (
   irule INDEX_OF_APPEND_right >> simp[] >>
   irule INDEX_OF_APPEND_right >> simp[]) >>
 `INDEX_OF lbl' ([lbl] ++ c::FLAT (MAP dom_tree_labels cs) ++ FLAT (MAP dom_tree_labels rest)) = SOME (LENGTH ([lbl] ++ c::FLAT (MAP dom_tree_labels cs)) + il')` by (
   irule INDEX_OF_APPEND_right >> simp[] >>
   irule INDEX_OF_APPEND_right >> simp[]) >>
 `[lbl] ++ c::FLAT (MAP dom_tree_labels cs) ++ FLAT (MAP dom_tree_labels rest) = lbl::c::(FLAT (MAP dom_tree_labels cs) ++ FLAT (MAP dom_tree_labels rest))` by simp[] >>
 pop_assum (fn eq =>
   qpat_x_assum `INDEX_OF q ([lbl] ++ _ ++ _) = _` (fn th => assume_tac (REWRITE_RULE [eq] th)) >>
   qpat_x_assum `INDEX_OF lbl' ([lbl] ++ _ ++ _) = _` (fn th => assume_tac (REWRITE_RULE [eq] th))) >>
 `i_q = LENGTH ([lbl] ++ c::FLAT (MAP dom_tree_labels cs)) + iq'` by fs[] >>
 `i_lbl = LENGTH ([lbl] ++ c::FLAT (MAP dom_tree_labels cs)) + il'` by fs[] >>
 decide_tac
  ) >>
  (* Goal 2: SOME case - lbl' in first child *)
  `MEM lbl' (dom_tree_labels (DNode c cs))` by
    (irule dtree_parent_in_tree >> metis_tac[]) >>
  `MEM q (dom_tree_labels (DNode c cs))` by
    (irule dtree_parent_parent_in_tree >> metis_tac[]) >>
  `MEM lbl' (c::FLAT (MAP dom_tree_labels cs))` by
    (gvs[dom_tree_labels_def, ETA_THM]) >>
  `MEM q (c::FLAT (MAP dom_tree_labels cs))` by
    (gvs[dom_tree_labels_def, ETA_THM]) >>
  `~MEM lbl' (FLAT (MAP dom_tree_labels rest))` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `~MEM q (FLAT (MAP dom_tree_labels rest))` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `lbl' <> lbl` by (strip_tac >> gvs[]) >>
  `q <> lbl` by (strip_tac >> gvs[]) >>
  `ALL_DISTINCT (FLAT (MAP dom_tree_labels cs))` by
    gvs[ALL_DISTINCT_APPEND] >>
  `MEM lbl' (c::FLAT (MAP dom_tree_labels cs))` by
    (Cases_on `lbl' = c` >> gvs[]) >>
  `MEM q (c::FLAT (MAP dom_tree_labels cs))` by
    (Cases_on `q = c` >> gvs[]) >>
  `?j_lbl. INDEX_OF lbl' (c::FLAT (MAP dom_tree_labels cs)) = SOME j_lbl` by
    (Cases_on `INDEX_OF lbl' (c::FLAT (MAP dom_tree_labels cs))` >>
     gvs[INDEX_OF_eq_NONE]) >>
  `?j_q. INDEX_OF q (c::FLAT (MAP dom_tree_labels cs)) = SOME j_q` by
    (Cases_on `INDEX_OF q (c::FLAT (MAP dom_tree_labels cs))` >>
     gvs[INDEX_OF_eq_NONE]) >>
  `j_q < j_lbl` by
    (first_x_assum irule >> simp[]) >>
  `INDEX_OF lbl' ((c::FLAT (MAP dom_tree_labels cs)) ++ FLAT (MAP dom_tree_labels rest)) = SOME j_lbl` by
    (irule INDEX_OF_APPEND_left >> simp[]) >>
  `INDEX_OF q ((c::FLAT (MAP dom_tree_labels cs)) ++ FLAT (MAP dom_tree_labels rest)) = SOME j_q` by
    (irule INDEX_OF_APPEND_left >> simp[]) >>
  `INDEX_OF lbl' (c::(FLAT (MAP dom_tree_labels cs) ++ FLAT (MAP dom_tree_labels rest))) = SOME j_lbl` by
    (qpat_x_assum `INDEX_OF lbl' ((_ :: _) ++ _) = _` mp_tac >>
     simp[APPEND]) >>
  `INDEX_OF q (c::(FLAT (MAP dom_tree_labels cs) ++ FLAT (MAP dom_tree_labels rest))) = SOME j_q` by
    (qpat_x_assum `INDEX_OF q ((_ :: _) ++ _) = _` mp_tac >>
     simp[APPEND]) >>
  `INDEX_OF lbl' ([lbl] ++ c::(FLAT (MAP dom_tree_labels cs) ++ FLAT (MAP dom_tree_labels rest))) = SOME (LENGTH [lbl] + j_lbl)` by
    (irule INDEX_OF_APPEND_right >> simp[INDEX_OF_eq_NONE]) >>
  `INDEX_OF q ([lbl] ++ c::(FLAT (MAP dom_tree_labels cs) ++ FLAT (MAP dom_tree_labels rest))) = SOME (LENGTH [lbl] + j_q)` by
    (irule INDEX_OF_APPEND_right >> simp[INDEX_OF_eq_NONE]) >>
  `i_lbl = 1 + j_lbl` by
    (qpat_x_assum `INDEX_OF lbl' (lbl::_) = SOME i_lbl` mp_tac >>
     qpat_x_assum `INDEX_OF lbl' ([lbl] ++ _) = SOME _` mp_tac >>
     simp[]) >>
  `i_q = 1 + j_q` by
    (qpat_x_assum `INDEX_OF q (lbl::_) = SOME i_q` mp_tac >>
     qpat_x_assum `INDEX_OF q ([lbl] ++ _) = SOME _` mp_tac >>
     simp[]) >>
  simp[]
QED

(* child_entry_stacks: If x has parent p in the dom tree, then x's entry
   stacks in block_rename_states equal the stacks from p's exit state
   (SND of FST of rename_block_insts applied to p's block).
   CONJUNCT2: mutual induction helper for children_rename_states.
   When x is the root of a child, its entry stacks = parent stacks.
   When x is deeper, the IH applies within that child's subtree. *)
Triviality child_entry_stacks:
  (!dt rs bbs sm x rs_x p.
    ALOOKUP (block_rename_states rs bbs sm dt) x = SOME rs_x /\
    dtree_parent dt x = SOME p /\
    ALL_DISTINCT (dom_tree_labels dt) /\
    (!l. MEM l (dom_tree_labels dt) ==> ?b. lookup_block l bbs = SOME b) ==>
    ?rs_p bb_p.
      ALOOKUP (block_rename_states rs bbs sm dt) p = SOME rs_p /\
      lookup_block p bbs = SOME bb_p /\
      SND rs_x = SND (FST (rename_block_insts rs_p bb_p.bb_instructions))) /\
  (!children ctrs stacks bbs sm x rs_x p dt_c.
    ALOOKUP (children_rename_states ctrs stacks bbs sm children) x = SOME rs_x /\
    MEM dt_c children /\
    dtree_parent dt_c x = SOME p /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs = SOME b) ==>
    ?rs_p bb_p.
      ALOOKUP (children_rename_states ctrs stacks bbs sm children) p = SOME rs_p /\
      lookup_block p bbs = SOME bb_p /\
      SND rs_x = SND (FST (rename_block_insts rs_p bb_p.bb_instructions)))
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:dom_tree``) >>
  conj_tac >> TRY (conj_tac >- simp[]) >|
  [(* dnode case *)
  rpt strip_tac >>
  qpat_x_assum `ALOOKUP (block_rename_states _ _ _ _) _ = _` mp_tac >>
  simp[Once block_rename_states_def] >>
  Cases_on `lookup_block s bbs` >> simp[]
  >- (
    strip_tac >> gvs[] >>
    imp_res_tac dtree_parent_not_root >> gvs[])
  >>
  pairarg_tac >> simp[] >> strip_tac >>
  Cases_on `s = x` >> gvs[]
  >- (imp_res_tac dtree_parent_not_root >> gvs[])
  >>
  Cases_on `s = p` >> gvs[]
  >- (
    qexists_tac `rs` >>
    simp[block_rename_states_root_alookup] >>
    drule dtree_parent_returns_root >> simp[] >> strip_tac >>
    drule children_rename_states_root_stacks >>
    disch_then drule >>
    (impl_tac >- (
      gvs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND] >>
      rpt strip_tac >> first_x_assum match_mp_tac >>
      simp[dom_tree_labels_def, ETA_THM])) >>
    simp[])
  >>
  drule dtree_parent_decompose_non_root >>
  simp[] >> strip_tac >>
  last_x_assum (qspecl_then
    [`FST rs1`, `SND rs1`, `bbs`, `sm`, `x`, `rs_x`, `p`, `dt_c`] mp_tac) >>
  (impl_tac >- (
    simp[] >>
    gvs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND] >>
    rpt strip_tac >> first_x_assum match_mp_tac >>
    simp[dom_tree_labels_def, ETA_THM])) >>
  strip_tac >>
  qexistsl_tac [`rs_p`, `bb_p`] >> simp[] >>
  simp[Once block_rename_states_def],
  (* cons case *)
  rpt strip_tac >>
  qpat_x_assum `ALOOKUP (children_rename_states _ _ _ _ (_ :: _)) _ = _` mp_tac >>
  simp[Once block_rename_states_def, ALOOKUP_APPEND] >>
  Cases_on `MEM dt_c children` >- (
    `MEM x (FLAT (MAP dom_tree_labels children))` by (
      imp_res_tac dtree_parent_in_tree >>
      Cases_on `dt_c` >>
      gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      metis_tac[]) >>
    `~MEM x (dom_tree_labels dt)` by
      (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
    `ALOOKUP (block_rename_states (ctrs,stacks) bbs sm dt) x = NONE` by (
      simp[ALOOKUP_NONE] >>
      `MAP FST (block_rename_states (ctrs,stacks) bbs sm dt) =
       dom_tree_labels dt` suffices_by simp[] >>
      irule (CONJUNCT1 block_rename_states_keys) >>
      rpt strip_tac >> first_x_assum (qspec_then `l` mp_tac) >> simp[]) >>
    simp[] >> strip_tac >>
    last_x_assum (qspecl_then
      [`case rename_blocks (ctrs,stacks) bbs sm dt of (c',v1) => c'`,
       `stacks`, `bbs`, `sm`, `x`, `rs_x`, `p`, `dt_c`] mp_tac) >>
    (impl_tac >- (
      simp[] >>
      fs[ALL_DISTINCT_APPEND] >>
      rpt strip_tac >> first_x_assum (qspec_then `l` mp_tac) >> simp[])) >>
    strip_tac >>
    qexistsl_tac [`rs_p`, `bb_p`] >> simp[] >>
    simp[Once block_rename_states_def, ALOOKUP_APPEND] >>
    imp_res_tac dtree_parent_parent_in_tree >>
    `MEM p (FLAT (MAP dom_tree_labels children))` by (
      Cases_on `dt_c` >>
      gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      metis_tac[]) >>
    `~MEM p (dom_tree_labels dt)` by
      (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
    `ALOOKUP (block_rename_states (ctrs,stacks) bbs sm dt) p = NONE` by (
      simp[ALOOKUP_NONE] >>
      `MAP FST (block_rename_states (ctrs,stacks) bbs sm dt) =
       dom_tree_labels dt` suffices_by simp[] >>
      irule (CONJUNCT1 block_rename_states_keys) >>
      rpt strip_tac >> first_x_assum (qspec_then `l` mp_tac) >> simp[]) >>
    simp[])
  >>
  gvs[] >> strip_tac >> Cases_on `ALOOKUP (block_rename_states (ctrs,stacks) bbs sm dt) x` >> gvs[]
  >- (
    `MAP FST (block_rename_states (ctrs,stacks) bbs sm dt) = dom_tree_labels dt` by (
      irule (CONJUNCT1 block_rename_states_keys) >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
    fs[ALOOKUP_NONE] >>
    metis_tac[dtree_parent_in_tree]) >>
  last_x_assum $ qspecl_then [`(ctrs,stacks)`,`bbs`,`sm`,`x`,`rs_x`,`p`] mp_tac >> simp[] >> (impl_tac >- (gvs[ALL_DISTINCT_APPEND] >> metis_tac[])) >> strip_tac >> qexistsl [`rs_p`,`bb_p`] >> simp[] >> simp[Once block_rename_states_def, ALOOKUP_APPEND]]
QED

(* version_diff_finds_def: If the entry rename state of some node lbl
   has a different latest_version for v than the subtree root's entry,
   then some block in the subtree has v as an instruction output and
   dominates lbl. Mutual induction on dom_tree. *)
Triviality version_diff_finds_def:
  (!dt rs bbs sm lbl rs_lbl v entry.
    ALOOKUP (block_rename_states rs bbs sm dt) lbl = SOME rs_lbl /\
    latest_version rs_lbl v <> latest_version rs v /\
    ALL_DISTINCT (dom_tree_labels dt) /\
    (!c p. dtree_parent dt c = SOME p ==>
       cfg_dominates bbs entry p c) /\
    (!l. MEM l (dom_tree_labels dt) ==>
       ?b. lookup_block l bbs = SOME b) ==>
    ?D bb_D. lookup_block D bbs = SOME bb_D /\
             MEM D (dom_tree_labels dt) /\
             (?inst. MEM inst bb_D.bb_instructions /\
                     MEM v inst.inst_outputs) /\
             cfg_dominates bbs entry D lbl) /\
  (!children ctrs stacks bbs sm lbl rs_lbl v entry.
    ALOOKUP (children_rename_states ctrs stacks bbs sm children) lbl =
      SOME rs_lbl /\
    latest_version rs_lbl v <> latest_version (ctrs, stacks) v /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
    (!c p dt. MEM dt children /\ dtree_parent dt c = SOME p ==>
       cfg_dominates bbs entry p c) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
       ?b. lookup_block l bbs = SOME b) ==>
    ?D bb_D. lookup_block D bbs = SOME bb_D /\
             MEM D (FLAT (MAP dom_tree_labels children)) /\
             (?inst. MEM inst bb_D.bb_instructions /\
                     MEM v inst.inst_outputs) /\
             cfg_dominates bbs entry D lbl)
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:dom_tree``) >>
  rpt conj_tac
  >- ((* P0: DNode s l *)
    rpt strip_tac >>
    qpat_x_assum `ALOOKUP _ _ = SOME _` mp_tac >>
    simp[Once block_rename_states_def] >>
    Cases_on `lookup_block s bbs` >> simp[pairTheory.UNCURRY]
    >- ((* NONE: alist is [(s,rs)], lbl=s, contradiction *)
      strip_tac >> gvs[])
    >> ((* SOME x *)
      Cases_on `s = lbl`
      >- (simp[] >> strip_tac >> gvs[])
      >> (simp[] >> strip_tac >>
        Cases_on `latest_version
          (FST (rename_block_insts rs x.bb_instructions)) v =
          latest_version rs v`
        >- ((* version unchanged: use children IH *)
          first_x_assum (qspecl_then [
            `FST (FST (rename_block_insts rs x.bb_instructions))`,
            `SND (FST (rename_block_insts rs x.bb_instructions))`,
            `bbs`, `sm`, `lbl`, `rs_lbl`, `v`, `entry`] mp_tac) >>
          impl_tac
          >- (rpt conj_tac
            >- gvs[]
            >- gvs[]
            >- gvs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND]
            >- (rpt strip_tac >>
                first_x_assum match_mp_tac >>
                irule dtree_parent_child_subtree >>
                simp[] >> qexists_tac `dt` >> simp[])
            >> (rpt strip_tac >> first_x_assum match_mp_tac >>
                simp[dom_tree_labels_def, ETA_THM]))
          >> (strip_tac >>
            qexists_tac `D` >> qexists_tac `bb_D` >> gvs[] >>
            simp[dom_tree_labels_def, ETA_THM] >>
            qexists_tac `inst` >> gvs[]))
        >> ((* version changed: D = s *)
          `?i. MEM i x.bb_instructions /\ MEM v i.inst_outputs` by
            (CCONTR_TAC >>
             `!i. MEM i x.bb_instructions ==> ~MEM v i.inst_outputs` by
               metis_tac[] >>
             `latest_version
                (FST (rename_block_insts rs x.bb_instructions)) v =
              latest_version rs v` by
               (match_mp_tac rename_block_insts_non_output_stable_any >>
                rpt strip_tac >> res_tac) >>
             fs[]) >>
          qexists_tac `s` >> qexists_tac `x` >>
          simp[dom_tree_labels_def, ETA_THM] >>
          conj_tac >- metis_tac[] >>
          `MEM lbl (FLAT (MAP dom_tree_labels children))` by
            (imp_res_tac alistTheory.ALOOKUP_MEM >>
             `MAP FST (children_rename_states
               (FST (FST (rename_block_insts rs x.bb_instructions)))
               (SND (FST (rename_block_insts rs x.bb_instructions)))
               bbs sm children) =
              FLAT (MAP dom_tree_labels children)` by
               (irule (CONJUNCT2 block_rename_states_keys) >>
                rpt strip_tac >> first_x_assum match_mp_tac >>
                simp[dom_tree_labels_def, ETA_THM]) >>
             metis_tac[MEM_MAP, pairTheory.FST]) >>
          irule dom_tree_root_dominates >>
          qexists_tac `children` >>
          qexists_tac `DNode s children` >>
          simp[dom_tree_labels_def, ETA_THM] >> gvs[]))))
  >- ((* P1 base: children = [] *)
    simp[block_rename_states_def])
  >> ((* P1 step: d::l *)
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qpat_x_assum `ALOOKUP (children_rename_states _ _ _ _ (_::_)) _ = _`
      mp_tac >>
    simp[block_rename_states_def, LET_THM, alistTheory.ALOOKUP_APPEND] >>
    Cases_on `ALOOKUP (block_rename_states (ctrs,stacks) bbs sm dt) lbl`
    >- ( (* NONE: lbl in rest children *)
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [
        `FST (rename_blocks (ctrs,stacks) bbs sm dt)`,
        `stacks`, `bbs`, `sm`, `lbl`, `rs_lbl`, `v`, `entry`] mp_tac) >>
      impl_tac
      >- (rpt conj_tac
        >- (Cases_on `rename_blocks (ctrs,stacks) bbs sm dt` >> gvs[])
        >- gvs[latest_version_def]
        >- gvs[ALL_DISTINCT_APPEND]
        >- metis_tac[MEM]
        >> (rpt strip_tac >> first_x_assum match_mp_tac >>
            simp[dom_tree_labels_def, ETA_THM]))
      >> (strip_tac >>
          qexists_tac `D` >> qexists_tac `bb_D` >> gvs[] >>
          qexists_tac `inst` >> gvs[]))
    >> ( (* SOME x: lbl in child dt *)
      strip_tac >>
      first_x_assum (qspecl_then [`(ctrs,stacks)`, `bbs`, `sm`,
        `lbl`, `x`, `v`, `entry`] mp_tac) >>
      impl_tac
      >- (rpt conj_tac
        >- gvs[]
        >- gvs[]
        >- (gvs[ALL_DISTINCT_APPEND, dom_tree_labels_def, ETA_THM])
        >- metis_tac[MEM]
        >> (rpt strip_tac >> first_x_assum match_mp_tac >>
            simp[dom_tree_labels_def, ETA_THM]))
      >> (strip_tac >>
          qexists_tac `D` >> qexists_tac `bb_D` >> gvs[] >>
          simp[MEM_FLAT, MEM_MAP] >> metis_tac[])))
QED

Triviality version_diff_below_root:
  !s children rs bbs sm lbl rs_lbl v entry bb_s.
    ALOOKUP (block_rename_states rs bbs sm (DNode s children)) lbl = SOME rs_lbl /\
    lookup_block s bbs = SOME bb_s /\
    latest_version rs_lbl v <>
      latest_version (FST (rename_block_insts rs bb_s.bb_instructions)) v /\
    lbl <> s /\
    ALL_DISTINCT (dom_tree_labels (DNode s children)) /\
    (!c p. dtree_parent (DNode s children) c = SOME p ==>
       cfg_dominates bbs entry p c) /\
    (!l. MEM l (dom_tree_labels (DNode s children)) ==>
       ?b. lookup_block l bbs = SOME b) ==>
    ?D bb_D. lookup_block D bbs = SOME bb_D /\
             MEM D (dom_tree_labels (DNode s children)) /\
             D <> s /\
             (?inst. MEM inst bb_D.bb_instructions /\
                     MEM v inst.inst_outputs) /\
             cfg_dominates bbs entry D lbl
Proof
  rpt gen_tac >> strip_tac >>
  gvs[Once block_rename_states_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `rs1` >> gvs[] >>
  `?D bb_D.
     lookup_block D bbs = SOME bb_D /\
     MEM D (FLAT (MAP dom_tree_labels children)) /\
     (?inst. MEM inst bb_D.bb_instructions /\ MEM v inst.inst_outputs) /\
     cfg_dominates bbs entry D lbl` by (
    match_mp_tac (Q.SPECL [`children`, `q`, `r`, `bbs`, `sm`,
        `lbl`, `rs_lbl`, `v`, `entry`] (CONJUNCT2 version_diff_finds_def)) >>
    gvs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND] >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`c`, `p`] mp_tac) >>
    (impl_tac >- (irule dtree_parent_child_subtree >>
                   gvs[dom_tree_labels_def, ETA_THM] >> metis_tac[])) >>
    simp[]) >>
  qexistsl_tac [`D`, `bb_D`] >>
  gvs[dom_tree_labels_def, ETA_THM, ALL_DISTINCT_APPEND] >>
  metis_tac[]
QED

Triviality version_propagation_finds_def:
  !n dtree rs bbs sm lbl rs_lbl v entry parent_b rs_pb bb_pb.
    n = THE (INDEX_OF lbl (dom_tree_labels dtree)) /\
    ALL_DISTINCT (dom_tree_labels dtree) /\
    ALOOKUP (block_rename_states rs bbs sm dtree) lbl = SOME rs_lbl /\
    ALOOKUP (block_rename_states rs bbs sm dtree) parent_b = SOME rs_pb /\
    lookup_block parent_b bbs = SOME bb_pb /\
    latest_version rs_lbl v <>
      latest_version (FST (rename_block_insts rs_pb bb_pb.bb_instructions)) v /\
    cfg_dominates bbs entry parent_b lbl /\
    parent_b <> lbl /\
    MEM parent_b (dom_tree_labels dtree) /\
    MEM lbl (dom_tree_labels dtree) /\
    (!c p. dtree_parent dtree c = SOME p ==>
       cfg_dominates bbs entry p c) /\
    (!d c. cfg_dominates bbs entry d c /\ d <> c /\
           (?p_c. dtree_parent dtree c = SOME p_c) ==>
           ?p_c. dtree_parent dtree c = SOME p_c /\
                 (cfg_dominates bbs entry d p_c \/ d = p_c)) /\
    (!d n'. cfg_dominates bbs entry d n' ==>
            cfg_dominates bbs entry n' d ==> d = n') /\
    (!l. MEM l (dom_tree_labels dtree) ==>
       ?b. lookup_block l bbs = SOME b) ==>
    ?D bb_D. lookup_block D bbs = SOME bb_D /\
             MEM D (dom_tree_labels dtree) /\
             cfg_dominates bbs entry parent_b D /\
             parent_b <> D /\
             (?inst. MEM inst bb_D.bb_instructions /\
                     MEM v inst.inst_outputs) /\
             cfg_dominates bbs entry D lbl
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `dtree` >>
  `lbl <> s` by (
    CCONTR_TAC >> fs[] >>
    `cfg_dominates bbs entry s parent_b` by (
      irule dom_tree_root_dominates >>
      qexists_tac `l` >> qexists_tac `DNode s l` >>
      gvs[]) >>
    `parent_b = s` by (
      first_x_assum (qspecl_then [`parent_b`, `s`] mp_tac) >> simp[]) >>
    gvs[]) >>
  mp_tac (Q.SPECL [`DNode s l`, `lbl`, `s`, `l`] non_root_has_parent) >> simp[] >> strip_tac >>
  qpat_assum `!d c. cfg_dominates _ _ d c /\ d <> c /\ _ ==> _` (qspecl_then [`parent_b`, `lbl`] mp_tac) >> (impl_tac >- (rpt conj_tac >> gvs[] >> metis_tac[])) >>
  disch_then (qx_choose_then `p_c` (fn th =>
    assume_tac (CONJUNCT1 th) >> assume_tac (CONJUNCT2 th))) >>
  `p_c = p` by gvs[] >> pop_assum (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq])) >>
  (* Now single goal with assumption: cfg_dominates bbs entry parent_b p \/ parent_b = p *)
  qspecl_then [`DNode s l`, `rs`, `bbs`, `sm`, `lbl`, `rs_lbl`, `p`] mp_tac (CONJUNCT1 child_entry_stacks) >> (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `latest_version rs_lbl v = latest_version (FST (rename_block_insts rs_p bb_p.bb_instructions)) v` by (
    Cases_on `rs_lbl` >> Cases_on `FST (rename_block_insts rs_p bb_p.bb_instructions)` >>
    gvs[] >> metis_tac[latest_version_stacks_eq]) >>
  `parent_b <> p` by (
  strip_tac >> gvs[]
) >>
  `cfg_dominates bbs entry parent_b p` by (
  qpat_x_assum `_ ∨ _` mp_tac >> simp[]
) >>
  imp_res_tac dtree_parent_parent_in_tree >>
  `cfg_dominates bbs entry p lbl` by
    (qpat_assum `!c p. dtree_parent _ c = SOME p ==> _` (qspecl_then [`lbl`, `p`] mp_tac) >> simp[]) >>
  Cases_on `latest_version (FST (rename_block_insts rs_p bb_p.bb_instructions)) v = latest_version rs_p v`
  >- (
    (* Case b: versions equal at p, apply IH *)
    gvs[] >>
    Cases_on `INDEX_OF lbl (dom_tree_labels (DNode s l))` >> Cases_on `INDEX_OF p (dom_tree_labels (DNode s l))` >> gvs[INDEX_OF_eq_NONE] >> rename1 `INDEX_OF lbl _ = SOME i_lbl` >> rename1 `INDEX_OF p _ = SOME i_p` >> qspecl_then [`DNode s l`, `lbl`, `p`, `i_lbl`, `i_p`] mp_tac parent_index_lt >> (impl_tac >- gvs[]) >> strip_tac >>
    first_x_assum (qspec_then `i_p` mp_tac) >> (impl_tac >- simp[]) >> disch_then (qspecl_then [`DNode s l`, `rs`, `bbs`, `sm`, `p`, `rs_p`, `v`, `entry`, `parent_b`, `rs_pb`, `bb_pb`] mp_tac) >> (impl_tac >- (rpt conj_tac >> gvs[] >> metis_tac[])) >>
    strip_tac >>
    qexistsl [`D`, `bb_D`] >> gvs[] >>
    conj_tac >- metis_tac[] >>
    irule cfg_dominates_trans >>
    qexists_tac `p` >> gvs[])
  >> (
    (* Case a: versions differ at p, D = p *)
    `?inst. MEM inst bb_p.bb_instructions /\ MEM v inst.inst_outputs` by (
      CCONTR_TAC >> fs[] >>
      `!i. MEM i bb_p.bb_instructions ==> ~MEM v i.inst_outputs` by metis_tac[] >>
      qpat_x_assum `latest_version (FST (rename_block_insts rs_p _)) v <> latest_version rs_p v` mp_tac >>
      simp[] >>
      match_mp_tac rename_block_insts_non_output_stable_any >> simp[]) >>
    qexistsl [`p`, `bb_p`] >> gvs[] >> metis_tac[])
QED

Triviality succs_preserved_cfg_path:
  !bbs1 bbs2 path.
    succs_preserved bbs1 bbs2 /\
    MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) bbs2 ==>
    (cfg_path bbs2 path <=> cfg_path bbs1 path)
Proof
  ntac 2 gen_tac >> Induct >- simp[cfg_path_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `path`
  >- (simp[cfg_path_def] >>
      drule lookup_block_labels_agree >>
      disch_then (qspec_then `h` mp_tac) >>
      Cases_on `lookup_block h bbs2` >> Cases_on `lookup_block h bbs1` >> gvs[]) >>
  simp[cfg_path_def] >>
  first_x_assum (drule_then assume_tac) >>
  EQ_TAC >> strip_tac
  >- (gvs[succs_preserved_def] >>
      first_x_assum drule >> strip_tac >>
      qexists_tac `bb0` >> gvs[])
  >- (conj_tac >- (
        drule (iffLR lookup_block_labels_agree) >>
        disch_then (qspec_then `h` mp_tac) >> simp[] >> strip_tac >>
        Cases_on `lookup_block h bbs2` >> gvs[] >>
        gvs[succs_preserved_def] >>
        first_x_assum (qspecl_then [`h`] mp_tac) >> simp[] >>
        strip_tac >> qexists_tac `x` >> gvs[]) >>
      first_assum ACCEPT_TAC)
QED

(* ===== Obligation 1: valid_phi_coverage ===== *)

Theorem phi_coverage:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI /\
              EVERY colon_free inst.inst_outputs) ==>
    let ordered_bbs = MAP THE (FILTER IS_SOME
          (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)) in
    let defs = compute_defs ordered_bbs in
    let bbs1 = add_phi_nodes dom_frontiers pred_map live_in
                 func.fn_blocks defs in
    let rs0 = init_rename_state defs in
    valid_phi_coverage bbs1 dtree succ_map rs0 live_in
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `valid_phi_coverage bbs1_ _ _ rs0_ _` >>
  simp[valid_phi_coverage_def] >> rpt strip_tac >>
  `MAP (\bb. bb.bb_label) bbs1_ = MAP (\bb. bb.bb_label) func.fn_blocks` by
    simp[Abbr `bbs1_`, add_phi_nodes_preserves_labels] >>
  `!l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs1_ = SOME b` by
    metis_tac[dom_labels_have_blocks, fn_labels_def] >>
  `succs_preserved func.fn_blocks bbs1_` by (
    irule phi_extends_succs_preserved >>
    simp[Abbr `bbs1_`, add_phi_nodes_phi_extends] >>
    fs[wf_function_def, fn_labels_def]) >>
  `!path. cfg_path bbs1_ path <=> cfg_path func.fn_blocks path` by
    (irule succs_preserved_cfg_path >> simp[]) >>
  `!entry' a b. cfg_dominates bbs1_ entry' a b <=> cfg_dominates func.fn_blocks entry' a b` by
    simp[cfg_dominates_def] >>
  qpat_x_assum `valid_dom_tree _ _ _ _`
    (fn th => EVERY [strip_assume_tac
      (REWRITE_RULE[makeSsaDefsTheory.valid_dom_tree_def] th),
      assume_tac th]) >>
  qmatch_asmsub_abbrev_tac `init_rename_state defs` >>
  (* Get original block for lbl_a *)
  `?bb_a_orig. lookup_block lbl_a func.fn_blocks = SOME bb_a_orig /\
    bb_succs bb_a = bb_succs bb_a_orig` by
    (fs[succs_preserved_def] >> metis_tac[]) >>
  `MEM bb_a_orig func.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `~MEM entry (bb_succs bb_a_orig)` by
    metis_tac[fn_entry_no_preds_def] >>
  `?bb_b_orig. lookup_block lbl_b func.fn_blocks = SOME bb_b_orig` by (
    fs[succs_preserved_def] >> metis_tac[]) >>
  `lbl_b <> entry` by (
    strip_tac >> gvs[] >>
    `~MEM entry (bb_succs bb_a_orig)` by
      metis_tac[fn_entry_no_preds_def] >> gvs[]) >>
  `MEM lbl_b (dom_tree_labels dtree)` by (
    `set (dom_tree_labels dtree) = set (fn_labels func)` by
      first_assum ACCEPT_TAC >>
    pop_assum (fn th => rewrite_tac[th, EXTENSION] >> assume_tac th) >>
    simp[fn_labels_def, MEM_MAP] >>
    imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
    qexists_tac `bb_b_orig` >> simp[]) >>
  `?parent_b. dtree_parent dtree lbl_b = SOME parent_b` by (
    mp_tac (Q.SPECL [`dtree`, `lbl_b`, `entry`, `children`]
      non_root_has_parent) >> simp[]) >>
  `MEM lbl_b (bb_succs bb_a_orig)` by gvs[] >>
  `cfg_dominates func.fn_blocks entry parent_b lbl_a` by (
    mp_tac (Q.SPECL [`dom_frontiers`, `dtree`, `dom_post_order`, `func`,
      `entry`, `parent_b`, `lbl_a`, `lbl_b`, `bb_a_orig`]
      idom_dominates_predecessor) >> simp[]) >>
  `MEM lbl_a (dom_tree_labels dtree)` by (
    `MEM lbl_a (fn_labels func)` by (
      simp[fn_labels_def, MEM_MAP] >>
      imp_res_tac lookup_block_MEM >>
      imp_res_tac lookup_block_label >>
      qexists_tac `bb_a_orig` >> simp[]) >>
    fs[EXTENSION]) >>
  Cases_on `lbl_a = parent_b`
  >- (
    mp_tac (Q.SPECL [`dtree`, `rs0_`, `bbs1_`, `succ_map`, `lbl_b`,
      `rs_b_entry`, `lbl_a`] (CONJUNCT1 child_entry_stacks)) >>
    (impl_tac >- (gvs[] >> rpt conj_tac >> gvs[])) >>
    strip_tac >>
    `rs_p = rs_a_entry` by
      (qpat_x_assum `ALOOKUP _ lbl_a = SOME rs_p` mp_tac >>
       qpat_x_assum `ALOOKUP _ lbl_a = SOME rs_a_entry` mp_tac >>
       simp[]) >>
    `bb_p = bb_a` by
      (qpat_x_assum `lookup_block lbl_a bbs1_ = SOME bb_p` mp_tac >>
       qpat_x_assum `lookup_block lbl_a bbs1_ = SOME bb_a` mp_tac >>
       simp[]) >>
    gvs[] >>
    `latest_version rs_b_entry v =
     latest_version (FST (rename_block_insts rs_a_entry bb_a.bb_instructions)) v` by (
      Cases_on `rs_b_entry` >>
      Cases_on `FST (rename_block_insts rs_a_entry bb_a.bb_instructions)` >>
      gvs[] >> metis_tac[latest_version_stacks_eq]) >>
    gvs[])
  >>
  mp_tac (CONJUNCT1 child_entry_stacks) >> disch_then (qspecl_then [`dtree`, `rs0_`, `bbs1_`, `succ_map`, `lbl_b`, `rs_b_entry`, `parent_b`] mp_tac) >> (impl_tac >- (gvs[] >> rpt conj_tac >> gvs[])) >> strip_tac >>
  `latest_version rs_b_entry v = latest_version (FST (rename_block_insts rs_p bb_p.bb_instructions)) v` by
  (Cases_on `rs_b_entry` >> qmatch_asmsub_abbrev_tac `SND (_,s1) = SND rbi_fst` >> Cases_on `rbi_fst` >> gvs[] >> irule latest_version_stacks_eq) >>
  imp_res_tac dtree_parent_parent_in_tree >>
  Cases_on `latest_version rs_a_entry v = latest_version (FST (rename_block_insts rs_p bb_p.bb_instructions)) v` >- suspend "case_eq" >>
  qpat_assum `!entry' a b. cfg_dominates bbs1_ entry' a b <=> _`
  (fn equiv =>
    mp_tac (REWRITE_RULE [equiv] (Q.SPECL [
      `THE (INDEX_OF lbl_a (dom_tree_labels dtree))`,
      `dtree`, `rs0_`, `bbs1_`, `succ_map`, `lbl_a`, `rs_a_entry`,
      `v`, `entry`, `parent_b`, `rs_p`, `bb_p`]
      version_propagation_finds_def)) >>
    assume_tac equiv) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >> metis_tac[]) >>
  strip_tac >>
  suspend "neq_case"
QED

Resume phi_coverage[neq_case]:
  (* Step 1: lbl_b in dominance frontier of D *)
  `MEM lbl_b (case ALOOKUP dom_frontiers D of SOME fs => fs | NONE => [])` by (
    qpat_x_assum `!b d entry. _ ==> (MEM d _ <=> _)` (qspecl_then [`D`, `lbl_b`, `entry`] mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (fn th => rewrite_tac [th]) >>
    qexistsl [`lbl_a`, `bb_a_orig`] >>
    rpt conj_tac >- first_assum ACCEPT_TAC
    >- gvs[]
    >- first_assum ACCEPT_TAC
    >- (Cases_on `D = lbl_b` >- simp[] >>
        disj2_tac >>
        mp_tac (Q.SPECL [`dom_frontiers`, `dtree`, `dom_post_order`, `func`,
          `entry`, `D`, `lbl_b`, `parent_b`] descendant_not_dom) >>
        simp[])) >>
  suspend "neq_phi"
QED

Resume phi_coverage[neq_phi]:
  (* Get indices and apply add_phi_nodes_all_covered *)
  `MEM bb_D bbs1_` by metis_tac[lookup_block_MEM] >>
  `bb_D.bb_label = D` by metis_tac[lookup_block_label] >>
  `?j_d. j_d < LENGTH bbs1_ /\ EL j_d bbs1_ = bb_D` by metis_tac[MEM_EL] >>
  `LENGTH bbs1_ = LENGTH func.fn_blocks` by
    metis_tac[add_phi_nodes_phi_extends, phi_extends_def, markerTheory.Abbrev_def] >>
  `(EL j_d func.fn_blocks).bb_label = D` by (
    `EL j_d (MAP (\bb. bb.bb_label) bbs1_) =
     EL j_d (MAP (\bb. bb.bb_label) func.fn_blocks)` by simp[] >>
    gvs[EL_MAP]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `?inst2. MEM inst2 bb_b.bb_instructions /\
    inst2.inst_opcode = PHI /\ inst2.inst_outputs = [v]` suffices_by
    (strip_tac >> qexists_tac `inst2` >> simp[]) >>
  `MEM bb_b bbs1_` by metis_tac[lookup_block_MEM] >>
  `bb_b.bb_label = lbl_b` by metis_tac[lookup_block_label] >>
  `?j_b. j_b < LENGTH bbs1_ /\ EL j_b bbs1_ = bb_b` by metis_tac[MEM_EL] >>
  pop_assum strip_assume_tac >>
  suspend "apply_covered"
QED

Resume phi_coverage[apply_covered]:
  `(EL j_b func.fn_blocks).bb_label = lbl_b` by (
  `j_b < LENGTH func.fn_blocks` by fs[] >>
  `EL j_b (MAP (\bb. bb.bb_label) bbs1_) = EL j_b (MAP (\bb. bb.bb_label) func.fn_blocks)` by (
    qpat_x_assum `MAP _ bbs1_ = MAP _ func.fn_blocks` (fn th => simp[th])
  ) >>
  rfs[EL_MAP]
) >>
  qpat_x_assum `lookup_block lbl_b bbs1_ = SOME bb_b` mp_tac >> simp[lookup_block_def] >> strip_tac >> qpat_x_assum `EL _ bbs1_ = bb_b` (SUBST1_TAC o SYM) >> simp[Abbr `bbs1_`] >> irule add_phi_nodes_all_covered >>
  conj_tac >- (
  rpt strip_tac >>
  qpat_x_assum `Abbrev (defs = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  pop_assum (fn defsth => REWRITE_TAC [defsth]) >>
  irule compute_defs_complete >>
  simp[MEM_MAP, MEM_FILTER] >>
  qexists `SOME bb` >> simp[] >>
  simp[MEM_MAP] >>
  qexists `bb.bb_label` >> simp[] >>
  conj_tac >- (
    irule (GSYM MEM_lookup_block) >>
    qpat_x_assum `wf_function func` mp_tac >>
    simp[wf_function_def] >>
    strip_tac >> simp[]
  ) >>
  qpat_x_assum `set dom_post_order = set (fn_labels func)` mp_tac >>
  simp[EXTENSION] >>
  disch_then (fn th => REWRITE_TAC [th]) >>
  simp[fn_labels_def, MEM_MAP] >>
  qexists `bb` >> simp[]
) >>
  conj_tac >- (
  `phi_extends func.fn_blocks (add_phi_nodes dom_frontiers pred_map live_in func.fn_blocks defs)` by simp[add_phi_nodes_phi_extends] >>
  fs[phi_extends_def]
) >>
qexistsl [`D`, `lbl_b`, `j_d`] >>
simp[] >>
rpt conj_tac >> gvs[] >>
  qexists `inst` >> gvs[]
QED

Resume phi_coverage[case_eq]:
  `latest_version rs_a_entry v = latest_version rs_b_entry v` by
  (qpat_x_assum `latest_version rs_a_entry v = _` mp_tac >>
   qpat_x_assum `latest_version rs_b_entry v = _` mp_tac >>
   simp[]) >>
`latest_version rs_a_entry v ≠ latest_version (FST (rename_block_insts rs_a_entry bb_a.bb_instructions)) v` by
  (qpat_x_assum `latest_version rs_b_entry v ≠ _` mp_tac >> gvs[]) >>
`∃i. MEM i bb_a.bb_instructions ∧ MEM v i.inst_outputs` by (
  CCONTR_TAC >> fs[] >>
  qpat_x_assum `latest_version rs_a_entry v ≠ _` mp_tac >> simp[] >>
  mp_tac (Q.SPECL [`bb_a.bb_instructions`, `rs_a_entry`, `v`] rename_block_insts_non_output_stable_any) >>
  (impl_tac >- (rpt strip_tac >> CCONTR_TAC >> fs[] >> metis_tac[])) >>
  simp[]
) >>
qpat_x_assum `!b d entry. fn_entry_label _ = SOME entry ==> _` (fn df_thm =>
  mp_tac (Q.SPECL [`lbl_a`, `lbl_b`, `entry`] df_thm)) >>
(impl_tac >- gvs[]) >>
disch_then (fn thm => mp_tac (iffRL thm)) >>
(impl_tac >- (
  qexistsl [`lbl_a`, `bb_a_orig`] >>
  rpt conj_tac >- gvs[]
  >- gvs[]
  >- simp[cfg_dominates_refl]
  >- (
    Cases_on `lbl_a = lbl_b` >- simp[] >>
    disj2_tac >>
    strip_tac >>
    drule_all descendant_not_dom >>
    simp[]
  )
)) >>
strip_tac >>
  `MEM bb_b bbs1_` by metis_tac[lookup_block_MEM] >>
  `MEM bb_a bbs1_` by metis_tac[lookup_block_MEM] >>
  `bb_b.bb_label = lbl_b` by metis_tac[lookup_block_label] >>
  `bb_a.bb_label = lbl_a` by metis_tac[lookup_block_label] >>
  `∃j_b. j_b < LENGTH bbs1_ ∧ EL j_b bbs1_ = bb_b` by metis_tac[MEM_EL] >>
  pop_assum strip_assume_tac >>
  `∃j_a. j_a < LENGTH bbs1_ ∧ EL j_a bbs1_ = bb_a` by metis_tac[MEM_EL] >>
  pop_assum strip_assume_tac >>
  `LENGTH bbs1_ = LENGTH func.fn_blocks` by
    metis_tac[add_phi_nodes_phi_extends, phi_extends_def, markerTheory.Abbrev_def] >>
  suspend "case_eq_phi"
QED

Resume phi_coverage[case_eq_phi]:
  `?inst2. MEM inst2 bb_b.bb_instructions /\
    inst2.inst_opcode = PHI /\ inst2.inst_outputs = [v]` suffices_by
    (strip_tac >> qexists_tac `inst2` >> simp[]) >>
  `(EL j_b func.fn_blocks).bb_label = lbl_b` by (
    `j_b < LENGTH func.fn_blocks` by fs[] >>
    `EL j_b (MAP (\bb. bb.bb_label) bbs1_) = EL j_b (MAP (\bb. bb.bb_label) func.fn_blocks)` by (
      qpat_x_assum `MAP _ bbs1_ = MAP _ func.fn_blocks` (fn th => simp[th])
    ) >>
    rfs[EL_MAP]
  ) >>
  `(EL j_a func.fn_blocks).bb_label = lbl_a` by (
    `j_a < LENGTH func.fn_blocks` by fs[] >>
    `EL j_a (MAP (\bb. bb.bb_label) bbs1_) = EL j_a (MAP (\bb. bb.bb_label) func.fn_blocks)` by (
      qpat_x_assum `MAP _ bbs1_ = MAP _ func.fn_blocks` (fn th => simp[th])
    ) >>
    rfs[EL_MAP]
  ) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  qpat_x_assum `EL _ bbs1_ = bb_b` (SUBST1_TAC o SYM) >>
  simp[Abbr `bbs1_`] >>
  irule add_phi_nodes_all_covered >>
  conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `Abbrev (defs = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    pop_assum (fn defsth => REWRITE_TAC [defsth]) >>
    irule compute_defs_complete >>
    simp[MEM_MAP, MEM_FILTER] >>
    qexists `SOME bb` >> simp[] >>
    simp[MEM_MAP] >>
    qexists `bb.bb_label` >> simp[] >>
    conj_tac >- (
      irule (GSYM MEM_lookup_block) >>
      qpat_x_assum `wf_function func` mp_tac >>
      simp[wf_function_def] >>
      strip_tac >> simp[]
    ) >>
    qpat_x_assum `set dom_post_order = set (fn_labels func)` mp_tac >>
    simp[EXTENSION] >>
    disch_then (fn th => REWRITE_TAC [th]) >>
    simp[fn_labels_def, MEM_MAP] >>
    qexists `bb` >> simp[]
  ) >>
  conj_tac >- (
    `phi_extends func.fn_blocks (add_phi_nodes dom_frontiers pred_map live_in func.fn_blocks defs)` by simp[add_phi_nodes_phi_extends] >>
    fs[phi_extends_def]
  ) >>
  qexistsl [`lbl_a`, `lbl_b`, `j_a`] >>
  simp[] >>
  rpt conj_tac >> gvs[] >>
  qexists `i` >> gvs[]
QED

Finalise phi_coverage

(* ===== Obligation 2: valid_phi_operands ===== *)

Theorem phi_operands:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI /\
              EVERY colon_free inst.inst_outputs) ==>
    let ordered_bbs = MAP THE (FILTER IS_SOME
          (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)) in
    let defs = compute_defs ordered_bbs in
    let bbs1 = add_phi_nodes dom_frontiers pred_map live_in
                 func.fn_blocks defs in
    let rs0 = init_rename_state defs in
    valid_phi_operands bbs1
      (SND (rename_blocks rs0 bbs1 succ_map dtree))
      dtree succ_map rs0
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `valid_phi_operands bbs1 bbs2 _ _ rs0` >>
  simp[valid_phi_operands_def] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `defs = compute_defs
    (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)))` >>
  (* Infrastructure *)
  `MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) func.fn_blocks` by
    simp[Abbr `bbs1`, add_phi_nodes_preserves_labels] >>
  `phi_extends func.fn_blocks bbs1` by
    simp[Abbr `bbs1`, add_phi_nodes_phi_extends] >>
  `LENGTH bbs1 = LENGTH func.fn_blocks` by gvs[phi_extends_def] >>
  `opcodes_preserved bbs1 bbs2` by
    simp[Abbr `bbs2`, CONJUNCT1 rename_blocks_opcodes_preserved] >>
  `ALL_DISTINCT (dom_tree_labels dtree)` by gvs[valid_dom_tree_def] >>
  `!l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs1 = SOME b` by (
    match_mp_tac dom_labels_have_blocks >>
    qexistsl_tac [`dom_frontiers`, `dom_post_order`, `func`] >>
    simp[fn_labels_def]) >>
  `ALL_DISTINCT (fn_labels func)` by gvs[wf_function_def] >>
  `succs_preserved func.fn_blocks bbs1` by (
    irule phi_extends_succs_preserved >> simp[] >> gvs[fn_labels_def]) >>
  `succs_preserved bbs1 bbs2` by
    simp[Abbr `bbs2`, CONJUNCT1 rename_blocks_succs_preserved_export] >>
  `succs_preserved func.fn_blocks bbs2` by
    metis_tac[succs_preserved_trans] >>
  (* bbs1 block for lbl_b *)
  `?bb_b1. lookup_block lbl_b bbs1 = SOME bb_b1` by (
    qpat_x_assum `succs_preserved bbs1 bbs2` mp_tac >>
    simp[succs_preserved_def] >> metis_tac[]) >>
  `LENGTH bb_b1.bb_instructions = LENGTH bb_b.bb_instructions /\
   !k. k < LENGTH bb_b1.bb_instructions ==>
       (EL k bb_b1.bb_instructions).inst_opcode =
       (EL k bb_b.bb_instructions).inst_opcode` by
    metis_tac[opcodes_preserved_lookup] >>
  (* inst at position j *)
  `?j. j < LENGTH bb_b.bb_instructions /\ inst = EL j bb_b.bb_instructions` by
    metis_tac[MEM_EL] >>
  `j < LENGTH bb_b1.bb_instructions` by simp[] >>
  `(EL j bb_b1.bb_instructions).inst_opcode = PHI` by (res_tac >> gvs[]) >>
  (* Original block for lbl_a *)
  `?bb_a_orig. lookup_block lbl_a func.fn_blocks = SOME bb_a_orig /\
              bb_succs bb_a2 = bb_succs bb_a_orig` by (
    gvs[succs_preserved_def] >> metis_tac[]) >>
  `MEM lbl_a (dom_tree_labels dtree)` by (
    `set (dom_tree_labels dtree) = set (fn_labels func)` by
      gvs[valid_dom_tree_def] >>
    gvs[EXTENSION, fn_labels_def, MEM_MAP] >>
    imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
    metis_tac[]) >>
  (* succ_map connection *)
  `ALOOKUP succ_map lbl_a = SOME (bb_succs bb_a_orig)` by
    gvs[valid_cfg_maps_def] >>
  `MEM lbl_b (case ALOOKUP succ_map lbl_a of NONE => [] | SOME ss => ss)` by
    gvs[] >>
  `ALL_DISTINCT (case ALOOKUP succ_map lbl_a of NONE => [] | SOME ss => ss)` by (
    simp[] >> irule bb_succs_all_distinct >> gvs[wf_function_def] >>
    metis_tac[lookup_block_MEM]) >>
  (* Apply rename_blocks_updates_resolve_phi *)
  mp_tac (CONJUNCT1 rename_blocks_updates_resolve_phi) >>
  disch_then (qspecl_then [`dtree`, `rs0`, `bbs1`, `succ_map`,
    `lbl_a`, `bb_a1`, `lbl_b`, `bb_b1`, `j`, `rs_a_entry`] mp_tac) >>
  simp[] >> disch_then strip_assume_tac >> gvs[] >>
  (* EL j_bb1 for add_phi_nodes_phi_is_build_phi *)
  `?j_bb1. j_bb1 < LENGTH func.fn_blocks /\
           bb_b1 = EL j_bb1 bbs1` by (
    imp_res_tac lookup_block_MEM >> gvs[MEM_EL] >> metis_tac[]) >>
  `(EL j (EL j_bb1 bbs1).bb_instructions).inst_opcode = PHI` by gvs[] >>
  (* Apply add_phi_nodes_phi_is_build_phi *)
  `!bb inst. MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions ==>
     inst.inst_opcode <> PHI` by (rpt strip_tac >> res_tac >> gvs[]) >>
  mp_tac (SIMP_RULE std_ss [LET_THM] add_phi_nodes_phi_is_build_phi) >>
  disch_then drule >>
  disch_then (qspecl_then [`dom_frontiers`, `pred_map`, `live_in`,
    `defs`, `j_bb1`,
    `EL j (EL j_bb1 bbs1).bb_instructions`] mp_tac) >>
  impl_tac >- (simp[Abbr `bbs1`] >> metis_tac[MEM_EL]) >>
  strip_tac >>
  (* bb_b1 instruction is build_phi_inst *)
  `bb_b1.bb_instructions❲j❳ = build_phi_inst var
     (case ALOOKUP pred_map func.fn_blocks❲j_bb1❳.bb_label of
        NONE => [] | SOME ps => ps)` by gvs[] >>
  (* func.fn_blocks❲j_bb1❳.bb_label = lbl_b *)
  `func.fn_blocks❲j_bb1❳.bb_label = lbl_b` by (
    `bbs1❲j_bb1❳.bb_label = func.fn_blocks❲j_bb1❳.bb_label` by (
      qpat_x_assum `MAP _ bbs1 = MAP _ func.fn_blocks` mp_tac >>
      simp[LIST_EQ_REWRITE] >> strip_tac >>
      first_x_assum (qspec_then `j_bb1` mp_tac) >> simp[EL_MAP]) >>
    imp_res_tac lookup_block_label >> gvs[]) >>
  (* Get preds from pred_map using completeness *)
  `?preds. ALOOKUP pred_map lbl_b = SOME preds` by (
    `lookup_block lbl_b func.fn_blocks <> NONE` by
      (imp_res_tac (REWRITE_RULE [succs_preserved_def] (ASSUME ``succs_preserved func.fn_blocks bbs1``)) >>
       gvs[]) >>
    gvs[valid_cfg_maps_def]) >>
  (* MEM lbl_a preds *)
  `MEM lbl_a preds` by (
    `set preds = {p | ?bb. lookup_block p func.fn_blocks = SOME bb /\
                           MEM lbl_b (bb_succs bb)}` by
      gvs[valid_cfg_maps_def] >>
    gvs[EXTENSION] >> metis_tac[]) >>
  (* resolve_phi gives SOME (Var var) *)
  qexists_tac `Var var` >> conj_tac >-
    simp[build_phi_inst_def, resolve_phi_build_phi_inst] >>
  simp[renamed_operand_def] >>
  (* var = base' via version_var_inj *)
  `var = base'` suffices_by simp[] >>
  (* MEM lbl_b in dtree *)
  `MEM lbl_b (dom_tree_labels dtree)` by (
    mp_tac bbs2_label_in_dtree >>
    disch_then (qspecl_then [`dtree`, `dom_frontiers`, `dom_post_order`,
      `func`, `rs0`, `bbs1`, `succ_map`, `lbl_b`, `bb_b`] mp_tac) >>
    simp[Abbr `bbs2`, fn_labels_def]) >>
  (* Get renamed outputs *)
  mp_tac (Q.SPECL [`dtree`, `rs0`, `bbs1`, `succ_map`]
    rename_blocks_inst_outputs) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`lbl_b`, `bb_b`, `j`] mp_tac) >>
  simp[Abbr `bbs2`] >> strip_tac >>
  (* bb1 = bb_b1 *)
  gvs[] >>
  (* Get version_var from PHI rename *)
  mp_tac rename_inst_phi_outputs_version_var >>
  disch_then (qspecl_then [`rs_k`, `build_phi_inst var preds`, `var`] mp_tac) >>
  simp[build_phi_inst_def] >> strip_tac >> fs[] >>
  (* Forward reasoning: colon_free var *)
  mp_tac (Q.SPECL [`dom_frontiers`, `pred_map`, `live_in`,
    `func.fn_blocks`, `defs`, `j_bb1`]
    (SIMP_RULE std_ss [LET_THM] add_phi_nodes_phi_live_in)) >>
  simp[] >>
  disch_then (qspec_then `bbs1❲j_bb1❳.bb_instructions❲j❳` mp_tac) >>
  strip_tac >>
  `~MEM bbs1❲j_bb1❳.bb_instructions❲j❳
       func.fn_blocks❲j_bb1❳.bb_instructions` by (
    spose_not_then ASSUME_TAC >>
    `MEM (EL j_bb1 func.fn_blocks) func.fn_blocks` by metis_tac[MEM_EL] >>
    res_tac >> gvs[]) >>
  (* Resolve phi_live_in implication *)
  qpat_x_assum `MEM _ _ /\ _ ==> _` mp_tac >>
  impl_tac >- metis_tac[MEM_EL] >>
  simp[build_phi_inst_def] >> strip_tac >>
  (* colon_free var from compute_defs_colon_free *)
  `EVERY (\p. colon_free (FST p)) defs` by (
    simp[Abbr `defs`] >>
    irule compute_defs_colon_free >>
    irule ordered_bbs_colon_free >>
    rpt strip_tac >> res_tac >> gvs[]) >>
  (* colon_free var: from MEM var (MAP FST defs) + EVERY colon_free defs *)
  `colon_free var` by (
    qpat_x_assum `EVERY _ defs` mp_tac >>
    qpat_x_assum `MEM var (MAP FST defs)` mp_tac >>
    simp[EVERY_MEM, MEM_MAP, PULL_EXISTS, pairTheory.FORALL_PROD] >>
    metis_tac[]) >>
  (* Chain version_var equalities and apply injectivity *)
  gvs[build_phi_inst_def] >>
  metis_tac[version_var_inj]
QED

