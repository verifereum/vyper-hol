Theory o1MakeSsaEventOwnership
Ancestors
  o1MakeSsaOwnership o1MakeSsaCallOwnership o1MakeSsaVisitTrace o1MakeSsaEventFrames
  o1MakeSsaTraversalFrames o1MakeSsaFrontier makeSsaCurrentProps makeSsaDefs irSupply
  makeSsaCurrentInduct list pair pred_set

Theorem visit_current_rename_owner:
  (!tree path s rs bbs sm ct t final events V H.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    current_rename_owner V H s rs /\
    EVERY (\e. EVERY (\i. set i.inst_outputs SUBSET V) e.sve_before) events ==>
    (?H'. H SUBSET H' /\ current_rename_owner V H' t (ct,SND rs)) /\
    (!e. MEM e events ==>
      ?He. current_rename_owner V He e.sve_supply_in e.sve_in)) /\
  (!trees path s ctrs stacks bbs sm ct t final events V H.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    current_rename_owner V H s (ctrs,stacks) /\
    EVERY (\e. EVERY (\i. set i.inst_outputs SUBSET V) e.sve_before) events ==>
    (?H'. H SUBSET H' /\ current_rename_owner V H' t (ct,stacks)) /\
    (!e. MEM e events ==>
      ?He. current_rename_owner V He e.sve_supply_in e.sve_in))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[]
      >- (rpt strip_tac >> gvs[] >> PairCases_on `rs` >> gvs[] >>
          metis_tac[SUBSET_REFL]) >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
      suspend "node")
  >- (simp[visit_blocks_def] >> rpt strip_tac >> gvs[] >>
      metis_tac[SUBSET_REFL]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  suspend "children"
QED

Resume visit_current_rename_owner[node]:
  drule_all current_rename_owner_block_insts >> strip_tac >>
  PairCases_on `rs1` >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  conj_tac
  >- (PairCases_on `rs` >> gvs[] >>
      `H SUBSET H''` by metis_tac[SUBSET_TRANS] >>
      qexists_tac `H''` >> simp[] >>
      irule current_rename_owner_restore >>
      conj_tac >- (qexistsl_tac [`H`,`rs0`,`s`] >> simp[]) >>
      qexists_tac `rs11` >> simp[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume visit_current_rename_owner[children]:
  qpat_x_assum `!path s rs bbs sm ct t final events V H. _` drule_all >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  conj_tac >- metis_tac[SUBSET_TRANS] >>
  metis_tac[]
QED

Finalise visit_current_rename_owner

Theorem indexed_patch_frame_output_domain:
  indexed_patch_frame a b /\
  EVERY (\i. set i.inst_outputs SUBSET V) a.bb_instructions ==>
  EVERY (\i. set i.inst_outputs SUBSET V) b.bb_instructions
Proof
  simp[indexed_patch_frame_def, EVERY_EL] >> rpt strip_tac >>
  metis_tac[]
QED

Theorem visit_event_output_domain:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\ MEM e events /\
  lookup_block e.sve_label bbs = SOME bb /\
  EVERY (\i. set i.inst_outputs SUBSET V) bb.bb_instructions ==>
  EVERY (\i. set i.inst_outputs SUBSET V) e.sve_before
Proof
  strip_tac >> drule_all (cj 1 visit_event_input_frame) >>
  strip_tac >> drule_all indexed_patch_frame_output_domain >> simp[]
QED

Theorem insert_phis_output_domain:
  insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') /\
  var IN V /\ EVERY (\bb. EVERY (\i. set i.inst_outputs SUBSET V)
                                      bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. set i.inst_outputs SUBSET V) bb.bb_instructions) bbs'
Proof
  strip_tac >> drule insert_phis_for_var_supply_invariant >>
  disch_then irule >> simp[] >> rpt strip_tac >> IF_CASES_TAC >>
  gvs[insert_phi_at_block_def, build_phi_inst_supply_def]
QED

Theorem add_phi_nodes_output_domain:
  !defs s df pm li bbs bbs' s' V.
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\
  set (MAP FST defs) SUBSET V /\
  EVERY (\bb. EVERY (\i. set i.inst_outputs SUBSET V) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. set i.inst_outputs SUBSET V) bb.bb_instructions) bbs'
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule_all insert_phis_output_domain >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem compute_defs_original_key_domain:
  set (MAP FST (compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) labels)))))
  SUBSET set (fn_ir_vars fn)
Proof
  simp[SUBSET_DEF] >> rpt strip_tac >>
  drule compute_defs_key_MEM_block_ir_vars >>
  rewrite_tac[MEM_FLAT] >> strip_tac >>
  qpat_x_assum `MEM l (MAP block_ir_vars _)` mp_tac >>
  once_rewrite_tac[MEM_MAP] >> strip_tac >> gvs[] >>
  drule lookup_blocks_filter_MEM >> strip_tac >>
  simp[fn_ir_vars_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem function_original_output_domain:
  EVERY (\bb. EVERY (\i. set i.inst_outputs SUBSET set (fn_ir_vars fn))
                         bb.bb_instructions) fn.fn_blocks
Proof
  simp[EVERY_MEM, SUBSET_DEF] >> rpt strip_tac >>
  simp[fn_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  qexists_tac `block_ir_vars bb` >> conj_tac >- metis_tac[] >>
  simp[block_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  qexists_tac `inst_ir_vars i` >> simp[inst_ir_vars_def] >> metis_tac[]
QED

Theorem prepared_original_output_domain:
  add_phi_nodes_supply s df pm li fn.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) labels)))) = (bbs',s') ==>
  EVERY (\bb. EVERY (\i. set i.inst_outputs SUBSET set (fn_ir_vars fn))
                         bb.bb_instructions) bbs'
Proof
  strip_tac >> drule add_phi_nodes_output_domain >>
  disch_then irule >>
  simp[compute_defs_original_key_domain, function_original_output_domain]
QED
