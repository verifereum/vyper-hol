Theory o1SymStaticMakeSSA
Ancestors
  o1MakeSsaFormats o1PassContract makeSsaCurrentInduct
  dfAnalyzeProofs makeSsaCurrentCfg makeSsaDefs list
  simplifyCfgDefs simplifyCfgStruct o1MakeSsaFrontier o1MakeSsaCfg
  venomInst venomWf unitShapeDefs vyperCompiler

Theorem rename_current_operands_label_mem:
  !ops. MEM (Label l) (rename_current_operands rs ops) = MEM (Label l) ops
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def]
QED

Theorem rename_current_inst_label_absent:
  rename_current_inst s rs i = (rs',s',i') /\
  ~MEM (Label l) i.inst_operands ==> ~MEM (Label l) i'.inst_operands
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[rename_current_operands_label_mem]
QED

Theorem rename_current_block_insts_label_absent:
  !insts s rs rs' s' insts'.
  rename_current_block_insts s rs insts = (rs',s',insts') /\
  EVERY (\i. ~MEM (Label l) i.inst_operands) insts ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands) insts'
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  conj_tac >- metis_tac[rename_current_inst_label_absent] >>
  first_x_assum drule_all >> simp[]
QED

Theorem update_current_phi_for_pred_label_mem:
  !rs lbl ops. MEM (Label l) (update_current_phi_for_pred rs lbl ops) =
    MEM (Label l) ops
Proof
  recInduct update_current_phi_for_pred_ind >>
  rw[update_current_phi_for_pred_def] >> simp[]
QED

Theorem update_current_succ_phis_label_absent:
  !succs bbs. EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands)
    bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands)
    bb.bb_instructions) (update_current_succ_phis rs lbl bbs succs)
Proof
  Induct >> gvs[update_current_succ_phis_def] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `lookup_block h bbs` >> simp[] >>
  irule EVERY_replace_block >> simp[] >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  gvs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode = PHI` >>
  gvs[update_current_phi_for_pred_label_mem] >> metis_tac[]
QED

Theorem rename_current_blocks_label_absent:
  (!t s rs bbs sm ctrs s' bbs'.
    rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
    EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs') /\
  (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
    rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
    EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs')
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >> gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >> first_x_assum drule >> disch_then irule >>
      irule update_current_succ_phis_label_absent >>
      irule EVERY_replace_block >> simp[] >>
      drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
      drule rename_current_block_insts_label_absent >> disch_then irule >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> disch_then irule >>
  first_x_assum drule_all >> simp[]
QED

Theorem simplify_current_phi_label_absent:
  ~MEM (Label l) i.inst_operands ==>
  ~MEM (Label l) (simplify_current_phi i).inst_operands
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[] >>
  simp[simplify_current_phi_raw_def] >> IF_CASES_TAC >> simp[] >>
  Cases_on `current_phi_output i.inst_outputs` >> simp[] >>
  Cases_on `current_phi_values (remove_current_phi_self x i.inst_operands)` >>
  simp[] >> Cases_on `x'` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem simplify_current_phi_prefix_parts_label_absent:
  !insts phis ordinary.
  simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
  EVERY (\i. ~MEM (Label l) i.inst_operands) insts ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands) (phis ++ ordinary)
Proof
  Induct >- simp[simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode <> PHI`
  >- (simp[simplify_current_phi_prefix_parts_def] >> strip_tac >> gvs[]) >>
  simp[simplify_current_phi_prefix_parts_def] >>
  pairarg_tac >> gvs[] >> CASE_TAC >> strip_tac >> gvs[] >>
  metis_tac[simplify_current_phi_label_absent]
QED

Theorem reassign_current_inst_ids_label_absent:
  !ids insts. EVERY (\i. ~MEM (Label l) i.inst_operands) insts ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands) (reassign_current_inst_ids ids insts)
Proof
  Induct >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem simplify_current_phi_prefix_label_absent:
  EVERY (\i. ~MEM (Label l) i.inst_operands) insts ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands) (simplify_current_phi_prefix insts)
Proof
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  irule reassign_current_inst_ids_label_absent >>
  drule_all simplify_current_phi_prefix_parts_label_absent >> simp[]
QED

Theorem simplify_current_phi_block_label_absent:
  EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands)
    (simplify_current_phi_block bb).bb_instructions
Proof
  simp[simplify_current_phi_block_def] >> rpt CASE_TAC >> gvs[] >>
  strip_tac >> irule simplify_current_phi_prefix_label_absent >> simp[]
QED

Theorem simplify_current_phis_if_label_absent:
  EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
    (simplify_current_phis_if enabled bbs)
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def] >>
  Cases_on `blocks_have_leading_phi bbs` >> simp[simplify_current_phis_def] >>
  simp[EVERY_MAP] >> strip_tac >> irule EVERY_MONOTONIC >>
  qexists_tac `\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions` >>
  simp[simplify_current_phi_block_label_absent]
QED

Theorem build_phi_inst_supply_label_mem:
  !preds. MEM (Label l) (build_phi_inst_supply id var preds).inst_operands = MEM l preds
Proof
  Induct >> gvs[build_phi_inst_supply_def]
QED

Theorem add_phi_nodes_supply_label_absent:
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\
  (!k ps. ALOOKUP pm k = SOME ps ==> ~MEM l ps) /\
  EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs'
Proof
  strip_tac >> drule add_phi_nodes_supply_invariant >> disch_then irule >>
  simp[] >> rpt strip_tac >> IF_CASES_TAC >>
  simp[insert_phi_at_block_def, build_phi_inst_supply_label_mem] >>
  Cases_on `ALOOKUP pm f` >> simp[] >> metis_tac[]
QED

Theorem current_query_map_label_absent:
  !labels query k ps. ALOOKUP (current_query_map labels query) k = SOME ps /\
  (!k. ~MEM l (query k)) ==> ~MEM l ps
Proof
  Induct >> gvs[current_query_map_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem make_ssa_current_fn_label_absent:
  ~MEM l (fn_labels f) /\
  EVERY (\i. ~MEM (Label l) i.inst_operands) (fn_insts f) /\
  make_ssa_current_fn s f = (f',s') ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands) (fn_insts f')
Proof
  Cases_on `fn_entry_label f` >> simp[make_ssa_current_fn_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[fn_insts_def, EVERY_fn_insts_blocks] >>
  irule simplify_current_phis_if_label_absent >>
  drule (cj 1 rename_current_blocks_label_absent) >> disch_then irule >>
  drule add_phi_nodes_supply_label_absent >> disch_then irule >> conj_tac
  >- (rpt gen_tac >> disch_tac >> drule current_query_map_label_absent >>
      disch_then (qspec_then `l` mp_tac) >>
      (impl_tac >- (gen_tac >>
        mp_tac (Q.SPECL [`f`,`k'`] preds_subset_fn_labels) >>
        simp[EVERY_MEM] >> metis_tac[])) >> simp[]) >>
  gvs[fn_insts_def, EVERY_fn_insts_blocks]
QED

Theorem make_ssa_current_fn_runtime_reflect:
  o1_fn_shape C f /\ make_ssa_current_fn s f = (f',s') ==>
  ((?i. MEM i (fn_insts f') /\ MEM (Label "runtime_begin") i.inst_operands) ==>
   (?i. MEM i (fn_insts f) /\ MEM (Label "runtime_begin") i.inst_operands))
Proof
  strip_tac >> spose_not_then strip_assume_tac >>
  `~MEM "runtime_begin" (fn_labels f)` by
    (gvs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def,
         fn_labels_def, MEM_MAP, EVERY_MEM, unitShapeDefsTheory.reserved_label_def] >>
     metis_tac[]) >>
  `EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands) (fn_insts f)` by
    simp[EVERY_MEM] >>
  `EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands) (fn_insts f')` by
    (irule make_ssa_current_fn_label_absent >>
     qexistsl_tac [`f`, `s`, `s'`] >> simp[]) >>
  gvs[EVERY_MEM]
QED
