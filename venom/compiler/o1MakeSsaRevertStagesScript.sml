Theory o1MakeSsaRevertStages
Ancestors
  o1MakeSsaCallPaths o1MakeSsaPreparation o1MakeSsaFormats o1MakeSsaCfg
  o1MakeSsaTraversalFrames o1MakeSsaPatchFrames o1MakeSsaVisitRetention
  makeSsaCurrentInduct makeSsaHelper makeSsaCurrentCfg makeSsaCurrentCleanupBoundary
  unitShapeDefs makeSsaCurrentDefs list pred_set rich_list o1ContractMakeSsaSrcOpcodes

Theorem prepared_prefix_revert_block:
  prepared_prefix a b ==> mssa_revert_block a b
Proof
  simp[prepared_prefix_def] >> strip_tac >>
  `!i. MEM i pre ==> i.inst_opcode <> INVOKE` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  simp[mssa_revert_block_def] >> strip_tac >>
  `LAST (pre ++ a.bb_instructions) = LAST a.bb_instructions` by
    (Cases_on `a.bb_instructions` >> fs[LAST_APPEND_CONS]) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem prepared_add_phi_revert:
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
  LENGTH bbs = LENGTH bbs' /\
  (!bb. MEM bb bbs ==> ?out. MEM out bbs' /\ mssa_revert_block bb out)
Proof
  strip_tac >> drule prepared_add_phi_nodes >>
  simp[LIST_REL_EL_EQN] >> strip_tac >> simp[] >>
  rpt strip_tac >> fs[MEM_EL] >>
  qexists `EL n bbs'` >> conj_tac
  >- metis_tac[] >>
  irule prepared_prefix_revert_block >> simp[]
QED

Theorem indexed_patch_frame_revert_block:
  indexed_patch_frame bb out ==> mssa_revert_block bb out
Proof
  simp[indexed_patch_frame_def, mssa_revert_block_def] >> strip_tac >>
  strip_tac >>
  `out.bb_instructions <> []` by metis_tac[LENGTH_NIL] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) out.bb_instructions` by
    (fs[EVERY_EL] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  simp[] >>
  `LAST bb.bb_instructions = EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions` by
    simp[LAST_EL] >>
  `LAST out.bb_instructions = EL (PRE (LENGTH bb.bb_instructions)) out.bb_instructions` by
    simp[LAST_EL] >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  first_x_assum drule >> rpt strip_tac >> gvs[]
QED

Theorem rename_current_inst_jmp_label:
  rename_current_inst s rs i = (rs',s',out) /\
  i.inst_opcode = JMP /\ i.inst_operands = [Label l] ==>
  out.inst_operands = [Label l]
Proof
  simp[rename_current_inst_def] >> strip_tac >>
  pairarg_tac >> gvs[rename_current_operands_def]
QED

Theorem rename_current_block_insts_last_jmp:
  !insts s rs rs' s' insts' l.
  insts <> [] /\
  rename_current_block_insts s rs insts = (rs',s',insts') /\
  (LAST insts).inst_opcode = JMP /\ (LAST insts).inst_operands = [Label l] ==>
  (LAST insts').inst_operands = [Label l]
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  Cases_on `insts = []`
  >- (gvs[rename_current_block_insts_def] >>
      drule_all rename_current_inst_jmp_label >> simp[]) >>
  `rest' <> []` by
    (drule rename_current_block_insts_length >> Cases_on `rest'` >> gvs[]) >>
  fs[LAST_DEF] >> first_x_assum irule >> metis_tac[]
QED

Theorem rename_current_block_insts_revert_block:
  rename_current_block_insts s rs bb.bb_instructions = (rs',s',insts') ==>
  mssa_revert_block bb (bb with bb_instructions := insts')
Proof
  strip_tac >> drule rename_current_block_insts_opcodes >> strip_tac >>
  drule rename_current_block_insts_length >> strip_tac >>
  simp[mssa_revert_block_def] >> strip_tac >>
  `insts' <> []` by metis_tac[LENGTH_NIL] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) insts'` by
    (`EVERY (\opc. opc <> INVOKE) (MAP (\i. i.inst_opcode) insts')` suffices_by
       simp[EVERY_MAP] >>
     asm_rewrite_tac[] >> simp[EVERY_MAP]) >>
  ` (LAST insts').inst_opcode = (LAST bb.bb_instructions).inst_opcode` by
    (qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LAST`) >>
     simp[LAST_MAP]) >>
  simp[] >> rpt strip_tac >> irule rename_current_block_insts_last_jmp >>
  metis_tac[]
QED

Theorem update_current_succ_phis_revert_lookup:
  lookup_block q bbs = SOME bb ==>
  ?out. lookup_block q (update_current_succ_phis rs pred bbs succs) = SOME out /\
    mssa_revert_block bb out
Proof
  strip_tac >> drule patch_lookup_indexed_frame >>
  disch_then (qspecl_then [`succs`,`rs`,`pred`] strip_assume_tac) >>
  qexists `out` >> simp[] >> irule indexed_patch_frame_revert_block >>
  simp[indexed_patch_frame_def]
QED

Theorem rename_current_blocks_revert_lookup:
  (!tree s rs bbs sm ct t final q bb.
    rename_current_blocks s rs bbs sm tree = (ct,t,final) /\
    lookup_block q bbs = SOME bb ==>
    ?out. lookup_block q final = SOME out /\ mssa_revert_block bb out) /\
  (!trees s ctrs stacks bbs sm ct t final q bb.
    rename_current_children s ctrs stacks bbs sm trees = (ct,t,final) /\
    lookup_block q bbs = SOME bb ==>
    ?out. lookup_block q final = SOME out /\ mssa_revert_block bb out)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once rename_current_blocks_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[]
      >- (rpt strip_tac >> gvs[]) >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
      `x.bb_label = lbl` by metis_tac[lookup_block_label] >>
      `?mid. lookup_block q (replace_block lbl (x with bb_instructions := insts') bbs) = SOME mid /\
        mssa_revert_block bb mid` by
        (Cases_on `q = lbl` >> gvs[retention_lookup_replace]
         >- (irule rename_current_block_insts_revert_block >> metis_tac[]) >>
         metis_tac[mssa_revert_block_refl]) >>
      drule_all update_current_succ_phis_revert_lookup >>
      disch_then (qspecl_then [`case ALOOKUP sm lbl of NONE => [] | SOME ss => ss`,`rs1`,`lbl`] strip_assume_tac) >>
      first_x_assum drule_all >> metis_tac[mssa_revert_block_trans])
  >- (simp[rename_current_blocks_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once rename_current_blocks_def] >> rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> metis_tac[mssa_revert_block_trans]
QED

Theorem simplify_current_phi_prefix_terminal:
  insts <> [] /\ is_terminator (LAST insts).inst_opcode ==>
  simplify_current_phi_prefix insts <> [] /\
  (LAST (simplify_current_phi_prefix insts)).inst_opcode = (LAST insts).inst_opcode /\
  (LAST (simplify_current_phi_prefix insts)).inst_operands = (LAST insts).inst_operands
Proof
  strip_tac >> simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  drule makeSsaCurrentCfgTheory.simplify_current_phi_prefix_parts_shape >> strip_tac >>
  `rest <> []` by
    (Cases_on `rest` >> gvs[EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  `LAST (phis ++ ordinary) = LAST insts` by
    (gvs[] >> Cases_on `rest` >> fs[LAST_APPEND_CONS]) >>
  `phis ++ ordinary <> []` by (strip_tac >> gvs[]) >>
  `PRE (LENGTH (phis ++ ordinary)) < LENGTH (phis ++ ordinary)` by
    (Cases_on `phis ++ ordinary` >> fs[]) >>
  qspecl_then [`MAP (\i. i.inst_id) insts`,`phis ++ ordinary`,
    `PRE (LENGTH (phis ++ ordinary))`] mp_tac current_reassign_content >>
  (impl_tac >- simp[]) >> strip_tac >>
  `reassign_current_inst_ids (MAP (\i. i.inst_id) insts) (phis ++ ordinary) <> []` by
    metis_tac[current_reassign_length,LENGTH_NIL] >>
  `LAST (reassign_current_inst_ids (MAP (\i. i.inst_id) insts) (phis ++ ordinary)) =
    EL (PRE (LENGTH (phis ++ ordinary)))
      (reassign_current_inst_ids (MAP (\i. i.inst_id) insts) (phis ++ ordinary))` by
    simp[LAST_EL] >>
  `LAST (phis ++ ordinary) = EL (PRE (LENGTH (phis ++ ordinary))) (phis ++ ordinary)` by
    metis_tac[LAST_EL] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem simplify_current_phi_block_revert_block:
  bb_well_formed bb ==> mssa_revert_block bb (simplify_current_phi_block bb)
Proof
  strip_tac >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[venomWfTheory.bb_well_formed_def] >>
  `simplify_current_phi_prefix bb.bb_instructions <> [] /\
   (LAST (simplify_current_phi_prefix bb.bb_instructions)).inst_opcode =
     (LAST bb.bb_instructions).inst_opcode /\
   (LAST (simplify_current_phi_prefix bb.bb_instructions)).inst_operands =
     (LAST bb.bb_instructions).inst_operands` by
    metis_tac[simplify_current_phi_prefix_terminal] >>
  simp[mssa_revert_block_def] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (simplify_current_phi_prefix bb.bb_instructions)` by
    (ho_match_mp_tac o1MakeSsaFormatsTheory.simplify_current_phi_prefix_opcodes >> simp[]) >>
  simp[simplify_current_phi_block_def] >> Cases_on `bb.bb_instructions` >> fs[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem rename_current_blocks_revert:
  rename_current_blocks s rs bbs sm tree = (ct,t,final) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
  LENGTH bbs = LENGTH final /\
  (!bb. MEM bb bbs ==> ?out. MEM out final /\ mssa_revert_block bb out)
Proof
  strip_tac >>
  drule (cj 1 makeSsaCurrentPropsTheory.rename_current_blocks_labels) >> strip_tac >>
  conj_tac >- metis_tac[LENGTH_MAP] >>
  rpt strip_tac >>
  `lookup_block bb.bb_label bbs = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >> simp[]) >>
  drule_all (cj 1 rename_current_blocks_revert_lookup) >> strip_tac >>
  metis_tac[venomExecPropsTheory.lookup_block_MEM]
QED

Theorem simplify_current_phis_if_revert:
  EVERY bb_well_formed bbs ==>
  LENGTH bbs = LENGTH (simplify_current_phis_if enabled bbs) /\
  (!bb. MEM bb bbs ==> ?out. MEM out (simplify_current_phis_if enabled bbs) /\
    mssa_revert_block bb out)
Proof
  strip_tac >> Cases_on `enabled`
  >- (simp[simplify_current_phis_if_def, simplify_current_phis_def] >>
      Cases_on `blocks_have_leading_phi bbs` >> simp[]
      >- (rpt strip_tac >> qexists `simplify_current_phi_block bb` >> conj_tac
          >- (simp[MEM_MAP] >> metis_tac[]) >>
          irule simplify_current_phi_block_revert_block >> fs[EVERY_MEM]) >>
      metis_tac[mssa_revert_block_refl]) >>
  simp[simplify_current_phis_if_def] >> metis_tac[mssa_revert_block_refl]
QED

Theorem make_ssa_current_fn_revert_environment:
  make_ssa_current_fn s fn = (fn',s') /\ wf_function fn ==>
  LENGTH fn.fn_blocks = LENGTH fn'.fn_blocks /\
  (!n l. revert_path fn.fn_blocks n l ==> revert_path fn'.fn_blocks n l)
Proof
  Cases_on `fn_entry_label fn`
  >- (simp[make_ssa_current_fn_def] >> rpt strip_tac >> gvs[]) >>
  simp[make_ssa_current_fn_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  `EVERY bb_well_formed bbs1` by
    (drule (SRULE[current_frontier_map_def, current_pred_map_def, LET_THM]
      o1MakeSsaFrontierTheory.add_phi_nodes_supply_well_formed) >> disch_then irule >>
     gvs[venomWfTheory.wf_function_def, EVERY_MEM, venomInstTheory.fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `EVERY bb_well_formed bbs2` by
    metis_tac[cj 1 o1MakeSsaFormatsTheory.rename_current_blocks_well_formed] >>
  drule makeSsaCurrentPropsTheory.add_phi_nodes_supply_labels >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
    fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
  drule prepared_add_phi_revert >> strip_tac >>
  drule_all rename_current_blocks_revert >> strip_tac >>
  qpat_x_assum `add_phi_nodes_supply _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `rename_current_blocks _ _ _ _ _ = _` kall_tac >>
  drule simplify_current_phis_if_revert >>
  disch_then (qspec_then `blocks_have_leading_phi fn.fn_blocks` strip_assume_tac) >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  irule mssa_revert_path_transport >>
  qexists `fn.fn_blocks` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> metis_tac[mssa_revert_block_trans]
QED
