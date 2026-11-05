Theory makeSsaCurrentAvailability
Ancestors
  makeSsaCurrentDemand passSharedDefs venomExecProofs
Libs
  listTheory arithmeticTheory venomWfTheory venomInstTheory

Definition current_available_def:
  current_available fn v l i <=>
  ?bb. lookup_block l fn.fn_blocks = SOME bb /\
    i <= LENGTH bb.bb_instructions /\
    !path. is_fn_path fn path /\ path <> [] /\
      (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
      LAST path = l ==>
      (?k db di. k < LENGTH path - 1 /\
        MEM db fn.fn_blocks /\ db.bb_label = EL k path /\
        MEM di db.bb_instructions /\ MEM v di.inst_outputs) \/
      (?j. j < i /\ MEM v (EL j bb.bb_instructions).inst_outputs)
End

Theorem current_available_skip:
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  ~MEM v (inst_defs (EL i bb.bb_instructions)) /\
  current_available fn v l (SUC i) ==>
  current_available fn v l i
Proof
  simp[current_available_def, inst_defs_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac
  >- metis_tac[] >>
  disj2_tac >> qexists_tac `j` >> Cases_on `j = i` >> gvs[]
QED

Theorem current_path_first_target:
  !path. is_fn_path fn path /\ path <> [] /\ LAST path = target ==>
    ?pre. is_fn_path fn (pre ++ [target]) /\
      HD (pre ++ [target]) = HD path /\ ~MEM target pre
Proof
  Induct >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `h = target`
  >- (qexists_tac `[]` >> simp[is_fn_path_def]) >>
  Cases_on `path` >> gvs[is_fn_path_def] >>
  qexists_tac `h::pre` >> simp[] >>
  Cases_on `pre` >> gvs[is_fn_path_def]
QED

Theorem current_available_cross:
  wf_function fn /\
  lookup_block l fn.fn_blocks = SOME bb /\
  MEM succ (bb_succs bb) /\
  current_available fn v succ 0 ==>
  current_available fn v l (LENGTH bb.bb_instructions)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `fn_cfg_edge fn l succ` by metis_tac[fn_cfg_edge_def,
    venomExecPropsTheory.lookup_block_label] >>
  fs[current_available_def] >>
  rpt strip_tac >>
  `is_fn_path fn (path ++ [succ])` by metis_tac[venomExecProofsTheory.is_fn_path_snoc] >>
  `HD (path ++ [succ]) = HD path` by (Cases_on `path` >> gvs[]) >>
  `LAST (path ++ [succ]) = succ` by simp[] >>
  qpat_x_assum `!path. _` (qspec_then `path ++ [succ]` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `k < LENGTH path - 1`
  >- (disj1_tac >> qexistsl_tac [`k`, `db`, `di`] >>
      gvs[EL_APPEND_EQN]) >>
  disj2_tac >>
  `k = LENGTH path - 1` by decide_tac >>
  `EL k (path ++ [succ]) = LAST path` by
    (gvs[] >> simp[EL_APPEND_EQN, LAST_EL, PRE_SUB1]) >>
  `db = bb` by
    (`ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       gvs[wf_function_def, fn_labels_def] >>
     `lookup_block l fn.fn_blocks = SOME db` by
       (irule venomExecPropsTheory.MEM_lookup_block >> simp[] >> metis_tac[]) >>
     metis_tac[optionTheory.SOME_11]) >>
  gvs[MEM_EL] >> metis_tac[]
QED

Theorem current_block_distinct_ids[local]:
  !bbs bb. ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) bbs)) /\
    MEM bb bbs ==> ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  Induct >> simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >> gvs[]
QED

Theorem current_block_index_unique:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
  EL i bb.bb_instructions = EL j bb.bb_instructions ==> i = j
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule current_block_distinct_ids >> qexists_tac `fn.fn_blocks` >>
     gvs[wf_function_def, fn_inst_ids_distinct_def]) >>
  drule ALL_DISTINCT_EL_IMP >>
  disch_then (qspecl_then [`i`, `j`] mp_tac) >> simp[EL_MAP]
QED

Theorem current_available_from_exit:
  lookup_block l fn.fn_blocks = SOME bb /\
  def_on_all_paths fn bb NONE v ==>
  current_available fn v l (LENGTH bb.bb_instructions)
Proof
  simp[current_available_def, def_on_all_paths_def] >> rpt strip_tac >>
  `bb.bb_label = l` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  gvs[] >> metis_tac[]
QED

Theorem current_available_from_inst:
  wf_function fn /\ lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  def_on_all_paths fn bb (SOME (EL i bb.bb_instructions)) v ==>
  current_available fn v l i
Proof
  simp[current_available_def, def_on_all_paths_def] >> rpt strip_tac >>
  `bb.bb_label = l` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  qpat_x_assum `!path. _` drule >> simp[] >> strip_tac
  >- metis_tac[] >>
  `j = i` by metis_tac[current_block_index_unique] >>
  metis_tac[]
QED

Theorem current_available_ordinary:
  wf_function fn /\ fn_defs_reach_uses fn /\
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode <> PHI /\
  MEM v (inst_uses (EL i bb.bb_instructions)) ==>
  current_available fn v l i
Proof
  strip_tac >> irule current_available_from_inst >>
  goal_assum (drule_at Any) >> simp[] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by metis_tac[MEM_EL] >>
  fs[fn_defs_reach_uses_def, inst_uses_def,
     passSharedDefsTheory.MEM_operand_vars_eq_Var] >> metis_tac[]
QED

Theorem current_available_edge:
  fn_defs_reach_uses fn /\
  lookup_block l fn.fn_blocks = SOME bb /\
  MEM succ (bb_succs bb) /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM phi (collect_phis sb.bb_instructions) /\
  MEM (l,v) (phi_pairs phi.inst_operands) ==>
  current_available fn v l (LENGTH bb.bb_instructions)
Proof
  strip_tac >> irule current_available_from_exit >>
  goal_assum (drule_at Any) >>
  `MEM bb fn.fn_blocks /\ MEM sb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb.bb_label = l /\ sb.bb_label = succ` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `fn_cfg_edge fn l succ` by metis_tac[fn_cfg_edge_def] >>
  drule livenessTransferProofsTheory.collect_phis_mem >> strip_tac >>
  fs[fn_defs_reach_uses_def] >> metis_tac[]
QED

Theorem current_demand_available:
  !fn v l i. current_demand fn v l i ==>
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn ==>
  current_available fn v l i
Proof
  ntac 2 gen_tac >> ho_match_mp_tac current_demand_ind >> rpt strip_tac
  >- metis_tac[current_available_ordinary]
  >- metis_tac[current_available_edge]
  >- metis_tac[current_available_skip] >>
  metis_tac[current_available_cross]
QED
