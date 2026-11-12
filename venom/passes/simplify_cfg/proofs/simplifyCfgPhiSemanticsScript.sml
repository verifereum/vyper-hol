Theory simplifyCfgPhiSemantics
Ancestors
  simplifyCfgDefs simplifyCfgAvailability venomExecProofs venomWf venomWfProps
  cfgTransform venomExecSemantics venomInst o1FnScheduleDecompHelpers
  analysisSimProofsBase dftCommutation simplifyCfgFragments instIdxIndep list relation
  simplifyCfgRepairDataflow simplifyCfgPhiRepair

Theorem scfg_single_pred_avoiding_path:
  fn_reachable fn b /\ fn_entry_label fn <> SOME b /\
  pred_labels fn b = [p] ==>
  ?route. is_fn_path fn route /\ route <> [] /\
    (?entry. fn_entry_label fn = SOME entry /\ HD route = entry) /\
    LAST route = p /\ ~MEM b route
Proof
  rpt strip_tac >>
  `!x. fn_cfg_edge fn x b ==> x = p` by
    (rpt strip_tac >>
     qpat_x_assum `fn_cfg_edge _ _ _`
       (qx_choose_then `pb` strip_assume_tac o REWRITE_RULE [fn_cfg_edge_def]) >>
     gvs[pred_labels_def, block_preds_def] >>
     `MEM pb (FILTER (\bb. MEM b (bb_succs bb)) fn.fn_blocks)` by
       (rewrite_tac[MEM_FILTER] >> simp[]) >> gvs[]) >>
  gvs[fn_reachable_def] >> drule rtc_to_fn_path >> strip_tac >>
  `HD path <> b` by simp[] >>
  drule_all is_fn_path_first_predecessor >> metis_tac[]
QED

Theorem scfg_path_member_reachable:
  is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ MEM b path ==>
  fn_reachable fn b
Proof
  rpt strip_tac >> drule_all is_fn_path_prefix >> strip_tac >>
  `pre ++ [b] <> []` by simp[] >>
  drule_all is_fn_path_rtc >> simp[] >> strip_tac >>
  simp[fn_reachable_def] >> metis_tac[]
QED

Theorem scfg_instruction_block_unique:
  fn_inst_ids_distinct fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  MEM i a.bb_instructions /\ MEM i b.bb_instructions ==> a = b
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
      fn.fn_blocks))` by gvs[fn_inst_ids_distinct_def] >>
  `MEM i.inst_id (MAP (\i. i.inst_id) a.bb_instructions)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  drule distinct_flat_map_members_disjoint >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem scfg_phi_not_entry:
  wf_function fn /\ simplify_cfg_fn_ok fn /\ MEM bb fn.fn_blocks /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
  fn_entry_label fn <> SOME bb.bb_label
Proof
  rpt strip_tac >>
  `fn.fn_blocks <> []` by metis_tac[MEM] >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `(HD fn.fn_blocks).bb_label = bb.bb_label` by
    gvs[fn_entry_label_def, entry_block_def, NULL_EQ] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >> simp[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME (HD fn.fn_blocks)` by
    (irule venomExecProofsTheory.MEM_lookup_block >> simp[]) >>
  `HD fn.fn_blocks = bb` by metis_tac[optionTheory.SOME_11] >>
  gvs[simplify_cfg_fn_ok_def, EVERY_MEM] >> metis_tac[]
QED

Theorem scfg_path_definition_witness:
  def_on_all_paths fn bb NONE v /\ is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ LAST path = bb.bb_label /\
  MEM bb fn.fn_blocks ==>
  ?db di. MEM db fn.fn_blocks /\ MEM db.bb_label path /\
    fn_reachable fn db.bb_label /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs
Proof
  rpt strip_tac >>
  qpat_x_assum `def_on_all_paths fn bb NONE v` mp_tac >>
  rewrite_tac[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> strip_tac
  >- (`MEM def_bb.bb_label path` by
        (gvs[] >> rewrite_tac[MEM_EL] >> qexists_tac `k` >> simp[]) >>
      metis_tac[scfg_path_member_reachable]) >>
  `MEM bb.bb_label path` by metis_tac[rich_listTheory.LAST_MEM] >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  metis_tac[scfg_path_member_reachable]
QED

Theorem scfg_phi_source_output_separate:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  pred_labels fn bb.bb_label = [p] /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  resolve_phi p i.inst_operands = SOME (Var v) /\
  MEM j bb.bb_instructions /\ j.inst_opcode = PHI ==>
  ~MEM v j.inst_outputs
Proof
  rpt strip_tac >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    metis_tac[scfg_phi_not_entry] >>
  drule_all scfg_single_pred_avoiding_path >> strip_tac >>
  `MEM (p,v) (phi_pairs i.inst_operands)` by
    metis_tac[resolve_phi_pair] >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = p /\
      fn_cfg_edge fn p bb.bb_label` by
    (qpat_x_assum `pred_labels fn bb.bb_label = [p]` mp_tac >>
     simp[pred_labels_def, block_preds_def, MAP_EQ_CONS] >>
     rpt strip_tac >> rename1 `FILTER _ _ = ob::_` >>
     `MEM ob (FILTER (\b. MEM bb.bb_label (bb_succs b)) fn.fn_blocks)` by
       simp[] >>
     fs[MEM_FILTER] >> simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `def_on_all_paths fn pb NONE v` by
    (gvs[simplify_cfg_fn_ok_def, fn_defs_reach_uses_def] >> metis_tac[]) >>
  `?db di. MEM db fn.fn_blocks /\ MEM db.bb_label route /\
      fn_reachable fn db.bb_label /\ MEM di db.bb_instructions /\
      MEM v di.inst_outputs` by
    (irule scfg_path_definition_witness >> simp[] >> metis_tac[]) >>
  `di = j` by (gvs[simplify_cfg_fn_ok_def] >> metis_tac[]) >>
  `db = bb` by
    (irule scfg_instruction_block_unique >>
     metis_tac[wf_function_def]) >> gvs[]
QED

Theorem scfg_phi_list_outputs_distinct:
  !ps. ALL_DISTINCT ps /\
    EVERY (\i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI) ps /\
    wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
    MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) ps))
Proof
  Induct >> simp[] >> qx_gen_tac `x` >> rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) ps))` by
    metis_tac[] >>
  `inst_wf x` by metis_tac[fn_inst_wf_def, EVERY_MEM] >>
  `LENGTH x.inst_outputs = 1` by gvs[inst_wf_def] >>
  `?v. x.inst_outputs = [v]` by
    (namedCases_on `x.inst_outputs` ["", "out outs"] >> gvs[] >>
     Cases_on `outs` >> gvs[]) >>
  simp[ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
  `MEM v x.inst_outputs` by simp[] >>
  `MEM i bb.bb_instructions /\ i.inst_opcode = PHI` by
    (fs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  `i = x` by (fs[simplify_cfg_fn_ok_def] >> metis_tac[MEM]) >>
  gvs[]
QED

Theorem scfg_phi_prefix_outputs_distinct:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
    (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)))
Proof
  rpt strip_tac >> irule scfg_phi_list_outputs_distinct >>
  conj_tac
  >- (`ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
        (`?xs ys. fn.fn_blocks = xs ++ bb::ys` by metis_tac[MEM_SPLIT] >>
         fs[wf_function_def, fn_inst_ids_distinct_def,
            MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
      metis_tac[ALL_DISTINCT_MAP, ALL_DISTINCT_TAKE]) >>
  qexistsl_tac [`bb`, `fn`] >> simp[] >>
  mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_all_phi) >>
  simp[EVERY_MEM] >> metis_tac[TAKE_DROP, MEM_APPEND]
QED

Theorem scfg_canon_jnz_step:
  inst_wf i /\ i.inst_opcode = JNZ /\
  i.inst_operands = [c; Label l; Label l] /\
  IS_SOME (eval_operand c s) ==>
  step_inst k C (canon_jnz_inst i) s = step_inst k C i s
Proof
  rpt strip_tac >>
  `i.inst_outputs = []` by gvs[inst_wf_def] >>
  Cases_on `i` >> gvs[] >>
  Cases_on `eval_operand c s` >> gvs[] >>
  simp[canon_jnz_inst_def, step_inst_def, step_inst_base_def]
QED

Theorem scfg_filter_phi_single_head:
  !ops p op. phi_well_formed ops /\ resolve_phi p ops = SOME op ==>
  ?rest. filter_phi_ops [p] ops = Label p :: op :: rest
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, filter_phi_ops_def, resolve_phi_def] >>
  rpt strip_tac >> Cases_on `lbl = p` >> gvs[]
QED

Theorem scfg_fix_phi_assign:
  !i preds p op. i.inst_opcode = PHI /\ filter_phi_ops preds i.inst_operands = [Label p; op] ==>
  fix_phi_inst preds i = i with <|inst_opcode := ASSIGN; inst_operands := [op]|>
Proof
  simp[fix_phi_inst_def]
QED

Theorem scfg_fix_phi_retained_resolve:
  !i preds p. phi_well_formed i.inst_operands /\ MEM p preds /\
  (fix_phi_inst preds i).inst_opcode = PHI ==>
  resolve_phi p (fix_phi_inst preds i).inst_operands = resolve_phi p i.inst_operands
Proof
  rpt strip_tac >> rename1 `MEM p actual_preds` >>
  Cases_on `i.inst_opcode = PHI`
  >- (qpat_x_assum `(fix_phi_inst _ _).inst_opcode = PHI` mp_tac >>
      simp[fix_phi_inst_def] >>
      namedCases_on `filter_phi_ops actual_preds i.inst_operands` ["", "o1 r1"] >>
      simp[] >> namedCases_on `r1` ["", "o2 r2"] >> simp[]
      >- metis_tac[resolve_phi_filter_phi_ops] >>
      Cases_on `r2` >> simp[] >>
      metis_tac[resolve_phi_filter_phi_ops]) >>
  simp[fix_phi_inst_def]
QED

Theorem scfg_eval_phis_snapshot:
  !ps kvs s. EVERY (\i. i.inst_opcode = PHI) ps /\
    LIST_REL (\i kv. eval_one_phi s i = SOME kv) ps kvs ==>
    eval_phis s ps = OK (FOLDR (\(x,v) t. update_var x v t) s kvs)
Proof
  Induct >> Cases_on `kvs` >> simp[eval_phis_def] >> rpt strip_tac >>
  rename1 `eval_one_phi s inst = SOME kv` >> PairCases_on `kv` >>
  simp[eval_phis_def] >> first_x_assum drule_all >> simp[]
QED

Theorem scfg_distinct_updates_order:
  !kvs s. ALL_DISTINCT (MAP FST kvs) ==>
    FOLDL (\t (x,v). update_var x v t) s kvs =
    FOLDR (\(x,v) t. update_var x v t) s kvs
Proof
  Induct >> simp[] >> Cases >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!s. FOLDL _ s kvs = _`
    (fn th => pure_once_rewrite_tac[GSYM th]) >>
  irule foldl_update_var_commute >> simp[]
QED

Theorem scfg_eval_phis_snapshot_forward:
  EVERY (\i. i.inst_opcode = PHI) ps /\
  LIST_REL (\i kv. eval_one_phi s i = SOME kv) ps kvs /\
  ALL_DISTINCT (MAP FST kvs) ==>
  eval_phis s ps = OK (FOLDL (\t (x,v). update_var x v t) s kvs)
Proof
  metis_tac[scfg_eval_phis_snapshot, scfg_distinct_updates_order]
QED

Theorem scfg_snapshot_operand_stable:
  !kvs s op. (!v. op = Var v ==> ~MEM v (MAP FST kvs)) ==>
  eval_operand op (FOLDL (\t (x,w). update_var x w t) s kvs) = eval_operand op s
Proof
  Induct >> simp[] >> Cases >> rpt strip_tac >> gvs[] >>
  irule eval_operand_update_var >> metis_tac[]
QED

Theorem scfg_snapshot_frame:
  !kvs s. execution_frame (FOLDL (\t (x,w). update_var x w t) s kvs) =
    execution_frame s
Proof
  Induct >- simp[] >> Cases >> rpt gen_tac >>
  pure_asm_rewrite_tac[FOLDL, pairTheory.pair_case_thm] >>
  simp[venomStateTheory.update_var_def]
QED

Theorem scfg_update_var_index[local]:
  update_var x v (s with vs_inst_idx := n) =
    update_var x v s with vs_inst_idx := n
Proof
  simp[venomStateTheory.update_var_def]
QED

Theorem scfg_assign_snapshot_prefix:
  !ps kvs acc pre post bb s C.
    bb.bb_instructions = pre ++ ps ++ post /\
    LIST_REL (\i kv. i.inst_opcode = ASSIGN /\
      i.inst_outputs = [FST kv] /\
      ?op. i.inst_operands = [op] /\ eval_operand op s = SOME (SND kv) /\
        (!v. op = Var v ==> ~MEM v (MAP FST (acc ++ kvs)))) ps kvs ==>
    scfg_iprefix C bb
      ((FOLDL (\t (x,w). update_var x w t) s acc)
        with vs_inst_idx := LENGTH pre)
      ((FOLDL (\t (x,w). update_var x w t) s (acc ++ kvs))
        with vs_inst_idx := LENGTH pre + LENGTH ps)
Proof
  Induct >> Cases_on `kvs` >> simp[] >> rpt strip_tac
  >- simp[scfg_iprefix_rules] >>
  rename1 `inst.inst_outputs = [FST kv]` >>
  PairCases_on `kv` >> gvs[] >>
  qmatch_goalsub_abbrev_tac `scfg_iprefix C bb ss0 tt0` >>
  `eval_operand op ss0 = SOME kv1` by
    (simp[Abbr `ss0`] >>
     `eval_operand op (FOLDL (\t (x,w). update_var x w t) s acc) = SOME kv1` by
       (mp_tac (Q.SPECL [`acc`, `s`, `op`] scfg_snapshot_operand_stable) >>
        simp[] >> metis_tac[]) >>
     Cases_on `op` >> gvs[venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def]) >>
  irule (cj 2 scfg_iprefix_rules) >>
  qexistsl_tac [`inst`, `0`, `update_var kv0 kv1 ss0`] >>
  simp[Abbr `ss0`, get_instruction_def, EL_APPEND_EQN,
    is_terminator_def, step_inst_def, step_inst_base_def] >>
  qpat_x_assum `!kvs acc pre post bb s C. _`
    (qspecl_then [`t`, `acc ++ [(kv0,kv1)]`, `pre ++ [inst]`, `post`] mp_tac) >>
  simp[MAP_APPEND, MEM_APPEND, rich_listTheory.FOLDL_APPEND, scfg_update_var_index,
    Abbr `tt0`, arithmeticTheory.ADD1, CONJ_ASSOC] >>
  disch_then irule >> fs[CONJ_ASSOC]
QED

Theorem scfg_single_phi_snapshot:
  phi_well_formed i.inst_operands /\
  filter_phi_ops [p] i.inst_operands = [Label p; op] /\
  i.inst_outputs = [x] /\ s.vs_prev_bb = SOME p /\
  eval_operand op s = SOME w ==>
  eval_one_phi s i = SOME (x,w)
Proof
  rpt strip_tac >>
  `resolve_phi p i.inst_operands = SOME op` by
    (`resolve_phi p (filter_phi_ops [p] i.inst_operands) =
      resolve_phi p i.inst_operands` by
       (irule resolve_phi_filter_phi_ops >> fs[]) >>
     gvs[resolve_phi_def]) >>
  simp[eval_one_phi_def]
QED

Theorem scfg_snapshot_lookup:
  ~MEM v (MAP FST kvs) ==>
  lookup_var v (FOLDL (\t (x,w). update_var x w t) s kvs) = lookup_var v s
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`kvs`, `s`, `Var v`] scfg_snapshot_operand_stable) >>
  simp[venomStateTheory.eval_operand_def]
QED

Theorem scfg_assign_snapshot_take:
  bb.bb_instructions = pre ++ ps ++ post /\ n <= LENGTH ps /\
  LIST_REL (\i kv. i.inst_opcode = ASSIGN /\
    i.inst_outputs = [FST kv] /\
    ?op. i.inst_operands = [op] /\ eval_operand op s = SOME (SND kv) /\
      (!v. op = Var v ==> ~MEM v (MAP FST kvs))) ps kvs ==>
  scfg_iprefix C bb (s with vs_inst_idx := LENGTH pre)
    ((FOLDL (\t (x,w). update_var x w t) s (TAKE n kvs))
      with vs_inst_idx := LENGTH pre + n)
Proof
  rpt strip_tac >>
  `LENGTH kvs = LENGTH ps` by fs[LIST_REL_EL_EQN] >>
  `!v. MEM v (MAP FST (TAKE n kvs)) ==> MEM v (MAP FST kvs)` by
    (simp[MEM_MAP] >> metis_tac[TAKE_DROP, MEM_APPEND]) >>
  mp_tac (Q.SPEC `TAKE n ps` scfg_assign_snapshot_prefix) >>
  disch_then (qspecl_then [`TAKE n kvs`, `[]`, `pre`, `DROP n ps ++ post`] mp_tac) >>
  simp[] >> disch_then irule >>
  conj_tac >- metis_tac[TAKE_DROP, APPEND_ASSOC] >>
  fs[LIST_REL_EL_EQN] >> simp[LIST_REL_EL_EQN, EL_TAKE] >>
  rpt strip_tac >> rename1 `j < n` >>
  `j < LENGTH ps` by decide_tac >>
  qpat_x_assum `!k. k < LENGTH ps ==> _` drule >> rpt strip_tac >>
  qexists_tac `op` >> simp[] >> metis_tac[]
QED

Theorem scfg_phi_serial_snapshot:
  s.vs_prev_bb = SOME p /\
  LIST_REL (\i kv. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    i.inst_outputs = [FST kv] /\
    ?op. filter_phi_ops [p] i.inst_operands = [Label p; op] /\
      eval_operand op s = SOME (SND kv) /\
      (!v. op = Var v ==> ~MEM v (MAP FST kvs))) ps kvs ==>
  LIST_REL (\i kv. eval_one_phi s i = SOME kv) ps kvs
Proof
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  qpat_x_assum `!n. n < LENGTH ps ==> _` (qspec_then `n` mp_tac) >>
  simp[] >> rpt strip_tac >>
  rename1 `eval_operand op s = SOME (SND kv)` >>
  PairCases_on `kv` >> gvs[] >>
  irule scfg_single_phi_snapshot >> metis_tac[]
QED

Theorem scfg_phi_serial_assigns:
  LIST_REL (\i kv. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    i.inst_outputs = [FST kv] /\
    ?op. filter_phi_ops [p] i.inst_operands = [Label p; op] /\
      eval_operand op s = SOME (SND kv) /\
      (!v. op = Var v ==> ~MEM v (MAP FST kvs))) ps kvs ==>
  LIST_REL (\i kv. i.inst_opcode = ASSIGN /\ i.inst_outputs = [FST kv] /\
    ?op. i.inst_operands = [op] /\ eval_operand op s = SOME (SND kv) /\
      (!v. op = Var v ==> ~MEM v (MAP FST kvs)))
    (MAP (fix_phi_inst [p]) ps) kvs
Proof
  simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
  qpat_x_assum `!n. n < LENGTH ps ==> _` (qspec_then `n` mp_tac) >>
  simp[] >> rpt strip_tac >>
  drule_all scfg_fix_phi_assign >> simp[] >> metis_tac[]
QED

Theorem scfg_phi_serialization:
  s.vs_prev_bb = SOME p /\ ALL_DISTINCT (MAP FST kvs) /\
  bb.bb_instructions = pre ++ MAP (fix_phi_inst [p]) ps ++ post /\
  LIST_REL (\i kv. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    i.inst_outputs = [FST kv] /\
    ?op. filter_phi_ops [p] i.inst_operands = [Label p; op] /\
      eval_operand op s = SOME (SND kv) /\
      (!v. op = Var v ==> ~MEM v (MAP FST kvs))) ps kvs ==>
  eval_phis s ps = OK (FOLDL (\t (x,w). update_var x w t) s kvs) /\
  (!n. n <= LENGTH ps ==>
    scfg_iprefix C bb (s with vs_inst_idx := LENGTH pre)
      ((FOLDL (\t (x,w). update_var x w t) s (TAKE n kvs))
        with vs_inst_idx := LENGTH pre + n))
Proof
  rpt strip_tac
  >- (irule scfg_eval_phis_snapshot_forward >> simp[] >>
      conj_tac
      >- (fs[EVERY_EL, LIST_REL_EL_EQN] >> metis_tac[]) >>
      irule scfg_phi_serial_snapshot >> metis_tac[]) >>
  irule scfg_assign_snapshot_take >> simp[] >>
  qexistsl_tac [`post`, `MAP (fix_phi_inst [p]) ps`] >>
  simp[] >> irule scfg_phi_serial_assigns >> simp[]
QED

Theorem scfg_snapshot_prefix_frame:
  execution_frame
    ((FOLDL (\t (x,w). update_var x w t) s (TAKE n kvs))
      with vs_inst_idx := idx) = execution_frame s
Proof
  `execution_frame ((FOLDL (\t (x,w). update_var x w t) s (TAKE n kvs))
     with vs_inst_idx := idx) =
   execution_frame (FOLDL (\t (x,w). update_var x w t) s (TAKE n kvs))` by simp[] >>
  metis_tac[scfg_snapshot_frame]
QED

Theorem scfg_snapshot_prefix_operand:
  (!v. op = Var v ==> ~MEM v (MAP FST kvs)) ==>
  eval_operand op
    ((FOLDL (\t (x,w). update_var x w t) s (TAKE n kvs))
      with vs_inst_idx := idx) = eval_operand op s
Proof
  strip_tac >> rewrite_tac[eval_op_inst_idx] >>
  irule scfg_snapshot_operand_stable >> rpt strip_tac >>
  fs[MEM_MAP] >> metis_tac[TAKE_DROP, MEM_APPEND]
QED

Theorem scfg_snapshot_prefix_lookup:
  ~MEM v (MAP FST (TAKE n kvs)) ==>
  lookup_var v
    ((FOLDL (\t (x,w). update_var x w t) s (TAKE n kvs))
      with vs_inst_idx := idx) = lookup_var v s
Proof
  strip_tac >>
  drule scfg_snapshot_lookup >>
  simp[venomStateTheory.lookup_var_def]
QED
