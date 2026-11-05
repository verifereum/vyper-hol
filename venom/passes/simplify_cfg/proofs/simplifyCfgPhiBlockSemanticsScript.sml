Theory simplifyCfgPhiBlockSemantics
Ancestors
  simplifyCfgPhiSemantics simplifyCfgDefs venomExecSemantics venomWf venomInst list
  venomExecProofs dftCommutation cfgTransform
  simplifyCfgRepairDataflow

Theorem scfg_fix_phis_no_phi:
  !bb actual_preds. EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions ==>
    fix_phis_in_block actual_preds bb = bb
Proof
  rpt strip_tac >>
  `MAP (fix_phi_inst actual_preds) bb.bb_instructions = bb.bb_instructions` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     fs[EVERY_EL] >> simp[fix_phi_inst_def]) >>
  `FILTER (\i. i.inst_opcode = PHI) bb.bb_instructions = []` by
    fs[FILTER_EQ_NIL, EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode <> PHI) bb.bb_instructions = bb.bb_instructions` by
    simp[FILTER_EQ_ID] >>
  simp[fix_phis_in_block_def]
QED

(* Audit probe: separating only converted outputs from sources is insufficient.
   A retained PHI can overwrite a source read by a later converted ASSIGN. *)
Definition scfg_mixed_probe_phis_def:
  scfg_mixed_probe_phis =
    [mk_inst 0 PHI [Label "a"; Var "u"; Label "b"; Var "u"] ["x"];
     mk_inst 1 PHI [Label "a"; Var "x"] ["y"]]
End

Theorem scfg_mixed_phi_read_probe:
  s.vs_prev_bb = SOME "a" /\ lookup_var "u" s = SOME 1w /\
  lookup_var "x" s = SOME 7w ==>
  eval_phis s scfg_mixed_probe_phis =
    OK (update_var "x" 1w (update_var "y" 7w s)) /\
  eval_phis s (TAKE 1 (MAP (fix_phi_inst ["a"; "b"]) scfg_mixed_probe_phis)) =
    OK (update_var "x" 1w s) /\
  step_inst_base (EL 1 (MAP (fix_phi_inst ["a"; "b"]) scfg_mixed_probe_phis))
    (update_var "x" 1w s) = OK (update_var "y" 1w (update_var "x" 1w s))
Proof
  strip_tac >> rpt conj_tac >>
  simp[scfg_mixed_probe_phis_def, mk_inst_def, fix_phi_inst_def,
    filter_phi_ops_def, eval_phis_def, eval_one_phi_def, resolve_phi_def,
    venomStateTheory.eval_operand_def] >>
  simp[step_inst_base_def, venomStateTheory.eval_operand_def] >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem scfg_mixed_phi_partition_probe:
  MAP (\i. i.inst_opcode)
    (MAP (fix_phi_inst ["a"; "b"]) scfg_mixed_probe_phis) = [PHI; ASSIGN] /\
  MAP (\i. i.inst_outputs)
    (FILTER (\i. i.inst_opcode = ASSIGN)
      (MAP (fix_phi_inst ["a"; "b"]) scfg_mixed_probe_phis)) = [["y"]] /\
  ~MEM "y" ["u"; "x"] /\ ALL_DISTINCT ["x"; "y"]
Proof
  EVAL_TAC >> simp[]
QED

Theorem scfg_resolve_phi_two:
  !a b p op. resolve_phi p [a;b] = SOME op ==> a = Label p /\ b = op
Proof
  Cases >> simp[resolve_phi_def] >> rpt strip_tac >> gvs[]
QED

Theorem scfg_fix_phi_covered_shape:
  phi_well_formed i.inst_operands /\ i.inst_opcode = PHI /\
  MEM p actual_preds /\ resolve_phi p i.inst_operands = SOME op ==>
  (fix_phi_inst actual_preds i).inst_opcode <> NOP /\
  ((fix_phi_inst actual_preds i).inst_opcode = PHI \/
   (fix_phi_inst actual_preds i).inst_opcode = ASSIGN) /\
  ((fix_phi_inst actual_preds i).inst_opcode = ASSIGN ==>
    filter_phi_ops actual_preds i.inst_operands = [Label p;op])
Proof
  rpt strip_tac >>
  `resolve_phi p (filter_phi_ops actual_preds i.inst_operands) = SOME op` by
    metis_tac[resolve_phi_filter_phi_ops] >>
  namedCases_on `filter_phi_ops actual_preds i.inst_operands` ["", "o1 r1"] >>
  gvs[fix_phi_inst_def, resolve_phi_def] >>
  namedCases_on `r1` ["", "o2 r2"] >> gvs[resolve_phi_def] >>
  Cases_on `r2` >> gvs[] >>
  drule scfg_resolve_phi_two >> simp[]
QED

Theorem scfg_fix_phi_assign_predecessor_unique:
  phi_well_formed i.inst_operands /\ i.inst_opcode = PHI /\
  (fix_phi_inst actual_preds i).inst_opcode = ASSIGN /\
  MEM p actual_preds /\ MEM q actual_preds /\
  resolve_phi p i.inst_operands = SOME a /\
  resolve_phi q i.inst_operands = SOME b ==> p = q
Proof
  rpt strip_tac >>
  `filter_phi_ops actual_preds i.inst_operands = [Label p;a]` by
    (irule (cj 3 scfg_fix_phi_covered_shape) >> simp[]) >>
  `filter_phi_ops actual_preds i.inst_operands = [Label q;b]` by
    (irule (cj 3 scfg_fix_phi_covered_shape) >> simp[]) >> gvs[]
QED

Theorem scfg_fix_phi_covered_assign_single_pred:
  !actual_preds i.
  actual_preds <> [] /\ ALL_DISTINCT actual_preds /\
  phi_well_formed i.inst_operands /\ i.inst_opcode = PHI /\
  EVERY (\p. ?op. resolve_phi p i.inst_operands = SOME op) actual_preds /\
  (fix_phi_inst actual_preds i).inst_opcode = ASSIGN ==>
  ?p. actual_preds = [p]
Proof
  rpt gen_tac >> strip_tac >>
  namedCases_on `actual_preds` ["", "p r"] >> gvs[] >>
  namedCases_on `r` ["", "q rest"] >- simp[] >> gvs[] >>
  `p = q` by metis_tac[scfg_fix_phi_assign_predecessor_unique, MEM] >> gvs[]
QED

Theorem scfg_fix_phi_covered_not_nop:
  !actual_preds i.
  actual_preds <> [] /\ phi_well_formed i.inst_operands /\
  i.inst_opcode = PHI /\
  EVERY (\p. ?op. resolve_phi p i.inst_operands = SOME op) actual_preds ==>
  (fix_phi_inst actual_preds i).inst_opcode <> NOP
Proof
  Cases >> simp[] >> rpt strip_tac >>
  drule scfg_fix_phi_covered_shape >> simp[] >> metis_tac[MEM]
QED

Theorem scfg_fix_phi_two_covered_retained:
  phi_well_formed i.inst_operands /\ i.inst_opcode = PHI /\
  MEM p actual_preds /\ MEM q actual_preds /\ p <> q /\
  resolve_phi p i.inst_operands = SOME a /\
  resolve_phi q i.inst_operands = SOME b ==>
  (fix_phi_inst actual_preds i).inst_opcode = PHI
Proof
  rpt strip_tac >> drule_all (cj 2 scfg_fix_phi_covered_shape) >>
  strip_tac >>
  `p = q` by (irule scfg_fix_phi_assign_predecessor_unique >>
    qexistsl_tac [`a`, `actual_preds`, `b`, `i`] >> simp[]) >> gvs[]
QED

Theorem scfg_mixed_phi_missing_coverage_probe:
  resolve_phi "b" (EL 1 scfg_mixed_probe_phis).inst_operands = NONE /\
  ~EVERY (\p. ?op. resolve_phi p (EL 1 scfg_mixed_probe_phis).inst_operands = SOME op)
    ["a";"b"]
Proof
  EVAL_TAC >> simp[]
QED

(* Retaining a PHI changes neither its destination nor its selected read. *)
Theorem scfg_fix_phi_outputs:
  !i actual_preds. (fix_phi_inst actual_preds i).inst_opcode <> NOP ==>
    (fix_phi_inst actual_preds i).inst_outputs = i.inst_outputs
Proof
  rpt gen_tac >> simp[fix_phi_inst_def] >>
  Cases_on `i.inst_opcode = PHI` >> simp[] >>
  namedCases_on `filter_phi_ops actual_preds i.inst_operands` ["", "o1 r1"] >>
  simp[] >> namedCases_on `r1` ["", "o2 r2"] >> simp[] >> Cases_on `r2` >> simp[]
QED

Theorem scfg_fix_phi_retained_eval:
  phi_well_formed i.inst_operands /\ MEM p actual_preds /\
  (fix_phi_inst actual_preds i).inst_opcode = PHI /\
  s.vs_prev_bb = SOME p ==>
  eval_one_phi s (fix_phi_inst actual_preds i) = eval_one_phi s i
Proof
  strip_tac >> drule_all scfg_fix_phi_retained_resolve >>
  simp[eval_one_phi_def, scfg_fix_phi_outputs]
QED

Theorem scfg_eval_phis_operand_stable:
  eval_phis s ps = OK t /\
  (!v i. op = Var v /\ MEM i ps /\ i.inst_opcode = PHI ==>
    ~MEM v i.inst_outputs) ==>
  eval_operand op t = eval_operand op s
Proof
  strip_tac >> Cases_on `op` >> simp[venomStateTheory.eval_operand_def]
  >- (simp[venomStateTheory.lookup_var_def] >>
      irule eval_phis_flookup_not_phi_output >> metis_tac[]) >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

(* Stable partition only reorders writes to distinct destinations. *)
Theorem scfg_snapshot_partition:
  !ps f P s. ALL_DISTINCT (MAP (FST o f) ps) ==>
  FOLDL (\t (x,w). update_var x w t) s (MAP f ps) =
  FOLDL (\t (x,w). update_var x w t) s
    (MAP f (FILTER P ps) ++ MAP f (FILTER (\i. ~P i) ps))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `f h` >> gvs[] >> Cases_on `P h` >>
  simp[rich_listTheory.FOLDL_APPEND] >>
  first_x_assum (qspecl_then [`f`, `P`, `update_var q r s`] mp_tac) >>
  simp[rich_listTheory.FOLDL_APPEND] >> disch_then SUBST1_TAC >>
  `~MEM q (MAP FST (MAP f (FILTER P ps)))` by
    (gvs[MEM_MAP] >> metis_tac[MEM_FILTER]) >>
  simp[foldl_update_var_commute]
QED

Theorem scfg_distinct_snapshot_filter[local]:
  !ps f P. ALL_DISTINCT (MAP f ps) ==> ALL_DISTINCT (MAP f (FILTER P ps))
Proof
  Induct >> simp[] >> rpt strip_tac >> Cases_on `P h` >> simp[] >>
  gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem scfg_retained_snapshot:
  MEM p actual_preds /\ s.vs_prev_bb = SOME p /\
  ALL_DISTINCT (MAP (FST o snap) ps) /\
  EVERY (\i. phi_well_formed i.inst_operands /\
    eval_one_phi s i = SOME (snap i)) ps ==>
  eval_phis s
    (MAP (fix_phi_inst actual_preds)
      (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps)) =
    OK (FOLDL (\t (x,w). update_var x w t) s
      (MAP snap (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps)))
Proof
  strip_tac >> irule scfg_eval_phis_snapshot_forward >>
  simp[EVERY_MAP, EVERY_FILTER, LIST_REL_EL_EQN, EL_MAP] >>
  conj_tac
  >- (simp[MAP_MAP_o] >> irule scfg_distinct_snapshot_filter >> simp[]) >>
  rpt strip_tac >>
  `MEM (EL n (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps))
    (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps)` by
    metis_tac[MEM_EL] >>
  fs[MEM_FILTER, EVERY_MEM] >>
  first_x_assum drule >> strip_tac >>
  drule_all scfg_fix_phi_retained_eval >> simp[]
QED

Theorem scfg_partition_assign_snapshot:
  EVERY (\i. ~P i ==>
    (g i).inst_opcode = ASSIGN /\ (g i).inst_outputs = [FST (snap i)] /\
    ?op. (g i).inst_operands = [op] /\ eval_operand op s = SOME (SND (snap i)) /\
      (!v. op = Var v ==> ~MEM v (MAP (FST o snap) ps))) ps ==>
  LIST_REL (\i kv. i.inst_opcode = ASSIGN /\ i.inst_outputs = [FST kv] /\
    ?op. i.inst_operands = [op] /\ eval_operand op s = SOME (SND kv) /\
      (!v. op = Var v ==>
        ~MEM v (MAP FST (MAP snap (FILTER P ps) ++ MAP snap (FILTER (\j. ~P j) ps)))))
    (MAP g (FILTER (\i. ~P i) ps)) (MAP snap (FILTER (\i. ~P i) ps))
Proof
  simp[LIST_REL_EL_EQN, EL_MAP, EVERY_MEM] >> rpt strip_tac >>
  `MEM (EL n (FILTER (\i. ~P i) ps)) (FILTER (\i. ~P i) ps)` by
    metis_tac[MEM_EL] >>
  fs[MEM_FILTER] >> first_x_assum drule >> simp[] >> rpt strip_tac >>
  qexists_tac `op` >> simp[MAP_APPEND, MEM_APPEND, MAP_MAP_o] >>
  gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

(* Converted reads avoid every snapshot destination, not merely converted
   destinations. Retained reads are unrestricted: they still read s. *)
Theorem scfg_mixed_phi_partition:
  MEM p actual_preds /\ s.vs_prev_bb = SOME p /\
  ALL_DISTINCT (MAP (FST o snap) ps) /\
  rs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps /\
  bb.bb_instructions = pre ++ MAP (fix_phi_inst actual_preds) cs ++ post /\
  EVERY (\i. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    eval_one_phi s i = SOME (snap i) /\
    ((fix_phi_inst actual_preds i).inst_opcode <> PHI ==>
      (fix_phi_inst actual_preds i).inst_opcode = ASSIGN /\
      (fix_phi_inst actual_preds i).inst_outputs = [FST (snap i)] /\
      ?op. (fix_phi_inst actual_preds i).inst_operands = [op] /\
        eval_operand op s = SOME (SND (snap i)) /\
        (!v. op = Var v ==> ~MEM v (MAP (FST o snap) ps)))) ps ==>
  eval_phis s ps = OK (FOLDL (\t (x,w). update_var x w t) s (MAP snap ps)) /\
  eval_phis s (MAP (fix_phi_inst actual_preds) rs) =
    OK (FOLDL (\t (x,w). update_var x w t) s (MAP snap rs)) /\
  scfg_iprefix C bb
    ((FOLDL (\t (x,w). update_var x w t) s (MAP snap rs))
      with vs_inst_idx := LENGTH pre)
    ((FOLDL (\t (x,w). update_var x w t) s (MAP snap ps))
      with vs_inst_idx := LENGTH pre + LENGTH cs)
Proof
  strip_tac >> conj_tac
  >- (irule scfg_eval_phis_snapshot_forward >>
      fs[EVERY_EL, LIST_REL_EL_EQN, EL_MAP, MAP_MAP_o] >> metis_tac[]) >>
  conj_tac
  >- (simp[] >> irule scfg_retained_snapshot >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  `FOLDL (\t (x,w). update_var x w t) s (MAP snap ps) =
    FOLDL (\t (x,w). update_var x w t) s (MAP snap rs ++ MAP snap cs)` by
    (simp[] >> ho_match_mp_tac scfg_snapshot_partition >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule (SRULE [LENGTH_MAP]
    (Q.SPEC `MAP (fix_phi_inst actual_preds) cs` scfg_assign_snapshot_prefix)) >>
  qexistsl_tac [`actual_preds`, `post`] >> simp[] >>
  ho_match_mp_tac (SRULE [MAP_APPEND, MEM_APPEND] scfg_partition_assign_snapshot) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem scfg_fix_phi_assign_read:
  phi_well_formed i.inst_operands /\ i.inst_opcode = PHI /\
  MEM p actual_preds /\ s.vs_prev_bb = SOME p /\
  eval_one_phi s i = SOME kv /\
  (fix_phi_inst actual_preds i).inst_opcode = ASSIGN ==>
  (fix_phi_inst actual_preds i).inst_outputs = [FST kv] /\
  ?op. (fix_phi_inst actual_preds i).inst_operands = [op] /\
    resolve_phi p i.inst_operands = SOME op /\ eval_operand op s = SOME (SND kv)
Proof
  PairCases_on `kv` >> strip_tac >> gvs[eval_one_phi_def, AllCaseEqs()] >>
  drule_all (cj 3 scfg_fix_phi_covered_shape) >> strip_tac >>
  drule_all scfg_fix_phi_assign >> simp[] >> metis_tac[]
QED

Theorem scfg_fix_phis_partition_instructions:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  rs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps ==>
  (fix_phis_in_block actual_preds bb).bb_instructions =
    MAP (fix_phi_inst actual_preds) rs ++
    MAP (fix_phi_inst actual_preds) cs ++ tail
Proof
  strip_tac >>
  `MAP (fix_phi_inst actual_preds) tail = tail` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     fs[EVERY_EL] >> simp[fix_phi_inst_def]) >>
  `FILTER (\i. i.inst_opcode = PHI) tail = []` by
    fs[FILTER_EQ_NIL, EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode <> PHI) tail = tail` by
    simp[FILTER_EQ_ID] >>
  simp[fix_phis_in_block_def, MAP_APPEND, FILTER_APPEND_DISTRIB,
    rich_listTheory.FILTER_MAP, combinTheory.o_DEF]
QED

Theorem scfg_covered_snapshot_conditions:
  MEM p actual_preds /\ s.vs_prev_bb = SOME p /\
  EVERY (\i. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    eval_one_phi s i = SOME (snap i) /\
    EVERY (\q. ?op. resolve_phi q i.inst_operands = SOME op) actual_preds) ps /\
  (!i v. MEM i ps /\ (fix_phi_inst actual_preds i).inst_opcode = ASSIGN /\
    resolve_phi p i.inst_operands = SOME (Var v) ==>
    ~MEM v (MAP (FST o snap) ps)) ==>
  EVERY (\i. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    eval_one_phi s i = SOME (snap i) /\
    ((fix_phi_inst actual_preds i).inst_opcode <> PHI ==>
      (fix_phi_inst actual_preds i).inst_opcode = ASSIGN /\
      (fix_phi_inst actual_preds i).inst_outputs = [FST (snap i)] /\
      ?op. (fix_phi_inst actual_preds i).inst_operands = [op] /\
        eval_operand op s = SOME (SND (snap i)) /\
        (!v. op = Var v ==> ~MEM v (MAP (FST o snap) ps)))) ps
Proof
  strip_tac >> simp[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
  `i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
   eval_one_phi s i = SOME (snap i) /\
   EVERY (\q. ?op. resolve_phi q i.inst_operands = SOME op) actual_preds` by
    fs[EVERY_MEM] >> simp[] >> strip_tac >>
  `?op. resolve_phi p i.inst_operands = SOME op` by fs[EVERY_MEM] >>
  `(fix_phi_inst actual_preds i).inst_opcode = ASSIGN` by
    metis_tac[scfg_fix_phi_covered_shape] >>
  drule_all scfg_fix_phi_assign_read >> strip_tac >> simp[] >>
  metis_tac[]
QED

Theorem scfg_fix_phis_block_snapshot:
  MEM p actual_preds /\ s.vs_prev_bb = SOME p /\
  ALL_DISTINCT (MAP (FST o snap) ps) /\
  bb.bb_instructions = ps ++ tail /\ EVERY (\i. i.inst_opcode <> PHI) tail /\
  rs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps /\
  EVERY (\i. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    eval_one_phi s i = SOME (snap i) /\
    EVERY (\q. ?op. resolve_phi q i.inst_operands = SOME op) actual_preds) ps /\
  (!i v. MEM i ps /\ (fix_phi_inst actual_preds i).inst_opcode = ASSIGN /\
    resolve_phi p i.inst_operands = SOME (Var v) ==>
    ~MEM v (MAP (FST o snap) ps)) ==>
  eval_phis s ps = OK (FOLDL (\t (x,w). update_var x w t) s (MAP snap ps)) /\
  eval_phis s (MAP (fix_phi_inst actual_preds) rs) =
    OK (FOLDL (\t (x,w). update_var x w t) s (MAP snap rs)) /\
  scfg_iprefix C (fix_phis_in_block actual_preds bb)
    ((FOLDL (\t (x,w). update_var x w t) s (MAP snap rs))
      with vs_inst_idx := LENGTH rs)
    ((FOLDL (\t (x,w). update_var x w t) s (MAP snap ps))
      with vs_inst_idx := LENGTH rs + LENGTH cs)
Proof
  strip_tac >>
  match_mp_tac (PURE_REWRITE_RULE [LENGTH_MAP]
    (Q.INST [`pre` |-> `MAP (fix_phi_inst actual_preds) rs`, `post` |-> `tail`]
      (SPEC_ALL scfg_mixed_phi_partition))) >>
  simp[] >> conj_tac
  >- (irule scfg_fix_phis_partition_instructions >> simp[]) >>
  irule scfg_covered_snapshot_conditions >> metis_tac[]
QED

Theorem scfg_reachable_pred_coverage:
  simplify_cfg_fn_ok fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  (!pb. MEM pb fn.fn_blocks /\ MEM bb.bb_label (bb_succs pb) ==>
    fn_reachable fn pb.bb_label) ==>
  EVERY (\p. ?op. resolve_phi p i.inst_operands = SOME op)
    (pred_labels fn bb.bb_label)
Proof
  strip_tac >> simp[EVERY_MEM, pred_labels_def, block_preds_def, MEM_MAP] >>
  rpt strip_tac >> fs[MEM_FILTER, simplify_cfg_fn_ok_def] >> metis_tac[]
QED

Theorem scfg_pred_labels_distinct:
  wf_function fn ==> ALL_DISTINCT (pred_labels fn lbl)
Proof
  strip_tac >> simp[pred_labels_def, block_preds_def] >>
  irule scfg_distinct_snapshot_filter >> gvs[wf_function_def, fn_labels_def]
QED

Theorem scfg_covered_conversion_source_separate:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = ASSIGN /\
  EVERY (\q. ?op. resolve_phi q i.inst_operands = SOME op)
    (pred_labels fn bb.bb_label) /\
  MEM p (pred_labels fn bb.bb_label) /\
  resolve_phi p i.inst_operands = SOME (Var v) /\
  MEM j bb.bb_instructions /\ j.inst_opcode = PHI ==>
  ~MEM v j.inst_outputs
Proof
  strip_tac >>
  `phi_well_formed i.inst_operands` by
    (fs[fn_inst_wf_def, EVERY_MEM] >>
     `inst_wf i` by metis_tac[] >> gvs[inst_wf_def]) >>
  `ALL_DISTINCT (pred_labels fn bb.bb_label)` by
    metis_tac[scfg_pred_labels_distinct] >>
  `pred_labels fn bb.bb_label <> []` by metis_tac[MEM] >>
  drule_all scfg_fix_phi_covered_assign_single_pred >> strip_tac >>
  `pred_labels fn bb.bb_label = [p]` by gvs[] >>
  irule scfg_phi_source_output_separate >> metis_tac[]
QED
