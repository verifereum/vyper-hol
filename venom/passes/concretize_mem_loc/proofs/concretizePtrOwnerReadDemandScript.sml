Theory concretizePtrOwnerReadDemand
Ancestors
  concretizePtrOwnerDemand concretizePtrLiveatProduction concretizePtrReadOrigin
  concretizePtrOwnerPath concretizePtrChronologicalHistory concretizePtrLifetime
  concretizeAnalysisLivenessTransfer concretizeAnalysisLivenessClosure
  concretizeMemLocDefs concretizePtrReadCoverage memLocDefs
  list indexedLists finite_map singleWriterScan relation pred_set
  venomExecSemantics concretizePtrHistoryUsed contextCodegenRel
  frameCfgBoundary frameHistoryCfg frameHistoryInstructions venomInstProps
  concretizePtrHistoryCfg o1PassContract enumeral

Theorem ptr_read_seed_not_kill[local]:
  ml_read_gen a bp mems inst ==> ~ptr_ml_can_kill a bp sizes inst
Proof
  simp[ml_read_gen_def, ml_callee_gen_def, ptr_ml_can_kill_def] >>
  rpt strip_tac >> gvs[inst_write_size_def, mem_write_ops_def]
QED

Theorem ptr_liveat_before_append[local]:
  !xs ys bit.
  ml_liveat_before_bit a bp mems sizes (xs ++ ys) bit =
  ml_liveat_before_bit a bp mems sizes xs
    (ml_liveat_before_bit a bp mems sizes ys bit)
Proof
  Induct >> simp[ml_liveat_before_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_liveat_before_bit_def]
QED

Theorem ptr_liveat_before_clear_prefix[local]:
  !xs bit. EVERY (\p. ~ptr_ml_can_kill a bp sizes (SND p)) xs /\ bit ==>
    ml_liveat_before_bit a bp mems sizes xs bit
Proof
  Induct >> simp[ml_liveat_before_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_liveat_before_bit_def]
QED

Theorem ptr_liveat_record_at_split[local]:
  !pre idx inst rest bit old.
  EVERY (\p. FST p <> idx) pre ==>
  ml_liveat_record_bit a bp mems sizes lbl (lbl,idx)
    (pre ++ (idx,inst)::rest) bit old =
    (ml_liveat_before_bit a bp mems sizes rest bit \/ ml_read_gen a bp mems inst)
Proof
  Induct >> simp[ml_liveat_record_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_liveat_record_bit_def] >> metis_tac[]
QED

Theorem ptr_liveat_before_seed[local]:
  EVERY (\p. ~ptr_ml_can_kill a bp sizes (SND p)) pre /\
  ml_read_gen a bp mems inst ==>
  ml_liveat_before_bit a bp mems sizes (pre ++ (idx,inst)::rest) bit
Proof
  strip_tac >> simp[ptr_liveat_before_append, ml_liveat_before_bit_def] >>
  irule ptr_liveat_before_clear_prefix >> simp[] >>
  metis_tac[ptr_read_seed_not_kill]
QED

Theorem ptr_liveat_indexed_record[local]:
  i < LENGTH insts ==>
  ml_liveat_record_bit a bp mems sizes lbl (lbl,i)
    (MAPi (\n inst. (n,inst)) insts) bit old =
  (ml_liveat_before_bit a bp mems sizes
     (DROP (SUC i) (MAPi (\n inst. (n,inst)) insts)) bit \/
   ml_read_gen a bp mems (EL i insts))
Proof
  strip_tac >>
  qabbrev_tac `xs = MAPi (\n inst. (n,inst)) insts` >>
  `i < LENGTH xs /\ EL i xs = (i,EL i insts)` by simp[Abbr `xs`, EL_MAPi] >>
  `xs = TAKE i xs ++ (i,EL i insts)::DROP (SUC i) xs` by
    metis_tac[rich_listTheory.TAKE_DROP_SUC, APPEND, APPEND_ASSOC] >>
  `EVERY (\p. FST p <> i) (TAKE i xs)` by
    (simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     `n < LENGTH xs` by simp[] >>
     gvs[Abbr `xs`, EL_MAPi] >> decide_tac) >>
  metis_tac[ptr_liveat_record_at_split]
QED

Theorem ptr_indexed_drop[local]:
  i < LENGTH insts ==>
  DROP i (MAPi (\n inst. (n,inst)) insts) =
    (i,EL i insts)::DROP (SUC i) (MAPi (\n inst. (n,inst)) insts)
Proof
  strip_tac >> qabbrev_tac `xs = MAPi (\n inst. (n,inst)) insts` >>
  `i < LENGTH xs /\ EL i xs = (i,EL i insts)` by simp[Abbr `xs`, EL_MAPi] >>
  `xs = TAKE i xs ++ (i,EL i insts)::DROP (SUC i) xs` by
    metis_tac[rich_listTheory.TAKE_DROP_SUC, APPEND, APPEND_ASSOC] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  `i - (i + 1) = 0` by decide_tac >>
  simp[DROP_APPEND, DROP_TAKE, arithmeticTheory.ADD1]
QED

Theorem ptr_liveat_before_record[local]:
  i < LENGTH insts /\
  ml_liveat_before_bit a bp mems sizes
    (DROP i (MAPi (\n inst. (n,inst)) insts)) bit ==>
  ml_liveat_record_bit a bp mems sizes lbl (lbl,i)
    (MAPi (\n inst. (n,inst)) insts) bit F
Proof
  strip_tac >> simp[ptr_liveat_indexed_record] >>
  `DROP i (MAPi (\n inst. (n,inst)) insts) =
    (i,EL i insts)::DROP (SUC i) (MAPi (\n inst. (n,inst)) insts)` by
    metis_tac[ptr_indexed_drop] >>
  gvs[ml_liveat_before_bit_def]
QED

Theorem ptr_liveat_suffix_seed[local]:
  i < LENGTH insts /\ ml_read_gen a bp mems (EL i insts) ==>
  ml_liveat_before_bit a bp mems sizes
    (DROP i (MAPi (\n inst. (n,inst)) insts)) bit
Proof
  strip_tac >>
  `DROP i (MAPi (\n inst. (n,inst)) insts) =
    (i,EL i insts)::DROP (SUC i) (MAPi (\n inst. (n,inst)) insts)` by
    metis_tac[ptr_indexed_drop] >>
  simp[ml_liveat_before_bit_def] >> metis_tac[ptr_read_seed_not_kill]
QED

Theorem ptr_liveat_suffix_step[local]:
  i < LENGTH insts /\ ~ptr_ml_can_kill a bp sizes (EL i insts) /\
  ml_liveat_before_bit a bp mems sizes
    (DROP (SUC i) (MAPi (\n inst. (n,inst)) insts)) bit ==>
  ml_liveat_before_bit a bp mems sizes
    (DROP i (MAPi (\n inst. (n,inst)) insts)) bit
Proof
  strip_tac >>
  `DROP i (MAPi (\n inst. (n,inst)) insts) =
    (i,EL i insts)::DROP (SUC i) (MAPi (\n inst. (n,inst)) insts)` by
    metis_tac[ptr_indexed_drop] >>
  simp[ml_liveat_before_bit_def]
QED

Theorem ptr_liveat_descriptor_seed[local]:
  MEM bb (ml_scan_blocks blocks order) /\
  ml_liveat_boundary_bit a bp mems sizes bb F ==>
  sw_seed (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks blocks order)) T bb.bb_label
Proof
  strip_tac >> simp[sw_seed_def] >>
  qexistsl_tac [`{T}`, `if ml_liveat_boundary_bit a bp mems sizes bb T
    then set (cfg_succs_of cfg bb.bb_label) else {}`] >>
  simp[MEM_MAP] >> qexists_tac `bb` >> simp[ml_liveat_boundary_desc_def]
QED

Theorem ptr_liveat_descriptor_edge[local]:
  MEM bb (ml_scan_blocks blocks order) /\
  ml_liveat_boundary_bit a bp mems sizes bb T /\
  MEM succ (cfg_succs_of cfg bb.bb_label) ==>
  sw_edge (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks blocks order)) succ bb.bb_label
Proof
  strip_tac >> simp[sw_edge_def] >>
  qexistsl_tac [`if ml_liveat_boundary_bit a bp mems sizes bb F then {T} else {}`,
    `set (cfg_succs_of cfg bb.bb_label)`] >>
  simp[MEM_MAP] >> qexists_tac `bb` >> simp[ml_liveat_boundary_desc_def]
QED

Theorem ptr_liveat_before_reachable[local]:
  MEM bb (ml_scan_blocks blocks order) /\ bb.bb_instructions <> [] /\
  ml_liveat_before_bit a bp mems sizes
    (MAPi (\n inst. (n,inst)) bb.bb_instructions)
    (?lbl x. MEM lbl (cfg_succs_of cfg bb.bb_label) /\
      sw_seed (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks blocks order)) T x /\
      RTC (sw_edge (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks blocks order))) x lbl) ==>
  ?x. sw_seed (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks blocks order)) T x /\
      RTC (sw_edge (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks blocks order))) x bb.bb_label
Proof
  strip_tac >>
  `ml_liveat_boundary_bit a bp mems sizes bb
    (?lbl x. MEM lbl (cfg_succs_of cfg bb.bb_label) /\
      sw_seed (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks blocks order)) T x /\
      RTC (sw_edge (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks blocks order))) x lbl)` by
    (simp[ml_liveat_boundary_bit_def] >> irule ptr_liveat_before_record >>
     simp[] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  pop_assum mp_tac >> once_rewrite_tac[ml_liveat_boundary_bit_affine] >>
  strip_tac
  >- (qexists_tac `bb.bb_label` >> simp[] >>
      metis_tac[ptr_liveat_descriptor_seed]) >>
  drule_all ptr_liveat_descriptor_edge >> strip_tac >>
  qexists_tac `x` >> simp[] >> metis_tac[relationTheory.RTC_CASES2]
QED

Theorem ptr_phi_prefix_no_kill[local]:
  EVERY (\inst. ~ptr_ml_can_kill a bp sizes inst)
    (TAKE (phi_prefix_length insts) insts)
Proof
  Induct_on `insts` >- simp[phi_prefix_length_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  gvs[phi_prefix_length_def] >>
  simp[ptr_ml_can_kill_def, inst_write_size_def, mem_write_ops_def]
QED

Theorem ptr_liveat_phi_entry[local]:
  ml_liveat_before_bit a bp mems sizes
    (DROP (phi_prefix_length insts) (MAPi (\n inst. (n,inst)) insts)) bit ==>
  ml_liveat_before_bit a bp mems sizes
    (MAPi (\n inst. (n,inst)) insts) bit
Proof
  strip_tac >>
  `EVERY (\p. ~ptr_ml_can_kill a bp sizes (SND p))
    (TAKE (phi_prefix_length insts) (MAPi (\n inst. (n,inst)) insts))` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     `n < phi_prefix_length insts /\ n < LENGTH insts` by
       gvs[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
     mp_tac ptr_phi_prefix_no_kill >>
     pure_rewrite_tac[EVERY_EL] >> disch_then (qspec_then `n` mp_tac) >>
     gvs[LENGTH_TAKE_EQ, EL_TAKE, EL_MAPi]) >>
  `MAPi (\n inst. (n,inst)) insts =
    TAKE (phi_prefix_length insts) (MAPi (\n inst. (n,inst)) insts) ++
    DROP (phi_prefix_length insts) (MAPi (\n inst. (n,inst)) insts)` by simp[] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  simp[ptr_liveat_before_append] >>
  irule ptr_liveat_before_clear_prefix >> simp[]
QED

Theorem ptr_liveat_active_block[local]:
  ptr_history_cfg_ok fn cfg /\ active_inst fn inst s ==>
  ?bb. MEM bb (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post) /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst
Proof
  simp[active_inst_def] >> strip_tac >> qexists_tac `bb` >> simp[] >>
  irule ptr_history_scan_member >> gvs[ptr_history_cfg_ok_def] >> metis_tac[]
QED

Theorem ptr_read_owner_control[local]:
  wf_function f.cf_fn /\ active_inst f.cf_fn f.cf_inst f.cf_state /\
  ptr_owner_transition ctx f g ==>
  f = g \/
  (g.cf_state.vs_current_bb = f.cf_state.vs_current_bb /\
   g.cf_state.vs_inst_idx = SUC f.cf_state.vs_inst_idx) \/
  (is_terminator f.cf_inst.inst_opcode /\
   fn_cfg_edge f.cf_fn f.cf_state.vs_current_bb g.cf_state.vs_current_bb /\
   ?bb. MEM bb f.cf_fn.fn_blocks /\ bb.bb_label = g.cf_state.vs_current_bb /\
     g.cf_state.vs_inst_idx = phi_prefix_length bb.bb_instructions)
Proof
  simp[ptr_owner_transition_def] >> rpt strip_tac >> gvs[]
  >- (drule_all step_preserves_control_flow >> simp[])
  >- (drule_all active_terminator_cfg_transition >> strip_tac >> simp[] >>
      metis_tac[enters_block_entry_index]) >>
  drule return_binding_current_bb >> simp[]
QED

Theorem ptr_liveat_control_back[local]:
  MEM next (ml_scan_blocks blocks order) /\
  i < LENGTH bb.bb_instructions /\
  ~ptr_ml_can_kill a bp sizes (EL i bb.bb_instructions) /\
  ml_liveat_before_bit a bp mems sizes
    (DROP j (MAPi (\n inst. (n,inst)) next.bb_instructions))
    (?lbl. MEM lbl (cfg_succs_of cfg next.bb_label) /\ X lbl) /\
  (!b. MEM b (ml_scan_blocks blocks order) /\ b.bb_instructions <> [] /\
    ml_liveat_before_bit a bp mems sizes
      (MAPi (\n inst. (n,inst)) b.bb_instructions)
      (?lbl. MEM lbl (cfg_succs_of cfg b.bb_label) /\ X lbl) ==> X b.bb_label) /\
  next.bb_instructions <> [] /\
  ((next = bb /\ j = SUC i) \/
   (SUC i = LENGTH bb.bb_instructions /\
    MEM next.bb_label (cfg_succs_of cfg bb.bb_label) /\
    j = phi_prefix_length next.bb_instructions)) ==>
  ml_liveat_before_bit a bp mems sizes
    (DROP i (MAPi (\n inst. (n,inst)) bb.bb_instructions))
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ X lbl)
Proof
  strip_tac
  >- (gvs[] >> irule ptr_liveat_suffix_step >> simp[]) >>
  `X next.bb_label` by
    (first_x_assum irule >> simp[] >> irule ptr_liveat_phi_entry >> gvs[]) >>
  `DROP (SUC i) (MAPi (\n inst. (n,inst)) bb.bb_instructions) = []` by simp[] >>
  simp[ptr_indexed_drop, ml_liveat_before_bit_def] >> metis_tac[]
QED

Theorem ptr_liveat_owner_step[local]:
  wf_function fn /\ ptr_history_cfg_ok fn cfg /\
  f.cf_fn = fn /\ g.cf_fn = fn /\
  active_inst fn f.cf_inst f.cf_state /\
  ptr_owner_transition ctx f g /\
  MEM bb fn.fn_blocks /\ bb.bb_label = f.cf_state.vs_current_bb /\
  f.cf_state.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL f.cf_state.vs_inst_idx bb.bb_instructions = f.cf_inst /\
  MEM next fn.fn_blocks /\ next.bb_label = g.cf_state.vs_current_bb /\
  ~ptr_ml_can_kill a bp sizes f.cf_inst /\
  ml_liveat_before_bit a bp mems sizes
    (DROP g.cf_state.vs_inst_idx (MAPi (\n inst. (n,inst)) next.bb_instructions))
    (?lbl. MEM lbl (cfg_succs_of cfg next.bb_label) /\ X lbl) /\
  (!b. MEM b (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post) /\
    b.bb_instructions <> [] /\
    ml_liveat_before_bit a bp mems sizes
      (MAPi (\n inst. (n,inst)) b.bb_instructions)
      (?lbl. MEM lbl (cfg_succs_of cfg b.bb_label) /\ X lbl) ==> X b.bb_label) ==>
  ml_liveat_before_bit a bp mems sizes
    (DROP f.cf_state.vs_inst_idx (MAPi (\n inst. (n,inst)) bb.bb_instructions))
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ X lbl)
Proof
  strip_tac >>
  `!b c. MEM b fn.fn_blocks /\ MEM c fn.fn_blocks /\ b.bb_label = c.bb_label ==>
      b = c` by
    (gvs[ptr_history_cfg_ok_def] >> metis_tac[optionTheory.SOME_11]) >>
  `MEM next (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post) /\
   next.bb_instructions <> []` by
    (gvs[ptr_history_cfg_ok_def] >> metis_tac[ptr_history_scan_member]) >>
  drule_at (Pat `ptr_owner_transition _ _ _`) ptr_read_owner_control >>
  simp[] >> strip_tac
  >- (`next = bb` by metis_tac[] >> gvs[])
  >- (`next = bb` by metis_tac[] >> gvs[] >>
      irule ptr_liveat_suffix_step >> simp[]) >>
  `next = bb'` by metis_tac[] >> gvs[] >>
  `SUC f.cf_state.vs_inst_idx = LENGTH bb.bb_instructions` by
    (`bb_well_formed bb` by metis_tac[venomWfTheory.wf_function_def] >>
     gvs[venomWfTheory.bb_well_formed_def] >> decide_tac) >>
  qpat_assum `bb.bb_label = _` (fn th => rewrite_tac[GSYM th]) >>
  irule ptr_liveat_control_back >> simp[] >>
  qexistsl_tac [`f.cf_fn.fn_blocks`, `phi_prefix_length bb'.bb_instructions`,
                `bb'`, `cfg.cfg_dfs_post`] >>
  gvs[ptr_history_cfg_ok_def] >> metis_tac[]
QED

Theorem ptr_read_history_active[local]:
  ptr_chrono_history vs C h endpoint /\ k < LENGTH h /\
  d <= LENGTH (EL k h).po_stack ==>
  active_inst (ptr_owner_view d (EL k h)).cf_fn
    (ptr_owner_view d (EL k h)).cf_inst (ptr_owner_view d (EL k h)).cf_state
Proof
  strip_tac >> irule (cj 1 ptr_owner_view_active) >> simp[] >>
  qexistsl_tac [`C`,`vs`] >>
  drule ptr_chrono_history_reachable >> simp[EVERY_EL]
QED

Theorem ptr_owner_interval_before[local]:
  !n i.
  ptr_chrono_history vs C h endpoint /\ i + n < LENGTH h /\
  (!k. i <= k /\ k <= i + n ==> d <= LENGTH (EL k h).po_stack) /\
  (ptr_owner_view d (EL i h)).cf_fn = fn /\
  wf_function fn /\ ptr_history_cfg_ok fn cfg /\
  (!k. i <= k /\ k < i + n ==>
    ~ptr_ml_can_kill a bp sizes (ptr_owner_view d (EL k h)).cf_inst) /\
  ml_read_gen a bp mems (ptr_owner_view d (EL (i + n) h)).cf_inst /\
  (!b. MEM b (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post) /\
    b.bb_instructions <> [] /\
    ml_liveat_before_bit a bp mems sizes
      (MAPi (\n inst. (n,inst)) b.bb_instructions)
      (?lbl. MEM lbl (cfg_succs_of cfg b.bb_label) /\ X lbl) ==> X b.bb_label) ==>
  !bb. MEM bb fn.fn_blocks /\
    bb.bb_label = (ptr_owner_view d (EL i h)).cf_state.vs_current_bb ==>
  ml_liveat_before_bit a bp mems sizes
    (DROP (ptr_owner_view d (EL i h)).cf_state.vs_inst_idx
      (MAPi (\n inst. (n,inst)) bb.bb_instructions))
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ X lbl)
Proof
  Induct >- (rpt strip_tac >>
    `active_inst fn (ptr_owner_view d (EL i h)).cf_inst
       (ptr_owner_view d (EL i h)).cf_state` by
      (gvs[] >> irule ptr_read_history_active >> simp[] >> metis_tac[]) >>
    gvs[active_inst_def] >>
    `bb = bb'` by
      (gvs[ptr_history_cfg_ok_def] >> metis_tac[optionTheory.SOME_11]) >>
    gvs[] >> irule ptr_liveat_suffix_seed >> simp[]) >>
  pop_assum (mk_asm "ih") >> rpt strip_tac >>
  `SUC i < LENGTH h /\ SUC i <= i + SUC n` by decide_tac >>
  `(ptr_owner_view d (EL (SUC i) h)).cf_fn = fn` by
    (`(ptr_owner_view d (EL i h)).cf_fn =
       (ptr_owner_view d (EL (SUC i) h)).cf_fn` by
      (irule ptr_owner_view_interval_function >> rpt conj_tac
       >- (rpt strip_tac >> first_x_assum irule >> decide_tac)
       >- decide_tac >- simp[] >> metis_tac[]) >> metis_tac[]) >>
  `active_inst fn (ptr_owner_view d (EL i h)).cf_inst
     (ptr_owner_view d (EL i h)).cf_state` by
    (gvs[] >> irule ptr_read_history_active >> simp[] >> metis_tac[]) >>
  `active_inst fn (ptr_owner_view d (EL (SUC i) h)).cf_inst
     (ptr_owner_view d (EL (SUC i) h)).cf_state` by
    (`active_inst (ptr_owner_view d (EL (SUC i) h)).cf_fn
       (ptr_owner_view d (EL (SUC i) h)).cf_inst
       (ptr_owner_view d (EL (SUC i) h)).cf_state` by
      (irule ptr_read_history_active >> simp[] >> metis_tac[]) >> metis_tac[]) >>
  drule_all ptr_liveat_active_block >> strip_tac >>
  asm_x "ih" (qspec_then `SUC i` mp_tac) >>
  impl_tac >- (fs[arithmeticTheory.ADD_CLAUSES] >> rpt conj_tac >>
    rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  disch_then (qspec_then `bb'` mp_tac) >> simp[] >> disch_tac >>
  qpat_assum `bb.bb_label = _` (fn th => rewrite_tac[GSYM th]) >>
  irule ptr_liveat_owner_step >> simp[] >>
  conj_tac >- (gvs[active_inst_def, ptr_history_cfg_ok_def] >> metis_tac[optionTheory.SOME_11]) >>
  conj_tac >- (gvs[active_inst_def, ptr_history_cfg_ok_def] >> metis_tac[optionTheory.SOME_11]) >>
  qexistsl_tac [`C`, `ptr_owner_view d (EL (SUC i) h)`, `bb'`] >> simp[] >>
  irule ptr_owner_view_step >> rpt conj_tac
  >- (first_x_assum irule >> decide_tac)
  >- (first_x_assum irule >> decide_tac) >>
  metis_tac[ptr_chrono_history_adjacent]

QED

Theorem ptr_owner_interval_liveat:
  ptr_chrono_history vs C h endpoint /\ i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
  (ptr_owner_view d (EL i h)).cf_fn = fn /\
  wf_function fn /\ ptr_history_cfg_ok fn cfg /\
  (!nm. OL alloc_to (mems nm)) /\
  (!k. i <= k /\ k < j ==>
    ~ptr_ml_can_kill a bp sizes (ptr_owner_view d (EL k h)).cf_inst) /\
  ml_read_gen a bp mems (ptr_owner_view d (EL j h)).cf_inst ==>
  MEM a (ml_lookup
    (FST (ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas cfg fn FEMPTY FEMPTY))
    ((ptr_owner_view d (EL i h)).cf_state.vs_current_bb,
     (ptr_owner_view d (EL i h)).cf_state.vs_inst_idx))
Proof
  strip_tac >>
  `active_inst fn (ptr_owner_view d (EL i h)).cf_inst
    (ptr_owner_view d (EL i h)).cf_state` by
    (gvs[] >> irule ptr_read_history_active >> simp[] >> metis_tac[]) >>
  drule_all ptr_liveat_active_block >> strip_tac >>
  qabbrev_tac `ds = MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)` >>
  qabbrev_tac `X = \lbl. ?x. sw_seed ds T x /\ RTC (sw_edge ds) x lbl` >>
  `!b. MEM b (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post) /\
    b.bb_instructions <> [] /\
    ml_liveat_before_bit a bp mems sizes
      (MAPi (\n inst. (n,inst)) b.bb_instructions)
      (?lbl. MEM lbl (cfg_succs_of cfg b.bb_label) /\ X lbl) ==> X b.bb_label` by
    (simp[Abbr `X`, Abbr `ds`, GSYM RIGHT_EXISTS_AND_THM] >> rpt strip_tac >>
     irule ptr_liveat_before_reachable >> simp[]) >>
  `ml_liveat_before_bit a bp mems sizes
    (DROP (ptr_owner_view d (EL i h)).cf_state.vs_inst_idx
      (MAPi (\n inst. (n,inst)) bb.bb_instructions))
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ X lbl)` by
    (irule ptr_owner_interval_before >> simp[] >>
     conj_tac >- (qexists_tac `j-i` >>
       `i + (j-i) = j` by decide_tac >> simp[]) >> metis_tac[]) >>
  qpat_assum `bb.bb_label = _` (fn th => rewrite_tac[GSYM th]) >>
  irule ptr_liveat_production_reachable_records >> simp[] >>
  conj_tac >- (gvs[ptr_history_cfg_ok_def, EVERY_MEM] >> metis_tac[]) >>
  irule ptr_liveat_before_record >> simp[] >>
  gvs[Abbr `X`, Abbr `ds`, GSYM RIGHT_EXISTS_AND_THM]
QED

Theorem ptr_stage_owner_interval_liveat:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  ptr_chrono_history vs C h endpoint /\ i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
  (ptr_owner_view d (EL i h)).cf_fn = fn /\
  FLOOKUP (ptr_owner_view d (EL i h)).cf_state.vs_allocas aid = SOME (b,sz) /\
  b <= byte /\ byte < b + sz /\
  (!k. i <= k /\ k < j ==>
    ~in_revert_forward (EL k h).po_fn (EL k h).po_state /\
    (!n off len. inst_write_size (EL k h).po_inst = SOME n /\
      MEM (off,len) (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state) ==>
      ~(off <= byte /\ byte < off + len))) /\
  o1_run_state_ok vs /\ o1_ctx_shape C /\ ~ctx_has_dalloca C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  EVERY (\f. EVERY (\inst. inst.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  wf_function fn /\ all_reachable fn /\ ptr_discipline lo C vs /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) /\
  (!nm. OL alloc_to (mems nm)) /\
  ml_read_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    mems (ptr_owner_view d (EL j h)).cf_inst ==>
  MEM (Allocation aid) (ml_lookup
    (FST (ml_iterate_fuel (concretize_memloc_fuel fn)
      (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
      mems
      (\a. if context_alloca_size fn (imported_mems_used observed.cu_context fn) a = 0
           then NONE else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a))
      pallocas (cfg_analyze fn) fn FEMPTY FEMPTY))
    ((ptr_owner_view d (EL i h)).cf_state.vs_current_bb,
     (ptr_owner_view d (EL i h)).cf_state.vs_inst_idx))
Proof
  strip_tac >>
  `!k. i <= k /\ k < j ==>
    ~ptr_ml_can_kill (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
      (\a. if context_alloca_size fn (imported_mems_used observed.cu_context fn) a = 0
           then NONE else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a))
      (ptr_owner_view d (EL k h)).cf_inst` by
    (gen_tac >> strip_tac >> drule_all ptr_stage_owner_interval_no_kill >> simp[]) >>
  irule ptr_owner_interval_liveat >> simp[] >>
  conj_tac >- (irule ptr_history_cfg_analyze_ok >> simp[]) >>
  conj_tac >- (qexists_tac `j` >> simp[]) >> metis_tac[]
QED
