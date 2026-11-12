(* Initialization boundaries for the selected allocation relation. *)
Theory lowerDloadSafetyEntry
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyBoundary lowerDloadSafetyKernel
  ptrDiscipline contextCodegenRel lowerDloadSafetyPhiEffects lowerDloadSafetyUpdates
  lowerDloadConfiguredOrigins venomInst venomExecProofs unitShapeDefs pair pred_set
  o1PassContract unitTransformDefs finite_map list venomExecSemantics lowerDloadDefs
  o1ContractLowerDload lowerDloadSafetyLocations

Theorem ld_entry_phis:
  s.vs_prev_bb = NONE /\ eval_phis s insts = OK s' ==>
  s' = s /\ phi_prefix_length insts = 0
Proof
  Cases_on `insts` >> simp[eval_phis_def, phi_prefix_length_def] >>
  strip_tac >> Cases_on `h.inst_opcode = PHI` >>
  gvs[eval_one_phi_def, AllCaseEqs()]
QED

Theorem ld_enters_entry:
  s.vs_prev_bb = NONE /\ s.vs_inst_idx = 0 /\ enters_block fn s s' ==>
  s' = s
Proof
  simp[enters_block_def] >> strip_tac >>
  drule_all ld_entry_phis >> strip_tac >> gvs[]
QED

Theorem ld_envelope_entry:
  s.vs_inst_idx = 0 /\ active_inst fn inst s ==>
  ?X. ld_envelope u fn s 0 X 0
Proof
  simp[active_inst_def, MEM_EL] >> strip_tac >>
  simp[ld_envelope_def, lower_dload_insts_supply_def] >>
  metis_tac[]
QED

Theorem ld_sync_entry:
  o1_run_state_ok vs0 /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst fn inst s /\ EVERY (fn_ptr_ok P) C.ctx_functions ==>
  ?f. f.lf_fn = fn /\ f.lf_supply = u /\ f.lf_Q = [] /\
    ld_sync lo P C vs0 [] [] FEMPTY entry_taint fn inst s s FEMPTY [f] 1 /\
    ld_global lo FEMPTY [f]
Proof
  strip_tac >>
  `s = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    (irule ld_enters_entry >> simp[] >> metis_tac[]) >>
  `frame_reachable vs0 C [] [] FEMPTY entry_taint fn inst s` by
    (irule frame_reachable_entry >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  drule lower_dload_initial_allocations >> strip_tac >>
  `s.vs_inst_idx = 0` by simp[] >>
  drule_all ld_envelope_entry >> disch_then (qspec_then `u` strip_assume_tac) >>
  qexists_tac `<|lf_serial := 0; lf_supply := u; lf_fn := fn;
    lf_src := s; lf_tgt := s; lf_H := FEMPTY; lf_Q := [];
    lf_E := {}; lf_tv := entry_taint.t_var|>` >>
  simp[ld_sync_def, ld_global_def, ld_vars_def, ld_maps_def, ld_intervals_def,
       ld_slots_def, ld_sites_def, ld_charge_def, ld_memory_def,
       fmap_eq_flookup, FLOOKUP_o_f] >>
  metis_tac[]
QED

(* The pointer classification is supplied by the frozen source invariant,
   not an additional assumption on a program's entry. *)
Theorem ld_sync_source_entry:
  o1_src_inv D C vs0 /\ o1_run_state_ok vs0 /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst fn inst s ==>
  ?lo P f. fixed_region_reserved lo C /\
    ptr_discipline lo C vs0 /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
    f.lf_fn = fn /\ f.lf_supply = u /\ f.lf_Q = [] /\
    ld_sync lo P C vs0 [] [] FEMPTY entry_taint fn inst s s FEMPTY [f] 1 /\
    ld_global lo FEMPTY [f]
Proof
  strip_tac >>
  `?lo. fixed_region_reserved lo C /\ ptr_discipline lo C vs0` by
    (fs[o1_src_inv_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def] >> qexists_tac `P` >> fs[EVERY_MEM]) >>
  pop_assum strip_assume_tac >>
  drule_all ld_sync_entry >> disch_then (qspecl_then [`u`, `lo`] strip_assume_tac) >>
  metis_tac[]
QED

Theorem ld_entry_effect:
  f.lf_fn = fn /\ f.lf_src = ss /\ f.lf_tgt = ts /\
  f.lf_tv = tn.t_var /\
  ld_vars P A f /\ ld_memory lo A tn ss ts /\ ld_nonghost tn ss ts /\
  ss.vs_prev_bb = ts.vs_prev_bb /\ ss.vs_current_bb = ts.vs_current_bb /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  (!a. a IN FRANGE f.lf_H ==> a IN FDOM A) /\
  enters_block (ld_image f) ts t1 ==>
  ?s1 H'. enters_block fn ss s1 /\
    ld_vars P A (f with <|lf_src := s1; lf_tgt := t1; lf_H := H';
      lf_tv := (entry_taint_vars fn ss tn).t_var|>) /\
    ld_memory lo A (entry_taint_vars fn ss tn) s1 t1 /\
    ld_nonghost (entry_taint_vars fn ss tn) s1 t1 /\
    entry_prov fn ss (ld_erase A o_f f.lf_H) = ld_erase A o_f H' /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    s1 = ss with <|vs_vars := s1.vs_vars; vs_inst_idx := s1.vs_inst_idx|> /\
    t1 = ts with <|vs_vars := t1.vs_vars; vs_inst_idx := t1.vs_inst_idx|>
Proof
  strip_tac >>
  `enters_block fn ts t1` by
    (irule lower_dload_function_supply_enters_block_origin >>
     qexistsl_tac [`ld_image f`, `f.lf_supply`,
       `SND (lower_dload_function_supply f.lf_supply fn)`] >>
     gvs[ld_image_def]) >>
  qpat_x_assum `enters_block fn ts t1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  `EVERY (\i. MEM i (fn_insts f.lf_fn)) bb.bb_instructions` by
    (drule lookup_block_MEM >> strip_tac >>
     gvs[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >>
     rpt strip_tac >> qexists_tac `bb` >> simp[]) >>
  gvs[] >>
  `f.lf_src.vs_labels = f.lf_tgt.vs_labels` by fs[ld_nonghost_def] >>
  `tn.t_var = f.lf_tv` by simp[] >>
  drule_all ld_phis_effect >> strip_tac >>
  `ss = f.lf_src with vs_vars := ss.vs_vars` by
    metis_tac[ld_phis_only_vars] >>
  `s_phi = f.lf_tgt with vs_vars := s_phi.vs_vars` by
    metis_tac[ld_phis_only_vars] >>
  qexistsl_tac [`ss with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
    `phis_prov f.lf_src.vs_prev_bb f.lf_H bb.bb_instructions`] >>
  simp[entry_taint_vars_def, entry_prov_def] >>
  conj_tac
  >- (qpat_x_assum `ld_vars P A (f with <|lf_src := ss; lf_tgt := s_phi;
        lf_H := _; lf_tv := _|>)` mp_tac >>
      simp[ld_vars_def]) >>
  conj_tac >- (fs[ld_memory_def] >> metis_tac[]) >>
  conj_tac >- (fs[ld_nonghost_def] >> metis_tac[]) >>
  conj_tac
  >- metis_tac[ld_phis_prov_range, SUBSET_DEF] >>
  conj_tac
  >- (qpat_x_assum `ss = _ with vs_vars := _`
        (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `s_phi = _ with vs_vars := _`
    (fn th => once_rewrite_tac[th]) >> simp[]
QED

(* Leading PHIs are singleton expansions and consume no fresh supply. *)
Theorem ld_phi_prefix_supply[local]:
  !u. lower_dload_insts_supply u (TAKE (phi_prefix_length ins) ins) =
        (TAKE (phi_prefix_length ins) ins,u) /\
      phi_prefix_length ins <= LENGTH ins
Proof
  Induct_on `ins` >- simp[phi_prefix_length_def, lower_dload_insts_supply_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def, lower_dload_insts_supply_def,
       lower_dload_inst_supply_def]
QED

Theorem ld_entry_active_envelope:
  lower_dload_function_supply u fn = (fn',v) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ss.vs_current_bb = ts.vs_current_bb /\
  enters_block fn ss s1 /\ enters_block fn' ts t1 /\
  active_inst fn' ti t1 ==>
  ?inst X. active_inst fn inst s1 /\
    ld_envelope u fn s1 s1.vs_inst_idx X t1.vs_inst_idx /\
    X <> [] /\ ti = HD X
Proof
  strip_tac >>
  `enters_block fn ts t1` by
    (irule lower_dload_function_supply_enters_block_origin >> metis_tac[]) >>
  `LENGTH fn'.fn_blocks = LENGTH fn.fn_blocks` by
    (drule lower_dload_function_supply_labels >>
     simp[fn_labels_def] >> metis_tac[LENGTH_MAP]) >>
  qpat_x_assum `active_inst _ _ _` mp_tac >>
  simp[active_inst_def, MEM_EL] >> strip_tac >>
  rename1 `bb = EL bi fn'.fn_blocks` >>
  `bi < LENGTH fn.fn_blocks` by metis_tac[] >>
  drule_all lower_dload_function_supply_block_at >> strip_tac >> gvs[] >>
  qpat_x_assum `enters_block fn' _ _` kall_tac >>
  gvs[enters_block_def] >>
  `s_phi = ss with vs_vars := s_phi.vs_vars` by metis_tac[ld_phis_only_vars] >>
  `s_phi' = ts with vs_vars := s_phi'.vs_vars` by metis_tac[ld_phis_only_vars] >>
  `s_phi.vs_current_bb = ts.vs_current_bb /\
   s_phi'.vs_current_bb = ts.vs_current_bb` by
    (qpat_x_assum `s_phi = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     qpat_x_assum `s_phi' = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  drule lookup_block_MEM >> strip_tac >>
  drule lookup_block_label >> strip_tac >>
  `MEM (EL (LENGTH pre) fn.fn_blocks) fn.fn_blocks` by
    (simp[MEM_EL] >> qexists_tac `LENGTH pre` >> simp[]) >>
  `bb = EL (LENGTH pre) fn.fn_blocks` by
    (irule ld_block_label_unique >> metis_tac[]) >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `phi_prefix_length ins` >>
  qabbrev_tac `j = phi_prefix_length ins` >>
  `lower_dload_insts_supply u0 (TAKE j ins) = (TAKE j ins,u0) /\
   j <= LENGTH ins` by metis_tac[ld_phi_prefix_supply] >>
  `j < LENGTH ins` by
    (spose_not_then assume_tac >>
     `j = LENGTH ins` by decide_tac >> gvs[TAKE_LENGTH_TOO_LONG]) >>
  drule_all lower_dload_insts_supply_at >> strip_tac >>
  gvs[] >>
  `X <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  qexistsl_tac [`EL j ins`,`X`] >>
  conj_tac
  >- (qexists_tac `EL (LENGTH pre) fn.fn_blocks` >>
      simp[Abbr `ins`] >> qexists_tac `LENGTH pre` >> simp[]) >>
  conj_tac
  >- (simp[ld_envelope_def] >>
      qexists_tac `LENGTH pre` >>
      fs[Abbr `ins`]) >>
  simp[] >>
  Cases_on `X` >> gvs[rich_listTheory.EL_APPEND, LENGTH_TAKE]
QED
