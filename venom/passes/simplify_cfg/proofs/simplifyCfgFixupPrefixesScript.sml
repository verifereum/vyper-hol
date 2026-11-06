(* Observations inside the converted ASSIGN interval, including failing runs. *)
Theory simplifyCfgFixupPrefixes
Ancestors
  simplifyCfgFragments simplifyCfgSimTools simplifyCfgPhiBlockSemantics
  simplifyCfgFixupStatic simplifyCfgFixupSemantics venomExecSemantics
  o1PassLift list rich_list venomInst venomState venomWf simplifyCfgDefs
  simplifyCfgPhiConsumer simplifyCfgAvailability analysisSimProofsBase
  venomExecProofs unitMemInv contextCodegenRel codegenRel

Theorem scfg_assign_interval_opcode:
  bb.bb_instructions = pre ++ assigns ++ tail /\
  EVERY (\i. i.inst_opcode = ASSIGN) assigns /\
  LENGTH pre <= n /\ n < LENGTH pre + LENGTH assigns /\
  get_instruction bb n = SOME j ==> j.inst_opcode = ASSIGN
Proof
  strip_tac >> gvs[get_instruction_def] >>
  `~(n < LENGTH pre) /\ n - LENGTH pre < LENGTH assigns` by decide_tac >>
  gvs[EL_APPEND] >> fs[EVERY_EL]
QED

Theorem scfg_assign_step_alloca[local]:
  i.inst_opcode = ASSIGN /\ step_inst n C i a = OK b ==>
  b.vs_alloca_next = a.vs_alloca_next /\ b.vs_allocas = a.vs_allocas /\
  b.vs_initial_fmp = a.vs_initial_fmp
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(), update_var_def]
QED

Theorem scfg_assign_prefix_alloca[local]:
  !C bb a t. scfg_iprefix C bb a t ==>
  !pre assigns tail. bb.bb_instructions = pre ++ assigns ++ tail /\
  EVERY (\i. i.inst_opcode = ASSIGN) assigns /\
  LENGTH pre <= a.vs_inst_idx /\
  t.vs_inst_idx <= LENGTH pre + LENGTH assigns ==>
  t.vs_alloca_next = a.vs_alloca_next /\ t.vs_allocas = a.vs_allocas /\
  t.vs_initial_fmp = a.vs_initial_fmp
Proof
  ho_match_mp_tac scfg_iprefix_strongind >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `SUC a.vs_inst_idx <= t.vs_inst_idx` by
    (drule scfg_iprefix_index >> simp[]) >>
  `a.vs_inst_idx < LENGTH pre + LENGTH assigns` by decide_tac >>
  `i.inst_opcode = ASSIGN` by
    (drule_all scfg_assign_interval_opcode >> simp[]) >>
  drule_all scfg_assign_step_alloca >> strip_tac >>
  first_x_assum (qspecl_then [`pre`, `assigns`, `tail`] mp_tac) >>
  simp[]
QED

Theorem scfg_assign_interval_alloca:
  bb.bb_instructions = pre ++ assigns ++ tail /\
  EVERY (\i. i.inst_opcode = ASSIGN) assigns /\
  a.vs_inst_idx = LENGTH pre /\ scfg_iprefix C bb a t /\
  t.vs_inst_idx <= LENGTH pre + LENGTH assigns ==>
  t.vs_alloca_next = a.vs_alloca_next /\ t.vs_allocas = a.vs_allocas /\
  t.vs_initial_fmp = a.vs_initial_fmp
Proof
  metis_tac[scfg_assign_prefix_alloca, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem scfg_assign_interval_active:
  bb.bb_instructions = pre ++ assigns ++ tail /\
  EVERY (\i. i.inst_opcode = ASSIGN) assigns /\
  a.vs_inst_idx = LENGTH pre /\ scfg_iprefix C bb a t /\
  t.vs_inst_idx < LENGTH pre + LENGTH assigns /\
  get_instruction bb t.vs_inst_idx = SOME j ==> j.inst_opcode = ASSIGN
Proof
  rpt strip_tac >>
  `LENGTH pre <= t.vs_inst_idx` by metis_tac[scfg_iprefix_index] >>
  drule_all scfg_assign_interval_opcode >> simp[]
QED

Theorem scfg_assign_interval_corr:
  bb.bb_instructions = pre ++ assigns ++ tail /\
  EVERY (\i. i.inst_opcode = ASSIGN) assigns /\
  a.vs_inst_idx = LENGTH pre /\ scfg_iprefix C bb a t /\
  t.vs_inst_idx < LENGTH pre + LENGTH assigns /\
  get_instruction bb t.vs_inst_idx = SOME j /\
  u.vs_alloca_next = a.vs_alloca_next /\ u.vs_allocas = a.vs_allocas /\
  u.vs_initial_fmp = a.vs_initial_fmp ==>
  mem_corr i u j t /\ call_corr i u j t
Proof
  rpt strip_tac >>
  `j.inst_opcode = ASSIGN` by metis_tac[scfg_assign_interval_active] >>
  `t.vs_alloca_next = a.vs_alloca_next /\ t.vs_allocas = a.vs_allocas /\
   t.vs_initial_fmp = a.vs_initial_fmp` by
    (`t.vs_inst_idx <= LENGTH pre + LENGTH assigns` by decide_tac >>
     drule_all scfg_assign_interval_alloca >> simp[]) >>
  simp[mem_corr_def, call_corr_def, inst_mem_ranges_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

(* Lookup equality includes indices beyond the end of the common tail. *)
Theorem scfg_fix_phis_tail_lookup:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\ LENGTH ps <= n ==>
  get_instruction bb n = get_instruction (fix_phis_in_block actual_preds bb) n
Proof
  strip_tac >>
  `LENGTH (fix_phis_in_block actual_preds bb).bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[scfg_fix_phis_length] >>
  `LENGTH bb.bb_instructions = LENGTH ps + LENGTH tail` by simp[] >>
  Cases_on `n < LENGTH bb.bb_instructions`
  >- (`n - LENGTH ps < LENGTH tail` by decide_tac >>
      `LENGTH ps + (n - LENGTH ps) = n` by decide_tac >>
      drule_all scfg_fix_phis_tail_el >>
      disch_then (qspec_then `actual_preds` assume_tac) >>
      simp[get_instruction_def, EL_APPEND] >> metis_tac[]) >>
  simp[get_instruction_def]
QED

Theorem scfg_fix_phis_tail_prefix:
  EVERY (\i. i.inst_opcode <> PHI)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  phi_prefix_length bb.bb_instructions <= a.vs_inst_idx /\
  scfg_iprefix C bb a t ==>
  scfg_iprefix C (fix_phis_in_block actual_preds bb) a t
Proof
  strip_tac >> drule scfg_iprefix_same_tail >> disch_then irule >>
  rpt strip_tac >> irule scfg_fix_phis_tail_lookup >>
  qexistsl_tac [`TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions`,
    `DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions`] >>
  simp[TAKE_DROP, LENGTH_TAKE_EQ, venomExecProofsTheory.phi_prefix_length_le] >>
  decide_tac
QED

Theorem scfg_fix_phis_tail_observe:
  EVERY (\i. i.inst_opcode <> PHI)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  phi_prefix_length bb.bb_instructions <= a.vs_inst_idx /\
  scfg_iprefix C bb a t /\ get_instruction bb t.vs_inst_idx = SOME j ==>
  get_instruction (fix_phis_in_block actual_preds bb) t.vs_inst_idx = SOME j
Proof
  strip_tac >> irule scfg_iprefix_same_tail_observe >>
  qexistsl_tac [`C`, `a`, `bb`] >> simp[] >>
  rpt strip_tac >> irule scfg_fix_phis_tail_lookup >>
  qexistsl_tac [`TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions`,
    `DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions`] >>
  simp[TAKE_DROP, LENGTH_TAKE_EQ, venomExecProofsTheory.phi_prefix_length_le] >>
  decide_tac
QED

(* A certified assignment interval ends at an already rooted original state. *)
Theorem scfg_assign_tail_observe:
  fb.bb_instructions = pre ++ assigns ++ tail /\
  EVERY (\i. i.inst_opcode = ASSIGN) assigns /\
  a.vs_inst_idx = LENGTH pre /\
  u.vs_inst_idx = LENGTH pre + LENGTH assigns /\
  scfg_iprefix C fb a u /\ scfg_iprefix C fb a t /\
  get_instruction fb t.vs_inst_idx = SOME j /\
  get_instruction bb u.vs_inst_idx = SOME i /\ frame_reach C fn s0 i u /\
  MEM bb fn.fn_blocks /\ bb.bb_label = u.vs_current_bb /\
  (!n. u.vs_inst_idx <= n ==> get_instruction bb n = get_instruction fb n) /\
  u.vs_alloca_next = a.vs_alloca_next /\ u.vs_allocas = a.vs_allocas /\
  u.vs_initial_fmp = a.vs_initial_fmp /\ fn_inst_wf fn ==>
  ?i' u'. frame_reach C fn s0 i' u' /\ mem_corr i' u' j t /\ call_corr i' u' j t
Proof
  strip_tac >> Cases_on `t.vs_inst_idx < u.vs_inst_idx`
  >- (qexistsl_tac [`i`, `u`] >> simp[] >>
      `t.vs_inst_idx < LENGTH pre + LENGTH assigns` by decide_tac >>
      drule_all scfg_assign_interval_corr >> simp[]) >>
  `scfg_iprefix C fb u t` by
    (irule scfg_iprefix_cut >> simp[] >> qexists_tac `a` >> simp[]) >>
  `scfg_iprefix C bb u t` by
    (drule scfg_iprefix_same_tail >> disch_then irule >> simp[]) >>
  `get_instruction bb t.vs_inst_idx = SOME j` by
    metis_tac[scfg_iprefix_same_tail_observe] >>
  `frame_reach C fn s0 j t` by
    (drule scfg_iprefix_frame_reach >> disch_then irule >> simp[] >>
     rpt strip_tac >> gvs[]) >>
  qexistsl_tac [`j`, `t`] >> simp[mem_corr_refl] >>
  irule call_corr_refl >> metis_tac[active_inst_wf, frame_reach_active]
QED

Theorem scfg_phi_alloca[local]:
  eval_phis s xs = OK u /\ eval_phis s ys = OK v ==>
  u.vs_alloca_next = v.vs_alloca_next /\ u.vs_allocas = v.vs_allocas /\
  u.vs_initial_fmp = v.vs_initial_fmp
Proof
  strip_tac >> imp_res_tac venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
  rpt conj_tac >>
  qpat_x_assum `u = _` (fn th => rewrite_tac[Once th]) >>
  qpat_x_assum `v = _` (fn th => rewrite_tac[Once th]) >> simp[]
QED

Theorem scfg_fix_phis_snapshot_observe[local]:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) ps /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\ tail <> [] /\
  rs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps /\
  EVERY (\i. i.inst_opcode = ASSIGN) (MAP (fix_phi_inst actual_preds) cs) /\
  eval_phis s ps = OK u /\
  eval_phis s (MAP (fix_phi_inst actual_preds) rs) = OK v /\
  scfg_iprefix C (fix_phis_in_block actual_preds bb)
    (v with vs_inst_idx := LENGTH rs) (u with vs_inst_idx := LENGTH rs + LENGTH cs) /\
  fb = fix_phis_in_block actual_preds bb /\ eval_phis s fb.bb_instructions = OK w /\
  a = w with vs_inst_idx := phi_prefix_length fb.bb_instructions /\
  scfg_iprefix C fb a t /\ get_instruction fb t.vs_inst_idx = SOME j /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  fn_inst_wf fn ==>
  ?i z. frame_reach C fn s0 i z /\ mem_corr i z j t /\ call_corr i z j t
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst actual_preds) rs) /\
   EVERY (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst actual_preds) cs ++ tail) /\
   LENGTH rs + LENGTH cs = LENGTH ps` by
    (irule scfg_fix_phis_prefix_shape >> metis_tac[]) >>
  `fb.bb_instructions = MAP (fix_phi_inst actual_preds) rs ++
      (MAP (fix_phi_inst actual_preds) cs ++ tail)` by
    metis_tac[scfg_fix_phis_partition_instructions, APPEND_ASSOC] >>
  `w = v /\ phi_prefix_length fb.bb_instructions = LENGTH rs` by
    (qpat_x_assum `eval_phis s fb.bb_instructions = OK w` mp_tac >>
     qpat_x_assum `rs = _` kall_tac >> qpat_x_assum `cs = _` kall_tac >>
     simp[Excl "APPEND_ASSOC", scfg_eval_phis_append, scfg_phi_prefix_append]) >>
  `phi_prefix_length bb.bb_instructions = LENGTH ps` by
    simp[scfg_phi_prefix_append] >>
  `get_instruction bb (LENGTH ps) = SOME (HD tail)` by
    (Cases_on `tail` >> gvs[get_instruction_def, EL_APPEND]) >>
  `frame_reach C fn s0 (HD tail) (u with vs_inst_idx := LENGTH ps)` by
    (irule scfg_rooted_prefix_frame_reach >>
     qexistsl_tac [`u with vs_inst_idx := LENGTH ps`, `bb`, `s`, `u`] >>
     simp[scfg_iprefix_rules, TAKE_APPEND]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[simplifyCfgDefsTheory.lookup_block_member_label] >>
  `u.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  qpat_x_assum `rs = _` kall_tac >> qpat_x_assum `cs = _` kall_tac >>
  irule scfg_assign_tail_observe >> simp[] >>
  qexistsl_tac [`a`, `MAP (fix_phi_inst actual_preds) cs`, `bb`, `fb`,
    `HD tail`, `MAP (fix_phi_inst actual_preds) rs`, `tail`,
    `u with vs_inst_idx := LENGTH ps`] >>
  `((u with vs_inst_idx := LENGTH ps).vs_alloca_next = a.vs_alloca_next) /\
   ((u with vs_inst_idx := LENGTH ps).vs_allocas = a.vs_allocas) /\
   ((u with vs_inst_idx := LENGTH ps).vs_initial_fmp = a.vs_initial_fmp)` by
    (simp[] >> irule scfg_phi_alloca >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> match_mp_tac scfg_fix_phis_tail_lookup >> metis_tac[]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem scfg_phi_tail_nonempty:
  bb_well_formed bb /\ bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) ps ==> tail <> []
Proof
  strip_tac >> strip_tac >> gvs[bb_well_formed_def] >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions` by metis_tac[LAST_MEM] >>
  `(LAST bb.bb_instructions).inst_opcode = PHI` by fs[EVERY_MEM] >>
  gvs[is_terminator_def]
QED

Theorem scfg_converted_assigns:
  EVERY (\i. i.inst_opcode = PHI) ps /\
  EVERY (\i. (fix_phi_inst actual_preds i).inst_opcode <> NOP) ps /\
  cs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps ==>
  EVERY (\i. i.inst_opcode = ASSIGN) (MAP (fix_phi_inst actual_preds) cs)
Proof
  simp[EVERY_MAP, EVERY_FILTER, EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
  rename1 `MEM i ps` >>
  `i.inst_opcode = PHI /\ (fix_phi_inst actual_preds i).inst_opcode <> NOP` by
    metis_tac[] >>
  qpat_x_assum `!i. MEM i ps ==> i.inst_opcode = PHI` kall_tac >>
  qpat_x_assum `!i. MEM i ps ==> (fix_phi_inst actual_preds i).inst_opcode <> NOP` kall_tac >>
  Cases_on `filter_phi_ops actual_preds i.inst_operands` >> gvs[fix_phi_inst_def] >>
  rename1 `filter_phi_ops actual_preds i.inst_operands = x::xs` >>
  Cases_on `xs` >> gvs[fix_phi_inst_def] >>
  rename1 `filter_phi_ops actual_preds i.inst_operands = x::y::ys` >>
  Cases_on `ys` >> gvs[fix_phi_inst_def]
QED

Theorem scfg_no_phi_observe[local]:
  EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions /\
  eval_phis s bb.bb_instructions = OK v /\
  a = v with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
  scfg_iprefix C bb a t /\ get_instruction bb t.vs_inst_idx = SOME j /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  fn_inst_wf fn ==>
  ?i z. frame_reach C fn s0 i z /\ mem_corr i z j t /\ call_corr i z j t
Proof
  strip_tac >>
  `frame_reach C fn s0 j t` by
    (irule scfg_rooted_prefix_frame_reach >>
     qexistsl_tac [`a`, `bb`, `s`, `v`] >> simp[] >>
     metis_tac[scfg_eval_phis_take_prefix]) >>
  qexistsl_tac [`j`, `t`] >> simp[mem_corr_refl] >>
  irule call_corr_refl >> metis_tac[active_inst_wf, frame_reach_active]
QED

Theorem scfg_rooted_fix_phis_observe:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  fb = fix_phis_in_block (pred_labels fn bb.bb_label) bb /\
  eval_phis s fb.bb_instructions = OK v /\
  a = v with vs_inst_idx := phi_prefix_length fb.bb_instructions /\
  scfg_iprefix C fb a t /\ get_instruction fb t.vs_inst_idx = SOME j ==>
  ?i z. frame_reach C fn s0 i z /\ mem_corr i z j t /\ call_corr i z j t
Proof
  strip_tac >> drule_all scfg_bprefix_incoming >> strip_tac
  >- (gvs[] >> drule_all scfg_entry_block_no_phi >> strip_tac >>
      `fix_phis_in_block (pred_labels fn bb.bb_label) bb = bb` by
        metis_tac[scfg_fix_phis_no_phi] >>
      irule scfg_no_phi_observe >> metis_tac[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  qabbrev_tac `ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  qabbrev_tac `tail = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  `bb.bb_instructions = ps ++ tail` by simp[Abbr `ps`, Abbr `tail`] >>
  `EVERY (\i. i.inst_opcode = PHI) ps` by
    metis_tac[phi_prefix_all_phi] >>
  `EVERY (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> NOP) ps /\
   EVERY (\i. i.inst_opcode <> PHI) tail` by
    (irule scfg_fn_fix_phis_parts >> simp[Abbr `ps`, Abbr `tail`] >> metis_tac[]) >>
  `tail <> []` by
    (irule scfg_phi_tail_nonempty >> fs[wf_function_def] >> metis_tac[]) >>
  qabbrev_tac `rs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = PHI) ps` >>
  qabbrev_tac `cs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> PHI) ps` >>
  `EVERY (\i. i.inst_opcode = ASSIGN) (MAP (fix_phi_inst (pred_labels fn bb.bb_label)) cs)` by
    (irule scfg_converted_assigns >> simp[Abbr `cs`] >> metis_tac[]) >>
  `ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
   rs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = PHI) ps /\
   cs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> PHI) ps` by
    simp[Abbr `ps`, Abbr `rs`, Abbr `cs`] >>
  `fn_reachable fn bb.bb_label /\
   (!qb. MEM qb fn.fn_blocks /\ MEM bb.bb_label (bb_succs qb) ==> fn_reachable fn qb.bb_label)` by
    metis_tac[] >>
  drule_all scfg_fn_fix_phis_block >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  irule scfg_fix_phis_snapshot_observe >> (conj_tac >- asm_rewrite_tac[]) >>
  qexistsl_tac [`a`, `pred_labels fn bb.bb_label`, `bb`, `cs`, `fb`, `ps`, `rs`, `s`, `tail`] >>
  metis_tac[]
QED
