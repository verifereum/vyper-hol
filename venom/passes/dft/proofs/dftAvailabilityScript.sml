(* SSA availability for a data-ready instruction, independently of its
   position in a reordered prefix. *)
Theory dftAvailability
Ancestors
  dftScheduleOrder dftCorrectness venomWf
  venomExecSemantics venomExecProofs venomState list finite_map
  dftWf dftIdempotent dftTopoSort venomInst dftIndexedExec sorting dftDefs
  venomWfProps

Theorem dft_ready_operand_defined:
  wf_ssa fn /\ wf_function fn /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI /\
  strict_dom_vars_defined fn s /\
  (!d v. MEM d bb.bb_instructions /\ MEM v d.inst_outputs /\
         MEM (Var v) inst.inst_operands /\
         id_before (MAP (\i. i.inst_id) bb.bb_instructions)
           d.inst_id inst.inst_id ==> v IN FDOM s.vs_vars) ==>
  !v. MEM (Var v) inst.inst_operands ==> v IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  `def_available_at fn bb (SOME inst) v` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  fs[def_available_at_def] >>
  Cases_on `def_bb.bb_label = bb.bb_label`
  >- (`def_bb = bb` by metis_tac[same_label_same_block] >>
      gvs[] >>
      qpat_x_assum `!d v. _` irule >>
      simp[] >> qexists_tac `EL i bb.bb_instructions` >> simp[] >>
      simp[id_before_def] >> qexistsl_tac [`i`, `j`] >>
      simp[EL_MAP]) >>
  fs[strict_dom_vars_defined_def] >> metis_tac[]
QED

Theorem dft_exec_block_initialized_outputs:
  exec_block fuel ctx bb s = OK t /\
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  (!i v. i < s.vs_inst_idx /\ i < LENGTH bb.bb_instructions /\
         MEM v (EL i bb.bb_instructions).inst_outputs ==> v IN FDOM s.vs_vars)
  ==> !i v. i < LENGTH bb.bb_instructions /\
            ~is_terminator (EL i bb.bb_instructions).inst_opcode /\
            MEM v (EL i bb.bb_instructions).inst_outputs ==>
            v IN FDOM t.vs_vars
Proof
  rpt strip_tac >> Cases_on `i < s.vs_inst_idx`
  >- (`v IN FDOM s.vs_vars` by metis_tac[] >>
      drule_all exec_block_fdom_mono >>
      simp[pred_setTheory.SUBSET_DEF]) >>
  irule exec_block_output_in_fdom_aux >>
  qexistsl_tac [`bb`, `ctx`, `fuel`, `i`,
    `LENGTH bb.bb_instructions - s.vs_inst_idx`, `s`] >> simp[]
QED

Theorem dft_dominance_transfer:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ fn_reachable fn s.vs_current_bb /\
  fn_cfg_edge fn s.vs_current_bb t.vs_current_bb /\
  strict_dom_vars_defined fn s /\
  FDOM s.vs_vars SUBSET FDOM t.vs_vars /\
  (!inst v. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==>
            v IN FDOM t.vs_vars) ==>
  strict_dom_vars_defined fn t
Proof
  rw[strict_dom_vars_defined_def] >>
  Cases_on `d_bb.bb_label = s.vs_current_bb`
  >- (`d_bb = bb` by metis_tac[same_label_same_block] >>
      gvs[] >> metis_tac[]) >>
  `fn_dominates fn d_bb.bb_label s.vs_current_bb` by
    metis_tac[fn_dominates_predecessor] >>
  fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem dft_successor_available:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ fn_reachable fn s.vs_current_bb /\
  strict_dom_vars_defined fn s /\ EVERY inst_wf bb.bb_instructions /\
  run_block fuel ctx bb s = OK t /\ ~t.vs_halted ==>
  fn_reachable fn t.vs_current_bb /\ strict_dom_vars_defined fn t
Proof
  strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (irule venomExecPropsTheory.run_block_current_bb_in_succs >>
     simp[] >> reverse conj_tac
     >- (fs[bb_well_formed_def] >> metis_tac[]) >>
     fs[bb_well_formed_def] >> rpt strip_tac >>
     spose_not_then assume_tac >>
     qpat_x_assum `!i. _ /\ is_terminator _ ==> _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `fn_cfg_edge fn s.vs_current_bb t.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[fn_reachable_step] >>
  irule dft_dominance_transfer >> simp[] >>
  qexistsl_tac [`bb`, `s`] >> simp[] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  simp[run_block_def] >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[] >> strip_tac >>
  drule_all eval_phis_vars_grow >> strip_tac >>
  drule_all exec_block_fdom_mono >> simp[] >> strip_tac >>
  reverse conj_tac >- metis_tac[pred_setTheory.SUBSET_TRANS] >>
  rpt strip_tac >>
  `?i. i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = inst`
    by metis_tac[MEM_EL] >>
  `~is_terminator inst.inst_opcode` by
    metis_tac[terminator_no_outputs, EVERY_MEM, MEM] >>
  `!j w. j < phi_prefix_length bb.bb_instructions /\
         j < LENGTH bb.bb_instructions /\
         MEM w (EL j bb.bb_instructions).inst_outputs ==>
         w IN FDOM s'.vs_vars` by
    (rpt strip_tac >> irule eval_phis_outputs_in_fdom_mem >>
     qexistsl_tac [`EL j bb.bb_instructions`, `bb.bb_instructions`, `s`] >>
     simp[] >> simp[MEM_EL] >> qexists_tac `j` >>
     simp[EL_TAKE, phi_prefix_length_le]) >>
  drule dft_exec_block_initialized_outputs >> simp[] >>
  disch_then (qspecl_then [`i`, `v`] mp_tac) >> simp[] >>
  impl_tac >- (rpt strip_tac >> first_x_assum irule >>
    qexists_tac `i'` >> simp[]) >> simp[]

QED

Theorem dft_local_producer_before:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  MEM d bb.bb_instructions /\ MEM u bb.bb_instructions /\
  ~is_pseudo u.inst_opcode /\ MEM v d.inst_outputs /\
  MEM (Var v) u.inst_operands ==>
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) d.inst_id u.inst_id
Proof
  strip_tac >>
  `np_defs_before_uses bb.bb_instructions` by metis_tac[wf_ssa_defs_before_uses] >>
  `producing_inst bb.bb_instructions v = SOME d` by
    (irule producing_inst_unique_definer >> simp[] >>
     rpt strip_tac >>
     `DISJOINT (set (inst_defs d)) (set (inst_defs j))` by
       metis_tac[ssa_disjoint_defs, wf_ssa_def] >>
     gvs[inst_defs_def, pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
     metis_tac[]) >>
  `?k. k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = u` by
    metis_tac[MEM_EL] >>
  `?j. j < k /\ EL j bb.bb_instructions = d` by
    (gvs[np_defs_before_uses_def] >> metis_tac[]) >>
  simp[id_before_def] >> qexistsl_tac [`j`, `k`] >> simp[EL_MAP]
QED

Theorem dft_prefix_fdom:
  !pre s t.
  EVERY (\i. inst_wf i /\ ~is_pseudo i.inst_opcode /\
             ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons fuel C) OK pre s = OK t ==>
  FDOM t.vs_vars = FDOM s.vs_vars UNION
    set (FLAT (MAP (\i. i.inst_outputs) pre))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[dft_exec_cons_def, AllCaseEqs()] >>
  `h.inst_opcode <> PHI` by (strip_tac >> gvs[is_pseudo_def]) >>
  drule_all step_inst_fdom >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  gvs[] >> pred_setLib.SET_TAC[]
QED

Theorem dft_prefix_frame:
  !pre s t.
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons fuel C) OK pre s = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_labels = s.vs_labels
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[dft_exec_cons_def, AllCaseEqs()] >>
  drule_all venomInstPropsTheory.step_preserves_control_flow >> strip_tac >>
  drule step_inst_preserves_labels_always >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem dft_prefix_dominators:
  EVERY (\i. inst_wf i /\ ~is_pseudo i.inst_opcode /\
             ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons fuel C) OK pre s = OK t /\
  strict_dom_vars_defined fn s ==>
  strict_dom_vars_defined fn t
Proof
  strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (cj 1 dft_prefix_frame) >>
     qexistsl_tac [`C`, `fuel`, `pre`] >> simp[EVERY_MEM] >>
     fs[EVERY_MEM]) >>
  drule_all dft_prefix_fdom >> strip_tac >>
  fs[strict_dom_vars_defined_def] >> rpt strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem dft_executed_producers:
  PERM (done ++ todo) (FILTER (\i. ~is_pseudo i.inst_opcode) original) /\
  (!d v. MEM d original /\ is_pseudo d.inst_opcode /\
         MEM v d.inst_outputs ==> v IN FDOM s.vs_vars) /\
  EVERY (\i. inst_wf i /\ ~is_pseudo i.inst_opcode /\
             ~is_terminator i.inst_opcode) done /\
  FOLDR (dft_exec_cons fuel C) OK done s = OK t ==>
  !d v. MEM d original /\ MEM v d.inst_outputs /\ ~MEM d todo ==>
        v IN FDOM t.vs_vars
Proof
  strip_tac >> drule_all dft_prefix_fdom >> strip_tac >> rpt strip_tac >>
  Cases_on `is_pseudo d.inst_opcode`
  >- (simp[] >> metis_tac[]) >>
  `MEM d (done ++ todo)` by
    (dxrule PERM_MEM_EQ >> disch_then (qspec_then `d` mp_tac) >> simp[MEM_FILTER]) >>
  `MEM d done` by gvs[] >>
  simp[MEM_FLAT, MEM_MAP] >> disj2_tac >>
  qexists_tac `d.inst_outputs` >> simp[] >>
  qexists_tac `d` >> simp[]
QED

Theorem dft_prefix_ready_preserved:
  EVERY (\i. inst_wf i /\ ~is_pseudo i.inst_opcode /\
             ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons fuel C) OK pre s = OK t /\
  (!v. MEM (Var v) y.inst_operands ==> v IN FDOM s.vs_vars) /\
  (y.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels) ==>
  (!v. MEM (Var v) y.inst_operands ==> v IN FDOM t.vs_vars) /\
  (y.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) y.inst_operands ==> l IN FDOM t.vs_labels)
Proof
  strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (irule (cj 2 dft_prefix_frame) >>
     qexistsl_tac [`C`, `fuel`, `pre`] >> simp[EVERY_MEM] >> fs[EVERY_MEM]) >>
  drule_all dft_prefix_fdom >> strip_tac >> simp[] >>
  rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem dft_initialized_prefix_fdom:
  !pre s t.
  EVERY (\i. inst_wf i /\ ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons fuel C) OK pre s = OK t ==>
  FDOM t.vs_vars = FDOM s.vs_vars UNION
    set (FLAT (MAP (\i. i.inst_outputs) pre))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[dft_exec_cons_def, AllCaseEqs()] >>
  `h.inst_opcode <> PHI` by metis_tac[step_inst_ok_imp_not_phi] >>
  drule_all step_inst_fdom >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  gvs[] >> pred_setLib.SET_TAC[]
QED

Theorem dft_pseudo_initialization:
  !pre s u t fuel C.
  EVERY (\i. inst_wf i /\ ~is_terminator i.inst_opcode) pre /\
  eval_phis s pre = OK u /\
  FOLDR (dft_exec_cons fuel C) OK (DROP (phi_prefix_length pre) pre)
    (u with vs_inst_idx := phi_prefix_length pre) = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_labels = s.vs_labels /\
  FDOM s.vs_vars SUBSET FDOM t.vs_vars /\
  (!d v. MEM d pre /\ MEM v d.inst_outputs ==> v IN FDOM t.vs_vars)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\i. inst_wf i /\ ~is_terminator i.inst_opcode)
    (DROP (phi_prefix_length pre) pre)` by metis_tac[TAKE_DROP, EVERY_APPEND] >>
  drule_all dft_initialized_prefix_fdom >> simp[] >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (DROP (phi_prefix_length pre) pre)` by fs[EVERY_MEM] >>
  drule_all dft_prefix_frame >> simp[] >> strip_tac >>
  drule eval_phis_vars_grow >> strip_tac >>
  drule eval_phis_only_updates_vs_vars >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[] >> conj_tac
  >- (fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM d (TAKE (phi_prefix_length pre) pre) \/
   MEM d (DROP (phi_prefix_length pre) pre)` by
    metis_tac[TAKE_DROP, MEM_APPEND] 
  >- (`v IN FDOM u.vs_vars` by metis_tac[eval_phis_outputs_in_fdom_mem] >> simp[]) >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED
