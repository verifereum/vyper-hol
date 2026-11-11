Theory loadElimOccurrenceCoverage
Ancestors
  loadElimOccurrence loadElimOperationalHistory simplifyCfgAvailability
  simplifyCfgSimTools o1PassLift contextCodegenRel venomExecProps venomInstProps venomExecProofs
  venomExecSemantics venomInst venomWf list

Definition le_occ_route_def:
  le_occ_route [] = [] /\
  le_occ_route (StepOcc bb n k s t :: es) = le_occ_route es /\
  le_occ_route (PhiOcc bb s t :: es) = bb.bb_label :: le_occ_route es
End

Theorem le_occ_route_append:
  !es fs. le_occ_route (es ++ fs) = le_occ_route es ++ le_occ_route fs
Proof
  Induct >> simp[le_occ_route_def] >> Cases_on `h` >> simp[le_occ_route_def]
QED

(* A successful active terminator chooses a syntactic CFG successor. *)
Theorem le_active_terminator_edge:
  wf_function fn /\ fn_inst_wf fn /\ active_inst fn i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  is_terminator i.inst_opcode /\ step_inst fuel C i s = OK t /\
  ~t.vs_halted ==>
  fn_cfg_edge fn bb.bb_label t.vs_current_bb
Proof
  rpt strip_tac >>
  `inst_wf i` by metis_tac[active_inst_wf] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = i` by
    (gvs[active_inst_def] >> metis_tac[same_label_same_block]) >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `LAST bb.bb_instructions = i` by
    (gvs[bb_well_formed_def, LAST_EL] >> metis_tac[]) >>
  `i.inst_opcode <> INVOKE` by
    (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
  `MEM t.vs_current_bb (get_successors i)` by
    metis_tac[step_inst_base_term_succs, step_inst_non_invoke] >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, MEM_nub, MEM_REVERSE]) >>
  simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem le_occ_prefix_route:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb ==>
  le_occ_route es <> [] /\ is_fn_path fn (le_occ_route es) /\
  HD (le_occ_route es) = s0.vs_current_bb /\
  LAST (le_occ_route es) = s.vs_current_bb
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      drule lookup_block_label >> strip_tac >>
      drule eval_phis_preserves_current_bb >>
      simp[le_occ_route_def, is_fn_path_def])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> first_x_assum drule_all >> strip_tac >>
      `u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_control_flow] >>
      simp[le_occ_route_append, le_occ_route_def]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> first_x_assum drule_all >> strip_tac >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  drule_all le_active_terminator_edge >> strip_tac >>
  `next.bb_label = u.vs_current_bb /\ p.vs_current_bb = u.vs_current_bb` by
    metis_tac[lookup_block_label, eval_phis_preserves_current_bb] >>
  simp[le_occ_route_append, le_occ_route_def] >>
  conj_tac >- metis_tac[is_fn_path_snoc, lookup_block_label] >>
  Cases_on `le_occ_route es` >> gvs[]
QED

Theorem le_phi_prefix_take:
  !xs. le_phi_prefix xs = TAKE (phi_prefix_length xs) xs
Proof
  Induct >> simp[le_phi_prefix_def, phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[le_phi_prefix_def, phi_prefix_length_def]
QED

Theorem le_phi_prefix_outputs:
  k < phi_prefix_length xs /\ k < LENGTH xs /\
  MEM v (EL k xs).inst_outputs ==> v IN le_phi_outputs xs
Proof
  simp[le_phi_outputs_def, le_phi_prefix_take, MEM_FLAT, MEM_MAP] >>
  strip_tac >> qexists_tac `(EL k xs).inst_outputs` >> simp[] >>
  qexists_tac `EL k xs` >> simp[] >>
  simp[MEM_EL] >> qexists_tac `k` >> simp[EL_TAKE, LENGTH_TAKE_EQ, phi_prefix_length_le]
QED

Definition le_occ_wrote_def:
  le_occ_wrote es v <=> ?e. MEM e es /\ v IN le_occ_writes e
End

Theorem le_occ_wrote_append[simp]:
  le_occ_wrote (es ++ fs) v <=> le_occ_wrote es v \/ le_occ_wrote fs v
Proof
  simp[le_occ_wrote_def, MEM_APPEND] >> metis_tac[]
QED

Theorem le_occ_wrote_phi:
  k < phi_prefix_length bb.bb_instructions /\
  k < LENGTH bb.bb_instructions /\ MEM v (EL k bb.bb_instructions).inst_outputs ==>
  le_occ_wrote [PhiOcc bb s t] v
Proof
  simp[le_occ_wrote_def, le_occ_writes_def] >>
  metis_tac[le_phi_prefix_outputs]
QED

Theorem le_occ_prefix_current_coverage:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  !bb k v. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    k < s.vs_inst_idx /\ k < LENGTH bb.bb_instructions /\
    MEM v (EL k bb.bb_instructions).inst_outputs ==>
    le_occ_wrote es v
Proof
  ho_match_mp_tac le_occ_prefix_ind >> rpt conj_tac
  >- (rpt strip_tac >>
      `p.vs_current_bb = s0.vs_current_bb` by
        metis_tac[eval_phis_preserves_current_bb] >>
      gvs[] >> metis_tac[le_occ_wrote_phi])
  >- (rpt strip_tac >>
      `u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_control_flow] >>
      gvs[] >> simp[] >>
      Cases_on `k' < s.vs_inst_idx`
      >- (disj1_tac >> first_x_assum irule >>
          qexists_tac `k'` >> simp[]) >>
      `k' = s.vs_inst_idx` by decide_tac >>
      gvs[le_occ_wrote_def, le_occ_writes_def]) >>
  rpt strip_tac >>
  `p.vs_current_bb = u.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  gvs[] >> simp[le_occ_wrote_def] >> disj2_tac >>
  qexists_tac `PhiOcc bb' u p` >> simp[le_occ_writes_def] >>
  irule le_phi_prefix_outputs >> qexists_tac `k'` >> simp[]
QED

Theorem le_occ_prefix_close_coverage:
  wf_function fn /\ le_occ_prefix C fn s0 es i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL s.vs_inst_idx bb.bb_instructions = i /\ is_terminator i.inst_opcode /\
  MEM d bb.bb_instructions /\ MEM v d.inst_outputs ==>
  le_occ_wrote (es ++ [StepOcc bb s.vs_inst_idx fuel s t]) v
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  qpat_x_assum `MEM d bb.bb_instructions` mp_tac >>
  simp[MEM_EL] >> strip_tac >>
  rename1 `n < LENGTH bb.bb_instructions` >>
  simp[] >> Cases_on `n < s.vs_inst_idx`
  >- (disj1_tac >> drule le_occ_prefix_current_coverage >>
      disch_then (qspecl_then [`bb`, `n`, `v`] mp_tac) >> gvs[]) >>
  `n = s.vs_inst_idx` by decide_tac >>
  gvs[le_occ_wrote_def, le_occ_writes_def]
QED

Theorem le_occ_prefix_completed_coverage:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  wf_function fn /\ fn_inst_wf fn /\ fn_entry_label fn = SOME s0.vs_current_bb ==>
  !k bb d v. k < LENGTH (le_occ_route es) - 1 /\
    lookup_block (EL k (le_occ_route es)) fn.fn_blocks = SOME bb /\
    MEM d bb.bb_instructions /\ MEM v d.inst_outputs ==>
    le_occ_wrote es v
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- simp[le_occ_route_def]
  >- (rpt strip_tac >> simp[] >> disj1_tac >>
      first_x_assum irule >> simp[] >>
      qexistsl_tac [`bb'`, `d`, `k'`] >>
      gvs[le_occ_route_append, le_occ_route_def]) >>
  rpt strip_tac >>
  `le_occ_route es <> [] /\ LAST (le_occ_route es) = s.vs_current_bb` by
    metis_tac[le_occ_prefix_route] >>
  gvs[le_occ_route_append, le_occ_route_def] >>
  Cases_on `k' < LENGTH (le_occ_route es) - 1`
  >- (simp[] >> disj1_tac >> first_x_assum irule >> simp[] >>
      qexistsl_tac [`bb'`, `d`, `k'`] >> simp[] >>
      gvs[EL_APPEND_EQN]) >>
  `k' = LENGTH (le_occ_route es) - 1` by decide_tac >>
  `EL k' (le_occ_route es ++ [next.bb_label]) = s.vs_current_bb` by
    (simp[EL_APPEND_EQN] >>
     `k' = PRE (LENGTH (le_occ_route es))` by decide_tac >>
     metis_tac[LAST_EL]) >>
  gvs[] >>
  `le_occ_wrote (es ++ [StepOcc bb s.vs_inst_idx k s u]) v` by
    (irule le_occ_prefix_close_coverage >> metis_tac[]) >>
  gvs[le_occ_wrote_def, MEM_APPEND] >> metis_tac[]
QED

Theorem le_occ_prefix_use_writer:
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  def_on_all_paths fn bb (SOME i) v ==>
  ?e. MEM e es /\ v IN le_occ_writes e
Proof
  rpt strip_tac >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = i` by
    (gvs[active_inst_def] >> metis_tac[same_label_same_block]) >>
  drule_all le_occ_prefix_route >> strip_tac >>
  qpat_x_assum `def_on_all_paths _ _ _ _` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `le_occ_route es` mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac
  >- (`lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      `le_occ_wrote es v` by metis_tac[le_occ_prefix_completed_coverage] >>
      gvs[le_occ_wrote_def] >> metis_tac[]) >>
  `j = s.vs_inst_idx` by metis_tac[inst_ids_el_eq, wf_function_def] >>
  `le_occ_wrote es v` by
    (drule le_occ_prefix_current_coverage >>
     disch_then (qspecl_then [`bb`, `i'`, `v`] mp_tac) >> gvs[]) >>
  gvs[le_occ_wrote_def] >> metis_tac[]
QED
