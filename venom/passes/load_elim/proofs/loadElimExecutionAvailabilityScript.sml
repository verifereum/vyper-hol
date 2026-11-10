Theory loadElimExecutionAvailability
Ancestors
  simplifyCfgAvailability simplifyCfgFragments contextCodegenRel
  o1PassLift venomExecProofs venomWf venomState

(* Only the entry label is needed for the path argument.  In particular the
   frozen load-elimination theorem does not require an empty variable map. *)
Theorem le_path_defined_entry:
  fn_entry_label fn = SOME s0.vs_current_bb /\
  lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s0 bb.bb_instructions = OK t ==>
  scfg_path_defined fn [bb.bb_label] bb
    (phi_prefix_length bb.bb_instructions)
    (t with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >>
  drule lookup_block_label >> strip_tac >>
  simp[scfg_path_defined_def, is_fn_path_def] >>
  rpt strip_tac >>
  drule_all eval_phis_outputs_in_fdom_idx >>
  simp[lookup_var_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem le_frame_path_start:
  fn_entry_label fn = SOME s0.vs_current_bb /\ enters_block fn s0 s ==>
  ?bb path. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    scfg_path_defined fn path bb s.vs_inst_idx s
Proof
  rw[enters_block_def] >>
  `s_phi.vs_current_bb = s0.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  qexistsl_tac [`bb`, `[bb.bb_label]`] >> simp[] >>
  irule le_path_defined_entry >> metis_tac[]
QED

Theorem le_frame_path_defined:
  !C fn s0 i s. frame_reach C fn s0 i s ==>
    wf_function fn /\ fn_inst_wf fn /\
    fn_entry_label fn = SOME s0.vs_current_bb ==>
    ?bb path. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      scfg_path_defined fn path bb s.vs_inst_idx s
Proof
  ho_match_mp_tac frame_reach_strongind >> rpt conj_tac
  >- (rpt strip_tac >> metis_tac[le_frame_path_start])
  >- (rpt strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      drule frame_reach_active >> strip_tac >>
      drule_all scfg_frame_path_next >> simp[] >> metis_tac[frame_reach_active]) >>
  rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule frame_reach_active >> strip_tac >>
  drule_all scfg_frame_path_block >> metis_tac[frame_reach_active]
QED
