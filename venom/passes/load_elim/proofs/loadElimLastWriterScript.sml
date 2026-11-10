Theory loadElimLastWriter
Ancestors
  loadElimOccurrenceCoverage loadElimOccurrence loadElimOperationalHistory
  loadElimReachableSSA simplifyCfgDataflow
  simplifyCfgAvailability o1ContractSimplifyCfg
  simplifyCfgPhiRepair venomWf venomState venomExecProofs finite_map list rich_list

(* A nonempty predicate-selected sublist has a last selected occurrence.
   No distinctness assumption is made: dynamic visits may repeat. *)
Theorem le_last_selected_split:
  !P xs. (?e. MEM e xs /\ P e) ==>
    ?pre e suffix. xs = pre ++ e::suffix /\ P e /\ EVERY (\q. ~P q) suffix
Proof
  gen_tac >> Induct >> simp[] >> gen_tac >> disch_tac >>
  Cases_on `?e. MEM e xs /\ P e`
  >- (first_x_assum drule >> strip_tac >>
      qexistsl_tac [`h::pre`, `e`, `suffix`] >> simp[]) >>
  qexistsl_tac [`[]`, `h`, `xs`] >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem le_occ_prefix_last_writer:
  le_occ_prefix C fn s0 es i s /\
  (?e. MEM e es /\ v IN le_occ_writes e) ==>
  ?pre e suffix.
    es = pre ++ e::suffix /\ v IN le_occ_writes e /\
    EVERY (\q. v NOTIN le_occ_writes q) suffix /\
    le_occ_valid C fn e /\
    lookup_var v s = lookup_var v (le_occ_post e)
Proof
  strip_tac >>
  `?pre e suffix. es = pre ++ e::suffix /\ v IN le_occ_writes e /\
    EVERY (\q. v NOTIN le_occ_writes q) suffix` by
    (qspecl_then [`\e. v IN le_occ_writes e`, `es`] mp_tac
       le_last_selected_split >> simp[] >> metis_tac[]) >>
  rename1 `es = pre ++ last::suffix` >>
  qexistsl_tac [`pre`, `last`, `suffix`] >> simp[] >>
  conj_tac >- (irule le_occ_prefix_member >>
    qexistsl_tac [`es`, `i`, `s`, `s0`] >> simp[]) >>
  metis_tac[le_occ_prefix_suffix_lookup]
QED

Theorem le_occ_valid_writer_defined:
  le_occ_valid C fn e /\ fn_inst_wf fn /\ v IN le_occ_writes e ==>
  IS_SOME (lookup_var v (le_occ_post e))
Proof
  Cases_on `e` >>
  simp[le_occ_valid_def, le_occ_writes_def, le_occ_post_def] >> strip_tac
  >- (irule scfg_step_outputs_defined >>
      `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
      `MEM (EL n b.bb_instructions) b.bb_instructions` by simp[EL_MEM] >>
      gvs[fn_inst_wf_def] >> metis_tac[]) >>
  gvs[le_phi_outputs_def, MEM_FLAT, MEM_MAP] >>
  `v IN FDOM v0.vs_vars` by
    (irule eval_phis_outputs_in_fdom_mem >>
     metis_tac[le_phi_prefix_take]) >>
  simp[lookup_var_def, FLOOKUP_DEF]
QED

Theorem le_occ_prefix_reachable:
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  fn_reachable fn bb.bb_label
Proof
  strip_tac >> drule_all le_occ_prefix_route >> strip_tac >>
  irule entry_path_member_reachable >>
  qexistsl_tac [`s0.vs_current_bb`, `le_occ_route es`] >>
  metis_tac[MEM_LAST_NOT_NIL, lookup_block_label]
QED

Theorem le_occ_ssa_use_writer:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\ i.inst_opcode <> PHI /\
  MEM (Var v) i.inst_operands ==>
  ?e. MEM e es /\ v IN le_occ_writes e
Proof
  strip_tac >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  drule_all le_active_inst_lookup >> strip_tac >>
  `MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions` by
    metis_tac[lookup_block_MEM, EL_MEM] >>
  `fn_reachable fn bb.bb_label` by metis_tac[le_occ_prefix_reachable] >>
  `def_available_at fn bb (SOME i) v` by
    (irule le_reachable_ssa_ordinary_available >> metis_tac[]) >>
  `def_on_all_paths fn bb (SOME i) v` by
    (irule def_available_on_all_paths >> metis_tac[]) >>
  irule le_occ_prefix_use_writer >> metis_tac[]
QED

Theorem le_frame_use_last_writer:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  frame_reach C fn s0 i s /\ i.inst_opcode <> PHI /\
  MEM (Var v) i.inst_operands ==>
  ?es pre e suffix.
    le_occ_prefix C fn s0 es i s /\
    es = pre ++ e::suffix /\ v IN le_occ_writes e /\
    EVERY (\q. v NOTIN le_occ_writes q) suffix /\
    le_occ_valid C fn e /\
    IS_SOME (lookup_var v (le_occ_post e)) /\
    lookup_var v s = lookup_var v (le_occ_post e)
Proof
  strip_tac >> drule_all le_occ_prefix_annotate >> strip_tac >>
  drule_all le_occ_ssa_use_writer >> strip_tac >>
  drule le_occ_prefix_last_writer >>
  disch_then (qspec_then `v` mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  rename1 `es = pre ++ last::suffix` >>
  qexistsl_tac [`es`, `pre`, `last`, `suffix`] >> simp[] >>
  metis_tac[le_occ_valid_writer_defined]
QED

Theorem le_occ_writer_instruction:
  le_occ_valid C fn e /\ v IN le_occ_writes e ==>
  case e of
    StepOcc bb n k pre post =>
      MEM bb fn.fn_blocks /\ MEM (EL n bb.bb_instructions) bb.bb_instructions /\
      MEM v (EL n bb.bb_instructions).inst_outputs
  | PhiOcc bb pre post =>
      MEM bb fn.fn_blocks /\
      ?inst. MEM inst (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
             MEM v inst.inst_outputs
Proof
  Cases_on `e` >>
  simp[le_occ_valid_def, le_occ_writes_def, le_phi_outputs_def,
       le_phi_prefix_take, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> simp[] >>
  metis_tac[lookup_block_MEM, EL_MEM]
QED

(* SSA identifies the static instruction, not a unique dynamic visit.
   PHIs remain a batch: membership does not assert sequential evaluation. *)
Theorem le_occ_writer_static_unique:
  ssa_form fn /\ le_occ_valid C fn e /\ v IN le_occ_writes e /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs ==>
  case e of
    StepOcc bb n k pre post => EL n bb.bb_instructions = di
  | PhiOcc bb pre post =>
      MEM di (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
Proof
  strip_tac >> drule_all le_occ_writer_instruction >>
  Cases_on `e` >> simp[] >> strip_tac
  >- (irule ssa_form_output_unique >> gvs[wf_ssa_def] >> metis_tac[]) >>
  `MEM inst b.bb_instructions` by metis_tac[MEM_APPEND, TAKE_DROP] >>
  `inst = di` by
    (irule ssa_form_output_unique >> gvs[wf_ssa_def] >> metis_tac[]) >>
  gvs[]
QED

(* Availability is stronger than occurrence at an immediate instruction use;
   recursive normalization sources consume this interface too. *)
Theorem le_occ_available_last_writer:
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  i.inst_opcode <> PHI /\ def_available_at fn bb (SOME i) v ==>
  ?pre e suffix.
    es = pre ++ e::suffix /\ v IN le_occ_writes e /\
    EVERY (\q. v NOTIN le_occ_writes q) suffix /\
    le_occ_valid C fn e /\ lookup_var v s = lookup_var v (le_occ_post e)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `def_on_all_paths fn bb (SOME i) v` by
    (irule def_available_on_all_paths >> metis_tac[]) >>
  `?e. MEM e es /\ v IN le_occ_writes e` by
    (irule le_occ_prefix_use_writer >> metis_tac[]) >>
  irule le_occ_prefix_last_writer >> metis_tac[]
QED
