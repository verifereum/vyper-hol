(* Fetch at singleton supplied instructions, including terminal positions. *)
Theory o1LowerDloadUnchangedFetch
Ancestors
  o1LowerDloadForwardAbort o1LowerDloadJointAssign o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1ContractLowerDload o1PassContract
  lowerDloadDefs contextCodegenRel venomExecSemantics venomExecProps venomWf venomInst list

Theorem ld_joint_control_unchanged_fetch:
  ld_joint_control u fn fn' s t /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn'.fn_blocks) /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] ==>
  ?bb'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    get_instruction bb' t.vs_inst_idx = SOME inst
Proof
  simp[ld_joint_control_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lower_dload_block_supply u1 bb` >>
  `MEM bb fn.fn_blocks` by
    (simp[MEM_EL] >> qexists_tac `k` >> simp[Abbr `bb`]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[]) >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    (qpat_x_assum `active_inst fn inst s` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     rename1 `MEM srcbb fn.fn_blocks` >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME srcbb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  qabbrev_tac `target = EL k fn'.fn_blocks` >>
  `MEM target fn'.fn_blocks` by (simp[MEM_EL, Abbr `target`] >> metis_tac[]) >>
  `target.bb_label = t.vs_current_bb` by
    (qpat_x_assum `lower_dload_block_supply _ _ = _` mp_tac >>
     simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME target` by
    (irule MEM_lookup_block >> simp[]) >>
  qexists_tac `target` >> simp[] >>
  qpat_assum `lower_dload_block_supply _ _ = _`
    (mp_tac o REWRITE_RULE [lower_dload_block_supply_def]) >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >>
  `lower_dload_inst_supply u3 inst = ([inst],u3)` by
    (irule lower_dload_inst_supply_special >> simp[]) >>
  drule_all ld_supply_insts_index >> strip_tac >>
  gvs[get_instruction_def]
QED

Theorem ld_joint_unchanged_fetch:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ active_inst fn inst s /\
  ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] ==>
  ?fn' bb'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    get_instruction bb' t.vs_inst_idx = SOME inst /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb
Proof
  strip_tac >>
  `wf_function fn` by
    (drule ld_joint_source >>
     disch_then (strip_assume_tac o MATCH_MP occ_frame_reachable_annotation) >>
     fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  qpat_x_assum `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  qpat_x_assum `ld_joint_frame _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn'.fn_blocks)` by
    (qpat_assum `ld_joint_control _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ld_joint_control_def]) >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  drule_all ld_joint_control_unchanged_fetch >> strip_tac >>
  qexistsl_tac [`fn'`, `bb'`] >> simp[] >>
  fs[ld_joint_control_def]
QED
