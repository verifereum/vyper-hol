Theory dftPacketCalleeInitialization
Ancestors
  dftPacketCalleeStructure dftPacketPseudoCursor dftPacketCallNative
  dftGasInvBlockInit dftRunRel dftIndexedExec dftCorrectness
  o1PassContract venomWf venomWfProps venomExecProofs venomExecSemantics
  venomInst venomState finite_map list rich_list

Theorem dft_packet_callee_body_initialized:
  dft_fn_rel sf tf /\ MEM sf C7.ctx_functions /\
  ctx_labels_bound C7 cs.vs_labels /\ strict_dom_vars_defined sf cs /\
  lookup_block cs.vs_current_bb sf.fn_blocks = SOME bb /\
  lookup_block cs.vs_current_bb tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis cs bt.bb_instructions = OK sp /\
  s1 = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions ==>
  eval_phis cs bb.bb_instructions = OK sp /\
  eval_phis cs ps = OK sp /\
  phi_prefix_length bb.bb_instructions = phi_prefix_length ps /\
  phi_prefix_length bt.bb_instructions = phi_prefix_length ps /\
  (s1.vs_inst_idx = LENGTH ps ==>
    dft_remaining_inv sf bb xs s1 /\
    !f C. FOLDR (dft_exec_cons f C) OK (DROP (phi_prefix_length ps) ps)
      (sp with vs_inst_idx := phi_prefix_length ps) = OK s1)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. i.inst_opcode <> PHI) ys` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `eval_phis cs ps = OK sp /\
   phi_prefix_length bt.bb_instructions = phi_prefix_length ps /\
   phi_prefix_length bb.bb_instructions = phi_prefix_length ps` by
    gvs[dft_eval_phis_append,dft_phi_prefix_append] >>
  `eval_phis cs bb.bb_instructions = OK sp` by
    simp[dft_eval_phis_append] >>
  simp[] >> strip_tac >>
  `phi_prefix_length ps = LENGTH ps` by gvs[] >>
  `MEM bb sf.fn_blocks /\ bb.bb_label = cs.vs_current_bb` by
    metis_tac[lookup_block_MEM,lookup_block_label] >>
  `wf_function sf /\ fn_inst_wf sf` by gvs[dft_fn_rel_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[fn_inst_wf_def,EVERY_MEM] >> metis_tac[MEM_APPEND]) >>
  irule dft_packet_pseudo_initialized >> simp[] >>
  qexistsl_tac [`cs`,`sp`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `ctx_labels_bound C7 cs.vs_labels` mp_tac >>
  simp[ctx_labels_bound_def] >> disch_then irule >>
  qexistsl_tac [`sf`,`i`] >> simp[fn_insts_def] >>
  irule (iffRL fn_insts_blocks_MEM) >> qexists_tac `bb` >> simp[]
QED
