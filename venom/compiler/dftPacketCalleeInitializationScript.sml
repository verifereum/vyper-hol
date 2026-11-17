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

Theorem dft_packet_callee_native_initialization:
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,i.inst_id),fn,i,s) /\
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) /\
  lookup_function nm C8.ctx_functions = SOME tf /\
  eval_operands ops s = SOME args /\ setup_callee tf args s = SOME cs /\
  enters_block tf cs s1 /\ ALL_DISTINCT (fn_labels tf) /\ active_inst tf ci s1 /\
  bt.bb_instructions = ps ++ ys /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis cs bt.bb_instructions = OK sp /\
  s1 = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions /\
  get_instruction bt s1.vs_inst_idx = SOME ci /\
  (s1.vs_inst_idx = LENGTH ps ==> dft_remaining_inv sf bb xs s1) ==>
  ?N' suffix body_entry.
    N <= N' /\
    trace_blocks [] 0 N' C8 root_tf root_entry =
      trace_blocks [] 0 N C8 root_tf root_entry ++ suffix /\
    SUC j < LENGTH (trace_blocks [] 0 N' C8 root_tf root_entry) /\
    EL (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) =
      (((d,i.inst_id)::p,SUC d,ci.inst_id),tf,ci,s1) /\
    TAKE (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) =
      TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) /\
    (!h. h < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) ==>
      EL h (trace_blocks [] 0 N' C8 root_tf root_entry) =
      EL h (trace_blocks [] 0 N C8 root_tf root_entry)) /\
    phi_prefix_length bt.bb_instructions <= s1.vs_inst_idx /\
    s1.vs_inst_idx <= LENGTH ps /\
    (case body_entry of
       NONE => s1.vs_inst_idx < LENGTH ps /\
         (!f C. FOLDR (dft_exec_cons f C) OK
           (DROP (phi_prefix_length bt.bb_instructions) (TAKE s1.vs_inst_idx ps))
           (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s1)
     | SOME (be,hbe) =>
         be = s1 /\ hbe = SUC j /\ s1.vs_inst_idx = LENGTH ps /\
         ys <> [] /\ ci = HD ys /\ dft_remaining_inv sf bb xs s1 /\
         (!f C. FOLDR (dft_exec_cons f C) OK
           (DROP (phi_prefix_length bt.bb_instructions) ps)
           (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s1))
Proof
  strip_tac >>
  drule_all dft_packet_native_call_entry >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) ys` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `phi_prefix_length bt.bb_instructions <= LENGTH ps` by
    simp[dft_phi_prefix_append,phi_prefix_length_le] >>
  qexistsl_tac [`m`,`suffix`] >> simp[EL_APPEND1] >>
  Cases_on `s1.vs_inst_idx < LENGTH ps`
  >- (qexists_tac `NONE` >> simp[] >> gvs[] >> simp[DROP_TAKE]) >>
  `s1.vs_inst_idx = LENGTH ps` by gvs[] >>
  `ys <> [] /\ ci = HD ys` by
    (gvs[get_instruction_def,EL_APPEND2] >> Cases_on `ys` >> gvs[]) >>
  qexists_tac `SOME (s1,SUC j)` >> simp[] >>
  gvs[] >> simp[DROP_LENGTH_TOO_LONG]
QED
