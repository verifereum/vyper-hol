Theory dftPacketCalleeStructure
Ancestors
  dftPacketCallRowStructure dftPacketCalleeAlignment dftGasFromListLookup
  dftGasInvBlockInit dftGasSimInvariant dftRunRel dftCorrectness
  o1PassContract unitShapeDefs venomWf venomWfProps venomExecSemantics
  venomExecProofs venomInst phiTransform list rich_list relation

Theorem dft_packet_callee_entry_invariants:
  dft_fn_rel sf tf /\ setup_callee tf args s = SOME cs /\
  ctx_labels_bound C7 s.vs_labels /\ ctx_labels_bound C8 s.vs_labels ==>
  setup_callee sf args s = SOME cs /\ strict_dom_vars_defined sf cs /\
  fn_reachable sf cs.vs_current_bb /\
  ctx_labels_bound C7 cs.vs_labels /\ ctx_labels_bound C8 cs.vs_labels
Proof
  strip_tac >>
  `setup_callee sf args s = SOME cs` by metis_tac[dft_fn_rel_setup_callee] >>
  `fn_entry_label sf = SOME cs.vs_current_bb` by metis_tac[dft_setup_callee_entry] >>
  simp[] >> rpt conj_tac
  >- metis_tac[ev_setup_callee_dominators]
  >- (simp[fn_reachable_def] >> metis_tac[RTC_REFL])
  >- metis_tac[ctx_labels_bound_setup_callee] >>
  metis_tac[ctx_labels_bound_setup_callee]
QED

Theorem dft_packet_callee_entered_structure:
  tf = dft_fn sf /\ dft_fn_rel sf tf /\ wf_function tf /\
  o1_ctx_shape C7 /\ MEM sf C7.ctx_functions /\
  setup_callee tf args s = SOME cs /\
  ctx_labels_bound C7 s.vs_labels /\ ctx_labels_bound C8 s.vs_labels /\
  enters_block tf cs s1 /\ active_inst tf ci s1 ==>
  ?bb bt ps xs ys schedule sp.
    lookup_block cs.vs_current_bb sf.fn_blocks = SOME bb /\
    lookup_block cs.vs_current_bb tf.fn_blocks = SOME bt /\
    bt.bb_label = bb.bb_label /\ bb.bb_label = cs.vs_current_bb /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    EVERY inst_shape_ok bb.bb_instructions /\
    EVERY inst_wf bb.bb_instructions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
    LENGTH xs = LENGTH ys /\ PERM schedule (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\
      y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) schedule ys /\
    strict_dom_vars_defined sf cs /\ fn_reachable sf cs.vs_current_bb /\
    ctx_labels_bound C7 cs.vs_labels /\ ctx_labels_bound C8 cs.vs_labels /\
    eval_phis cs bt.bb_instructions = OK sp /\
    s1 = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions /\
    get_instruction bt s1.vs_inst_idx = SOME ci
Proof
  strip_tac >> drule_all dft_packet_callee_entry_invariants >> strip_tac >>
  drule_all entered_active_lookup >> strip_tac >>
  rename1 `lookup_block cs.vs_current_bb tf.fn_blocks = SOME bt` >>
  `?bb. lookup_block cs.vs_current_bb sf.fn_blocks = SOME bb` by
    (Cases_on `lookup_block cs.vs_current_bb sf.fn_blocks` >>
     metis_tac[dft_fn_lookup_block_none,optionTheory.NOT_NONE_SOME]) >>
  drule_all dft_packet_paired_row_structure >> strip_tac >>
  rename1 `PERM schedule (COUNT_LIST (LENGTH xs))` >>
  `MEM bb sf.fn_blocks /\ bb.bb_label = cs.vs_current_bb` by
    metis_tac[lookup_block_MEM,lookup_block_label] >>
  `EVERY inst_shape_ok bb.bb_instructions` by
    (`EVERY inst_shape_ok (fn_insts sf)` by
       (qpat_x_assum `o1_ctx_shape C7` mp_tac >>
        simp[o1_ctx_shape_def,EVERY_MEM] >> strip_tac >>
        qpat_x_assum `!e. MEM e C7.ctx_functions ==> _`
          (qspec_then `sf` mp_tac) >>
        simp[o1_fn_shape_def,fn_shape_ok_def,EVERY_MEM] >> metis_tac[]) >>
     qpat_x_assum `EVERY inst_shape_ok (fn_insts sf)` mp_tac >>
     simp[EVERY_MEM,fn_insts_def] >> strip_tac >>
     simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
     irule fmp_fn_insts_blocks_intro >> qexists_tac `bb` >> simp[]) >>
  qexistsl [`bb`,`bt`,`ps`,`xs`,`ys`,`schedule`,`sp`] >> simp[] >>
  metis_tac[ctx_labels_bound_setup_callee]
QED
