Theory gasFocusDftEntryState
Ancestors
  dftContractGas dftRunRel o1PassContract lowerDloadDefs
  venomWfProps venomWf venomInst venomState venomExecSemantics simplifyCfgDefs
  list relation finite_map

(* The selected row starts at the normalized entry, without executing pseudos. *)
Theorem focus_dft_entry_state:
  let E = root_base with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> in
  code_layout_valid root_base /\ o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
  MEM sf C7.ctx_functions /\ MEM tf C8.ctx_functions /\
  fn_entry_label sf = SOME lbl /\ fn_entry_label tf = SOME lbl /\
  lookup_block lbl sf.fn_blocks = SOME bb /\ lookup_block lbl tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) xs ==>
  eval_phis E bt.bb_instructions = OK E /\
  phi_prefix_length bt.bb_instructions = 0 /\
  get_instruction bt 0 = SOME (HD bt.bb_instructions) /\
  strict_dom_vars_defined sf E /\ fn_reachable sf E.vs_current_bb /\
  ctx_labels_bound C7 E.vs_labels /\ ctx_labels_bound C8 E.vs_labels /\
  (phi_prefix_length bt.bb_instructions = LENGTH ps ==> dft_remaining_inv sf bb xs E)
Proof
  simp[LET_THM] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `eval_phis E _` >>
  `E.vs_current_bb = lbl /\ E.vs_labels = root_base.vs_labels` by simp[Abbr `E`] >>
  `o1_fn_shape C7 sf /\ o1_fn_shape C8 tf` by
    metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
  `eval_phis E bt.bb_instructions = OK E /\
   phi_prefix_length bt.bb_instructions = 0 /\
   get_instruction bt 0 = SOME (HD bt.bb_instructions)` by
    (Cases_on `tf.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm] >>
     `bt.bb_instructions <> []` by
       gvs[o1_fn_shape_def, wf_function_def, bb_well_formed_def] >>
     Cases_on `bt.bb_instructions` >>
     gvs[o1_fn_shape_def, first_block_no_phi_def, eval_phis_def,
         phi_prefix_length_def, get_instruction_def]) >>
  `strict_dom_vars_defined sf E` by simp[strict_dom_vars_defined_entry] >>
  `fn_reachable sf E.vs_current_bb` by simp[fn_reachable_def] >>
  `ctx_labels_bound C7 E.vs_labels /\ ctx_labels_bound C8 E.vs_labels` by
    simp[dft_ctx_labels_bound] >>
  gvs[] >> disch_tac >>
  `ps = []` by fs[LENGTH_NIL] >>
  `bb.bb_label = E.vs_current_bb /\ MEM bb sf.fn_blocks` by
    (qpat_assum `lookup_block _ sf.fn_blocks = SOME bb`
       (mp_then Any mp_tac lookup_block_member_label) >> simp[]) >>
  `fn_inst_ids_distinct sf` by fs[o1_fn_shape_def, wf_function_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (qspecl_then [`(\b. MAP (\i. i.inst_id) b.bb_instructions)`, `sf.fn_blocks`, `bb`]
       mp_tac venomWfPropsTheory.all_distinct_flat_map_member >>
     fs[fn_inst_ids_distinct_def]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = xs` by
    simp[FILTER_EQ_ID] >>
  pop_assum (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  irule dft_remaining_inv_initial >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `EVERY _ xs` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then (qspec_then `d` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `ctx_labels_bound C7 _`
    (mp_tac o REWRITE_RULE [ctx_labels_bound_def]) >>
  disch_then (qspecl_then [`sf`, `i`, `l`] mp_tac) >>
  simp[fn_insts_def, fn_insts_blocks_MEM] >>
  metis_tac[APPEND]
QED
