Theory o1LabelFlowMiddleTraversal
Ancestors
  o1LabelFlowMiddleRenameLocal o1MakeSsaEventFrames o1MakeSsaActualNames
  o1MakeSsaOwnership o1MakeSsaTraversalFrames
  makeSsaDefs venomInst list rich_list pair

Theorem indexed_patch_frame_adjacent:
  indexed_patch_frame bb out /\
  bb.bb_instructions = pre ++ d::j::post /\
  d.inst_opcode <> PHI /\ j.inst_opcode <> PHI ==>
  ?pre' post'. out.bb_instructions = pre' ++ d::j::post' /\
    LENGTH pre' = LENGTH pre
Proof
  strip_tac >>
  `LENGTH pre + 1 < LENGTH out.bb_instructions` by
    gvs[indexed_patch_frame_def] >>
  `EL (LENGTH pre) out.bb_instructions = d /\
   EL (LENGTH pre + 1) out.bb_instructions = j` by
    (gvs[indexed_patch_frame_def] >>
     first_assum (qspec_then `LENGTH pre` mp_tac) >>
     first_x_assum (qspec_then `LENGTH pre + 1` mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  qexistsl_tac [`TAKE (LENGTH pre) out.bb_instructions`,
                `DROP (LENGTH pre + 2) out.bb_instructions`] >>
  simp[LENGTH_TAKE] >>
  qspecl_then [`out.bb_instructions`, `LENGTH pre`] mp_tac DROP_EL_CONS >>
  qspecl_then [`out.bb_instructions`, `LENGTH pre + 1`] mp_tac DROP_EL_CONS >>
  simp[] >> rpt strip_tac >>
  qspecl_then [`LENGTH pre`, `out.bb_instructions`] mp_tac TAKE_DROP >>
  pure_asm_rewrite_tac[APPEND, GSYM APPEND_ASSOC] >> metis_tac[]
QED

Theorem visit_event_code_end_pair:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\ MEM e events /\
  lookup_block e.sve_label bbs = SOME bb /\
  bb.bb_instructions = pre ++ d::j::post /\
  d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
  d.inst_outputs = [x] /\
  j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var x; sz] ==>
  ?out pre' d' j' post' n a b c.
    lookup_block e.sve_label final = SOME out /\
    out.bb_instructions = pre' ++ d'::j'::post' /\
    LENGTH pre' = LENGTH pre /\
    d'.inst_opcode = ADD /\ d'.inst_outputs = [n] /\
    d'.inst_operands = [a; Label "code_end"] /\
    j'.inst_opcode = CODECOPY /\ j'.inst_operands = [b; Var n; c]
Proof
  strip_tac >>
  `indexed_patch_frame bb (bb with bb_instructions := e.sve_before)` by
    metis_tac[cj 1 visit_event_input_frame] >>
  drule indexed_patch_frame_adjacent >>
  disch_then (qspecl_then [`pre`,`post`,`j`,`d`] mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `rename_current_block_insts e.sve_supply_in e.sve_in e.sve_before =
    (e.sve_out,e.sve_supply_out,e.sve_after)` by
    (qspecl_then [`tree`,`path`,`s`,`rs`,`bbs`,`sm`] mp_tac
      (cj 1 visit_local_rename) >> simp[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `rename_current_block_insts _ _ _ = _` mp_tac >>
  asm_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  disch_then assume_tac >>
  drule_all rename_current_block_code_end_pair >> strip_tac >>
  drule_all (cj 1 visit_event_final_frame) >> strip_tac >>
  drule indexed_patch_frame_adjacent >>
  disch_then (qspecl_then [`pre''`,`post''`,`j'`,`d'`] mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  metis_tac[]
QED

Theorem visit_blocks_code_end_pair:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!q. MEM q (dom_tree_postorder tree) ==> IS_SOME (lookup_block q bbs)) /\
  lookup_block q bbs = SOME bb /\
  bb.bb_instructions = pre ++ d::j::post /\
  d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
  d.inst_outputs = [x] /\
  j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var x; sz] ==>
  ?out pre' d' j' post' n a b c.
    lookup_block q final = SOME out /\
    out.bb_instructions = pre' ++ d'::j'::post' /\
    LENGTH pre' = LENGTH pre /\
    d'.inst_opcode = ADD /\ d'.inst_outputs = [n] /\
    d'.inst_operands = [a; Label "code_end"] /\
    j'.inst_opcode = CODECOPY /\ j'.inst_operands = [b; Var n; c]
Proof
  strip_tac >> Cases_on `MEM q (dom_tree_postorder tree)`
  >- (drule_all (cj 1 visit_tree_coverage) >>
      simp[MEM_MAP] >>
      strip_tac >> qpat_x_assum `q = _` SUBST_ALL_TAC >>
      drule_all visit_event_code_end_pair >> simp[]) >>
  drule_all (cj 1 visit_excluded_frame) >> strip_tac >>
  drule indexed_patch_frame_adjacent >>
  disch_then (qspecl_then [`pre`,`post`,`j`,`d`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl [`out`,`pre'`,`d`,`j`,`post'`,`x`,`op`,`dst`,`sz`] >> simp[]
QED
