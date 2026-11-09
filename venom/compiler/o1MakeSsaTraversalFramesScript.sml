Theory o1MakeSsaTraversalFrames
Ancestors
  o1MakeSsaPatchFrames o1MakeSsaVisitTrace o1MakeSsaVisitRetention
  makeSsaDefs makeSsaCurrentInduct makeSsaCurrentProps list pair
  venomExecProofs

Theorem visit_excluded_projection:
  (!i ops. i.inst_opcode = PHI ==> f (i with inst_operands := ops) = f i) ==>
  (!tree path s rs bbs sm ct t final events q bb.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    lookup_block q bbs = SOME bb /\ ~MEM q (dom_tree_postorder tree) ==>
    ?out. lookup_block q final = SOME out /\ out.bb_label = bb.bb_label /\
      MAP f out.bb_instructions = MAP f bb.bb_instructions) /\
  (!trees path s ctrs stacks bbs sm ct t final events q bb.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    lookup_block q bbs = SOME bb /\
    ~MEM q (FLAT (MAP dom_tree_postorder trees)) ==>
    ?out. lookup_block q final = SOME out /\ out.bb_label = bb.bb_label /\
      MAP f out.bb_instructions = MAP f bb.bb_instructions)
Proof
  strip_tac >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[]
      >- (rpt strip_tac >> gvs[]) >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
      fs[dom_tree_postorder_def] >>
      `x.bb_label = lbl` by metis_tac[lookup_block_label] >>
      `lookup_block q (replace_block lbl (x with bb_instructions := insts) bbs) = SOME bb`
        by simp[retention_lookup_replace] >>
      drule_all patch_lookup_projection >>
      disch_then (qspecl_then [`case ALOOKUP sm lbl of NONE => [] | SOME ss => ss`,`rs1`,`lbl`] strip_assume_tac) >>
      first_x_assum drule_all >> metis_tac[])
  >- (simp[visit_blocks_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  fs[MEM_FLAT, MEM_MAP] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> metis_tac[]
QED

Theorem visit_lookup_domain:
  (!tree path s rs bbs sm ct t final events q.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) ==>
    (IS_SOME (lookup_block q final) <=> IS_SOME (lookup_block q bbs))) /\
  (!trees path s ctrs stacks bbs sm ct t final events q.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) ==>
    (IS_SOME (lookup_block q final) <=> IS_SOME (lookup_block q bbs)))
Proof
  conj_tac >> rpt strip_tac
  >- (`rename_current_blocks s rs bbs sm tree = (ct,t,final)` by
        metis_tac[visit_erasure,FST] >>
      drule (cj 1 rename_current_blocks_labels) >>
      disch_then (mp_tac o MATCH_MP lookup_block_labels_agree) >> simp[]) >>
  `rename_current_children s ctrs stacks bbs sm trees = (ct,t,final)` by
    metis_tac[visit_erasure,FST] >>
  drule (cj 2 rename_current_blocks_labels) >>
  disch_then (mp_tac o MATCH_MP lookup_block_labels_agree) >> simp[]
QED

Definition indexed_patch_frame_def:
  indexed_patch_frame bb out <=>
    out.bb_label = bb.bb_label /\
    LENGTH out.bb_instructions = LENGTH bb.bb_instructions /\
    !i. i < LENGTH bb.bb_instructions ==>
      (EL i out.bb_instructions).inst_opcode = (EL i bb.bb_instructions).inst_opcode /\
      (EL i out.bb_instructions).inst_outputs = (EL i bb.bb_instructions).inst_outputs /\
      ((EL i bb.bb_instructions).inst_opcode <> PHI ==>
        EL i out.bb_instructions = EL i bb.bb_instructions)
End

Theorem projection_indexed_frame:
  out.bb_label = bb.bb_label /\
  MAP (\i. (i.inst_opcode, i.inst_outputs,
    if i.inst_opcode = PHI then NONE else SOME i)) out.bb_instructions =
  MAP (\i. (i.inst_opcode, i.inst_outputs,
    if i.inst_opcode = PHI then NONE else SOME i)) bb.bb_instructions ==>
  indexed_patch_frame bb out
Proof
  strip_tac >>
  `LENGTH out.bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[LENGTH_MAP] >>
  simp[indexed_patch_frame_def] >> rpt strip_tac >>
  qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `EL i`) >>
  simp[EL_MAP] >> rpt strip_tac >> gvs[]
QED

Theorem visit_excluded_frame:
  (!tree path s rs bbs sm ct t final events q bb.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    lookup_block q bbs = SOME bb /\ ~MEM q (dom_tree_postorder tree) ==>
    ?out. lookup_block q final = SOME out /\ indexed_patch_frame bb out) /\
  (!trees path s ctrs stacks bbs sm ct t final events q bb.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    lookup_block q bbs = SOME bb /\
    ~MEM q (FLAT (MAP dom_tree_postorder trees)) ==>
    ?out. lookup_block q final = SOME out /\ indexed_patch_frame bb out)
Proof
  qspec_then `\i. (i.inst_opcode, i.inst_outputs,
    if i.inst_opcode = PHI then NONE else SOME i)` mp_tac
    (Q.GEN `f` visit_excluded_projection) >> simp[] >> strip_tac >>
  conj_tac >> rpt strip_tac >> first_x_assum drule_all >>
  metis_tac[projection_indexed_frame]
QED
