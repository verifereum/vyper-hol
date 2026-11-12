Theory o1LabelFlowMiddleTraversal
Ancestors
  o1LabelFlowMiddleRenameLocal o1MakeSsaEventFrames o1MakeSsaActualNames
  o1MakeSsaOwnership o1MakeSsaTraversalFrames o1MakeSsaVisitTrace
  o1LabelFlowMiddleOperandOwners o1LabelFlowMiddlePhiOwners
  makeSsaDefs makeSsaCurrentLockstepShape codegenSymRel
  venomInst list rich_list pair

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

Theorem rename_current_block_operand_lengths:
  !xs s rs rt t ys.
  rename_current_block_insts s rs xs = (rt,t,ys) ==>
  MAP (\i. (i.inst_opcode, LENGTH i.inst_operands)) ys =
  MAP (\i. (i.inst_opcode, LENGTH i.inst_operands)) xs
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  conj_tac
  >- (gvs[rename_current_inst_def] >>
      Cases_on `h.inst_opcode = PHI` >> gvs[] >>
      rpt (pairarg_tac >> gvs[]) >>
      simp[o1MakeSsaFormatsTheory.rename_current_operands_length]) >>
  metis_tac[]
QED

Theorem current_block_owned_operands:
  rename_current_block_insts s rs xs = (rt,t,ys) /\
  current_name_owner V H u /\ current_stack_owner V H (SND rs) /\
  LIST_REL (\i j. LIST_REL (\v n. (n,v) IN H)
    i.inst_outputs j.inst_outputs) xs ys /\
  k < LENGTH xs /\ (EL k xs).inst_opcode <> PHI /\
  (!v. MEM (Var v) (EL k xs).inst_operands ==> v IN V) ==>
  LIST_REL (\a b. case a of Var v => ?n. b = Var n /\ (n,v) IN H
                   | _ => b = a)
    (EL k xs).inst_operands (EL k ys).inst_operands
Proof
  strip_tac >>
  drule rename_current_block_operand_lengths >> strip_tac >>
  `LENGTH ys = LENGTH xs` by
    metis_tac[o1MakeSsaCfgTheory.rename_current_block_insts_length] >>
  `LENGTH (EL k ys).inst_operands = LENGTH (EL k xs).inst_operands` by
    (qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `EL k`) >>
     simp[EL_MAP]) >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  Cases_on `EL n (EL k xs).inst_operands` >> simp[]
  >- (irule current_rename_block_nonvar >> simp[] >> metis_tac[])
  >- metis_tac[current_fixed_owner_block_operand, EL_MEM] >>
  irule current_rename_block_nonvar >> simp[] >> metis_tac[]
QED

Theorem visit_event_owned_position:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\ MEM e events /\
  lookup_block e.sve_label bbs = SOME bb /\
  current_name_owner V H u /\ current_stack_owner V H (SND e.sve_in) /\
  LIST_REL (\i j. LIST_REL (\v n. (n,v) IN H)
    i.inst_outputs j.inst_outputs) e.sve_before e.sve_after /\
  k < LENGTH bb.bb_instructions /\
  (!v. MEM (Var v) (EL k bb.bb_instructions).inst_operands ==> v IN V) ==>
  ?out. lookup_block e.sve_label final = SOME out /\
    LENGTH out.bb_instructions = LENGTH bb.bb_instructions /\
    (EL k out.bb_instructions).inst_opcode = (EL k bb.bb_instructions).inst_opcode /\
    LIST_REL (\v n. (n,v) IN H) (EL k bb.bb_instructions).inst_outputs
      (EL k out.bb_instructions).inst_outputs /\
    ((EL k bb.bb_instructions).inst_opcode <> PHI ==>
     LIST_REL (\a b. case a of Var v => ?n. b = Var n /\ (n,v) IN H
                      | _ => b = a)
       (EL k bb.bb_instructions).inst_operands (EL k out.bb_instructions).inst_operands)
Proof
  strip_tac >>
  `indexed_patch_frame bb (bb with bb_instructions := e.sve_before)` by
    metis_tac[cj 1 visit_event_input_frame] >>
  `rename_current_block_insts e.sve_supply_in e.sve_in e.sve_before =
    (e.sve_out,e.sve_supply_out,e.sve_after)` by
    (qspecl_then [`tree`,`path`,`s`,`rs`,`bbs`,`sm`] mp_tac
      (cj 1 visit_local_rename) >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all (cj 1 visit_event_final_frame) >> strip_tac >>
  drule rename_current_block_operand_lengths >> strip_tac >>
  `LENGTH e.sve_after = LENGTH e.sve_before` by
    metis_tac[o1MakeSsaCfgTheory.rename_current_block_insts_length] >>
  `(EL k e.sve_after).inst_opcode = (EL k e.sve_before).inst_opcode` by
    (qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `EL k`) >>
     fs[indexed_patch_frame_def] >> simp[EL_MAP]) >>
  qexists `out` >> fs[indexed_patch_frame_def, LIST_REL_EL_EQN] >>
  strip_tac >>
  `(EL k e.sve_before) = EL k bb.bb_instructions /\
   (EL k out.bb_instructions) = EL k e.sve_after` by metis_tac[] >>
  `LIST_REL (\a b. case a of Var v => ?n. b = Var n /\ (n,v) IN H
                        | _ => b = a)
     (EL k e.sve_before).inst_operands (EL k e.sve_after).inst_operands` by
    (irule current_block_owned_operands >> simp[LIST_REL_EL_EQN] >>
     metis_tac[]) >>
  gvs[LIST_REL_EL_EQN]
QED

Theorem owned_operands_identity:
  current_name_owner V H u /\
  (!v. MEM (Var v) ops ==> v IN V) ==>
  LIST_REL (\a b. case a of Var v => ?n. b = Var n /\ (n,v) IN H
                   | _ => b = a) ops ops
Proof
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  Cases_on `EL n ops` >> simp[] >>
  metis_tac[current_name_owner_identity, EL_MEM]
QED

Theorem visit_blocks_owned_position:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!q. MEM q (dom_tree_postorder tree) ==> IS_SOME (lookup_block q bbs)) /\
  current_name_owner V H u /\
  (!e. MEM e events ==> current_stack_owner V H (SND e.sve_in) /\
    LIST_REL (\i j. LIST_REL (\v n. (n,v) IN H)
      i.inst_outputs j.inst_outputs) e.sve_before e.sve_after) /\
  lookup_block q bbs = SOME bb /\ k < LENGTH bb.bb_instructions /\
  (!v. MEM (Var v) (EL k bb.bb_instructions).inst_operands ==> v IN V) /\
  (!v. MEM v (EL k bb.bb_instructions).inst_outputs ==> v IN V) ==>
  ?out. lookup_block q final = SOME out /\
    LENGTH out.bb_instructions = LENGTH bb.bb_instructions /\
    (EL k out.bb_instructions).inst_opcode = (EL k bb.bb_instructions).inst_opcode /\
    LIST_REL (\v n. (n,v) IN H) (EL k bb.bb_instructions).inst_outputs
      (EL k out.bb_instructions).inst_outputs /\
    ((EL k bb.bb_instructions).inst_opcode <> PHI ==>
     LIST_REL (\a b. case a of Var v => ?n. b = Var n /\ (n,v) IN H
                      | _ => b = a)
       (EL k bb.bb_instructions).inst_operands (EL k out.bb_instructions).inst_operands)
Proof
  strip_tac >> Cases_on `MEM q (dom_tree_postorder tree)`
  >- (drule_all (cj 1 visit_tree_coverage) >> simp[MEM_MAP] >> strip_tac >>
      qpat_x_assum `q = _` SUBST_ALL_TAC >>
      irule visit_event_owned_position >> metis_tac[]) >>
  drule_all (cj 1 visit_excluded_frame) >> strip_tac >>
  qexists `out` >> fs[indexed_patch_frame_def] >>
  conj_tac
  >- (simp[LIST_REL_EL_EQN] >> metis_tac[current_name_owner_identity, EL_MEM]) >>
  strip_tac >> irule owned_operands_identity >> metis_tac[]
QED

Theorem owned_operand_var_origin:
  LIST_REL (\a b. case a of Var v => ?n. b = Var n /\ (n,v) IN H
                   | _ => b = a) ops outs /\
  current_name_owner V H u /\ (n,x) IN H /\
  k < LENGTH outs /\ EL k outs = Var n ==>
  k < LENGTH ops /\ EL k ops = Var x
Proof
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
  Cases_on `EL k ops` >> simp[] >> strip_tac >>
  metis_tac[current_name_owner_unique]
QED

Theorem owned_output_origin:
  LIST_REL (\v n. (n,v) IN H) vs ns /\
  current_name_owner V H u /\ (n,x) IN H /\ MEM n ns ==> MEM x vs
Proof
  simp[MEM_EL, LIST_REL_EL_EQN] >> rpt strip_tac >>
  `EL n' vs = x` by metis_tac[current_name_owner_unique] >> metis_tac[]
QED

Theorem owned_codecopy_read:
  LIST_REL (\a b. case a of Var v => ?n. b = Var n /\ (n,v) IN H
                   | _ => b = a) ops outs /\
  current_name_owner V H u /\ (n,x) IN H /\ MEM (Var n) outs /\
  (!v. MEM (Var v) ops /\ v = x ==>
     ?dst sz. ops = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x) ==>
  ?dst sz. outs = [dst; Var n; sz] /\ dst <> Var n /\ sz <> Var n
Proof
  strip_tac >>
  `MEM (Var x) ops` by
    (gvs[MEM_EL] >> metis_tac[owned_operand_var_origin]) >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `dst` >> Cases_on `sz` >> gvs[] >>
  metis_tac[current_name_owner_unique]
QED

Theorem visit_blocks_owned_origin:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!q. MEM q (dom_tree_postorder tree) ==> IS_SOME (lookup_block q bbs)) /\
  current_name_owner V H u /\
  (!e. MEM e events ==> current_stack_owner V H (SND e.sve_in) /\
    LIST_REL (\i j. LIST_REL (\v n. (n,v) IN H)
      i.inst_outputs j.inst_outputs) e.sve_before e.sve_after) /\
  (!bb i v. MEM bb bbs /\ MEM i bb.bb_instructions ==>
    (MEM (Var v) i.inst_operands \/ MEM v i.inst_outputs ==> v IN V)) /\
  lookup_block q final = SOME out /\ k < LENGTH out.bb_instructions ==>
  ?bb. lookup_block q bbs = SOME bb /\ k < LENGTH bb.bb_instructions /\
    (EL k out.bb_instructions).inst_opcode = (EL k bb.bb_instructions).inst_opcode /\
    LIST_REL (\v n. (n,v) IN H) (EL k bb.bb_instructions).inst_outputs
      (EL k out.bb_instructions).inst_outputs /\
    ((EL k bb.bb_instructions).inst_opcode <> PHI ==>
     LIST_REL (\a b. case a of Var v => ?n. b = Var n /\ (n,v) IN H
                      | _ => b = a)
       (EL k bb.bb_instructions).inst_operands (EL k out.bb_instructions).inst_operands)
Proof
  strip_tac >>
  `IS_SOME (lookup_block q bbs)` by
    metis_tac[cj 1 visit_lookup_domain, optionTheory.IS_SOME_DEF] >>
  Cases_on `lookup_block q bbs` >> gvs[] >> rename1 `lookup_block q bbs = SOME bb` >>
  `rename_current_blocks s rs bbs sm tree = (ct,t,final)` by
    metis_tac[visit_erasure, FST] >>
  `ALL_DISTINCT (MAP basic_block_bb_label bbs)` by
    (qpat_x_assum `ALL_DISTINCT (MAP _ bbs)` mp_tac >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  drule_all rename_current_blocks_lookup_signatures >> strip_tac >> gvs[] >>
  rename1 `lookup_block q final = SOME out` >>
  `LENGTH out.bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[LENGTH_MAP] >>
  `MEM bb bbs /\ MEM (EL k bb.bb_instructions) bb.bb_instructions` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem, EL_MEM] >>
  `!v. MEM (Var v) (EL k bb.bb_instructions).inst_operands ==> v IN V` by
    metis_tac[] >>
  `!v. MEM v (EL k bb.bb_instructions).inst_outputs ==> v IN V` by
    metis_tac[] >>
  drule visit_blocks_owned_position >> simp[] >>
  disch_then (qspecl_then [`u`,`q`,`k`,`bb`,`V`,`H`] mp_tac) >> simp[] >>
  metis_tac[]
QED
