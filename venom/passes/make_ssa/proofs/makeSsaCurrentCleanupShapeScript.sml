Theory makeSsaCurrentCleanupShape
Ancestors
  makeSsaDefs makeSsaCurrentProps cfgTransformProps venomInst
  list rich_list pair

Definition current_inst_no_id_def:
  current_inst_no_id inst = inst with inst_id := 0
End

Theorem current_cleanup_partition:
  !pre tail.
    EVERY (\inst. inst.inst_opcode = PHI) pre /\
    (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
    simplify_current_phi_prefix_parts (pre ++ tail) =
      (FILTER (\inst. inst.inst_opcode = PHI) (MAP simplify_current_phi pre),
       FILTER (\inst. inst.inst_opcode <> PHI) (MAP simplify_current_phi pre) ++ tail)
Proof
  Induct
  >- (Cases >> simp[simplify_current_phi_prefix_parts_def]) >>
  rpt gen_tac >>
  simp_tac std_ss [EVERY_DEF] >> strip_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >>
  ASM_SIMP_TAC std_ss [APPEND, simplify_current_phi_prefix_parts_def] >>
  Cases_on `(simplify_current_phi h).inst_opcode = PHI` >> simp[]
QED

Theorem current_cleanup_partition_length:
  !insts. LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts) +
    LENGTH (FILTER (\inst. inst.inst_opcode <> PHI) insts) = LENGTH insts
Proof
  Induct >> simp[] >> Cases_on `h.inst_opcode = PHI` >> simp[]
QED

Theorem current_cleanup_partition_classes:
  EVERY (\inst. inst.inst_opcode = PHI)
    (FILTER (\inst. inst.inst_opcode = PHI) insts) /\
  EVERY (\inst. inst.inst_opcode <> PHI)
    (FILTER (\inst. inst.inst_opcode <> PHI) insts)
Proof
  simp[EVERY_FILTER, EVERY_MEM]
QED

Theorem current_reassign_no_id:
  !ids insts. LENGTH ids = LENGTH insts ==>
    MAP current_inst_no_id (reassign_current_inst_ids ids insts) =
    MAP current_inst_no_id insts
Proof
  Induct >> Cases_on `insts` >>
  simp[reassign_current_inst_ids_def, current_inst_no_id_def]
QED

Theorem current_reassign_length:
  LENGTH ids = LENGTH insts ==>
  LENGTH (reassign_current_inst_ids ids insts) = LENGTH insts
Proof
  strip_tac >> drule current_reassign_no_id >> disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]
QED

Theorem current_cleanup_length:
  LENGTH (simplify_current_phi_prefix insts) = LENGTH insts
Proof
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  drule simplify_current_phi_prefix_parts_length >> strip_tac >>
  irule EQ_TRANS >> irule_at Any current_reassign_length >> simp[]
QED

Theorem current_cleanup_ordinary_index:
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH tail ==>
  current_inst_no_id (EL (LENGTH pre + i)
    (simplify_current_phi_prefix (pre ++ tail))) =
  current_inst_no_id (EL i tail)
Proof
  strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`pre`, `tail`] current_cleanup_partition) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >>
  simp[simplify_current_phi_prefix_def] >>
  qmatch_goalsub_abbrev_tac `reassign_current_inst_ids ids insts` >>
  `LENGTH ids = LENGTH insts` by
    (simp[Abbr `ids`, Abbr `insts`] >>
     mp_tac (Q.SPEC `MAP simplify_current_phi pre` current_cleanup_partition_length) >>
     simp[]) >>
  drule current_reassign_no_id >>
  disch_then (mp_tac o Q.AP_TERM `EL (LENGTH (pre:instruction list) + i)`) >>
  `LENGTH pre + i < LENGTH insts` by
    (simp[Abbr `insts`] >>
     mp_tac (Q.SPEC `MAP simplify_current_phi pre` current_cleanup_partition_length) >>
     simp[]) >>
  simp[EL_MAP, current_reassign_length] >>
  `LENGTH pre = LENGTH (FILTER (\inst. inst.inst_opcode = PHI)
       (MAP simplify_current_phi pre)) +
     LENGTH (FILTER (\inst. inst.inst_opcode <> PHI)
       (MAP simplify_current_phi pre))` by
    metis_tac[current_cleanup_partition_length, LENGTH_MAP] >>
  simp[Abbr `insts`, EL_APPEND_EQN]
QED

Theorem current_cleanup_block_label[simp]:
  (simplify_current_phi_block bb).bb_label = bb.bb_label
Proof
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[]
QED

Theorem current_cleanup_block_length:
  LENGTH (simplify_current_phi_block bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[current_cleanup_length]
QED

Theorem current_cleanup_block_ordinary_index:
  bb.bb_instructions = pre ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH tail ==>
  current_inst_no_id (EL (LENGTH pre + i)
    (simplify_current_phi_block bb).bb_instructions) =
  current_inst_no_id (EL i tail)
Proof
  strip_tac >> gvs[] >> Cases_on `pre`
  >- (Cases_on `tail` >> gvs[simplify_current_phi_block_def]) >>
  gvs[] >> simp[simplify_current_phi_block_def] >>
  mp_tac (Q.INST [`pre` |-> `h::t`] current_cleanup_ordinary_index) >> simp[]
QED

Theorem current_cleanup_phis_map:
  simplify_current_phis bbs = MAP simplify_current_phi_block bbs
Proof
  Induct_on `bbs` >- simp[simplify_current_phis_def] >> gen_tac >>
  Cases_on `blocks_have_leading_phi (h::bbs)`
  >- simp[simplify_current_phis_def] >>
  `~blocks_have_leading_phi bbs /\ simplify_current_phi_block h = h` by
    (Cases_on `h.bb_instructions` >>
     gvs[blocks_have_leading_phi_def, simplify_current_phi_block_def]) >>
  gvs[simplify_current_phis_def]
QED

Theorem current_cleanup_if_lookup:
  lookup_block l (simplify_current_phis_if enabled bbs) =
    OPTION_MAP (\bb. if enabled then simplify_current_phi_block bb else bb)
      (lookup_block l bbs)
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def, current_cleanup_phis_map]
  >- (Induct_on `bbs` >>
      simp[lookup_block_def, FIND_thm] >>
      Cases_on `h.bb_label = l` >> gvs[lookup_block_def]) >>
  Cases_on `lookup_block l bbs` >> simp[]
QED

Theorem current_cleanup_if_ordinary_index:
  lookup_block l bbs = SOME bb /\ bb.bb_instructions = pre ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH tail ==>
  ?bb'. lookup_block l (simplify_current_phis_if enabled bbs) = SOME bb' /\
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    current_inst_no_id (EL (LENGTH pre + i) bb'.bb_instructions) =
    current_inst_no_id (EL i tail)
Proof
  strip_tac >> gvs[] >> simp[current_cleanup_if_lookup] >>
  Cases_on `enabled` >> simp[current_cleanup_block_length]
  >- (mp_tac current_cleanup_block_ordinary_index >> simp[]) >>
  simp[EL_APPEND_EQN]
QED
