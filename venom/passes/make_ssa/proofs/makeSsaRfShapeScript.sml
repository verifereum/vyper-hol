Theory makeSsaRfShape
Ancestors makeSsaRfWitness makeSsaCurrentDefs makeSsaCurrentProps makeSsaDefs
  cfgTransformProps contextCodegenRel venomInst list rich_list pair

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
  rpt gen_tac >> simp_tac std_ss [EVERY_DEF] >> strip_tac >>
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
  strip_tac >> drule current_reassign_no_id >>
  disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]
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
  >- (Induct_on `bbs` >> simp[lookup_block_def, FIND_thm] >>
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

Definition rf_phi_prefix_def:
  rf_phi_prefix old new <=>
    ?pre. new = old with bb_instructions := pre ++ old.bb_instructions /\
      EVERY (\inst. inst.inst_opcode = PHI) pre
End

Theorem rf_phi_prefix_refl[simp]:
  rf_phi_prefix bb bb
Proof
  simp[rf_phi_prefix_def] >> qexists_tac `[]` >> simp[]
QED

Theorem rf_phi_prefix_trans:
  rf_phi_prefix a b /\ rf_phi_prefix b c ==> rf_phi_prefix a c
Proof
  simp[rf_phi_prefix_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `pre' ++ pre` >> simp[]
QED

Theorem rf_phi_prefix_list_trans:
  !as bs cs. LIST_REL rf_phi_prefix as bs /\ LIST_REL rf_phi_prefix bs cs ==>
    LIST_REL rf_phi_prefix as cs
Proof
  Induct >> Cases_on `bs` >> Cases_on `cs` >> simp[] >>
  metis_tac[rf_phi_prefix_trans]
QED

Theorem rf_phi_prefix_map_insert:
  phi.inst_opcode = PHI ==>
  LIST_REL rf_phi_prefix bbs
    (MAP (\bb. if bb.bb_label = l then insert_phi_at_block phi bb else bb) bbs)
Proof
  strip_tac >> simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
  Cases_on `(EL n bbs).bb_label = l` >> simp[] >>
  simp[rf_phi_prefix_def, insert_phi_at_block_def] >>
  qexists_tac `[phi]` >> simp[]
QED

Theorem rf_process_frontiers_prefix:
  !fs s v pm li bbs rest hp bbs' rest' hp' s'.
  process_frontiers_supply s v pm li bbs rest hp fs = (bbs',rest',hp',s') ==>
  LIST_REL rf_phi_prefix bbs bbs'
Proof
  Induct >> simp[process_frontiers_supply_def]
  >- simp[LIST_REL_EL_EQN] >>
  rpt gen_tac >> Cases_on `MEM h hp` >> simp[]
  >- metis_tac[] >>
  Cases_on `case ALOOKUP li h of NONE => F | SOME vars => MEM v vars` >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      irule rf_phi_prefix_list_trans >> goal_assum $ drule_at Any >>
      irule rf_phi_prefix_map_insert >> simp[build_phi_inst_supply_def]) >>
  metis_tac[]
QED

Theorem rf_insert_phis_prefix:
  !s v df pm li bbs work hp bbs' s'.
  insert_phis_for_var_supply s v df pm li bbs work hp = (bbs',s') ==>
  LIST_REL rf_phi_prefix bbs bbs'
Proof
  ho_match_mp_tac insert_phis_for_var_supply_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[Once insert_phis_for_var_supply_def]
  >- simp[LIST_REL_EL_EQN] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule rf_process_frontiers_prefix >> strip_tac >>
  metis_tac[rf_phi_prefix_list_trans]
QED

Theorem rf_add_phi_nodes_prefix:
  !defs s df pm li bbs bbs' s'.
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
  LIST_REL rf_phi_prefix bbs bbs'
Proof
  Induct >> simp[add_phi_nodes_supply_def]
  >- simp[LIST_REL_EL_EQN] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[add_phi_nodes_supply_def] >> pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> drule rf_insert_phis_prefix >> strip_tac >>
  metis_tac[rf_phi_prefix_list_trans]
QED

Theorem rf_phi_prefix_lookup:
  !bbs bbs' l bb. LIST_REL rf_phi_prefix bbs bbs' /\
    lookup_block l bbs = SOME bb ==>
  ?pre. lookup_block l bbs' =
    SOME (bb with bb_instructions := pre ++ bb.bb_instructions) /\
    EVERY (\inst. inst.inst_opcode = PHI) pre
Proof
  Induct >> Cases_on `bbs'` >> simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >> strip_tac >> rename1 `rf_phi_prefix src dst` >>
  `dst.bb_label = src.bb_label` by fs[rf_phi_prefix_def] >>
  Cases_on `src.bb_label = l` >> gvs[]
  >- (fs[rf_phi_prefix_def] >> metis_tac[]) >> metis_tac[lookup_block_def]
QED

Theorem rf_same_after_phi_prefix:
  !pre a b. EVERY (\inst. inst.inst_opcode = PHI) pre ==>
    (same_after_assigns pre a b <=> a = b)
Proof
  Induct >> simp[same_after_assigns_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `a = b` >> simp[same_after_assigns_def] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[step_back_assign_def, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem rf_same_after_drop_phi_suffix:
  !xs a b pre. EVERY (\inst. inst.inst_opcode = PHI) pre /\
    same_after_assigns (xs ++ pre) a b ==> same_after_assigns xs a b
Proof
  Induct >- (simp[same_after_assigns_def] >> metis_tac[rf_same_after_phi_prefix]) >>
  rpt gen_tac >> simp[Once same_after_assigns_def] >>
  Cases_on `a = b` >> simp[rf_same_after_assigns_refl] >>
  Cases_on `step_back_assign h a` >> simp[] >>
  Cases_on `step_back_assign h b` >> simp[same_after_assigns_def] >> metis_tac[]
QED

Theorem rf_same_after_replace_phi_suffix:
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  same_after_assigns (xs ++ pre) a b ==>
  same_after_assigns (xs ++ replacement) a b
Proof
  metis_tac[rf_same_after_drop_phi_suffix, rf_same_after_assigns_append]
QED

Theorem rf_prepend_get_instruction:
  get_instruction (bb with bb_instructions := pre ++ bb.bb_instructions)
    (LENGTH pre + k) = get_instruction bb k
Proof
  simp[get_instruction_def, EL_APPEND_EQN]
QED

Theorem rf_prepend_pair:
  revert_forward_pair bb i j ==>
  revert_forward_pair (bb with bb_instructions := pre ++ bb.bb_instructions)
    (LENGTH pre + i) (LENGTH pre + j)
Proof
  simp[revert_forward_pair_def, rf_prepend_get_instruction] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      `?n. k = LENGTH pre + n /\ i < n /\ n < j` by
        (qexists_tac `k - LENGTH pre` >> decide_tac) >>
      gvs[] >> metis_tac[rf_prepend_get_instruction, arithmeticTheory.ADD_COMM]) >>
  qexistsl [`inst1`, `inst2`, `p`, `src`, `rds`, `p'`, `rds'`] >>
  `j + LENGTH pre - SUC (i + LENGTH pre) = j - SUC i` by decide_tac >>
  `SUC (i + LENGTH pre) - LENGTH pre = SUC i` by decide_tac >>
  simp[TAKE_APPEND, DROP_APPEND, REVERSE_APPEND,
       DROP_LENGTH_TOO_LONG, arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> irule rf_same_after_assigns_append >> simp[]
QED

Theorem rf_prepend_at:
  revert_forward_at bb k ==>
  revert_forward_at (bb with bb_instructions := pre ++ bb.bb_instructions)
    (LENGTH pre + k)
Proof
  simp[revert_forward_at_def] >> metis_tac[rf_prepend_pair, arithmeticTheory.ADD_COMM]
QED

Theorem rf_add_phi_nodes_lookup:
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\
  lookup_block l bbs = SOME bb ==>
  ?pre. lookup_block l bbs' =
    SOME (bb with bb_instructions := pre ++ bb.bb_instructions) /\
    EVERY (\inst. inst.inst_opcode = PHI) pre
Proof
  metis_tac[rf_add_phi_nodes_prefix, rf_phi_prefix_lookup]
QED

Theorem rf_insert_phis_lookup:
  insert_phis_for_var_supply s v df pm li bbs work hp = (bbs',s') /\
  lookup_block l bbs = SOME bb ==>
  ?pre. lookup_block l bbs' =
    SOME (bb with bb_instructions := pre ++ bb.bb_instructions) /\
    EVERY (\inst. inst.inst_opcode = PHI) pre
Proof
  metis_tac[rf_insert_phis_prefix, rf_phi_prefix_lookup]
QED

Theorem rf_process_frontiers_lookup:
  process_frontiers_supply s v pm li bbs rest hp fs = (bbs',rest',hp',s') /\
  lookup_block l bbs = SOME bb ==>
  ?pre. lookup_block l bbs' =
    SOME (bb with bb_instructions := pre ++ bb.bb_instructions) /\
    EVERY (\inst. inst.inst_opcode = PHI) pre
Proof
  metis_tac[rf_process_frontiers_prefix, rf_phi_prefix_lookup]
QED
