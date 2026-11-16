Theory o1LabelFlowMiddleCleanup
Ancestors
  makeSsaCurrentCleanupBoundary makeSsaCurrentLockstepShape venomExecProofs
  makeSsaDefs venomInst irSupply list

Theorem cleanup_suffix_content:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (rest = [] \/ (HD rest).inst_opcode <> PHI) /\ k < LENGTH rest ==>
  (EL (LENGTH pre + k) (simplify_current_phi_prefix (pre ++ rest))).inst_opcode = (EL k rest).inst_opcode /\
  (EL (LENGTH pre + k) (simplify_current_phi_prefix (pre ++ rest))).inst_operands = (EL k rest).inst_operands /\
  (EL (LENGTH pre + k) (simplify_current_phi_prefix (pre ++ rest))).inst_outputs = (EL k rest).inst_outputs
Proof
  strip_tac >> gvs[] >>
  drule current_phi_prefix_partition >>
  disch_then (qspec_then `rest` mp_tac) >> simp[] >> strip_tac >>
  simp[simplify_current_phi_prefix_def] >>
  qmatch_goalsub_abbrev_tac `reassign_current_inst_ids ids (ps ++ cs ++ rest)` >>
  `LENGTH ps + LENGTH cs = LENGTH pre` by
    (drule current_phi_prefix_parts_length >> simp[Abbr `ps`, Abbr `cs`]) >>
  mp_tac (Q.SPECL [`ids`, `ps ++ cs ++ rest`, `LENGTH (pre:instruction list) + k`] current_reassign_content) >>
  simp[EL_APPEND_EQN]
QED

Theorem cleanup_index_content:
  phi_prefix_length xs <= k /\ k < LENGTH xs ==>
  (EL k (simplify_current_phi_prefix xs)).inst_opcode = (EL k xs).inst_opcode /\
  (EL k (simplify_current_phi_prefix xs)).inst_operands = (EL k xs).inst_operands /\
  (EL k (simplify_current_phi_prefix xs)).inst_outputs = (EL k xs).inst_outputs
Proof
  strip_tac >>
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  drule simplify_current_phi_prefix_parts_length >> strip_tac >>
  drule simplify_current_phi_prefix_partition >> strip_tac >>
  `k < LENGTH (phis ++ ordinary)` by simp[] >>
  drule current_reassign_content >>
  disch_then (qspec_then `MAP (\i. i.inst_id) xs` strip_assume_tac) >>
  `EL k (phis ++ ordinary) = EL k xs` by
    (gvs[] >>
     `k - LENGTH phis - LENGTH copies = k - phi_prefix_length xs` by decide_tac >>
     simp[EL_APPEND_EQN, EL_DROP]) >>
  metis_tac[]
QED

Theorem cleanup_block_content:
  phi_prefix_length b.bb_instructions <= k /\ k < LENGTH b.bb_instructions ==>
  (EL k (simplify_current_phi_block b).bb_instructions).inst_opcode = (EL k b.bb_instructions).inst_opcode /\
  (EL k (simplify_current_phi_block b).bb_instructions).inst_operands = (EL k b.bb_instructions).inst_operands /\
  (EL k (simplify_current_phi_block b).bb_instructions).inst_outputs = (EL k b.bb_instructions).inst_outputs
Proof
  Cases_on `b.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC >> simp[] >> rpt strip_tac >>
  metis_tac[cleanup_index_content, LENGTH]
QED

Theorem cleanup_if_lookup_content:
  lookup_block l bs = SOME b ==>
  ?b'. lookup_block l (simplify_current_phis_if enabled bs) = SOME b' /\
    b'.bb_label = b.bb_label /\ LENGTH b'.bb_instructions = LENGTH b.bb_instructions /\
    (!k. phi_prefix_length b.bb_instructions <= k /\ k < LENGTH b.bb_instructions ==>
      (EL k b'.bb_instructions).inst_opcode = (EL k b.bb_instructions).inst_opcode /\
      (EL k b'.bb_instructions).inst_operands = (EL k b.bb_instructions).inst_operands /\
      (EL k b'.bb_instructions).inst_outputs = (EL k b.bb_instructions).inst_outputs)
Proof
  strip_tac >> simp[simplify_current_phis_if_def, simplify_current_phis_def] >>
  Cases_on `enabled /\ blocks_have_leading_phi bs` >> fs[]
  >- (drule_at (Pos last) lookup_block_map_relation >>
      disch_then (qspec_then `simplify_current_phi_block` mp_tac) >> simp[] >>
      strip_tac >>
      simp[cleanup_block_content, simplify_current_phi_block_layout]) >>
  qexists `b` >> simp[]
QED

Theorem cleanup_partition_protected:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  EVERY (\i. !v. P v ==> ~MEM v (inst_ir_vars i)) pre /\
  (rest = [] \/ (HD rest).inst_opcode <> PHI) ==>
  ?ps cs. simplify_current_phi_prefix_parts (pre ++ rest) = (ps,cs ++ rest) /\
    LENGTH ps + LENGTH cs = LENGTH pre /\
    EVERY (\i. !v. P v ==> ~MEM v (inst_ir_vars i)) (ps ++ cs)
Proof
  rpt gen_tac >> disch_tac >>
  `simplify_current_phi_prefix_parts (pre ++ rest) =
    (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre),
     FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre) ++ rest)` by
    metis_tac[current_phi_prefix_partition] >>
  qexistsl [`FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre)`,
            `FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)`] >>
  simp[] >> conj_tac
  >- (drule current_phi_prefix_parts_length >> simp[]) >>
  gvs[EVERY_MEM, MEM_FILTER, MEM_MAP] >> rpt strip_tac >>
  metis_tac[simplify_current_phi_vars]
QED

Theorem cleanup_prefix_protected:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  EVERY (\i. !v. P v ==> ~MEM v (inst_ir_vars i)) pre /\
  (rest = [] \/ (HD rest).inst_opcode <> PHI) /\ k < LENGTH pre /\ P v ==>
  ~MEM v (inst_ir_vars (EL k (simplify_current_phi_prefix (pre ++ rest))))
Proof
  rpt strip_tac >>
  `?ps cs. simplify_current_phi_prefix_parts (pre ++ rest) = (ps,cs ++ rest) /\
    LENGTH ps + LENGTH cs = LENGTH pre /\
    EVERY (\i. !v. P v ==> ~MEM v (inst_ir_vars i)) (ps ++ cs)` by
      metis_tac[cleanup_partition_protected] >>
  simp[simplify_current_phi_prefix_def] >>
  `k < LENGTH (ps ++ cs ++ rest)` by simp[] >>
  drule current_reassign_content >>
  disch_then (qspec_then `MAP (\i. i.inst_id) (pre ++ rest)` strip_assume_tac) >>
  `EL k (ps ++ cs ++ rest) = EL k (ps ++ cs)` by simp[EL_APPEND_EQN] >>
  `~MEM v (inst_ir_vars (EL k (ps ++ cs)))` by
    (fs[EVERY_EL] >> Cases_on `k < LENGTH ps` >>
     simp[EL_APPEND_EQN] >>
     `k - LENGTH ps < LENGTH cs` by decide_tac >> metis_tac[]) >>
  gvs[simplify_current_phi_prefix_def, inst_ir_vars_def, inst_uses_def]
QED

Theorem cleanup_adjacent_content:
  phi_prefix_length xs <= k /\ k + 1 < LENGTH xs ==>
  (EL k (simplify_current_phi_prefix xs)).inst_opcode = (EL k xs).inst_opcode /\
  (EL k (simplify_current_phi_prefix xs)).inst_operands = (EL k xs).inst_operands /\
  (EL k (simplify_current_phi_prefix xs)).inst_outputs = (EL k xs).inst_outputs /\
  (EL (k+1) (simplify_current_phi_prefix xs)).inst_opcode = (EL (k+1) xs).inst_opcode /\
  (EL (k+1) (simplify_current_phi_prefix xs)).inst_operands = (EL (k+1) xs).inst_operands /\
  (EL (k+1) (simplify_current_phi_prefix xs)).inst_outputs = (EL (k+1) xs).inst_outputs
Proof
  strip_tac >> conj_tac >- (irule (cj 1 cleanup_index_content) >> simp[]) >>
  conj_tac >- (irule (cj 2 cleanup_index_content) >> simp[]) >>
  conj_tac >- (irule (cj 3 cleanup_index_content) >> simp[]) >>
  irule cleanup_index_content >> simp[]
QED

Theorem cleanup_block_prefix_protected:
  b.bb_instructions = pre ++ rest /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  EVERY (\i. !v. P v ==> ~MEM v (inst_ir_vars i)) pre /\
  (rest = [] \/ (HD rest).inst_opcode <> PHI) /\ k < LENGTH pre /\ P v ==>
  ~MEM v (inst_ir_vars (EL k (simplify_current_phi_block b).bb_instructions))
Proof
  strip_tac >>
  `~MEM v (inst_ir_vars (EL k (simplify_current_phi_prefix (pre ++ rest))))` by
    metis_tac[cleanup_prefix_protected] >>
  Cases_on `pre` >> gvs[EVERY_DEF, simplify_current_phi_block_def]
QED

Theorem cleanup_if_lookup_prefix_protected:
  lookup_block l bs = SOME b /\ b.bb_instructions = pre ++ rest /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  EVERY (\i. !v. P v ==> ~MEM v (inst_ir_vars i)) pre /\
  (rest = [] \/ (HD rest).inst_opcode <> PHI) ==>
  ?b'. lookup_block l (simplify_current_phis_if enabled bs) = SOME b' /\
    b'.bb_label = b.bb_label /\ LENGTH b'.bb_instructions = LENGTH b.bb_instructions /\
    (!k v. k < LENGTH pre /\ P v ==> ~MEM v (inst_ir_vars (EL k b'.bb_instructions)))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  simp[simplify_current_phis_if_def, simplify_current_phis_def] >>
  Cases_on `enabled /\ blocks_have_leading_phi bs` >> gns[]
  >- (drule_at (Pos last) lookup_block_map_relation >>
      disch_then (qspec_then `simplify_current_phi_block` mp_tac) >> simp[] >>
      strip_tac >> simp[simplify_current_phi_block_layout] >>
      rpt gen_tac >> disch_tac >> irule cleanup_block_prefix_protected >>
      qexistsl [`P`, `pre`, `rest`] >> simp[]) >>
  qexists `b` >>
  `~enabled \/ ~blocks_have_leading_phi bs` by metis_tac[] >>
  simp[] >> rpt strip_tac >>
  `EL k (pre ++ rest) = EL k pre` by simp[EL_APPEND_EQN] >>
  fs[EVERY_EL] >> metis_tac[]
QED
