Theory makeSsaCurrentCleanupCopyOrigin
Ancestors makeSsaCurrentCleanupShape makeSsaCurrentDefs venomInst list rich_list

Theorem current_cleanup_partition_no_id:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
  MAP current_inst_no_id (simplify_current_phi_prefix (pre ++ tail)) =
  MAP current_inst_no_id
    (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
     FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre) ++ tail)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_cleanup_partition >> strip_tac >>
  pure_rewrite_tac[simplify_current_phi_prefix_def] >>
  asm_rewrite_tac[] >> simp_tac std_ss [LET_THM] >>
  pure_rewrite_tac[GSYM MAP_APPEND, APPEND_ASSOC] >>
  irule current_reassign_no_id >> simp[] >>
  qspec_then `MAP simplify_current_phi pre` mp_tac
    current_cleanup_partition_length >> simp[]
QED

Theorem current_cleanup_copy_segment_no_id:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  k = LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre)) /\
  m = LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) ==>
  MAP current_inst_no_id
    (TAKE m (DROP k (simplify_current_phi_prefix (pre ++ tail)))) =
  MAP current_inst_no_id
    (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule_all current_cleanup_partition_no_id >>
  disch_then (mp_tac o Q.AP_TERM `\xs. TAKE m (DROP k xs)`) >>
  simp[MAP_TAKE, MAP_DROP, MAP_APPEND, DROP_APPEND, TAKE_APPEND,
    GSYM LENGTH_MAP, DROP_LENGTH_NIL, TAKE_LENGTH_TOO_LONG]
QED

Theorem current_cleanup_copy_inverse:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  k = LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre)) /\
  m = LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) /\
  MEM inst (TAKE m (DROP k (simplify_current_phi_prefix (pre ++ tail)))) ==>
  ?original. MEM original pre /\ (simplify_current_phi original).inst_opcode <> PHI /\
    current_inst_no_id inst = current_inst_no_id (simplify_current_phi original)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule_all current_cleanup_copy_segment_no_id >> strip_tac >>
  `MEM (current_inst_no_id inst)
    (MAP current_inst_no_id
      (TAKE m (DROP k (simplify_current_phi_prefix (pre ++ tail)))))` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `MAP _ _ = _` (fn th => fs[th]) >>
  gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem current_cleanup_copy_segment_length:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  k = LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre)) /\
  m = LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) ==>
  LENGTH (TAKE k (simplify_current_phi_prefix (pre ++ tail))) = k /\
  LENGTH (TAKE m (DROP k (simplify_current_phi_prefix (pre ++ tail)))) = m
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `k + m = LENGTH pre` by metis_tac[current_cleanup_partition_length, LENGTH_MAP] >>
  simp[current_cleanup_length] >> decide_tac
QED

Theorem current_cleanup_block_prefix_eq:
  bb.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
  (simplify_current_phi_block bb).bb_instructions =
    simplify_current_phi_prefix (pre ++ tail)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `pre`
  >- (Cases_on `tail` >> gvs[simplify_current_phi_block_def,
       simplify_current_phi_prefix_def, simplify_current_phi_prefix_parts_def,
       reassign_current_inst_ids_def] >>
      qpat_x_assum `bb.bb_instructions = _` kall_tac >>
      Induct_on `t` >> simp[reassign_current_inst_ids_def]) >>
  gvs[simplify_current_phi_block_def]
QED

Theorem current_cleanup_if_copy_inverse:
  lookup_block h bbs = SOME bb /\ bb.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  k = (if enabled then
    LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre))
    else LENGTH pre) /\
  m = (if enabled then
    LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) else 0) ==>
  ?out. lookup_block h (simplify_current_phis_if enabled bbs) = SOME out /\
    LENGTH (TAKE k out.bb_instructions) = k /\
    LENGTH (TAKE m (DROP k out.bb_instructions)) = m /\
    (!inst. MEM inst (TAKE m (DROP k out.bb_instructions)) ==>
      ?original. MEM original pre /\ (simplify_current_phi original).inst_opcode <> PHI /\
        current_inst_no_id inst = current_inst_no_id (simplify_current_phi original))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[current_cleanup_if_lookup] >> Cases_on `enabled` >> gvs[] >>
  `(simplify_current_phi_block bb).bb_instructions =
    simplify_current_phi_prefix (pre ++ tail)` by
    (irule current_cleanup_block_prefix_eq >> metis_tac[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[current_cleanup_copy_segment_length] >>
  conj_tac >- metis_tac[current_cleanup_copy_segment_length] >>
  rpt strip_tac >> irule current_cleanup_copy_inverse >> metis_tac[]
QED
