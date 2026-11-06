(* TOP-LEVEL: native writes stay inside the final records of their actual
   allocation identities. Frames compose through allocation growth, including
   cached slots, and protect both allocated reads and fixed memory prefixes.
   Helpers lift exact native write windows into this common frame. *)
Theory abiWriterFrame
Ancestors
  allocationGrowth abiAllocatedWindows abiMemoryFrame
  compileEnv venomMemDefs venomState finite_map list pair arithmetic

Definition abi_writer_separated_def:
  abi_writer_separated writers ss offset byte_count <=>
    !id region_base region_size.
      MEM id writers /\ FLOOKUP ss.vs_allocas id = SOME (region_base,region_size) ==>
      abi_window_separated offset byte_count region_base region_size
End

Definition abi_writer_frame_def:
  abi_writer_frame writers before after <=>
    !offset byte_count. abi_writer_separated writers after offset byte_count ==>
      read_memory offset byte_count after = read_memory offset byte_count before
End

Theorem abi_writer_separated_append[simp]:
  !left right ss offset byte_count.
    abi_writer_separated (left ++ right) ss offset byte_count <=>
    abi_writer_separated left ss offset byte_count /\ abi_writer_separated right ss offset byte_count
Proof
  simp[abi_writer_separated_def, MEM_APPEND] >> metis_tac[]
QED

Theorem abi_writer_separated_growth:
  !before after writers offset byte_count.
    allocation_growth before after /\ abi_writer_separated writers after offset byte_count ==>
    abi_writer_separated writers before offset byte_count
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_writer_separated_def] >>
  rpt gen_tac >> strip_tac >>
  `FLOOKUP after.vs_allocas id = SOME (region_base,region_size)` by
    (drule_all allocation_growth_old >> simp[]) >>
  qpat_x_assum `abi_writer_separated _ _ _ _`
    (mp_tac o REWRITE_RULE [abi_writer_separated_def]) >>
  disch_then (qspecl_then [`id`, `region_base`, `region_size`] mp_tac) >> simp[]
QED

Theorem abi_writer_frame_refl[simp]:
  !writers ss. abi_writer_frame writers ss ss
Proof
  simp[abi_writer_frame_def]
QED

Theorem abi_writer_frame_memory:
  !writers before after. after.vs_memory = before.vs_memory ==> abi_writer_frame writers before after
Proof
  simp[abi_writer_frame_def, read_memory_def]
QED

Theorem abi_writer_frame_read:
  !writers before after offset byte_count.
    abi_writer_frame writers before after /\ abi_writer_separated writers after offset byte_count ==>
    read_memory offset byte_count after = read_memory offset byte_count before
Proof
  simp[abi_writer_frame_def]
QED

Theorem abi_writer_frame_trans:
  !left right before middle after.
    allocation_growth middle after /\ abi_writer_frame left before middle /\ abi_writer_frame right middle after ==>
    abi_writer_frame (left ++ right) before after
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_writer_frame_def, abi_writer_separated_append] >>
  rpt gen_tac >> strip_tac >>
  `abi_writer_separated left middle offset byte_count` by
    (mp_tac (Q.SPECL [`middle`, `after`, `left`, `offset`, `byte_count`] abi_writer_separated_growth) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `read_memory offset byte_count after = read_memory offset byte_count middle` by
    (mp_tac (Q.SPECL [`right`, `middle`, `after`, `offset`, `byte_count`] abi_writer_frame_read) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `read_memory offset byte_count middle = read_memory offset byte_count before` by
    (mp_tac (Q.SPECL [`left`, `before`, `middle`, `offset`, `byte_count`] abi_writer_frame_read) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >> simp[]
QED

Theorem abi_writer_separated_window:
  !writers ss read_offset read_len id offset byte_count.
    abi_writer_separated writers ss read_offset read_len /\ MEM id writers /\
    abi_allocated_window ss id offset byte_count ==>
    abi_window_separated read_offset read_len offset byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_allocated_window _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP ss.vs_allocas id = SOME (window_base,window_size)` >>
  `abi_window_separated read_offset read_len window_base window_size` by
    (qpat_x_assum `abi_writer_separated _ _ _ _`
       (mp_tac o REWRITE_RULE [abi_writer_separated_def]) >>
     disch_then (qspecl_then [`id`, `window_base`, `window_size`] mp_tac) >> simp[]) >>
  drule_all abi_window_separated_subwindow >> simp[]
QED

Theorem abi_writer_frame_windows:
  !writers windows before after.
    EVERY (\window. MEM (FST window) writers /\
      abi_allocated_window after (FST window) (FST (SND window)) (SND (SND window))) windows /\
    abi_memory_frame (MAP SND windows) before after ==>
    abi_writer_frame writers before after
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_writer_frame_def] >> rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`MAP SND (windows:(num # (num # num)) list)`, `before`, `after`, `offset`, `byte_count`]
    abi_memory_frame_read) >> impl_tac >- (
    conj_tac >- first_assum MATCH_ACCEPT_TAC >>
    simp_tac (srw_ss()) [EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    MAP_EVERY qx_gen_tac [`id`, `write_base`, `write_count`] >> DISCH_TAC >>
    `MEM id writers /\ abi_allocated_window after id write_base write_count` by
      (qpat_x_assum `EVERY _ windows` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
       disch_then (qspec_then `(id,(write_base,write_count))` mp_tac) >> simp[]) >>
    drule_all abi_writer_separated_window >> simp[]) >> simp[]
QED

Theorem allocation_growth_window:
  !before after id offset byte_count.
    allocation_growth before after /\ abi_allocated_window before id offset byte_count ==>
    abi_allocated_window after id offset byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_allocated_window _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP before.vs_allocas id = SOME (window_base,window_size)` >>
  simp_tac bool_ss [abi_allocated_window_def] >> qexistsl_tac [`window_base`, `window_size`] >>
  rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >> drule_all allocation_growth_old >> simp[]
QED

Theorem abi_writer_separated_allocation:
  !writers ss read_id offset byte_count.
    allocas_non_overlapping ss /\ ~MEM read_id writers /\ abi_allocated_window ss read_id offset byte_count ==>
    abi_writer_separated writers ss offset byte_count
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_writer_separated_def] >> rpt gen_tac >> strip_tac >>
  `read_id <> id` by (strip_tac >> gvs[]) >>
  `abi_allocated_window ss id region_base region_size` by
    (simp_tac bool_ss [abi_allocated_window_def] >> qexistsl_tac [`region_base`, `region_size`] >> simp[]) >>
  mp_tac (Q.SPECL [`ss`, `(read_id,(offset,byte_count))`, `(id,(region_base,region_size))`]
    abi_allocated_window_disjoint) >> impl_tac >- simp[] >> simp[abi_window_separated_def]
QED

Theorem abi_writer_frame_allocation:
  !writers before after read_id offset byte_count.
    allocation_growth before after /\ allocas_non_overlapping after /\ abi_writer_frame writers before after /\
    ~MEM read_id writers /\ abi_allocated_window before read_id offset byte_count ==>
    read_memory offset byte_count after = read_memory offset byte_count before
Proof
  rpt gen_tac >> strip_tac >> drule_all allocation_growth_window >> DISCH_TAC >>
  drule_all abi_writer_separated_allocation >> DISCH_TAC >> drule_all abi_writer_frame_read >> simp[]
QED

Theorem abi_writer_separated_prefix:
  !writers before after offset byte_count.
    allocation_growth before after /\ offset + byte_count <= before.vs_alloca_next /\
    (!id region_base region_size. MEM id writers /\ FLOOKUP before.vs_allocas id = SOME (region_base,region_size) ==>
      offset + byte_count <= region_base) ==>
    abi_writer_separated writers after offset byte_count
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_writer_separated_def] >> rpt gen_tac >> strip_tac >>
  `offset + byte_count <= region_base` by (
    Cases_on `FLOOKUP before.vs_allocas id`
    >- (drule_all allocation_growth_new >> DISCH_TAC >> decide_tac) >>
    rename1 `FLOOKUP before.vs_allocas id = SOME allocation` >>
    `FLOOKUP after.vs_allocas id = SOME allocation` by (drule_all allocation_growth_old >> simp[]) >>
    `allocation = (region_base,region_size)` by fs[] >> gvs[] >>
    qpat_x_assum `!id region_base region_size. _` (qspecl_then [`id`, `region_base`, `region_size`] mp_tac) >> simp[]) >>
  simp[abi_window_separated_def, compileEnvTheory.regions_disjoint_def]
QED

Theorem abi_writer_frame_prefix:
  !writers before after offset byte_count.
    allocation_growth before after /\ abi_writer_frame writers before after /\
    offset + byte_count <= before.vs_alloca_next /\
    (!id region_base region_size. MEM id writers /\ FLOOKUP before.vs_allocas id = SOME (region_base,region_size) ==>
      offset + byte_count <= region_base) ==>
    read_memory offset byte_count after = read_memory offset byte_count before
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_writer_separated_prefix >> DISCH_TAC >>
  drule_all abi_writer_frame_read >> simp[]
QED
