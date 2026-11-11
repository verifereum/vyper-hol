(* TOP-LEVEL: actual allocation records turn a compiler's computed ID
   profile into concrete scratch windows. Frames retain the local profile,
   so recursive children protect ancestor counters as well as source data.
   Helpers transport windows through allocation growth and larger profiles. *)
Theory abiAllocationWindows
Ancestors
  abiWriterFrame abiAllocatedWindows abiMemoryFrame allocationGrowth
  compileEnv venomState finite_map list pair pred_set arithmetic

Definition abi_allocation_windows_def:
  abi_allocation_windows [] (ss:venom_state) = [] /\
  abi_allocation_windows (id::ids) ss =
    case FLOOKUP ss.vs_allocas id of
      NONE => abi_allocation_windows ids ss
    | SOME window => window::abi_allocation_windows ids ss
End

Theorem abi_allocation_windows_member:
  !ids ss window.
    MEM window (abi_allocation_windows ids ss) <=>
    ?id. MEM id ids /\ FLOOKUP ss.vs_allocas id = SOME window
Proof
  Induct_on `ids` >- simp[abi_allocation_windows_def] >>
  qx_gen_tac `id` >> rpt gen_tac >> Cases_on `FLOOKUP ss.vs_allocas id` >>
  simp[abi_allocation_windows_def, RIGHT_AND_OVER_OR, EXISTS_OR_THM, EQ_SYM_EQ]
QED

Theorem abi_allocation_windows_fields:
  !ids before after.
    after.vs_allocas = before.vs_allocas ==>
    abi_allocation_windows ids after = abi_allocation_windows ids before
Proof
  Induct_on `ids` >- simp[abi_allocation_windows_def] >>
  qx_gen_tac `id` >> rpt gen_tac >> DISCH_TAC >>
  `abi_allocation_windows ids after = abi_allocation_windows ids before` by
    (first_x_assum irule >> simp[]) >> simp[abi_allocation_windows_def]
QED

Theorem abi_allocation_windows_append:
  !left right ss.
    abi_allocation_windows (left ++ right) ss =
    abi_allocation_windows left ss ++ abi_allocation_windows right ss
Proof
  Induct_on `left` >- simp[abi_allocation_windows_def] >>
  qx_gen_tac `id` >> rpt gen_tac >> Cases_on `FLOOKUP ss.vs_allocas id` >>
  simp[abi_allocation_windows_def]
QED

Theorem abi_allocation_windows_separated:
  !ids ss offset byte_count.
    EVERY (\(region_base,region_size).
      abi_window_separated offset byte_count region_base region_size)
      (abi_allocation_windows ids ss) <=>
    abi_writer_separated ids ss offset byte_count
Proof
  simp[EVERY_MEM, FORALL_PROD, abi_allocation_windows_member, abi_writer_separated_def] >> metis_tac[]
QED

Theorem abi_allocation_windows_owned:
  !ids ss region_base region_size.
    MEM (region_base,region_size) (abi_allocation_windows ids ss) ==>
    ?id. MEM id ids /\ abi_allocated_window ss id region_base region_size
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_windows_member] >>
  disch_then (qx_choose_then `id` strip_assume_tac) >> qexists_tac `id` >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  simp_tac bool_ss [abi_allocated_window_def] >>
  qexistsl_tac [`region_base`, `region_size`] >> simp[]
QED

Theorem abi_allocation_windows_growth:
  !before after small large window.
    allocation_growth before after /\ set small SUBSET set large /\
    MEM window (abi_allocation_windows small before) ==>
    MEM window (abi_allocation_windows large after)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_windows_member] >> strip_tac >>
  rename1 `FLOOKUP before.vs_allocas id = SOME window` >> Cases_on `window` >>
  rename1 `FLOOKUP before.vs_allocas id = SOME (region_base,region_size)` >>
  `FLOOKUP after.vs_allocas id = SOME (region_base,region_size)` by
    (drule_all allocation_growth_old >> simp[]) >>
  qexists_tac `id` >> fs[SUBSET_DEF]
QED

Theorem abi_memory_frame_subset:
  !small large before after.
    (!window. MEM window small ==> MEM window large) /\ abi_memory_frame small before after ==>
    abi_memory_frame large before after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_memory_frame_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum irule >> rpt strip_tac >> first_x_assum irule >>
  first_x_assum irule >> simp[]
QED

Theorem abi_allocation_windows_frame_growth:
  !recorded later small large data before after.
    allocation_growth recorded later /\ set small SUBSET set large /\
    abi_memory_frame (data::abi_allocation_windows small recorded) before after ==>
    abi_memory_frame (data::abi_allocation_windows large later) before after
Proof
  rpt gen_tac >> strip_tac >> irule abi_memory_frame_subset >>
  qexists_tac `data::abi_allocation_windows small recorded` >> conj_tac
  >- (simp_tac bool_ss [MEM] >> rpt strip_tac >> simp[] >>
      disj2_tac >> drule_all abi_allocation_windows_growth >> simp[]) >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_allocation_windows_protect_owned:
  !ids ss read_id offset byte_count.
    allocas_non_overlapping ss /\ ~MEM read_id ids /\
    abi_allocated_window ss read_id offset byte_count ==>
    EVERY (\(region_base,region_size).
      abi_window_separated offset byte_count region_base region_size)
      (abi_allocation_windows ids ss)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[abi_allocation_windows_separated] >>
  drule_all abi_writer_separated_allocation >> simp[]
QED
