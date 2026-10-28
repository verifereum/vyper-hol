(* TOP-LEVEL: windows backed by distinct allocation records are pairwise
   disjoint. Reuse the existing allocation-map theorem for arbitrary
   subwindows, including source fields within larger aggregate buffers. *)
Theory abiAllocatedWindows
Ancestors
  abiBytestringAllocation abiAllocationSequence compileEnv venomMemDefs venomState finite_map list pair words arithmetic

Definition abi_allocated_window_def:
  abi_allocated_window ss id offset byte_count <=>
    ?allocation_base allocation_size.
      FLOOKUP ss.vs_allocas id = SOME (allocation_base,allocation_size) /\
      allocation_base <= offset /\ offset + byte_count <= allocation_base + allocation_size
End

Definition abi_windows_disjoint_def:
  abi_windows_disjoint [] = T /\
  abi_windows_disjoint (window::windows) =
    (EVERY (\other. compileEnv$regions_disjoint
      (FST (SND window)) (SND (SND window)) (FST (SND other)) (SND (SND other))) windows /\
     abi_windows_disjoint windows)
End

Theorem abi_allocated_window_sequence:
  !allocations ss id offset byte_count.
    abi_allocated_window ss id offset byte_count ==>
    abi_allocated_window (abi_allocation_sequence allocations ss) id offset byte_count
Proof
  rpt gen_tac >> DISCH_TAC >>
  qpat_x_assum `abi_allocated_window _ _ _ _` (strip_assume_tac o REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP ss.vs_allocas id = SOME (window_base,window_size)` >>
  simp_tac bool_ss [abi_allocated_window_def] >> qexistsl_tac [`window_base`, `window_size`] >>
  rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >>
  irule abi_allocation_sequence_lookup_old >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_allocated_window_shrink:
  !ss id offset byte_count smaller.
    abi_allocated_window ss id offset byte_count /\ smaller <= byte_count ==>
    abi_allocated_window ss id offset smaller
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_allocated_window _ _ _ _` (strip_assume_tac o REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP ss.vs_allocas id = SOME (window_base,window_size)` >>
  simp_tac bool_ss [abi_allocated_window_def] >> qexistsl_tac [`window_base`, `window_size`] >>
  simp[] >> decide_tac
QED

Theorem abi_allocated_window_frontier:
  !ss id offset byte_count.
    alloca_next_valid ss /\ abi_allocated_window ss id offset byte_count ==>
    offset + byte_count <= ss.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_allocated_window _ _ _ _` (strip_assume_tac o REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP ss.vs_allocas id = SOME (window_base,window_size)` >>
  qpat_x_assum `alloca_next_valid ss` (mp_tac o REWRITE_RULE [alloca_next_valid_def]) >>
  disch_then (qspecl_then [`id`, `window_base`, `window_size`] mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> decide_tac
QED

Theorem abi_allocated_window_disjoint:
  !ss left right.
    allocas_non_overlapping ss /\ FST left <> FST right /\
    abi_allocated_window ss (FST left) (FST (SND left)) (SND (SND left)) /\
    abi_allocated_window ss (FST right) (FST (SND right)) (SND (SND right)) ==>
    compileEnv$regions_disjoint (FST (SND left)) (SND (SND left)) (FST (SND right)) (SND (SND right))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_allocated_window ss (FST left) _ _`
    (strip_assume_tac o REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP ss.vs_allocas (FST left) = SOME (left_base,left_size)` >>
  qpat_x_assum `abi_allocated_window ss (FST right) _ _`
    (strip_assume_tac o REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP ss.vs_allocas (FST right) = SOME (right_base,right_size)` >>
  mp_tac (Q.SPECL [`ss`, `FST (left:num # (num # num))`, `FST (right:num # (num # num))`,
    `left_base`, `left_size`, `right_base`, `right_size`,
    `FST (SND (left:num # (num # num)))`, `SND (SND (left:num # (num # num)))`,
    `FST (SND (right:num # (num # num)))`, `SND (SND (right:num # (num # num)))`]
    allocated_windows_disjoint) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp[compileEnvTheory.regions_disjoint_def]
QED

Theorem abi_allocated_windows_pairwise:
  !windows ss.
    allocas_non_overlapping ss /\ ALL_DISTINCT (MAP FST windows) /\
    EVERY (\window. abi_allocated_window ss (FST window) (FST (SND window)) (SND (SND window))) windows ==>
    abi_windows_disjoint windows
Proof
  Induct_on `windows` >- simp[abi_windows_disjoint_def] >> qx_gen_tac `window` >> rpt gen_tac >>
  simp_tac bool_ss [MAP, ALL_DISTINCT, EVERY_DEF, abi_windows_disjoint_def] >> strip_tac >> conj_tac
  >- (simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `other` >> DISCH_TAC >>
      `FST window <> FST other` by
        (strip_tac >> qpat_x_assum `~MEM _ (MAP FST windows)` mp_tac >>
         simp[MEM_MAP] >> qexists_tac `other` >> simp[]) >>
      `abi_allocated_window ss (FST other) (FST (SND other)) (SND (SND other))` by fs[EVERY_MEM] >>
      mp_tac (Q.SPECL [`ss`, `window:num # (num # num)`, `other:num # (num # num)`]
        abi_allocated_window_disjoint) >> impl_tac >- simp[] >> simp[]) >>
  first_x_assum (qspec_then `ss` mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI allocation-backed window separation: " ^ name)
  end) (DB.thms "abiAllocatedWindows")
