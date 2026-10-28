(* TOP-LEVEL: recursive calls obtain current resources from the enclosing
   encoder's computed profile and allocation trace. Actual native results
   preserve allocation ownership and fit the enclosing output/scratch frame. *)
Theory abiNativeResources
Ancestors
  abiNativeEncodingDefs abiMemoryLeafRun abiAllocationWindows abiAllocationBudgetNested
  abiAllocationTrace abiAllocationBudget abiAllocationFrame abiAllocatorState
  abiAllocatedSubwindows abiAllocatedWindows abiMemoryFrameCover
  abiMemoryFrame abiPathAllocInv allocationPathGrowth allocationGrowth
  compileAllocaProfiles compileAllocaProvenance compileIdFlow
  compileEnv venomMemDefs venomState list pair pred_set words arithmetic

Theorem abi_native_ready_allocator_state:
  !func cs cs' source_id target_id src_addr span dst_addr payload before after.
    abi_native_memory_ready func cs cs' source_id target_id src_addr span dst_addr payload before /\
    abi_allocator_state after = abi_allocator_state before ==>
    abi_native_memory_ready func cs cs' source_id target_id src_addr span dst_addr payload after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocator_state_eq] >> strip_tac >>
  fs[abi_native_memory_ready_def, abi_alloca_budget_def, abi_alloca_pending_def,
    abi_alloca_request_ok_def, abi_allocated_window_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_child_ready:
  !func before after source_id target_id root_src root_span root_dst root_payload initial
      child_before child_after current src_addr span dst_addr payload.
    abi_native_memory_ready func before after source_id target_id root_src root_span
      root_dst root_payload initial /\
    cs_extends before child_before /\ cs_extends child_after after /\
    compiler_id_history child_before /\
    abi_allocation_trace 32 (compiler_alloca_ids before after) initial current /\
    w2n root_src <= w2n src_addr /\ w2n src_addr + span <= w2n root_src + root_span /\
    w2n root_dst <= w2n dst_addr /\
    w2n dst_addr + LENGTH payload <= w2n root_dst + LENGTH root_payload ==>
    abi_native_memory_ready func child_before child_after source_id target_id
      src_addr span dst_addr payload current
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_memory_ready_def] >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `set (compiler_alloca_ids child_before child_after) SUBSET
    set (compiler_alloca_ids before after)` by
    (irule compiler_alloca_profile_subprofile >> simp[]) >>
  `alloca_inv current /\
    abi_alloca_budget 32 (compiler_alloca_ids child_before child_after) current < dimword (:256) /\
    !id. MEM id (compiler_alloca_ids child_before child_after) ==> abi_alloca_request_ok id 32 current` by
    (qspecl_then [`before`, `child_before`, `child_after`, `after`, `initial`, `current`]
       mp_tac abi_compiled_child_allocation_ready >> simp[]) >>
  `abi_allocated_window initial source_id (w2n src_addr) span` by
    (qspecl_then [`initial`, `source_id`, `w2n root_src`, `root_span`, `w2n src_addr`, `span`]
       mp_tac abi_allocated_window_subwindow >> simp[]) >>
  `abi_allocated_window initial target_id (w2n dst_addr) (LENGTH payload)` by
    (qspecl_then [`initial`, `target_id`, `w2n root_dst`, `LENGTH root_payload`,
       `w2n dst_addr`, `LENGTH payload`] mp_tac abi_allocated_window_subwindow >> simp[]) >>
  `abi_allocated_window current source_id (w2n src_addr) span` by
    (qspecl_then [`32`, `compiler_alloca_ids before after`, `initial`, `current`,
       `source_id`, `w2n src_addr`, `span`] mp_tac abi_allocation_trace_window >> simp[]) >>
  `abi_allocated_window current target_id (w2n dst_addr) (LENGTH payload)` by
    (qspecl_then [`32`, `compiler_alloca_ids before after`, `initial`, `current`,
       `target_id`, `w2n dst_addr`, `LENGTH payload`] mp_tac abi_allocation_trace_window >> simp[]) >>
  asm_simp_tac bool_ss [] >> fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem abi_native_result_allocation:
  !ctx func cs cs' ret dst_addr payload before after.
    abi_native_encoding_result ctx func cs cs' ret dst_addr payload before after /\ alloca_inv before ==>
    alloca_inv after /\ allocation_growth before after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_encoding_result_def, abi_encoding_result_def] >>
  strip_tac >> conj_tac
  >- (drule_all fragment_path_alloca_inv >> simp[]) >>
  drule_all fragment_path_allocation_growth >> simp[]
QED

Theorem abi_native_result_enclosing_frame:
  !ctx func child_before child_after ret dst_addr payload current out before after root_dst root_payload.
    abi_native_encoding_result ctx func child_before child_after ret dst_addr payload current out /\
    cs_extends before child_before /\ cs_extends child_after after /\
    w2n root_dst <= w2n dst_addr /\
    w2n dst_addr + LENGTH payload <= w2n root_dst + LENGTH root_payload ==>
    abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
      abi_allocation_windows (compiler_alloca_ids before after) out) current out
Proof
  rpt gen_tac >> strip_tac >>
  `set (compiler_alloca_ids child_before child_after) SUBSET
    set (compiler_alloca_ids before after)` by
    (irule compiler_alloca_profile_subprofile >> simp[]) >>
  qpat_x_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  irule abi_memory_frame_cover >>
  qexists_tac `(w2n dst_addr,LENGTH payload)::
    abi_allocation_windows (compiler_alloca_ids child_before child_after) out` >>
  conj_tac >- (
    simp_tac bool_ss [abi_writes_cover_def, MEM] >>
    MAP_EVERY qx_gen_tac [`write_base`, `write_count`] >> strip_tac
    >- (gvs[] >> qexistsl_tac [`w2n root_dst`, `LENGTH root_payload`] >> simp[]) >>
    qexistsl_tac [`write_base`, `write_count`] >> simp[] >>
    qspecl_then [`out`, `out`, `compiler_alloca_ids child_before child_after`,
      `compiler_alloca_ids before after`, `(write_base,write_count)`]
      mp_tac abi_allocation_windows_growth >> simp[]) >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_encoding_result_scratch_subset:
  !ctx func cs cs' ret dst_addr payload small large before after.
    abi_encoding_result ctx func cs cs' ret dst_addr payload small before after /\
    (!window. MEM window small ==> MEM window large) ==>
    abi_encoding_result ctx func cs cs' ret dst_addr payload large before after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_encoding_result_def] >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `abi_memory_frame ((w2n dst_addr,LENGTH payload)::large) before after` by
    (irule abi_memory_frame_subset >>
     qexists_tac `(w2n dst_addr,LENGTH payload)::small` >> simp[MEM] >>
     rpt strip_tac >> simp[] >> disj2_tac >> first_x_assum irule >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_allocation_scratch_subset:
  !recorded later small large extra.
    allocation_growth recorded later /\ set small SUBSET set large ==>
    !window. MEM window (abi_allocation_windows small recorded ++ extra) ==>
      MEM window (abi_allocation_windows large later ++ extra)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [MEM_APPEND] >>
  qx_gen_tac `window` >> strip_tac
  >- (disj1_tac >> drule_all abi_allocation_windows_growth >> simp[]) >> simp[]
QED

Theorem abi_native_result_enclosing_trace:
  !ctx func child_before child_after ret dst_addr payload current out before after initial.
    abi_native_encoding_result ctx func child_before child_after ret dst_addr payload current out /\
    cs_extends before child_before /\ cs_extends child_after after /\
    abi_allocation_trace 32 (compiler_alloca_ids before after) initial current ==>
    abi_allocation_trace 32 (compiler_alloca_ids before after) initial out
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_encoding_result_def] >> strip_tac >>
  `set (compiler_alloca_ids child_before child_after) SUBSET
    set (compiler_alloca_ids before after)` by
    (irule compiler_alloca_profile_subprofile >> simp[]) >>
  `abi_allocation_trace 32 (compiler_alloca_ids before after) current out` by
    (drule_all abi_allocation_trace_weaken >> simp[]) >>
  irule abi_allocation_trace_trans >> qexists_tac `current` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native recursive allocation resources: " ^ name)
  end) (DB.thms "abiNativeResources")
