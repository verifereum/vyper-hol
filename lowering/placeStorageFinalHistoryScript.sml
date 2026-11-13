(* Allocation history at the final, storage-only compiler prefix. *)
Theory placeStorageFinalHistory
Ancestors
  placeStorageControlCounted placeStorageLayoutCounted placeStorageElementPaths
  stmtSimStoreCopy allocaHistory fragExec venomInst venomState
  list rich_list

Theorem alloca_history_allocation_free_prefix[local]:
  alloca_history fn s /\ t.vs_allocas = s.vs_allocas /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code bb.bb_instructions /\ t.vs_inst_idx = LENGTH code /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) code ==>
  alloca_history fn t
Proof
  simp[alloca_history_def] >> strip_tac >>
  rpt strip_tac >> gvs[IS_PREFIX_APPEND, get_instruction_def] >>
  fs[EL_APPEND_EQN, EVERY_EL] >> metis_tac[]
QED

Theorem dyn_storage_final_prefix[local]:
  compile_dynarray_to_storage src dst ew em tr sa = ((),sb) ==>
  EVERY (\inst. inst.inst_opcode <> ALLOCA) sb.cs_current_insts
Proof
  strip_tac >> Cases_on `ew = 1`
  >- (gvs[] >> drule dyn_storage_word_layout >>
      Cases_on `tr` >> simp[mk_inst_def]) >>
  drule_all dyn_storage_multi_split >> strip_tac >>
  drule dyn_storage_suffix_layout >>
  Cases_on `tr` >> simp[mk_inst_def]
QED

Theorem dyn_storage_endpoint_history:
  compile_dynarray_to_storage src dst ew em tr sa = ((),sb) /\
  fn_has_code sa sb fn /\ alloca_history fn s /\
  t.vs_allocas = s.vs_allocas /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  alloca_history fn t
Proof
  strip_tac >> drule dyn_storage_final_prefix >> strip_tac >>
  fs[fn_has_code_def] >>
  irule alloca_history_allocation_free_prefix >>
  metis_tac[]
QED

Theorem dyn_storage_normalized_history:
  compile_dynarray_to_storage src dst ew em tr sa = ((),sb) /\
  fn_has_code sa sb fn /\ alloca_history fn s /\
  store_copy_normalize s t =
    (if tr then tstore d v else sstore d v)
      (FOLDL (\a j. store_copy_prefix
        (if tr then LocTransient else LocStorage)
        (p+n2w (32+j*stride)) (d+n2w (1+j*ew)) a ew)
        s (COUNT_LIST n)) /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  alloca_history fn t
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas` suffices_by
    metis_tac[dyn_storage_endpoint_history] >>
  qmatch_asmsub_abbrev_tac `store_copy_normalize s t = h` >>
  `h.vs_allocas = s.vs_allocas` by
    (qabbrev_tac `H = \i. FOLDL (\a j. store_copy_prefix
       (if tr then LocTransient else LocStorage)
       (p+n2w (32+j*stride)) (d+n2w (1+j*ew)) a ew) s (COUNT_LIST i)` >>
     `!j. (H j).vs_allocas = s.vs_allocas` by
       (irule (cj 2 storage_element_fold_fields) >>
        simp[Abbr `H`] >> metis_tac[]) >>
     Cases_on `tr` >> fs[Abbr `h`, Abbr `H`, sstore_def, tstore_def]) >>
  qpat_x_assum `store_copy_normalize s t = h` mp_tac >>
  disch_then (mp_tac o Q.AP_TERM `(\a. a.vs_allocas)`) >>
  simp[store_copy_normalize_def]
QED
