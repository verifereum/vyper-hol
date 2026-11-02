(* Canonical encoder source frame. Live source regions lie below scratch
   and miss the output; no exact allocation trace or native path is used. *)
Theory logSourceFrame
Ancestors
  logDataPacking sourceLogFrames sourceMemoryFrames sourceValueFrames
  localPtrsProps memoryValueFrame memoryValueTyping abiFieldOperands
  abiBufferAllocationPath allocationGrowth abiStateFrame memoryValueSnapshot
  compileEnv vyperTypeEnv vyperTypeInvariants vyperState venomState venomMemDefs valueLoadProps
  finite_map list words arithmetic

Definition log_source_regions_def:
  log_source_regions st lo outs cenv scopes before <=>
    (!name entry p sz. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
      not_fresh_at st p) /\
    (!name entry offset sz. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset sz) ==>
      offset + type_memory_size entry.type <= lo /\
      EVERY (\(b,n). regions_disjoint (offset,type_memory_size entry.type) (b,n)) outs) /\
    (!name b sz. local_region cenv scopes before name b sz ==>
      b+sz <= lo /\ EVERY (\(d,n). regions_disjoint (b,sz) (d,n)) outs)
End

Theorem log_public_vars_rel:
  state_well_typed es /\ vars_rel cenv es.scopes before /\
  log_source_regions st lo outs cenv es.scopes before /\
  log_packing_public_frame st lo outs before after ==>
  vars_rel cenv es.scopes after
Proof
  strip_tac >>
  `EVERY scope_well_typed es.scopes` by fs[state_well_typed_def] >>
  simp_tac bool_ss [vars_rel_def] >> rpt strip_tac >>
  drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  drule_all vars_rel_memloc_value >> strip_tac >>
  drule value_has_type_val_wf >> strip_tac >>
  irule memory_value_rel_mem_agree_region >> simp[] >>
  qexistsl_tac [`type_memory_size entry.type`,`before.vs_memory`] >>
  fs[state_well_typed_def, log_source_regions_def, log_packing_public_frame_def] >>
  metis_tac[]
QED

Theorem log_source_frontier_fields[simp]:
  lookup_var p (s with vs_alloca_next := lo) = lookup_var p s /\
  (local_region cenv scopes (s with vs_alloca_next := lo) name b sz <=>
   local_region cenv scopes s name b sz) /\
  (local_backed func p (s with vs_alloca_next := lo) b sz <=>
   local_backed func p s b sz)
Proof
  simp[local_region_def, local_backed_def, lookup_var_def]
QED

Theorem log_local_ptrs_frontier:
  local_ptrs_rel func cenv scopes before /\
  (!name b sz. local_region cenv scopes before name b sz ==> b+sz <= lo) ==>
  local_ptrs_rel func cenv scopes (before with vs_alloca_next := lo)
Proof
  strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  simp_tac (srw_ss()) [local_ptrs_rel_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name entry p sz. _ ==> ?w. _`
        (qspecl_then [`name`,`entry`,`p`,`sz`] mp_tac) >> simp[] >>
      disch_then (qx_choose_then `w` strip_assume_tac) >>
      `local_region cenv scopes before name (w2n w) sz` by
        (simp[local_region_def] >> qexistsl_tac [`entry`,`p`,`w`] >> simp[]) >>
      qexists_tac `w` >> simp[] >> res_tac >> decide_tac) >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem log_public_local_ptrs:
  local_ptrs_rel func cenv scopes before /\
  log_source_regions st lo outs cenv scopes before /\
  log_packing_public_frame st lo outs before after ==>
  local_ptrs_rel func cenv scopes after
Proof
  strip_tac >>
  (* Normalize only the proof's reference frontier to the live-region bound.
     Cached scratch may lie above lo in the real starting allocator. *)
  `local_ptrs_rel func cenv scopes (before with vs_alloca_next := lo)` by
    (irule log_local_ptrs_frontier >> simp[] >>
     fs[log_source_regions_def] >> metis_tac[]) >>
  irule local_ptrs_rel_mem_agree >>
  qexists_tac `before with vs_alloca_next := lo` >>
  simp_tac (srw_ss()) [] >>
  qpat_x_assum `log_source_regions _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [log_source_regions_def]) >>
  qpat_x_assum `log_packing_public_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [log_packing_public_frame_def]) >>
  rpt strip_tac >> res_tac >> simp[] >>
  qpat_x_assum `local_ptrs_rel func cenv scopes before`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
  disch_then (qspecl_then [`name`,`entry`,`p`,`sz`] mp_tac) >>
  simp[] >> strip_tac >> res_tac >> simp[]
QED

Theorem log_source_regions_shrink:
  log_source_regions st lo [(dst,capacity)] cenv scopes before /\ n <= capacity ==>
  log_source_regions st lo [(dst,n)] cenv scopes before
Proof
  simp[log_source_regions_def, venomMemDefsTheory.regions_disjoint_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

Theorem log_source_regions_transport:
  log_source_regions st lo outs cenv scopes before /\
  st.cs_next_var <= cut.cs_next_var /\
  (!name entry p sz. lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p after = lookup_var p before) ==>
  log_source_regions cut lo outs cenv scopes after
Proof
  strip_tac >>
  `!name b sz. local_region cenv scopes after name b sz ==>
      local_region cenv scopes before name b sz` by
    (rpt gen_tac >> simp_tac bool_ss [local_region_def] >> strip_tac >>
     qexistsl_tac [`entry`,`p`,`w`] >> simp[] >>
     qpat_x_assum `!name entry p sz. _ ==> lookup_var p after = _`
       (qspecl_then [`name`,`entry`,`p`,`sz`] mp_tac) >> simp[]) >>
  qpat_x_assum `log_source_regions _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [log_source_regions_def]) >>
  simp_tac bool_ss [log_source_regions_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name entry p sz. _ ==> not_fresh_at st p`
        (qspecl_then [`name`,`entry`,`p`,`sz`] mp_tac) >>
      simp[not_fresh_at_def] >> rpt strip_tac >> res_tac >> decide_tac)
  >- first_assum MATCH_ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `local_region cenv scopes before name b sz` by
    (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `!name b sz. local_region cenv scopes before name b sz ==> _`
    (qspecl_then [`name`,`b`,`sz`] mp_tac) >> simp[]
QED

Theorem log_buffer_source_relations:
  !func cenv cx es before st capacity.
  state_rel_simple cenv cx es before /\ local_ptrs_rel func cenv es.scopes before /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    abi_operand_before st.cs_next_var (Var p)) ==>
  state_rel_simple cenv cx es (memory_snapshot_allocated st.cs_next_id st.cs_next_var capacity before) /\
  local_ptrs_rel func cenv es.scopes (memory_snapshot_allocated st.cs_next_id st.cs_next_var capacity before)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_state_frame before (memory_snapshot_allocated st.cs_next_id st.cs_next_var capacity before)` by
    simp[buffer_allocation_context] >>
  `allocation_growth before (memory_snapshot_allocated st.cs_next_id st.cs_next_var capacity before)` by
    (irule allocation_growth_snapshot_fields >>
     qexistsl_tac [`capacity`,`st.cs_next_id`] >> simp[buffer_allocation_context]) >>
  irule source_relations_memory_frame >> qexistsl_tac [`before`,`st.cs_next_var`] >>
  simp[buffer_allocation_context, buffer_allocation_old_operand] >>
  first_assum MATCH_ACCEPT_TAC
QED

(* Only fields actually read by state_rel_simple are needed. *)
Theorem log_public_source_relations:
  !func cenv cx es before after st lo outs events.
  state_well_typed es /\ state_rel_simple cenv cx es before /\
  local_ptrs_rel func cenv es.scopes before /\
  log_source_regions st lo outs cenv es.scopes before /\
  log_packing_public_frame st lo outs before after /\
  after.vs_tx_ctx = before.vs_tx_ctx /\
  after.vs_block_ctx = before.vs_block_ctx /\
  after.vs_immutables = before.vs_immutables /\
  after.vs_outcomes = before.vs_outcomes /\
  after.vs_logs = before.vs_logs ++ events ==>
  state_rel_simple cenv cx (es with logs := es.logs ++ events) after /\
  local_ptrs_rel func cenv es.scopes after
Proof
  rpt gen_tac >> strip_tac >>
  `vars_rel cenv es.scopes before` by fs[state_rel_simple_def] >>
  drule_all log_public_vars_rel >> strip_tac >>
  drule_all log_public_local_ptrs >> strip_tac >> simp[] >>
  fs[state_rel_simple_def, logs_rel_eq, log_packing_public_frame_def,
    storage_rel_def, transient_rel_def, immutables_rel_simple_def,
    contract_storage_def, contract_transient_def]
QED
