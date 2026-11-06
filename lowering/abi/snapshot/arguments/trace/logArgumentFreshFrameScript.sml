(* TOP-LEVEL: retained argument values survive writes in a later fresh
   heap interval, even when a callee's allocation records are not retained
   in the caller. This is a frame rule, not a classification of callee writes. *)
Theory logArgumentFreshFrame
Ancestors
  logArgumentOrigins logArgumentBacking logArgumentBackingFrames logArgumentWriteFrame
  logArgumentSourceWindows sourceMemorySeparation sourceAllocationPrivacy
  abiAllocatedWindows abiAllocationWindows abiMemoryFrame allocationGrowth
  sourceMemoryFrames typedLogArgs compileEnv venomMemDefs venomState list pair words arithmetic

Theorem argument_origin_fresh_separated:
  !cenv scopes ss writers source_ok offset read_len dst byte_count.
    argument_origin cenv scopes ss writers source_ok offset read_len /\
    alloca_next_valid ss /\ ss.vs_alloca_next <= dst /\
    (source_ok ==> source_memory_separated cenv scopes ss dst byte_count) ==>
    abi_window_separated offset read_len dst byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `argument_origin _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [argument_origin_def]) >>
  strip_tac >- simp[abi_window_separated_def]
  >- (qpat_x_assum `private_value_window _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [private_value_window_def]) >>
      disch_then (qx_choose_then `owner` strip_assume_tac) >>
      `offset + read_len <= ss.vs_alloca_next` by
        (qspecl_then [`ss`, `owner`, `offset`, `read_len`] mp_tac abi_allocated_window_frontier >> simp[]) >>
      simp[abi_window_separated_def, compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `source_memory_separated cenv scopes ss dst byte_count` by fs[] >>
  drule_all source_value_window_separated >> simp[]
QED

Theorem source_floor_fresh_window:
  !func cenv scopes ids ss dst byte_count.
    local_ptrs_rel func cenv scopes ss /\ source_alloca_floor cenv scopes ids ss /\ ss.vs_alloca_next <= dst ==>
    source_memory_separated cenv scopes ss dst byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`func`, `cenv`, `scopes`, `ss`, `dst`, `byte_count`]
    mp_tac source_memory_separated_above_frontier >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >>
    MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
    qpat_x_assum `source_alloca_floor _ _ _ _` (mp_tac o REWRITE_RULE [source_alloca_floor_def]) >>
    disch_then (qspecl_then [`name`, `entry`, `offset`, `region_size`] mp_tac) >> simp[]) >> simp[]
QED

Theorem log_args_origins_fresh_separated:
  !args tvs cenv scopes ss writers source_ok dst byte_count.
    log_args_origins cenv scopes ss writers source_ok args tvs /\
    alloca_next_valid ss /\ ss.vs_alloca_next <= dst /\
    (source_ok ==> source_memory_separated cenv scopes ss dst byte_count) ==>
    log_args_writes_separated args tvs ss [(dst,byte_count)]
Proof
  simp_tac bool_ss [log_args_origins_def] >> Induct_on `args`
  >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_writes_separated_def]) >>
  rpt gen_tac >> Cases_on `tvs` >- simp[] >>
  rename1 `LIST_REL _ (arg::rest) (tv::rest_tvs)` >> Cases_on `arg` >>
  rename1 `LIST_REL _ ((src,ty)::rest) (tv::rest_tvs)` >>
  simp_tac (srw_ss()) [log_args_writes_separated_def] >> strip_tac >> conj_tac
  >- (strip_tac >> qx_gen_tac `src_addr` >> DISCH_TAC >>
      `argument_origin cenv scopes ss writers source_ok (w2n src_addr) (type_memory_size tv)` by
        (qpat_x_assum `~is_word_type ty ==> _` mp_tac >> asm_simp_tac bool_ss [] >>
         disch_then (qspec_then `src_addr` mp_tac) >> simp[]) >>
      qspecl_then [`cenv`, `scopes`, `ss`, `writers`, `source_ok`, `w2n src_addr`, `type_memory_size tv`, `dst`, `byte_count`]
        mp_tac argument_origin_fresh_separated >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_args_origins_fresh_execution_frame:
  !args tvs values cenv scopes before after writers source_ok semantic_writes.
    log_args_rel args tvs values before /\ log_args_origins cenv scopes before writers source_ok args tvs /\
    allocation_growth before after /\ alloca_inv before /\ allocas_non_overlapping after /\
    source_writes_contained cenv scopes before semantic_writes /\ (source_ok ==> semantic_writes = []) /\
    (source_ok ==> source_memory_separated cenv scopes before before.vs_alloca_next
      (after.vs_alloca_next - before.vs_alloca_next)) /\
    source_writes_separated cenv scopes before (abi_allocation_windows writers after) /\
    abi_memory_frame (semantic_writes ++ abi_allocation_windows writers after ++
      [(before.vs_alloca_next,after.vs_alloca_next - before.vs_alloca_next)]) before after /\
    EVERY (\arg. eval_operand (FST arg) after = eval_operand (FST arg) before) args ==>
    log_args_rel args tvs values after
Proof
  rpt gen_tac >> strip_tac >>
  `log_args_backed cenv scopes before writers source_ok args tvs` by (drule_all log_args_origins_backed >> simp[]) >>
  `log_args_writes_separated args tvs before (semantic_writes ++ abi_allocation_windows writers after)` by
    (qspecl_then [`args`, `tvs`, `cenv`, `scopes`, `before`, `after`, `writers`, `source_ok`, `semantic_writes`]
      mp_tac log_args_backed_writes >> simp[]) >>
  `alloca_next_valid before` by fs[alloca_inv_def] >>
  `log_args_writes_separated args tvs before
    [(before.vs_alloca_next,after.vs_alloca_next - before.vs_alloca_next)]` by
    (qspecl_then [`args`, `tvs`, `cenv`, `scopes`, `before`, `writers`, `source_ok`, `before.vs_alloca_next`,
       `after.vs_alloca_next - before.vs_alloca_next`] mp_tac log_args_origins_fresh_separated >> simp[]) >>
  `log_args_writes_separated args tvs before (semantic_writes ++ abi_allocation_windows writers after ++
    [(before.vs_alloca_next,after.vs_alloca_next - before.vs_alloca_next)])` by
    fs[log_args_writes_separated_append] >>
  drule_all log_args_rel_write_frame >> simp[]
QED
