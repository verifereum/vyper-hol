(* TOP-LEVEL: saved Log arguments cannot overlap the actual payload buffer.
   This discharges log_args_safe at the boundary between argument evaluation
   and Log packing. Helpers handle source-backed and snapshot-backed ranges. *)
Theory logArgumentLogSafety
Ancestors
  logArgumentListContract logArgumentOrigins logArgumentOriginSafety logArgumentSourceWindows logArgumentBacking
  logArgumentWriters sourceAllocationPrivacy sourceMemoryFrames nameLoweringProps
  abiRequestCredit abiRequestProfile abiAllocationBudgetBounds abiAllocatedWindows abiMemoryFrame abiFieldOperands typedLogArgs
  memoryValueSnapshot compileAllocaProvenance compileEnv venomMemDefs venomState
  list pair words arithmetic

Theorem source_window_log_buffer_range[local]:
  !func cenv scopes ids ss offset read_len dst byte_count.
    local_ptrs_rel func cenv scopes ss /\ source_alloca_floor cenv scopes ids ss /\
    source_value_window cenv scopes ss offset read_len /\
    source_memory_separated cenv scopes ss dst byte_count ==>
    offset + read_len <= ss.vs_alloca_next /\
    compileEnv$regions_disjoint offset read_len dst byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_value_window _ _ _ _ _`
    (mp_tac o REWRITE_RULE [source_value_window_def]) >>
  disch_then (qx_choose_then `name` (qx_choose_then `entry`
    (qx_choose_then `region_base` (qx_choose_then `region_size` strip_assume_tac)))) >|
   [qpat_assum `source_alloca_floor _ _ _ _`
      (mp_tac o Q.SPECL [`name`, `entry`, `region_base`, `region_size`] o
        REWRITE_RULE [source_alloca_floor_def]) >> simp[] >> strip_tac >>
    qpat_assum `source_memory_separated _ _ _ _ _`
      (mp_tac o Q.SPECL [`name`, `entry`, `region_base`, `region_size`] o
        CONJUNCT1 o REWRITE_RULE [source_memory_separated_def]) >> simp[] >>
    fs[compileEnvTheory.regions_disjoint_def] >> decide_tac,
    rename1 `lookup_var p ss = SOME ptr_addr` >>
    drule_all local_ptrs_rel_value >> strip_tac >>
    qpat_assum `source_memory_separated _ _ _ _ _`
      (mp_tac o Q.SPECL [`name`, `entry`, `p`, `region_size`, `ptr_addr`] o
        CONJUNCT2 o REWRITE_RULE [source_memory_separated_def]) >>
    gvs[eval_operand_def, compileEnvTheory.regions_disjoint_def] >> decide_tac]
QED

Theorem argument_origin_log_buffer[local]:
  !func cenv scopes ids ss writers id capacity byte_count offset read_len.
    argument_origin cenv scopes ss writers T offset read_len /\
    local_ptrs_rel func cenv scopes ss /\ source_alloca_floor cenv scopes ids ss /\
    MEM id writers /\ alloca_inv ss /\ abi_alloca_request_ok id capacity ss /\
    ss.vs_alloca_next + capacity < dimword(:256) /\ byte_count <= capacity /\
    source_memory_separated cenv scopes ss (w2n (memory_snapshot_addr id ss)) byte_count ==>
    offset + read_len < dimword(:256) /\
    compileEnv$regions_disjoint offset read_len (w2n (memory_snapshot_addr id ss)) byte_count
Proof
  rpt gen_tac >> strip_tac >> Cases_on `offset = 0 /\ read_len = 0`
  >- (gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  Cases_on `private_value_window cenv scopes ss writers offset read_len`
  >- (`argument_origin cenv scopes ss writers F offset read_len` by simp[argument_origin_def] >>
      qspecl_then [`cenv`, `scopes`, `ss`, `writers`, `offset`, `read_len`, `id`, `capacity`]
        mp_tac argument_origin_request_safe >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
      simp[compileEnvTheory.regions_disjoint_def] >> strip_tac >> decide_tac) >>
  `source_value_window cenv scopes ss offset read_len` by fs[argument_origin_def] >>
  drule_all source_window_log_buffer_range >> strip_tac >>
  conj_tac >- decide_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem log_args_origins_log_buffer[local]:
  !args tvs func cenv scopes ids ss writers id capacity byte_count.
    log_args_origins cenv scopes ss writers T args tvs /\
    local_ptrs_rel func cenv scopes ss /\ source_alloca_floor cenv scopes ids ss /\
    MEM id writers /\ alloca_inv ss /\ abi_alloca_request_ok id capacity ss /\
    ss.vs_alloca_next + capacity < dimword(:256) /\ byte_count <= capacity /\
    source_memory_separated cenv scopes ss (w2n (memory_snapshot_addr id ss)) byte_count ==>
    log_args_safe args tvs ss (w2n (memory_snapshot_addr id ss)) byte_count
Proof
  simp_tac bool_ss [log_args_origins_def] >>
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_safe_def]) >>
  rpt gen_tac >> Cases_on `tvs` >- simp[] >>
  rename1 `LIST_REL _ (arg::rest) (tv::rest_tvs)` >> Cases_on `arg` >>
  rename1 `LIST_REL _ ((src,ty)::rest) (tv::rest_tvs)` >>
  simp_tac (srw_ss()) [log_args_safe_def] >> strip_tac >> conj_tac
  >- (simp_tac bool_ss [log_arg_safe_def] >> strip_tac >> qx_gen_tac `src_addr` >> DISCH_TAC >>
      `argument_origin cenv scopes ss writers T (w2n src_addr) (type_memory_size tv)` by
        (qpat_x_assum `~is_word_type ty ==> _` mp_tac >> asm_simp_tac bool_ss [] >>
         disch_then (qspec_then `src_addr` mp_tac) >> simp[]) >>
      qspecl_then [`func`, `cenv`, `scopes`, `ids`, `ss`, `writers`, `id`, `capacity`, `byte_count`,
        `w2n src_addr`, `type_memory_size tv`] mp_tac argument_origin_log_buffer >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
      simp[compileEnvTheory.regions_disjoint_def]) >>
  qpat_x_assum `!tvs func cenv scopes ids ss writers id capacity byte_count. _`
    (qspecl_then [`rest_tvs`, `func`, `cenv`, `scopes`, `ids`, `ss`, `writers`, `id`, `capacity`, `byte_count`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem log_ready_arguments_buffer_safe:
  !env cx cenv func ids reserved requests final_cut cs allocation_cs es ss credit args tvs values
    capacity buf cut byte_count.
    log_prefix_ready env cx cenv func ids reserved requests final_cut [] cs es ss credit args tvs values /\
    compile_alloc_buffer capacity allocation_cs = (buf,cut) /\ fn_has_code allocation_cs cut func /\
    fn_inst_ids_distinct func /\ cs.cs_next_var <= allocation_cs.cs_next_var /\
    MEM allocation_cs.cs_next_id (compiler_alloca_ids cs final_cut) /\
    MEM (allocation_cs.cs_next_id,capacity) requests /\ byte_count <= capacity ==>
    log_args_safe args tvs ss (w2n (memory_snapshot_addr allocation_cs.cs_next_id ss)) byte_count
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `log_prefix_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [log_prefix_ready_def]) >>
  `log_args_origins cenv es.scopes ss (compiler_alloca_ids cs final_cut) T args tvs` by fs[] >>
  `abi_request_reservation reserved requests ss` by (drule_all abi_request_credit_reservation >> simp[]) >>
  qspecl_then [`reserved`, `requests`, `allocation_cs.cs_next_id`, `capacity`, `ss`]
    mp_tac abi_request_reservation_room >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `ss.vs_alloca_next < dimword(:256)` by decide_tac >>
  `MEM allocation_cs.cs_next_id ids` by
    (qpat_x_assum `log_argument_writers _ _ _ _ _`
      (mp_tac o Q.SPEC `allocation_cs.cs_next_id` o REWRITE_RULE [log_argument_writers_def]) >> simp[]) >>
  `!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==>
    abi_operand_before allocation_cs.cs_next_var (Var p)` by
    (qspecl_then [`cenv`, `es.scopes`, `cs.cs_next_var`, `allocation_cs.cs_next_var`]
      mp_tac source_pointer_lifetimes_mono >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==> abi_operand_before allocation_cs.cs_next_var (Var x)` by
    (rpt strip_tac >> irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >>
     conj_tac >- (qpat_x_assum `!x. cenv.ce_imm_alloca = SOME (Var x) ==> _` irule >>
                  first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `source_memory_separated cenv es.scopes ss (w2n (memory_snapshot_addr allocation_cs.cs_next_id ss)) byte_count` by
    (qspecl_then [`func`, `cenv`, `es.scopes`, `ss`, `capacity`, `allocation_cs`, `buf`, `cut`, `byte_count`, `ids`]
      mp_tac compile_buffer_payload_private >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qspecl_then [`args`, `tvs`, `func`, `cenv`, `es.scopes`, `ids`, `ss`, `compiler_alloca_ids cs final_cut`,
    `allocation_cs.cs_next_id`, `capacity`, `byte_count`] mp_tac log_args_origins_log_buffer >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> simp[]
QED

(* Helper: indexed-only Log still reads its byte/string topics, but writes
   no data buffer. The same saved origins bound those reads. *)
Theorem argument_origin_log_read_bound[local]:
  !func cenv scopes ids ss writers offset read_len.
    argument_origin cenv scopes ss writers T offset read_len /\
    local_ptrs_rel func cenv scopes ss /\ source_alloca_floor cenv scopes ids ss /\
    alloca_inv ss ==>
    offset + read_len <= ss.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `argument_origin _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [argument_origin_def]) >> strip_tac
  >- simp[]
  >- (fs[private_value_window_def] >>
      `alloca_next_valid ss` by fs[alloca_inv_def] >>
      drule_all abi_allocated_window_frontier >> simp[]) >>
  `source_memory_separated cenv scopes ss 0 0` by
    simp[source_memory_separated_def, compileEnvTheory.regions_disjoint_def] >>
  qspecl_then [`func`, `cenv`, `scopes`, `ids`, `ss`, `offset`, `read_len`, `0`, `0`]
    mp_tac source_window_log_buffer_range >> simp[]
QED

Theorem log_args_origins_empty_write_safe[local]:
  !args tvs func cenv scopes ids ss writers.
    log_args_origins cenv scopes ss writers T args tvs /\
    local_ptrs_rel func cenv scopes ss /\ source_alloca_floor cenv scopes ids ss /\
    alloca_inv ss /\ ss.vs_alloca_next < dimword(:256) ==>
    log_args_safe args tvs ss 0 0
Proof
  simp_tac bool_ss [log_args_origins_def] >>
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_safe_def]) >>
  rpt gen_tac >> Cases_on `tvs` >- simp[] >>
  rename1 `LIST_REL _ (arg::rest) (tv::rest_tvs)` >> Cases_on `arg` >>
  rename1 `LIST_REL _ ((src,ty)::rest) (tv::rest_tvs)` >>
  simp_tac (srw_ss()) [log_args_safe_def] >> strip_tac >> conj_tac
  >- (simp_tac bool_ss [log_arg_safe_def] >> strip_tac >> qx_gen_tac `src_addr` >> DISCH_TAC >>
      `argument_origin cenv scopes ss writers T (w2n src_addr) (type_memory_size tv)` by
        (qpat_x_assum `~is_word_type ty ==> _` mp_tac >> asm_simp_tac bool_ss [] >>
         disch_then (qspec_then `src_addr` mp_tac) >> simp[]) >>
      qspecl_then [`func`, `cenv`, `scopes`, `ids`, `ss`, `writers`,
        `w2n src_addr`, `type_memory_size tv`] mp_tac argument_origin_log_read_bound >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
      simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_ready_arguments_empty_safe:
  !env cx cenv func ids reserved requests final_cut cs es ss credit args tvs values.
    log_prefix_ready env cx cenv func ids reserved requests final_cut [] cs es ss credit args tvs values ==>
    log_args_safe args tvs ss 0 0
Proof
  rpt gen_tac >>
  disch_then (strip_assume_tac o REWRITE_RULE [log_prefix_ready_def]) >>
  `log_args_origins cenv es.scopes ss (compiler_alloca_ids cs final_cut) T args tvs` by fs[] >>
  `abi_request_reservation reserved requests ss` by (drule_all abi_request_credit_reservation >> simp[]) >>
  `ss.vs_alloca_next < dimword(:256)` by
    (qspecl_then [`reserved`, `MAP FST requests`, `ss`, `0`] mp_tac abi_alloca_budget_request_room >>
     impl_tac >- fs[abi_request_reservation_def] >> simp[]) >>
  qspecl_then [`args`, `tvs`, `func`, `cenv`, `es.scopes`, `ids`, `ss`, `compiler_alloca_ids cs final_cut`]
    mp_tac log_args_origins_empty_write_safe >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> simp[]
QED
