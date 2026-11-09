(* TOP-LEVEL: pointer origins establish the concrete safety premise of
   actual snapshots. Canonical empty pointers and private allocated
   windows cover every argument before an impure suffix. *)
Theory logArgumentOriginSafety
Ancestors
  logArgumentOrigins logArgumentBacking typedLogArgs abiAllocatedWindows
  abiAllocationFrame abiAllocationSequence memoryValueSnapshot
  compileEnv venomMemDefs venomState list pair words arithmetic

Theorem allocated_read_window_request:
  !ss owner id offset read_len byte_count.
    abi_allocated_window ss owner offset read_len /\ owner <> id /\ alloca_inv ss /\
    abi_alloca_request_ok id byte_count ss /\ ss.vs_alloca_next + byte_count < dimword(:256) ==>
    offset + read_len < dimword(:256) /\
    loweringStateRelDefs$regions_disjoint offset read_len (w2n (memory_snapshot_addr id ss)) byte_count
Proof
  rpt gen_tac >> strip_tac >> `byte_count < dimword(:256)` by decide_tac >>
  `alloca_next_valid ss` by fs[alloca_inv_def] >>
  `offset + read_len <= ss.vs_alloca_next` by
    (qspecl_then [`ss`, `owner`, `offset`, `read_len`] mp_tac abi_allocated_window_frontier >> simp[]) >>
  qspecl_then [`id`, `byte_count`, `ss`] mp_tac abi_allocation_frame_record >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `new_base` (qx_choose_then `new_size` strip_assume_tac)) >>
  `alloca_inv (memory_snapshot_alloc_frame id byte_count ss)` by
    (irule abi_allocation_frame_inv >> simp[]) >>
  `abi_allocated_window (memory_snapshot_alloc_frame id byte_count ss) owner offset read_len` by
    (qspecl_then [`[(id,byte_count)]`, `ss`, `owner`, `offset`, `read_len`]
      mp_tac abi_allocated_window_sequence >> simp[]) >>
  `abi_allocated_window (memory_snapshot_alloc_frame id byte_count ss) id
    (w2n (memory_snapshot_addr id ss)) byte_count` by
    (simp_tac bool_ss [abi_allocated_window_def] >> qexistsl_tac [`new_base`, `new_size`] >> simp[]) >>
  `loweringStateRelDefs$regions_disjoint offset read_len (w2n (memory_snapshot_addr id ss)) byte_count` by
    (qspecl_then [`memory_snapshot_alloc_frame id byte_count ss`, `(owner,(offset,read_len))`,
      `(id,(w2n (memory_snapshot_addr id ss),byte_count))`] mp_tac abi_allocated_window_disjoint >>
     impl_tac >- gvs[alloca_inv_def] >> simp[]) >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

Theorem argument_origin_request_safe:
  !cenv scopes ss writers offset read_len id byte_count.
    argument_origin cenv scopes ss writers F offset read_len /\ MEM id writers /\ alloca_inv ss /\
    abi_alloca_request_ok id byte_count ss /\ ss.vs_alloca_next + byte_count < dimword(:256) ==>
    offset + read_len < dimword(:256) /\
    loweringStateRelDefs$regions_disjoint offset read_len (w2n (memory_snapshot_addr id ss)) byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `argument_origin _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [argument_origin_def]) >>
  simp_tac bool_ss [] >> strip_tac >|
   [simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac,
    qpat_x_assum `private_value_window _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [private_value_window_def]) >>
    disch_then (qx_choose_then `owner` strip_assume_tac) >>
    `owner <> id` by (strip_tac >> gvs[]) >>
    qspecl_then [`ss`, `owner`, `id`, `offset`, `read_len`, `byte_count`] mp_tac allocated_read_window_request >>
    impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]]
QED

Theorem log_args_origins_request_safe:
  !args tvs cenv scopes ss writers id byte_count.
    log_args_origins cenv scopes ss writers F args tvs /\ MEM id writers /\ alloca_inv ss /\
    abi_alloca_request_ok id byte_count ss /\ ss.vs_alloca_next + byte_count < dimword(:256) ==>
    log_args_safe args tvs ss (w2n (memory_snapshot_addr id ss)) byte_count
Proof
  simp_tac bool_ss [log_args_origins_def] >>
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_safe_def]) >>
  rpt gen_tac >> Cases_on `tvs` >- simp[] >>
  rename1 `LIST_REL _ (arg::rest) (tv::rest_tvs)` >> Cases_on `arg` >>
  rename1 `LIST_REL _ ((src,ty)::rest) (tv::rest_tvs)` >>
  simp_tac (srw_ss()) [log_args_safe_def] >> strip_tac >> conj_tac
  >- (simp_tac bool_ss [log_arg_safe_def] >> strip_tac >> qx_gen_tac `src_addr` >> DISCH_TAC >>
      `argument_origin cenv scopes ss writers F (w2n src_addr) (type_memory_size tv)` by
        (qpat_x_assum `~is_word_type ty ==> _` mp_tac >> asm_simp_tac bool_ss [] >>
         disch_then (qspec_then `src_addr` mp_tac) >> simp[]) >>
      qspecl_then [`cenv`, `scopes`, `ss`, `writers`, `w2n src_addr`, `type_memory_size tv`, `id`, `byte_count`]
        mp_tac argument_origin_request_safe >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  first_x_assum drule_all >> simp[]
QED
