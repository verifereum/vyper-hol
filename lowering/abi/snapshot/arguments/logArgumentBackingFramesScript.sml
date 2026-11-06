(* TOP-LEVEL: argument backing derives separation from both source writes
   and actual allocation-profile writes. Private snapshots survive source
   mutation; source aliases survive the writes of a pure suffix. *)
Theory logArgumentBackingFrames
Ancestors
  logArgumentBacking logArgumentSourceWindows logArgumentWriteFrame
  abiAllocationWindows abiAllocatedWindows abiWriterFrame allocationGrowth abiMemoryFrame
  sourceAbiFrames sourceMemoryFrames typedLogArgs valueEncoding compileEnv venomState list pair words

Definition source_writes_contained_def:
  source_writes_contained cenv scopes ss writes <=>
    EVERY (\(region_base,write_len). write_len = 0 \/
      source_value_window cenv scopes ss region_base write_len) writes
End

Theorem private_value_window_source_writes:
  !cenv scopes ss writers offset byte_count writes.
    private_value_window cenv scopes ss writers offset byte_count /\ source_writes_contained cenv scopes ss writes ==>
    EVERY (\(dst,write_len). abi_window_separated offset byte_count dst write_len) writes
Proof
  rpt gen_tac >> strip_tac >> fs[private_value_window_def] >>
  simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >>
  MAP_EVERY qx_gen_tac [`dst`, `write_len`] >> DISCH_TAC >>
  qpat_x_assum `source_writes_contained _ _ _ _`
    (mp_tac o REWRITE_RULE [source_writes_contained_def, EVERY_MEM]) >>
  disch_then (qspec_then `(dst,write_len)` mp_tac) >> simp[] >> strip_tac
  >- simp[abi_window_separated_def] >>
  ONCE_REWRITE_TAC [abi_window_separated_sym] >> drule_all source_value_window_separated >> simp[]
QED

Theorem argument_value_window_writes:
  !cenv scopes before after writers source_ok offset byte_count semantic_writes.
    argument_value_window cenv scopes before writers source_ok offset byte_count /\
    allocation_growth before after /\ allocas_non_overlapping after /\
    source_writes_contained cenv scopes before semantic_writes /\ (source_ok ==> semantic_writes = []) /\
    source_writes_separated cenv scopes before (abi_allocation_windows writers after) ==>
    EVERY (\(dst,write_len). abi_window_separated offset byte_count dst write_len)
      (semantic_writes ++ abi_allocation_windows writers after)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `argument_value_window _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [argument_value_window_def]) >> strip_tac >|
   [simp[EVERY_MEM, FORALL_PROD, abi_window_separated_def],
    `EVERY (\(dst,write_len). abi_window_separated offset byte_count dst write_len) semantic_writes` by
      (drule_all private_value_window_source_writes >> simp[]) >>
    qpat_x_assum `private_value_window _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [private_value_window_def]) >>
    disch_then (qx_choose_then `owner` strip_assume_tac) >>
    `abi_allocated_window after owner offset byte_count` by (drule_all allocation_growth_window >> simp[]) >>
    qspecl_then [`writers`, `after`, `owner`, `offset`, `byte_count`] mp_tac abi_allocation_windows_protect_owned >>
    impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[EVERY_APPEND],
    `semantic_writes = []` by fs[] >> simp_tac (srw_ss()) [EVERY_APPEND] >>
    drule_all source_value_window_writes >> simp[]]
QED

Theorem log_args_backed_writes:
  !args tvs cenv scopes before after writers source_ok semantic_writes.
    log_args_backed cenv scopes before writers source_ok args tvs /\
    allocation_growth before after /\ allocas_non_overlapping after /\
    source_writes_contained cenv scopes before semantic_writes /\ (source_ok ==> semantic_writes = []) /\
    source_writes_separated cenv scopes before (abi_allocation_windows writers after) ==>
    log_args_writes_separated args tvs before (semantic_writes ++ abi_allocation_windows writers after)
Proof
  simp_tac bool_ss [log_args_backed_def] >>
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_writes_separated_def]) >>
  rpt gen_tac >> Cases_on `tvs` >- simp[] >>
  rename1 `LIST_REL _ (arg::rest) (tv::rest_tvs)` >> Cases_on `arg` >>
  rename1 `LIST_REL _ ((src,ty)::rest) (tv::rest_tvs)` >>
  simp_tac (srw_ss()) [log_args_writes_separated_def] >> strip_tac >> conj_tac
  >- (strip_tac >> qx_gen_tac `src_addr` >> DISCH_TAC >>
      `argument_value_window cenv scopes before writers source_ok (w2n src_addr) (type_memory_size tv)` by
        (qpat_x_assum `~is_word_type ty ==> _` mp_tac >> asm_simp_tac bool_ss [] >>
         disch_then (qspec_then `src_addr` mp_tac) >> simp[]) >>
      qspecl_then [`cenv`, `scopes`, `before`, `after`, `writers`, `source_ok`, `w2n src_addr`,
        `type_memory_size tv`, `semantic_writes`] mp_tac argument_value_window_writes >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_args_backed_execution_frame:
  !args tvs values cenv scopes before after writers source_ok semantic_writes.
    log_args_rel args tvs values before /\ log_args_backed cenv scopes before writers source_ok args tvs /\
    allocation_growth before after /\ allocas_non_overlapping after /\
    source_writes_contained cenv scopes before semantic_writes /\ (source_ok ==> semantic_writes = []) /\
    source_writes_separated cenv scopes before (abi_allocation_windows writers after) /\
    abi_memory_frame (semantic_writes ++ abi_allocation_windows writers after) before after /\
    EVERY (\arg. eval_operand (FST arg) after = eval_operand (FST arg) before) args ==>
    log_args_rel args tvs values after
Proof
  rpt gen_tac >> strip_tac >> drule_all log_args_backed_writes >> DISCH_TAC >>
  drule_all log_args_rel_write_frame >> simp[]
QED
