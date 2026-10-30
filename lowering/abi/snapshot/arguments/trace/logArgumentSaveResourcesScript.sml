(* TOP-LEVEL: the actual save's allocator fields give a local request
   trace and preserve unused call credit. Origins and this reservation
   discharge snapshot safety; skipped saves require no allocation ID. *)
Theory logArgumentSaveResources
Ancestors
  logArgumentOrigins logArgumentOriginSafety logArgumentSnapshotBacking
  abiRequestCredit abiRequestProfile abiRequestTrace abiAllocatorState
  memoryValueSnapshot abiAllocatedWindows sourceAllocationPrivacy
  logArgumentCode compileAppendProps compileAllocaProfiles compileAllocaProvenance compileIdFlow
  stmtLowering context compileEnv fragExec venomInst venomState list pair words pred_set

Theorem compile_log_save_arg_remaining_profile:
  !cenv ty src suffix cs saved cut final_cut.
    compile_log_save_arg cenv ty src suffix cs = (saved,cut) /\
    compiler_id_history cs /\ cs_extends cut final_cut ==>
    cs_extends cs cut /\
    (!id. MEM id (compiler_alloca_ids cut final_cut) ==> MEM id (compiler_alloca_ids cs final_cut)) /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==> MEM cs.cs_next_id (compiler_alloca_ids cs final_cut))
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends cs cut` by
    (qspecl_then [`compile_log_save_arg cenv ty src suffix`, `cs`, `saved`, `cut`]
      mp_tac cs_appends_result_extends >> simp[cs_appends_compile_log_save_arg]) >>
  `!id. MEM id (compiler_alloca_ids cut final_cut) ==> MEM id (compiler_alloca_ids cs final_cut)` by
    (qspecl_then [`cs`, `cut`, `final_cut`, `final_cut`] mp_tac compiler_alloca_profile_subprofile >>
     simp[cs_extends_refl, SUBSET_DEF]) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all compile_log_save_arg_allocation_current >> DISCH_TAC >>
  qabbrev_tac `inst = mk_inst cs.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
    [compiler_var_name cs.cs_next_var 0]` >>
  `compiler_instruction_member cut inst` by simp[Abbr`inst`, compiler_instruction_member_def] >>
  `compiler_instruction_member final_cut inst` by
    (qspecl_then [`cut`, `final_cut`, `inst`] mp_tac compiler_instruction_member_extends >> simp[]) >>
  `~compiler_instruction_member cs inst` by
    (qspecl_then [`cs`, `inst`] mp_tac compiler_id_history_fresh >> simp[Abbr`inst`, mk_inst_def]) >>
  simp_tac bool_ss [compiler_alloca_ids_member] >> qexists_tac `inst` >> simp[Abbr`inst`, mk_inst_def]
QED

Theorem log_argument_save_request_trace:
  !requests ty tv suffix cs loaded out.
    (is_word_type ty \/ EVERY pure_expr suffix ==> out = loaded) /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      MEM (cs.cs_next_id,type_memory_size tv) requests /\
      out.vs_allocas = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) loaded).vs_allocas /\
      out.vs_alloca_next = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) loaded).vs_alloca_next) ==>
    abi_request_trace requests loaded out
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type ty \/ EVERY pure_expr suffix`
  >- (`out = loaded` by fs[] >> simp[abi_request_trace_identity]) >>
  `MEM (cs.cs_next_id,type_memory_size tv) requests /\
    out.vs_allocas = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) loaded).vs_allocas /\
    out.vs_alloca_next = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) loaded).vs_alloca_next` by fs[] >>
  qspecl_then [`requests`, `cs.cs_next_id`, `type_memory_size tv`, `loaded`, `out`]
    mp_tac abi_request_trace_frame >> simp[abi_allocator_state_eq]
QED

Theorem log_argument_reserved_snapshot_safe:
  !prefix ptvs cenv scopes ss writers ty tv suffix cs reserved requests credit.
    log_args_origins cenv scopes ss writers (EVERY pure_expr suffix) prefix ptvs /\
    alloca_inv ss /\ abi_request_credit reserved requests credit ss /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      MEM cs.cs_next_id writers /\ MEM (cs.cs_next_id,type_memory_size tv) requests) ==>
    ~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      ss.vs_alloca_next + type_memory_size tv < dimword(:256) /\
      abi_alloca_request_ok cs.cs_next_id (type_memory_size tv) ss /\
      log_args_safe prefix ptvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `MEM cs.cs_next_id writers /\ MEM (cs.cs_next_id,type_memory_size tv) requests` by fs[] >>
  `abi_request_reservation reserved requests ss` by (drule_all abi_request_credit_reservation >> simp[]) >>
  qspecl_then [`reserved`, `requests`, `cs.cs_next_id`, `type_memory_size tv`, `ss`]
    mp_tac abi_request_reservation_room >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `log_args_origins cenv scopes ss writers F prefix ptvs` by
    (qpat_x_assum `log_args_origins _ _ _ _ _ _ _` mp_tac >> asm_simp_tac bool_ss []) >>
  `log_args_safe prefix ptvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)` by
    (qspecl_then [`prefix`, `ptvs`, `cenv`, `scopes`, `ss`, `writers`, `cs.cs_next_id`, `type_memory_size tv`]
      mp_tac log_args_origins_request_safe >> simp[]) >> simp[]
QED

Theorem compile_log_save_arg_value_origin:
  !func cenv scopes ty src suffix cs saved cut final_cut loaded out ids byte_count.
    compile_log_save_arg cenv ty src suffix cs = (saved,cut) /\
    fn_has_code cs cut func /\ fn_inst_ids_distinct func /\
    cs_extends cut final_cut /\ fn_has_code cut final_cut func /\
    alloca_inv out /\ local_ptrs_rel func cenv scopes out /\
    source_alloca_floor cenv scopes ids out /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    (is_word_type ty \/ EVERY pure_expr suffix ==> out = loaded) /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      MEM cs.cs_next_id ids /\ ?ptr_addr. eval_operand saved out = SOME ptr_addr /\
        abi_allocated_window out cs.cs_next_id (w2n ptr_addr) byte_count) /\
    (~is_word_type ty /\ EVERY pure_expr suffix ==> !src_addr. eval_operand src loaded = SOME src_addr ==>
      argument_origin cenv scopes loaded (compiler_alloca_ids cut final_cut) T (w2n src_addr) byte_count) ==>
    ~is_word_type ty ==> !saved_addr. eval_operand saved out = SOME saved_addr ==>
      argument_origin cenv scopes out (compiler_alloca_ids cut final_cut)
        (EVERY pure_expr suffix) (w2n saved_addr) byte_count
Proof
  rpt gen_tac >> strip_tac >> DISCH_TAC >> qx_gen_tac `saved_addr` >> DISCH_TAC >>
  Cases_on `EVERY pure_expr suffix`
  >- (`out = loaded` by fs[] >>
      `saved = src` by
        (qpat_x_assum `compile_log_save_arg _ _ _ _ _ = _` mp_tac >>
         asm_simp_tac (srw_ss()) [compile_log_save_arg_def, comp_return_def]) >>
      qpat_x_assum `~is_word_type ty /\ EVERY pure_expr suffix ==> _` mp_tac >>
      asm_simp_tac bool_ss [] >> disch_then (qspec_then `saved_addr` mp_tac) >> gvs[]) >>
  `MEM cs.cs_next_id ids /\ abi_allocated_window out cs.cs_next_id (w2n saved_addr) byte_count` by
    (qpat_x_assum `~is_word_type ty /\ ~EVERY pure_expr suffix ==> _` mp_tac >>
     asm_simp_tac bool_ss [] >> strip_tac >> gvs[]) >>
  `private_value_window cenv scopes out (compiler_alloca_ids cut final_cut) (w2n saved_addr) byte_count` by
    (qspecl_then [`func`, `cenv`, `scopes`, `ty`, `src`, `suffix`, `cs`, `saved`, `cut`, `final_cut`, `out`,
       `ids`, `w2n saved_addr`, `byte_count`] mp_tac compile_log_save_arg_private_window >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  simp[argument_origin_def]
QED
