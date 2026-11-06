(* TOP-LEVEL: a snapshot's actual instruction supplies its concrete request
   in the enclosing emitted-code profile, including the exact evaluated
   memory size. Freshness is a compiler code fact, not a runtime-ID range. *)
Theory logArgumentSnapshotRequests
Ancestors
  compileAllocationRequests compileAllocaProvenance compileAllocaProfiles compileIdFlow
  logArgumentSnapshotBacking typeLayoutProps compileEnv stmtLowering
  fragExec venomInst list pair words

Theorem compile_log_save_arg_profile_request:
  !tops cenv ty src suffix cs saved cut profile_start final_cut tv.
    ~is_word_type ty /\ ~EVERY pure_expr suffix /\
    compile_log_save_arg cenv ty src suffix cs = (saved,cut) /\
    compiler_id_history cs /\ cs_extends profile_start cs /\ cs_extends cut final_cut /\
    struct_args_unique tops /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\ type_memory_size tv < dimword(:256) ==>
    MEM (cs.cs_next_id,type_memory_size tv) (compiler_alloca_requests profile_start final_cut) /\
    MEM cs.cs_next_id (compiler_alloca_ids profile_start final_cut)
Proof
  rpt gen_tac >> strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by (drule_all type_memory_bytes_evaluated >> simp[]) >>
  drule_all compile_log_save_arg_allocation_current >> DISCH_TAC >>
  qabbrev_tac `inst = mk_inst cs.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))]
    [compiler_var_name cs.cs_next_var 0]` >>
  `MEM inst cut.cs_current_insts` by
    (qpat_x_assum `MEM (mk_inst cs.cs_next_id ALLOCA _ _) cut.cs_current_insts`
       (mp_tac o PURE_REWRITE_RULE [ASSUME ``type_memory_bytes cenv ty = type_memory_size tv``]) >>
     simp_tac bool_ss [Abbr`inst`]) >>
  `compiler_instruction_member final_cut inst` by
    (qspecl_then [`cut`, `final_cut`, `inst`] mp_tac compiler_current_instruction_extends >> simp[]) >>
  `~compiler_instruction_member cs inst` by
    (qspecl_then [`cs`, `inst`] mp_tac compiler_id_history_fresh >> simp[Abbr`inst`, mk_inst_def]) >>
  `~compiler_instruction_member profile_start inst` by
    (DISCH_TAC >> qspecl_then [`profile_start`, `cs`, `inst`] mp_tac compiler_instruction_member_extends >> simp[]) >>
  `MEM (cs.cs_next_id,type_memory_size tv) (compiler_alloca_requests profile_start final_cut)` by
    (qspecl_then [`profile_start`, `final_cut`, `inst`, `type_memory_size tv`] mp_tac compiler_alloca_requests_literal >>
     simp[Abbr`inst`, mk_inst_def]) >>
  drule_all compiler_alloca_requests_ids >> simp[]
QED
