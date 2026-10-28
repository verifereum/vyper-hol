(* TOP-LEVEL: execute the real argument save using a reservation and
   pointer provenance. The resulting prefix retains values, origins,
   source state and unused allocation credit for the next argument. *)
Theory logArgumentReservedSave
Ancestors
  logArgumentSaveState logArgumentSaveResources logArgumentOrigins
  logArgumentSnapshotBacking logArgumentBacking abiRequestCredit abiRequestTrace
  sourceAllocationPrivacy sourceMemoryFrames abiAllocatedWindows abiStateFrame
  allocationGrowth typedLogArgs abiFieldOperands memoryValueSnapshot
  compileAllocaProvenance compileIdFlow compileVyper vyperTypeContract vyperContext
  stmtLowering context compileEnv vyperTypeInvariants vyperExprEffects
  fragExec fragBlockPath venomState list pair words

Theorem checked_log_argument_reserved_save:
  !tops dep layouts addr art env ctx func cenv cx es ty tv v src suffix cs saved cut final_cut
    ss prefix ptvs pvs ids reserved requests credit.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\
    compile_log_save_arg cenv ty src suffix cs = (saved,cut) /\
    lowered_value_rel ty tv v src ss /\ abi_operand_before cs.cs_next_var src /\
    env_scopes_consistent env cx es /\ state_well_typed es /\ state_rel_simple cenv cx es ss /\
    local_ptrs_rel func cenv es.scopes ss /\ fn_inst_ids_distinct func /\ compiler_id_history cs /\
    source_alloca_floor cenv es.scopes ids ss /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==>
      abi_operand_before cs.cs_next_var (Var p)) /\
    alloca_inv ss /\ log_args_rel prefix ptvs pvs ss /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) prefix /\
    log_args_origins cenv es.scopes ss (compiler_alloca_ids cs final_cut) (EVERY pure_expr suffix) prefix ptvs /\
    (~is_word_type ty /\ EVERY pure_expr suffix ==> !src_addr. eval_operand src ss = SOME src_addr ==>
      argument_origin cenv es.scopes ss (compiler_alloca_ids cut final_cut) T (w2n src_addr) (type_memory_size tv)) /\
    abi_request_credit reserved requests credit ss /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      MEM (cs.cs_next_id,type_memory_size tv) requests /\ MEM cs.cs_next_id ids) /\
    fn_has_code cs cut func /\ cs_extends cut final_cut /\ fn_has_code cut final_cut func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cut.cs_current_bb /\ out.vs_inst_idx = LENGTH cut.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v saved out /\
      state_rel_simple cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      source_alloca_floor cenv es.scopes ids out /\
      log_args_rel (prefix ++ [(saved,ty)]) (ptvs ++ [tv]) (pvs ++ [v]) out /\
      EVERY (\arg. abi_operand_before cut.cs_next_var (FST arg)) (prefix ++ [(saved,ty)]) /\
      log_args_origins cenv es.scopes out (compiler_alloca_ids cut final_cut) (EVERY pure_expr suffix)
        (prefix ++ [(saved,ty)]) (ptvs ++ [tv]) /\
      abi_request_trace requests ss out /\ abi_request_credit reserved requests credit out /\
      (fresh_vars_wrt cs ss ==> fresh_vars_wrt cut out) /\ alloca_inv out /\
      abi_state_frame ss out /\ allocation_growth ss out /\ cs.cs_next_var <= cut.cs_next_var /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      (is_word_type ty \/ EVERY pure_expr suffix ==> out = ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qspecl_then [`cenv`, `ty`, `src`, `suffix`, `cs`, `saved`, `cut`, `final_cut`]
    mp_tac compile_log_save_arg_remaining_profile >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `~is_word_type ty /\ ~EVERY pure_expr suffix ==>
    ss.vs_alloca_next + type_memory_size tv < dimword(:256) /\
    abi_alloca_request_ok cs.cs_next_id (type_memory_size tv) ss /\
    log_args_safe prefix ptvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)` by
    (qspecl_then [`prefix`, `ptvs`, `cenv`, `es.scopes`, `ss`, `compiler_alloca_ids cs final_cut`,
       `ty`, `tv`, `suffix`, `cs`, `reserved`, `requests`, `credit`] mp_tac log_argument_reserved_snapshot_safe >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, fs[]]) >> simp[]) >>
  `~is_word_type ty /\ ~EVERY pure_expr suffix ==>
    ss.vs_alloca_next + type_memory_size tv < dimword(:256) /\
    abi_alloca_request_ok cs.cs_next_id (type_memory_size tv) ss /\
    log_args_safe prefix ptvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv) /\ MEM cs.cs_next_id ids` by
    (strip_tac >> rpt conj_tac >> fs[]) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `cx`, `es`, `ty`, `tv`, `v`,
    `src`, `suffix`, `cs`, `saved`, `cut`, `ss`, `prefix`, `ptvs`, `pvs`, `ids`] mp_tac checked_log_argument_save_state >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `abi_request_trace requests ss out` by
    (qspecl_then [`requests`, `ty`, `tv`, `suffix`, `cs`, `ss`, `out`] mp_tac log_argument_save_request_trace >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, fs[]]) >> simp[]) >>
  `abi_request_credit reserved requests credit out` by (drule_all abi_request_trace_credit >> simp[]) >>
  `~is_word_type ty ==> !saved_addr. eval_operand saved out = SOME saved_addr ==>
    argument_origin cenv es.scopes out (compiler_alloca_ids cut final_cut)
      (EVERY pure_expr suffix) (w2n saved_addr) (type_memory_size tv)` by
    (qspecl_then [`func`, `cenv`, `es.scopes`, `ty`, `src`, `suffix`, `cs`, `saved`, `cut`, `final_cut`,
       `ss`, `out`, `ids`, `type_memory_size tv`] mp_tac compile_log_save_arg_value_origin >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, fs[]]) >> simp[]) >>
  `!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p out = lookup_var p ss` by
    (MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`] >> strip_tac >>
     `abi_operand_before cs.cs_next_var (Var p)` by
       (qpat_x_assum `!name entry p region_size. _ ==> abi_operand_before _ _`
         (qspecl_then [`name`, `entry`, `p`, `region_size`] mp_tac) >> simp[]) >>
     qpat_x_assum `!arg_op. _` (qspec_then `Var p` mp_tac) >> simp[eval_operand_def]) >>
  `EVERY (\arg. eval_operand (FST arg) out = eval_operand (FST arg) ss) prefix` by
    (simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `arg` >> DISCH_TAC >>
     qpat_x_assum `!arg_op. _` irule >> fs[EVERY_MEM]) >>
  `log_args_origins cenv es.scopes out (compiler_alloca_ids cut final_cut) (EVERY pure_expr suffix) prefix ptvs` by
    (qspecl_then [`prefix`, `ptvs`, `env`, `cx`, `es`, `es`, `cenv`, `ss`, `out`, `compiler_alloca_ids cs final_cut`,
       `compiler_alloca_ids cut final_cut`, `EVERY pure_expr suffix`, `EVERY pure_expr suffix`]
       mp_tac log_args_origins_consistent_growth >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> simp[]) >>
  `log_args_origins cenv es.scopes out (compiler_alloca_ids cut final_cut) (EVERY pure_expr suffix)
    (prefix ++ [(saved,ty)]) (ptvs ++ [tv])` by (irule log_args_origins_snoc >> simp[]) >>
  qexists_tac `out` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed reserved execution of Log argument save: " ^ name)
  end) (DB.thms "logArgumentReservedSave")
