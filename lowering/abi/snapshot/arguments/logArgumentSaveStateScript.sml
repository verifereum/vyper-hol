(* TOP-LEVEL: saving the next Log argument extends the retained prefix
   while preserving source state, local backing and the allocation floor.
   Snapshot privacy follows from the profile's floor and real compiler
   allocation provenance, including cached allocations. *)
Theory logArgumentSaveState
Ancestors
  snapshotSourceState sourceAllocationPrivacy logArgumentLoadFrame
  logArgumentSnapshotFrame typedLogArgs allocationGrowth abiAllocatedWindows
  abiAllocationFrame abiFieldOperands abiStateFrame memoryValueSnapshot
  sourceMemoryFrames valueLoadProps compileVyper vyperTypeContract vyperContext
  stmtLowering context compileEnv vyperTypeInvariants vyperExprEffects
  fragExec fragBlockPath venomState list pair words arithmetic

Theorem checked_log_argument_save_state:
  !tops dep layouts addr art ctx func cenv cx es ty tv v src suffix cs op cs' ss prefix ptvs pvs ids.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\
    compile_log_save_arg cenv ty src suffix cs = (op,cs') /\
    lowered_value_rel ty tv v src ss /\ abi_operand_before cs.cs_next_var src /\
    state_well_typed es /\ state_rel_simple cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    fn_inst_ids_distinct func /\ source_alloca_floor cenv es.scopes ids ss /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==>
      abi_operand_before cs.cs_next_var (Var p)) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> abi_operand_before cs.cs_next_var (Var x)) /\
    alloca_inv ss /\ log_args_rel prefix ptvs pvs ss /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) prefix /\
    (~is_word_type ty /\ exprs_can_mutate cenv suffix ==>
      ss.vs_alloca_next + type_memory_size tv < dimword(:256) /\
      abi_alloca_request_ok cs.cs_next_id (type_memory_size tv) ss /\
      log_args_safe prefix ptvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv) /\
      MEM cs.cs_next_id ids) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      state_rel_simple cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      source_alloca_floor cenv es.scopes ids out /\
      log_args_rel (prefix ++ [(op,ty)]) (ptvs ++ [tv]) (pvs ++ [v]) out /\
      EVERY (\arg. abi_operand_before cs'.cs_next_var (FST arg)) (prefix ++ [(op,ty)]) /\
      (fresh_vars_wrt cs ss ==> fresh_vars_wrt cs' out) /\ alloca_inv out /\
      abi_state_frame ss out /\ allocation_growth ss out /\
      (is_word_type ty \/ ~exprs_can_mutate cenv suffix ==> out = ss) /\ cs.cs_next_var <= cs'.cs_next_var /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      (~is_word_type ty /\ exprs_can_mutate cenv suffix ==>
        eval_operand op out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
        abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv) /\
        out.vs_allocas = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_allocas /\
        out.vs_alloca_next = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_alloca_next /\
        ss.vs_alloca_next <= out.vs_alloca_next /\ out.vs_alloca_next <= ss.vs_alloca_next + type_memory_size tv)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `~is_word_type ty /\ exprs_can_mutate cenv suffix ==>
    !name entry offset region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= w2n (memory_snapshot_addr cs.cs_next_id ss)` by
    (strip_tac >>
     qpat_x_assum `_ ==> _ /\ abi_alloca_request_ok _ _ _ /\ _` mp_tac >>
     asm_simp_tac bool_ss [] >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
     `ss.vs_alloca_next < dimword(:256)` by decide_tac >>
     qspecl_then [`cenv`, `es.scopes`, `ids`, `ss`, `cs.cs_next_id`] mp_tac source_alloca_floor_snapshot >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `~is_word_type ty /\ exprs_can_mutate cenv suffix ==>
    ss.vs_alloca_next + type_memory_size tv < dimword(:256) /\
    abi_alloca_request_ok cs.cs_next_id (type_memory_size tv) ss /\
    log_args_safe prefix ptvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)` by
    (strip_tac >> first_x_assum drule_all >> simp[]) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `cx`, `es`, `ty`, `tv`, `v`,
    `src`, `suffix`, `cs`, `op`, `cs'`, `ss`, `prefix`, `ptvs`, `pvs`]
    mp_tac checked_compile_log_save_arg_allocated_state >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `source_alloca_floor cenv es.scopes ids out` by (drule_all source_alloca_floor_growth >> simp[]) >>
  `log_args_rel (prefix ++ [(op,ty)]) (ptvs ++ [tv]) (pvs ++ [v]) out` by
    (drule_all log_args_rel_snoc >> simp[]) >>
  `EVERY (\arg. abi_operand_before cs'.cs_next_var (FST arg)) prefix` by
    (irule log_args_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss [EVERY_APPEND, EVERY_DEF, FST] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
