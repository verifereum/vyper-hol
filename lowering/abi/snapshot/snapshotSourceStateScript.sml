(* TOP-LEVEL: the actual Log argument snapshot preserves the source-state
   and live-local invariants needed to evaluate the remaining arguments.
   No snapshot is required for words or a pure suffix. *)
Theory snapshotSourceState
Ancestors
  logArgumentSnapshotFrame sourceMemoryFrames allocationGrowth materializeSeparation typeLayoutProps typedCopyProducer
  typedLogArgs typedSArrayDynInvariant abiAllocationFrame abiAllocatedWindows
  abiStateFrame abiFieldOperands memoryValueSnapshot memoryValueDefs valueLoadProps
  compileVyper vyperTypeContract vyperContext compileEnv context stmtLowering
  vyperTypeInvariants vyperExprEffects fragExec fragBlockPath venomState list words arithmetic

Theorem checked_compile_log_save_arg_state:
  !tops dep layouts addr art ctx func cenv cx es ty tv v src suffix cs op cs' ss args atvs values.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\
    compile_log_save_arg cenv ty src suffix cs = (op,cs') /\
    lowered_value_rel ty tv v src ss /\ abi_operand_before cs.cs_next_var src /\
    state_well_typed es /\ state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==>
      abi_operand_before cs.cs_next_var (Var p)) /\
    alloca_inv ss /\ log_args_rel args atvs values ss /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      ss.vs_alloca_next + type_memory_size tv < dimword(:256) /\
      abi_alloca_request_ok cs.cs_next_id (type_memory_size tv) ss /\
      log_args_safe args atvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)) /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      source_memory_separated cenv es.scopes ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      state_rel cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      log_args_rel args atvs values out /\ (fresh_vars_wrt cs ss ==> fresh_vars_wrt cs' out) /\ alloca_inv out /\
      array_copy_frame tv 1 (w2n (memory_snapshot_addr cs.cs_next_id ss)) ss.vs_memory out.vs_memory /\
      abi_state_frame ss out /\ allocation_growth ss out /\
      (is_word_type ty \/ EVERY pure_expr suffix ==> out = ss) /\ cs.cs_next_var <= cs'.cs_next_var /\
      abi_operand_before cs'.cs_next_var op /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
        eval_operand op out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
        abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv) /\
        out.vs_allocas = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_allocas /\
        out.vs_alloca_next = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_alloca_next /\
        ss.vs_alloca_next <= out.vs_alloca_next /\ out.vs_alloca_next <= ss.vs_alloca_next + type_memory_size tv)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `ty`, `tv`, `v`,
    `src`, `suffix`, `cs`, `op`, `cs'`, `ss`, `args`, `atvs`, `values`] checked_compile_log_save_arg_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  Cases_on `is_word_type ty \/ EVERY pure_expr suffix`
  >- (`out = ss` by fs[] >> qexists_tac `out` >> asm_simp_tac bool_ss [] >> gvs[]) >>
  `source_memory_separated cenv es.scopes ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)` by
    (qpat_x_assum `_ ==> source_memory_separated _ _ _ _ _` mp_tac >> impl_tac >- fs[] >> simp[]) >>
  mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `ss`, `out`, `tv`, `1`,
    `w2n (memory_snapshot_addr cs.cs_next_id ss)`, `cs.cs_next_var`] source_relations_copy_frame) >>
  impl_tac >- (simp_tac bool_ss [MULT_CLAUSES] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  strip_tac >> qexists_tac `out` >> asm_simp_tac bool_ss []
QED

(* Allocation ownership discharges separation from live pointer-backed
   locals. The remaining spatial premise concerns fixed source locations. *)
Theorem checked_compile_log_save_arg_allocated_state:
  !tops dep layouts addr art ctx func cenv cx es ty tv v src suffix cs op cs' ss args atvs values.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\
    compile_log_save_arg cenv ty src suffix cs = (op,cs') /\
    lowered_value_rel ty tv v src ss /\ abi_operand_before cs.cs_next_var src /\
    state_well_typed es /\ state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    fn_inst_ids_distinct func /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==>
      abi_operand_before cs.cs_next_var (Var p)) /\
    alloca_inv ss /\ log_args_rel args atvs values ss /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      ss.vs_alloca_next + type_memory_size tv < dimword(:256) /\
      abi_alloca_request_ok cs.cs_next_id (type_memory_size tv) ss /\
      log_args_safe args atvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)) /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      !name entry offset region_size. lookup_scopes name es.scopes = SOME entry /\
        FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
        offset + type_memory_size entry.type <= w2n (memory_snapshot_addr cs.cs_next_id ss)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      state_rel cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      log_args_rel args atvs values out /\ (fresh_vars_wrt cs ss ==> fresh_vars_wrt cs' out) /\ alloca_inv out /\
      array_copy_frame tv 1 (w2n (memory_snapshot_addr cs.cs_next_id ss)) ss.vs_memory out.vs_memory /\
      abi_state_frame ss out /\ allocation_growth ss out /\
      (is_word_type ty \/ EVERY pure_expr suffix ==> out = ss) /\ cs.cs_next_var <= cs'.cs_next_var /\
      abi_operand_before cs'.cs_next_var op /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
        eval_operand op out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
        abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv) /\
        out.vs_allocas = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_allocas /\
        out.vs_alloca_next = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_alloca_next /\
        ss.vs_alloca_next <= out.vs_alloca_next /\ out.vs_alloca_next <= ss.vs_alloca_next + type_memory_size tv)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `~is_word_type ty /\ ~EVERY pure_expr suffix ==>
    source_memory_separated cenv es.scopes ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)` by
    (strip_tac >>
     qpat_x_assum `_ ==> _ /\ abi_alloca_request_ok _ _ _ /\ _` mp_tac >>
     asm_simp_tac bool_ss [] >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
     qpat_x_assum `_ ==> !name entry offset region_size. _` mp_tac >>
     asm_simp_tac bool_ss [] >> DISCH_TAC >>
     drule checked_contract_struct_args_unique >> DISCH_TAC >>
     `type_memory_bytes cenv ty = type_memory_size tv` by
       (drule_all type_memory_bytes_evaluated >> simp[]) >>
     `compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs')` by
       (qpat_x_assum `compile_log_save_arg _ _ _ _ _ = _` mp_tac >>
        asm_simp_tac bool_ss [compile_log_save_arg_def]) >>
     `ss.vs_alloca_next < dimword(:256)` by decide_tac >>
     mp_tac (Q.SPECL [`func`, `cenv`, `es.scopes`, `ss`, `ty`, `src`, `cs`, `op`, `cs'`]
       compile_materialize_source_separated) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
       asm_simp_tac bool_ss [] >> first_assum MATCH_ACCEPT_TAC]) >> simp[]) >>
  mp_tac (Q.SPECL [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `cx`, `es`, `ty`, `tv`, `v`,
    `src`, `suffix`, `cs`, `op`, `cs'`, `ss`, `args`, `atvs`, `values`] checked_compile_log_save_arg_state) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed snapshot source-state preservation: " ^ name)
  end) (DB.thms "snapshotSourceState")
