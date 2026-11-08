(* TOP-LEVEL: combine an expression-lowering induction result with the
   actual Log save. Earlier argument values follow from write frames;
   snapshot safety follows from origins and reserved allocation space.
   The expression may change source state and consume allocation credit. *)
Theory logArgumentReservedStep
Ancestors
  logArgumentLoadOrigins logArgumentReservedSave logArgumentOrigins logArgumentBackingFrames logArgumentIdFlow
  sourceAllocationPrivacy sourceMemoryFrames allocationGrowth abiAllocationWindows abiMemoryFrame
  abiRequestCredit abiFieldOperands typedLogArgs abiFlatRun compileAllocaProfiles
  compileAllocaProvenance compileIdFlow compileVyper vyperTypeContract vyperContext
  exprLowering stmtLowering context compileEnv vyperTypeInvariants vyperExprEffects
  fragExec fragBlockPath venomMemDefs venomState list pair words arithmetic pred_set

Theorem checked_log_argument_reserved_step:
  !tops dep layouts addr art env ctx func cenv cx es es1 e tv v src suffix
    cs load_cut saved save_cut final_cut before loaded prefix ptvs pvs ids
    reserved requests remaining_credit semantic_writes.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) (lowered_value_type cenv e) = SOME tv /\
    lower_value compile_expr cenv (expr_type e) e cs = (src,load_cut) /\
    compile_log_save_arg cenv (lowered_value_type cenv e) src suffix load_cut = (saved,save_cut) /\
    cs_extends cs load_cut /\ cs_extends save_cut final_cut /\
    compiler_id_history load_cut /\ fn_inst_ids_distinct func /\
    fn_has_code load_cut save_cut func /\ fn_has_code save_cut final_cut func /\
    fragment_path ctx func before loaded /\
    loaded.vs_current_bb = load_cut.cs_current_bb /\ loaded.vs_inst_idx = LENGTH load_cut.cs_current_insts /\
    loaded.vs_halted = before.vs_halted /\
    lowered_value_rel (lowered_value_type cenv e) tv v src loaded /\ abi_operand_before load_cut.cs_next_var src /\
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    state_well_typed es1 /\ state_rel_simple cenv cx es1 loaded /\ local_ptrs_rel func cenv es1.scopes loaded /\
    local_ptrs_rel func cenv es.scopes before /\ source_alloca_floor cenv es.scopes ids before /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> abi_operand_before cs.cs_next_var (Var x)) /\
    alloca_inv before /\ alloca_inv loaded /\ allocation_growth before loaded /\ cs.cs_next_var <= load_cut.cs_next_var /\
    (fresh_vars_wrt cs before ==> fresh_vars_wrt load_cut loaded) /\
    (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op loaded = eval_operand arg_op before) /\
    log_args_rel prefix ptvs pvs before /\ EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) prefix /\
    log_args_origins cenv es.scopes before (compiler_alloca_ids cs final_cut) (~exprs_can_mutate cenv (e::suffix)) prefix ptvs /\
    source_writes_contained cenv es.scopes before semantic_writes /\
    (~exprs_can_mutate cenv (e::suffix) ==> semantic_writes = []) /\
    source_writes_separated cenv es.scopes before (abi_allocation_windows (compiler_alloca_ids cs final_cut) loaded) /\
    abi_memory_frame (semantic_writes ++ abi_allocation_windows (compiler_alloca_ids cs final_cut) loaded ++
      [(before.vs_alloca_next,loaded.vs_alloca_next - before.vs_alloca_next)]) before loaded /\
    (~is_word_type (lowered_value_type cenv e) /\ ~exprs_can_mutate cenv suffix ==> !src_addr.
      eval_operand src loaded = SOME src_addr ==>
      argument_origin cenv es1.scopes loaded (compiler_alloca_ids save_cut final_cut) T
        (w2n src_addr) (type_memory_size tv)) /\
    abi_request_credit reserved requests remaining_credit loaded /\
    (~is_word_type (lowered_value_type cenv e) /\ exprs_can_mutate cenv suffix ==>
      MEM (load_cut.cs_next_id,type_memory_size tv) requests /\ MEM load_cut.cs_next_id ids) ==>
    ?out.
      comp_bind (lower_value compile_expr cenv (expr_type e) e)
        (\op. compile_log_save_arg cenv (lowered_value_type cenv e) op suffix) cs = (saved,save_cut) /\
      fragment_path ctx func before out /\
      out.vs_current_bb = save_cut.cs_current_bb /\ out.vs_inst_idx = LENGTH save_cut.cs_current_insts /\
      out.vs_halted = before.vs_halted /\ lowered_value_rel (lowered_value_type cenv e) tv v saved out /\
      state_rel_simple cenv cx es1 out /\ local_ptrs_rel func cenv es1.scopes out /\
      source_alloca_floor cenv es1.scopes ids out /\
      log_args_rel (prefix ++ [(saved,lowered_value_type cenv e)]) (ptvs ++ [tv]) (pvs ++ [v]) out /\
      EVERY (\arg. abi_operand_before save_cut.cs_next_var (FST arg)) (prefix ++ [(saved,lowered_value_type cenv e)]) /\
      log_args_origins cenv es1.scopes out (compiler_alloca_ids save_cut final_cut) (~exprs_can_mutate cenv suffix)
        (prefix ++ [(saved,lowered_value_type cenv e)]) (ptvs ++ [tv]) /\
      abi_request_credit reserved requests remaining_credit out /\
      (fresh_vars_wrt cs before ==> fresh_vars_wrt save_cut out) /\ alloca_inv out /\
      allocation_growth before out /\ cs.cs_next_var <= save_cut.cs_next_var /\
      compiler_id_history save_cut /\ load_cut.cs_next_id <= save_cut.cs_next_id /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op before)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all compile_log_save_arg_id_history >> strip_tac >>
  `!id. MEM id (compiler_alloca_ids load_cut final_cut) ==> MEM id (compiler_alloca_ids cs final_cut)` by
    (qspecl_then [`cs`, `load_cut`, `final_cut`, `final_cut`] mp_tac compiler_alloca_profile_subprofile >>
     simp[cs_extends_refl, SUBSET_DEF]) >>
  `allocas_non_overlapping loaded` by fs[alloca_inv_def] >>
  qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `func`, `ids`, `prefix`, `ptvs`, `pvs`, `before`, `loaded`,
    `compiler_alloca_ids cs final_cut`, `compiler_alloca_ids load_cut final_cut`, `~exprs_can_mutate cenv (e::suffix)`,
    `~exprs_can_mutate cenv suffix`, `cs.cs_next_var`, `load_cut.cs_next_var`, `semantic_writes`]
    mp_tac log_argument_load_origins_state >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[EVERY_DEF]]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==> abi_operand_before load_cut.cs_next_var (Var x)` by
    (rpt strip_tac >> MATCH_MP_TAC abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >>
     conj_tac >- (qpat_x_assum `!x. cenv.ce_imm_alloca = SOME (Var x) ==> _` irule >>
                  first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ctx`, `func`, `cenv`, `cx`, `es1`,
    `lowered_value_type cenv e`, `tv`, `v`, `src`, `suffix`, `load_cut`, `saved`, `save_cut`, `final_cut`,
    `loaded`, `prefix`, `ptvs`, `pvs`, `ids`, `reserved`, `requests`, `remaining_credit`]
    mp_tac checked_log_argument_reserved_save >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `fragment_path ctx func before out` by
    (irule fragment_path_trans >> qexists_tac `loaded` >> simp[]) >>
  `allocation_growth before out` by
    (irule allocation_growth_trans >> qexists_tac `loaded` >> simp[]) >>
  qspecl_then [`cs.cs_next_var`, `load_cut.cs_next_var`, `before`, `loaded`, `out`]
    mp_tac abi_operand_before_frame_trans >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `fresh_vars_wrt cs before ==> fresh_vars_wrt save_cut out` by
    (DISCH_TAC >> `fresh_vars_wrt load_cut loaded` by
       (qpat_x_assum `fresh_vars_wrt cs before ==> _` irule >> first_assum MATCH_ACCEPT_TAC) >>
     qpat_x_assum `fresh_vars_wrt load_cut loaded ==> _` irule >> first_assum MATCH_ACCEPT_TAC) >>
  qexists_tac `out` >> asm_simp_tac bool_ss [comp_bind_def, LET_THM] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[] >> decide_tac]
QED
