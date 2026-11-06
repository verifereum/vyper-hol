(* TOP-LEVEL: one argument advances the list invariant from the ordinary
   expression-lowering IH. The actual save and preservation of the old
   prefix are supplied by the proved reserved-step theorem. *)
Theory logArgumentListStep
Ancestors
  logArgumentListContract logArgumentReservedStep logArgumentSourceTypes
  logArgumentExecution
  logArgumentWriters logArgumentCode compileAppendProps compileAllocaProfiles
  logArgumentOrigins logArgumentBackingFrames sourceAllocationPrivacy sourceMemoryFrames
  allocationGrowth abiAllocationWindows abiMemoryFrame abiRequestCredit abiFieldOperands typedLogArgs
  compileAllocaProvenance compileIdFlow compileVyper vyperTypeContract vyperContext
  exprLowering stmtLowering context compileEnv vyperTypeInvariants vyperExprEffects
  vyperInterpreter fragExec venomMemDefs venomState list pair words arithmetic pred_set

Theorem log_argument_prefix_advance:
  !tops dep layouts addr art env ctx func cenv cx ids reserved requests final_cut charge
    e suffix cs src load_cut saved save_cut tv es es1 v before credit prefix ptvs pvs.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ fn_inst_ids_distinct func /\
    log_prefix_ready env cx cenv func ids reserved requests final_cut (e::suffix)
      cs es before credit prefix ptvs pvs /\
    log_argument_lowering tops env ctx func cenv cx ids reserved requests final_cut charge e /\
    eval_argument cx e es = (INL v,es1) /\ charge e es <= credit /\
    lower_value compile_expr cenv (expr_type e) e cs = (src,load_cut) /\
    compile_log_save_arg cenv (lowered_value_type cenv e) src suffix load_cut = (saved,save_cut) /\
    evaluate_type (type_env tops) (lowered_value_type cenv e) = SOME tv /\
    type_memory_size tv < dimword(:256) /\
    (!request. MEM request (compiler_alloca_requests cs load_cut) ==> MEM request requests) /\
    cs_extends cs load_cut /\ cs_extends save_cut final_cut /\
    fn_has_code cs load_cut func /\ fn_has_code load_cut save_cut func /\ fn_has_code save_cut final_cut func /\
    (~is_word_type (lowered_value_type cenv e) /\ ~EVERY pure_expr suffix ==>
      MEM (load_cut.cs_next_id,type_memory_size tv) requests /\ MEM load_cut.cs_next_id ids) ==>
    ?out. fragment_path ctx func before out /\ out.vs_halted = before.vs_halted /\
      allocation_growth before out /\ cs.cs_next_var <= save_cut.cs_next_var /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op before) /\
      log_prefix_ready env cx cenv func ids reserved requests final_cut suffix save_cut es1 out
        (credit - charge e es) (prefix ++ [(saved,lowered_value_type cenv e)]) (ptvs ++ [tv]) (pvs ++ [v])
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `log_argument_lowering tops env ctx func cenv cx ids reserved requests final_cut charge e`
    (mp_tac o REWRITE_RULE [log_argument_lowering_def]) >>
  disch_then (qspecl_then [`suffix`, `cs`, `src`, `load_cut`, `saved`, `save_cut`, `tv`, `es`, `es1`, `v`,
    `before`, `credit`, `prefix`, `ptvs`, `pvs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `loaded` (qx_choose_then `writes` ASSUME_TAC)) >>
  qpat_x_assum `log_prefix_ready env cx cenv func ids reserved requests final_cut (e::suffix) cs es before credit prefix ptvs pvs`
    (strip_assume_tac o REWRITE_RULE [log_prefix_ready_def]) >>
  qpat_x_assum `log_argument_load_certificate env ctx func cenv cx es es1 e tv v src suffix cs load_cut save_cut final_cut before loaded reserved requests (credit - charge e es) writes`
    (strip_assume_tac o REWRITE_RULE [log_argument_load_certificate_def]) >>
  `source_writes_separated cenv es.scopes before (abi_allocation_windows (compiler_alloca_ids cs final_cut) loaded)` by
    (qspecl_then [`func`, `cenv`, `es.scopes`, `ids`, `compiler_alloca_ids cs final_cut`, `before`, `loaded`]
      mp_tac log_argument_writers_private >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ctx`, `func`, `cenv`, `cx`, `es`, `es1`, `e`, `tv`, `v`,
    `src`, `suffix`, `cs`, `load_cut`, `saved`, `save_cut`, `final_cut`, `before`, `loaded`, `prefix`, `ptvs`, `pvs`,
    `ids`, `reserved`, `requests`, `credit - charge e es`, `writes`] mp_tac checked_log_argument_reserved_step >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `cs_extends load_cut save_cut` by
    (qspecl_then [`compile_log_save_arg cenv (lowered_value_type cenv e) src suffix`, `load_cut`, `saved`, `save_cut`]
      mp_tac cs_appends_result_extends >> simp[cs_appends_compile_log_save_arg]) >>
  `cs_extends cs save_cut` by (irule cs_extends_trans >> qexists_tac `load_cut` >> simp[]) >>
  `!id. MEM id (compiler_alloca_ids save_cut final_cut) ==> MEM id (compiler_alloca_ids cs final_cut)` by
    (qspecl_then [`cs`, `save_cut`, `final_cut`, `final_cut`] mp_tac compiler_alloca_profile_subprofile >>
     simp[cs_extends_refl, SUBSET_DEF]) >>
  `log_argument_writers func cenv es1.scopes ids (compiler_alloca_ids save_cut final_cut)` by
    (qspecl_then [`env`, `cx`, `es`, `es1`, `func`, `cenv`, `ids`, `compiler_alloca_ids cs final_cut`,
       `compiler_alloca_ids save_cut final_cut`] mp_tac log_argument_writers_transport >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `!name entry p region_size. lookup_scopes name es1.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before save_cut.cs_next_var (Var p)` by
    (qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `cs.cs_next_var`, `save_cut.cs_next_var`]
      mp_tac source_pointer_lifetimes_consistent_scopes >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qexists_tac `out` >> simp_tac bool_ss [log_prefix_ready_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
