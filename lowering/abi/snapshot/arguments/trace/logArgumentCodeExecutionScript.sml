(* TOP-LEVEL: execute compiled Log arguments using the actual emitted
   allocation profile. The recursive compiler plan is derived here;
   expression execution and its source charge remain the expression IH. *)
Theory logArgumentCodeExecution
Ancestors
  logArgumentPlan logArgumentList logArgumentListContract logArgumentCharges
  compileAllocationRequests compileAllocaProvenance compileIdFlow compileAppendProps
  typedLogArgs typedCopyProducer compileVyper vyperTypeContract exprLowering stmtLowering context compileEnv
  fragExec list pair words

Theorem checked_compile_log_arguments_from_code:
  !es_list layout_tvs tops dep layouts addr art env ctx func cenv cx ids reserved requests final_cut charge
    cs cut args es values es' total_charge before credit.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ fn_inst_ids_distinct func /\
    ids = compiler_alloca_ids cs final_cut /\ requests = compiler_alloca_requests cs final_cut /\
    EVERY (\e. cs_appends (lower_value compile_expr cenv (expr_type e) e)) es_list /\
    EVERY (\e. compiler_id_flow (lower_value compile_expr cenv (expr_type e) e)) es_list /\
    LIST_REL (\e tv. evaluate_type (type_env tops) (lowered_value_type cenv e) = SOME tv /\
      type_memory_size tv < dimword(:256)) es_list layout_tvs /\
    EVERY (log_argument_lowering tops env ctx func cenv cx ids reserved requests final_cut charge) es_list /\
    compile_log_eval_all cenv es_list cs = (args,cut) /\ cs_extends cut final_cut /\ fn_has_code cs final_cut func /\
    log_argument_charges charge cx es_list es values es' total_charge /\ total_charge <= credit /\
    log_prefix_ready env cx cenv func ids reserved requests final_cut es_list cs es before credit [] [] [] ==>
    ?out tvs. fragment_path ctx func before out /\ out.vs_halted = before.vs_halted /\
      LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args tvs /\
      log_args_rel args tvs values out /\
      log_prefix_ready env cx cenv func ids reserved requests final_cut [] cut es' out
        (credit - total_charge) args tvs values
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `struct_args_unique tops` by (drule checked_contract_struct_args_unique >> simp[]) >>
  `compiler_id_history cs` by fs[log_prefix_ready_def] >>
  `log_argument_plan tops cenv func ids requests final_cut es_list cs cut` by
    (asm_simp_tac bool_ss [] >>
     qspecl_then [`es_list`, `layout_tvs`, `tops`, `cenv`, `func`, `cs`, `cs`, `args`, `cut`, `final_cut`]
       mp_tac compile_log_eval_all_plan >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[cs_extends_refl]]) >> simp[]) >>
  drule_all checked_compile_log_arguments >> simp[]
QED
