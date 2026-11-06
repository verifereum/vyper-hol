(* TOP-LEVEL: actual compile_log_eval_all execution by argument-list
   induction. Native execution is assumed only for individual expressions;
   source-only charges bound the credit consumed along their evaluations. *)
Theory logArgumentList
Ancestors
  logArgumentListContract logArgumentListStep logArgumentCharges logArgumentCompile
  logArgumentExecution allocationGrowth abiFlatRun abiFieldOperands
  compileVyper vyperTypeContract exprLowering stmtLowering context compileEnv
  fragExec fragBlockPath venomState list pair arithmetic

Theorem log_argument_plan_compile_cons:
  !tops cenv func ids requests final_cut e suffix cs cut args.
    log_argument_plan tops cenv func ids requests final_cut (e::suffix) cs cut /\
    compile_log_eval_all cenv (e::suffix) cs = (args,cut) ==>
    ?src load_cut saved save_cut tv rest.
      lower_value compile_expr cenv (expr_type e) e cs = (src,load_cut) /\
      compile_log_save_arg cenv (lowered_value_type cenv e) src suffix load_cut = (saved,save_cut) /\
      evaluate_type (type_env tops) (lowered_value_type cenv e) = SOME tv /\
      type_memory_size tv < dimword(:256) /\
      (!request. MEM request (compiler_alloca_requests cs load_cut) ==> MEM request requests) /\
      cs_extends cs load_cut /\ cs_extends save_cut final_cut /\
      fn_has_code cs load_cut func /\ fn_has_code load_cut save_cut func /\ fn_has_code save_cut final_cut func /\
      (~is_word_type (lowered_value_type cenv e) /\ ~EVERY pure_expr suffix ==>
        MEM (load_cut.cs_next_id,type_memory_size tv) requests /\ MEM load_cut.cs_next_id ids) /\
      log_argument_plan tops cenv func ids requests final_cut suffix save_cut cut /\
      compile_log_eval_all cenv suffix save_cut = (rest,cut) /\ args = (saved,lowered_value_type cenv e)::rest
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `log_argument_plan _ _ _ _ _ _ _ _ _`
    (mp_tac o ONCE_REWRITE_RULE [log_argument_plan_def]) >>
  disch_then (qx_choose_then `src` (qx_choose_then `load_cut` (qx_choose_then `saved`
    (qx_choose_then `save_cut` (qx_choose_then `tv` strip_assume_tac))))) >>
  Cases_on `compile_log_eval_all cenv suffix save_cut` >>
  rename1 `compile_log_eval_all cenv suffix save_cut = (rest,end_cut)` >>
  gvs[Once compile_log_eval_all_def, comp_bind_def, comp_return_def, LET_THM] >>
  qexistsl_tac [`src`, `load_cut`, `saved`, `save_cut`, `tv`, `rest`] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem checked_compile_log_eval_all_reserved:
  !es_list tops dep layouts addr art env ctx func cenv cx ids reserved requests final_cut charge
    cs cut args es values es' total_charge before credit prefix ptvs pvs.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ fn_inst_ids_distinct func /\
    EVERY (log_argument_lowering tops env ctx func cenv cx ids reserved requests final_cut charge) es_list /\
    log_argument_plan tops cenv func ids requests final_cut es_list cs cut /\
    compile_log_eval_all cenv es_list cs = (args,cut) /\
    log_argument_charges charge cx es_list es values es' total_charge /\ total_charge <= credit /\
    log_prefix_ready env cx cenv func ids reserved requests final_cut es_list cs es before credit prefix ptvs pvs ==>
    ?out tvs. fragment_path ctx func before out /\ out.vs_halted = before.vs_halted /\
      LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args tvs /\
      allocation_growth before out /\ cs.cs_next_var <= cut.cs_next_var /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op before) /\
      log_prefix_ready env cx cenv func ids reserved requests final_cut [] cut es' out
        (credit - total_charge) (prefix ++ args) (ptvs ++ tvs) (pvs ++ values)
Proof
  Induct_on `es_list`
  >- (rpt gen_tac >> strip_tac >>
      gvs[log_argument_plan_def, log_argument_charges_def, Once compile_log_eval_all_def, comp_return_def] >>
      qexists_tac `before` >> simp[fragment_path_refl, allocation_growth_refl]) >>
  rpt gen_tac >> rename1 `compile_log_eval_all cenv (e::suffix) cs = (args,cut)` >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qspecl_then [`tops`, `cenv`, `func`, `ids`, `requests`, `final_cut`, `e`, `suffix`, `cs`, `cut`, `args`]
    mp_tac log_argument_plan_compile_cons >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `src` (qx_choose_then `load_cut` (qx_choose_then `saved`
    (qx_choose_then `save_cut` (qx_choose_then `tv` (qx_choose_then `rest` strip_assume_tac)))))) >>
  qpat_x_assum `log_argument_charges _ _ _ _ _ _ _`
    (mp_tac o ONCE_REWRITE_RULE [log_argument_charges_def]) >>
  disch_then (qx_choose_then `v` (qx_choose_then `middle` (qx_choose_then `vs`
    (qx_choose_then `rest_charge` strip_assume_tac)))) >>
  qpat_x_assum `EVERY _ (e::suffix)` (strip_assume_tac o REWRITE_RULE [EVERY_DEF]) >>
  `charge e es <= credit` by decide_tac >> `rest_charge <= credit - charge e es` by decide_tac >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ctx`, `func`, `cenv`, `cx`, `ids`, `reserved`,
    `requests`, `final_cut`, `charge`, `e`, `suffix`, `cs`, `src`, `load_cut`, `saved`, `save_cut`, `tv`, `es`,
    `middle`, `v`, `before`, `credit`, `prefix`, `ptvs`, `pvs`] mp_tac log_argument_prefix_advance >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `saved_state` strip_assume_tac) >>
  qpat_x_assum `!tops dep layouts addr art env ctx func cenv cx ids reserved requests final_cut charge
    cs cut args es values es' total_charge before credit prefix ptvs pvs. _`
    (qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ctx`, `func`, `cenv`, `cx`, `ids`, `reserved`,
      `requests`, `final_cut`, `charge`, `save_cut`, `cut`, `rest`, `middle`, `vs`, `es'`, `rest_charge`,
      `saved_state`, `credit - charge e es`, `prefix ++ [(saved,lowered_value_type cenv e)]`,
      `ptvs ++ [tv]`, `pvs ++ [v]`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` (qx_choose_then `tvs` strip_assume_tac)) >>
  `fragment_path ctx func before out` by (irule fragment_path_trans >> qexists_tac `saved_state` >> simp[]) >>
  `allocation_growth before out` by (irule allocation_growth_trans >> qexists_tac `saved_state` >> simp[]) >>
  qspecl_then [`cs.cs_next_var`, `save_cut.cs_next_var`, `before`, `saved_state`, `out`]
    mp_tac abi_operand_before_frame_trans >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `credit - charge e es - rest_charge = credit - total_charge` by decide_tac >>
  qexistsl_tac [`out`, `tv::tvs`] >> asm_simp_tac (srw_ss()) [GSYM APPEND_ASSOC] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac,
    qpat_x_assum `log_prefix_ready env cx cenv func ids reserved requests final_cut [] cut es' out _ _ _ _`
      (MATCH_ACCEPT_TAC o PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND, SUB_RIGHT_SUB])]
QED

Theorem checked_compile_log_arguments:
  !es_list tops dep layouts addr art env ctx func cenv cx ids reserved requests final_cut charge
    cs cut args es values es' total_charge before credit.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ fn_inst_ids_distinct func /\
    EVERY (log_argument_lowering tops env ctx func cenv cx ids reserved requests final_cut charge) es_list /\
    log_argument_plan tops cenv func ids requests final_cut es_list cs cut /\
    compile_log_eval_all cenv es_list cs = (args,cut) /\
    log_argument_charges charge cx es_list es values es' total_charge /\ total_charge <= credit /\
    log_prefix_ready env cx cenv func ids reserved requests final_cut es_list cs es before credit [] [] [] ==>
    ?out tvs. fragment_path ctx func before out /\ out.vs_halted = before.vs_halted /\
      LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args tvs /\
      log_args_rel args tvs values out /\
      log_prefix_ready env cx cenv func ids reserved requests final_cut [] cut es' out
        (credit - total_charge) args tvs values
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`es_list`, `tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ctx`, `func`, `cenv`, `cx`, `ids`,
    `reserved`, `requests`, `final_cut`, `charge`, `cs`, `cut`, `args`, `es`, `values`, `es'`, `total_charge`,
    `before`, `credit`, `[]`, `[]`, `[]`] mp_tac checked_compile_log_eval_all_reserved >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp_tac (srw_ss()) [] >> disch_then (qx_choose_then `out` (qx_choose_then `tvs` strip_assume_tac)) >>
  `log_args_rel args tvs values out` by fs[log_prefix_ready_def] >>
  qexistsl_tac [`out`, `tvs`] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
