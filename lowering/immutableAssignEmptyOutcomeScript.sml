(* Source and memory outcome of an empty deploy-time immutable assignment. *)
Theory immutableAssignEmptyOutcome
Ancestors
  immutableAssignEmpty immutableAssignEmptyEndpointMem immutableAssignCode
  bodyMemoryPreds bodyAssignPlace memoryLocalRhsProps exprSimHypsDefs
  stmtSimDefs stmtLowering compileEnv loweringPosts
  vyperTypeInvariants vyperInterpreter vyperState
  immutableAssignStoreMem immutableStoreOptionPathMem immutableStoreOptionMem
  fragGasSeqMem fragGasMode bodyMemoryDefs
  instMemFrontier memSafeRun emitHelperProps emitHelper
  venomExecSemantics venomState venomInst valueEncodingProps
  loweringStateRelDefs finite_map list rich_list arithmetic words
  bodyDeclMemoryCounted localPtrsProps allocaHistory valueEncodingProofs vyperTypeValues
  context exprLoweringProps fragExecMem immutableRelation
  gasOutcome gasSummary fragExec
  immutableDeployAssignBytes immutableDeployAssignAdmissible stmtSimProps
  bodyImmutableAugAssignStore
  immutableAssignSource bodyMemAggregatePath fragGasPathFrameMem
  placeStore bodyImmutableAssignFacts
Libs monadsyntax

Theorem immutable_assign_empty_source[local]:
  env_consistent env cx es /\
  FLOOKUP env.bare_globals (src,id) = SOME ity /\
  well_typed_expr env e /\ is_empty_value_expr e /\
  has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) ity /\
  evaluate_type (get_tenv cx) ity = SOME tv /\
  imms = (case ALOOKUP es.immutables cx.txn.target of NONE => [] | SOME m => m)
  ==>
  eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) es =
    (INL (),es with immutables :=
      (cx.txn.target,set_source_immutables src
        (get_source_immutables src imms |+ (id,(tv,default_value tv))) imms) ::
      ADELKEY cx.txn.target es.immutables)
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def,env_context_consistent_def] >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL (default_value tv),es)` by
    (irule memory_rhs_empty_read_destination >> simp[] >> metis_tac[]) >>
  Cases_on `eval_expr cx e es` >>
  gvs[bind_def, AllCaseEqs()] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  mp_tac (Q.INST [`ee` |-> `es:evaluation_state`, `pv` |-> `x'`,
    `v` |-> `default_value tv`,
    `imms` |-> `(case ALOOKUP (es:evaluation_state).immutables cx.txn.target of NONE => [] | SOME m => m)`]
    (SPEC_ALL immutable_assignment_source_tail)) >>
  simp[] >> disch_then (qspec_then `es.gas_obs` assume_tac) >>
  once_rewrite_tac[evaluate_def] >> simp[bind_def] >>
  gvs[bind_def,evaluation_state_component_equality]
QED

Theorem immutable_assign_empty_stmt_mem:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  type_widens_to env.type_defs (expr_type e) ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\ ce.ce_is_ctor /\
  has_length_word (expr_type e) /\ is_empty_value_expr e ==>
  stmt_frag_mem d ctx func cx lc RetQ ce
    (stmt_env ce lc ty (Assign (BaseTarget (TopLevelNameTarget (ce.ce_module,id))) e))
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (ce.ce_module,id))) e)) es
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `env_consistent env cx es /\ well_typed_expr env e` by
    fs[expr_body_pre_def,expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def,env_context_consistent_def] >>
  `?tv old imms.
     imms = (case ALOOKUP es.immutables cx.txn.target of NONE => [] | SOME m => m) /\
     FLOOKUP (get_source_immutables ce.ce_module imms) id = SOME (tv,old) /\
     evaluate_type (get_tenv cx) ity = SOME tv` by
    (fs[env_consistent_def,env_immutables_consistent_def] >>
     gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[pairTheory.PAIR]) >>
  `has_length_word ity` by metis_tac[type_widens_to_has_length_word] >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `compile_get_target_ptr compile_expr ce (TopLevelNameTarget (ce.ce_module,id)) =
     comp_return (Lit (n2w off),SOME LocCode,SOME (ValPT ity))` by
    (simp[FUN_EQ_THM,comp_return_def] >> gen_tac >>
     irule immutable_assignment_target_lowering >> simp[]) >>
  `compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) (Lit 0w) sa = ((),sb) /\
   cenv' = ce` by
    (drule_all immutableAssignCodeTheory.immutable_assign_empty_code >>
     simp[compile_store_at_loc_def]) >>
  suspend "endpoint"
QED

Resume immutable_assign_empty_stmt_mem[endpoint]:
  `immutable_value_admissible tv (default_value tv)` by
    metis_tac[default_immutable_admissible,evaluate_type_well_formed_type_value] >>
  `val_in_memory tv (default_value tv) off (mstore off 0w s0).vs_memory /\
   32 <= type_memory_size tv` by
    (irule place_store_empty_representation >>
     simp[mstore_mem_word_at_same] >> metis_tac[]) >>
  `alloca_inv s0 /\ alloca_room ctx func s0 /\ fmp_room ctx func s0 /\
   immutable_base_zero ce s0` by fs[stmt_state_rel_def] >>
  drule_all immutable_assignment_destination >> strip_tac >>
  `off < dimword (:256) /\ off+32 <= s0.vs_alloca_next` by decide_tac >>
  mp_tac (Q.INST [`imm` |-> `ce.ce_imm_alloca`, `dst` |-> `Lit (n2w off)`,
    `value` |-> `Lit 0w`, `a` |-> `n2w off`, `v` |-> `0w`, `s` |-> `s0`]
    (SPEC_ALL immutable_store_option_path_mem)) >>
  (impl_tac >- (simp[eval_operand_def] >> fs[immutable_base_zero_def])) >>
  simp[] >>
  disch_then (qx_choose_then `u` (map_every assume_tac o CONJUNCTS)) >>
  drule immutable_store_option_code >> strip_tac >>
  `~block_is_terminated sb` by
    (Cases_on `ce.ce_imm_alloca` >>
     qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     simp[compile_imm_store_word_def,emit_op_def,emit_void_def,fresh_id_def,
       fresh_var_def,emit_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     strip_tac >> gvs[block_is_terminated_def,LAST_APPEND,mk_inst_def,is_terminator_def] >>
     Cases_on `sa.cs_current_insts` >> simp[LAST_CONS_cond,LAST_APPEND,mk_inst_def,is_terminator_def]) >>
  `!q k. q+k <= off \/ off+32 <= q ==>
     mem_bytes_at q k u.vs_memory = mem_bytes_at q k s0.vs_memory` by
    (rpt strip_tac >> simp[] >>
     irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  qpat_x_assum `_ = s0`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  qabbrev_tac `ee = es with immutables :=
    (cx.txn.target,set_source_immutables ce.ce_module
      (get_source_immutables ce.ce_module imms |+ (id,(tv,default_value tv))) imms) ::
    ADELKEY cx.txn.target es.immutables` >>
  suspend "state"
QED

Resume immutable_assign_empty_stmt_mem[state]:
  `stmt_state_rel ctx func ce cx ee u` by suspend "reconstruction" >>
  suspend "outcome"
QED

Resume immutable_assign_empty_stmt_mem[reconstruction]:
  `write_place cx (ImmutablePlace ce.ce_module id []) (default_value tv) es =
     (INL (),ee)` by
    (Cases_on `ALOOKUP es.immutables cx.txn.target`
     >- gvs[get_source_immutables_def] >>
     gvs[] >>
     drule_all immutable_augassign_write_source >>
     disch_then (qspec_then `default_value tv` mp_tac) >>
     simp[Abbr `ee`,update_immutable_def]) >>
  mp_tac (Q.INST [`s` |-> `s0`, `q` |-> `u`, `ty` |-> `ity`]
    (SPEC_ALL immutable_assign_empty_store_restore)) >>
  impl_tac >- (simp[venom_state_component_equality] >> metis_tac[]) >> simp[]
QED

Resume immutable_assign_empty_stmt_mem[outcome]:
  `gas_path_mem ctx func s0 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    fs[gas_marked_path_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (mp_tac (Q.INST [`fn` |-> `func`, `s` |-> `s0`,
       `t` |-> `u with vs_inst_idx := LENGTH sb.cs_current_insts`]
       (SPEC_ALL gas_path_mem_zero_history)) >>
     impl_tac >- (simp[] >> metis_tac[aggregate_mem_path_alloca_inv]) >> simp[]) >>
  `!tail. eval_stmt cx
    (Assign (BaseTarget (TopLevelNameTarget (ce.ce_module,id))) e)
      (es with gas_obs := tail) = (INL (),ee with gas_obs := tail)` by
    (gen_tac >>
     mp_tac (Q.INST [`es` |-> `es with gas_obs := tail`,
       `src` |-> `ce.ce_module`] (SPEC_ALL immutable_assign_empty_source)) >>
     simp[Abbr `ee`] >> metis_tac[]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `ee`, `OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[gas_marked_exec_def,stmt_lands_def,cenv_top_ext_refl,
       stmt_state_rel_inst_idx] >>
  `return_buf_frame d ce sb (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `cenv'` |-> `ce`, `s` |-> `s0`,
       `s'` |-> `u with vs_inst_idx := LENGTH sb.cs_current_insts`]
       (SPEC_ALL return_buf_frame_frame)) >>
     simp[lookup_var_def] >> fs[lookup_var_def] >> metis_tac[]) >>
  gvs[lookup_var_def,LENGTH_APPEND,same_blocks_def] >> metis_tac[]
QED

Finalise immutable_assign_empty_stmt_mem
