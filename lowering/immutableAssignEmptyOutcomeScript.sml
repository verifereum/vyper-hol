(* Source and memory outcome of an empty deploy-time immutable assignment. *)
Theory immutableAssignEmptyOutcome
Ancestors
  immutableAssignEmpty immutableAssignState immutableAssignAdmissibility
  bodyMemoryPreds bodyAssignPlace memoryLocalRhsProps exprSimHypsDefs
  stmtSimDefs stmtLowering compileEnv loweringPosts
  vyperTypeInvariants vyperInterpreter vyperState
  immutableAssignStoreMem abiEncoderWindowSequence windowSequenceMem
  fragGasSeqMem fragGasMode allocaHistoryFragment bodyMemoryDefs
  instMemFrontier memSafeRun emitHelperProps emitHelper
  venomExecSemantics venomState venomInst valueEncodingProps
  loweringStateRelDefs finite_map list rich_list arithmetic words
  typedNormalizeStraightPathMem localPtrsProps allocaHistory valueEncodingProofs
  context exprLoweringProps fragExecMem immutableRelation
  gasOutcome gasSummary fragExec
  exprSimPopImmutableTarget stmtSimProps
  immutableAssignSource immutableWordPathMem immutableAssignSeparation
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
  `compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) (Lit 0w) sa = ((),sb) /\
   cenv' = ce` by
    (drule_all immutable_assign_empty_code >>
     disch_then (qspecl_then [`ty`,`sa`,`lc`] assume_tac) >>
     Cases_on `compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) (Lit 0w) sa` >>
     gvs[stmt_env_def,declare_stmt_local_def,comp_bind_def,
         comp_ignore_bind_def,comp_return_def]) >>
  suspend "endpoint"
QED

Resume immutable_assign_empty_stmt_mem[endpoint]:
  `immutable_value_admissible tv (default_value tv)` by
    (drule_all memory_rhs_empty_read_destination >>
     disch_then (qspec_then `es` mp_tac) >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     drule read_result_state >> strip_tac >> gvs[] >>
     irule immutable_assignment_rhs_admissible >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `val_in_memory tv (default_value tv) off (mstore off 0w s0).vs_memory /\
   32 <= type_memory_size tv` by
    (irule place_store_empty_representation >>
     simp[mstore_mem_word_at_same] >> metis_tac[]) >>
  `alloca_inv s0 /\ alloca_room ctx func s0 /\ fmp_room ctx func s0 /\
   immutable_base_zero ce s0` by fs[stmt_state_rel_def] >>
  drule_all immutable_assignment_destination >> strip_tac >>
  `off < dimword (:256) /\ off+32 <= s0.vs_alloca_next` by decide_tac >>
  `eval_operand (Lit (0w:bytes32)) s0 = SOME 0w /\
   (!x. Lit (0w:bytes32) = Var x ==> not_fresh_at sa x)` by simp[eval_operand_def] >>
  drule_all immutable_word_store_window >>
  disch_then (qx_choose_then `u` (map_every assume_tac o CONJUNCTS)) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0` by
    fs[window_seq_def] >>
  `!q k. q+k <= off \/ off+32 <= q ==>
     mem_bytes_at q k u.vs_memory = mem_bytes_at q k s0.vs_memory` by
    (rpt strip_tac >> simp[] >>
     irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  qpat_x_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s0`
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
  `immutable_value_bytes_rel tv (default_value tv)
     (mem_bytes_at off (type_memory_size tv) u.vs_memory)` by
    (irule immutable_admissible_memory_bytes >> gvs[]) >>
  `!name tv0 v0 off0. name <> id /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off0) /\
    FLOOKUP (get_source_immutables ce.ce_module imms) name = SOME (tv0,v0) ==>
    mem_bytes_at off0 (type_memory_size tv0) u.vs_memory =
    mem_bytes_at off0 (type_memory_size tv0) s0.vs_memory` by
    (mp_tac (Q.INST [`s` |-> `s0`, `t` |-> `u`, `n` |-> `32`]
       (SPEC_ALL immutable_assignment_other_regions)) >>
     impl_tac >- (simp[] >> rpt strip_tac >>
       qpat_x_assum `!q k. _ \/ _ ==> _`
         (qspecl_then [`q`, `k`] mp_tac) >> simp[ADD_COMM]) >> simp[]) >>
  `!name b sz. local_region ce es.scopes s0 name b sz ==>
     mem_bytes_at b sz s0.vs_memory = mem_bytes_at b sz u.vs_memory` by
    (mp_tac (Q.INST [`s` |-> `s0`, `t` |-> `u`, `n` |-> `32`]
       (SPEC_ALL immutable_assignment_local_regions)) >>
     impl_tac >- (simp[] >> rpt strip_tac >>
       qpat_x_assum `!q k. _ \/ _ ==> _`
         (qspecl_then [`q`, `k`] mp_tac) >> simp[ADD_COMM]) >> simp[]) >>
  `!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     lookup_var p u = lookup_var p s0` by
    (rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!p. ce.ce_imm_alloca = SOME (Var p) ==> lookup_var p u = lookup_var p s0` by
    (rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  suspend "state_fields"
QED

Resume immutable_assign_empty_stmt_mem[state_fields]:
  `alloca_inv u` by (irule alloca_inv_fields >> qexists_tac `s0` >> simp[]) >>
  `alloca_room ctx func u` by
    (irule alloca_room_fields >> qexists_tac `s0` >> simp[]) >>
  `fmp_room ctx func u` by
    (irule fmp_room_fields >> qexists_tac `s0` >> simp[]) >>
  mp_tac (Q.INST [`es` |-> `es`, `s` |-> `s0`, `es'` |-> `ee`, `t` |-> `u`,
    `id` |-> `id`, `ty` |-> `ity`, `tv` |-> `tv`, `off` |-> `off`,
    `imms` |-> `imms`, `v` |-> `default_value tv`]
    (SPEC_ALL immutable_assign_stmt_state_rel)) >>
  impl_tac >- (gvs[Abbr `ee`] >> rpt strip_tac >> gvs[] >> metis_tac[]) >> simp[]
QED

Resume immutable_assign_empty_stmt_mem[outcome]:
  qpat_x_assum `window_seq sa sb s0 u`
    (strip_assume_tac o REWRITE_RULE [window_seq_def,inst_extends_def]) >>
  `gas_marked_path T ctx func s0 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all typed_normalize_straight_mem_path >>
     disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  `?bb rest. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s0.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (fs[fn_has_code_def,IS_PREFIX_APPEND] >> gvs[] >>
     qexists_tac `l` >> simp[DROP_APPEND,SUB_PLUS]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule_all alloca_history_run_inst_seq >>
     gvs[LENGTH_APPEND]) >>
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
  gvs[lookup_var_def,LENGTH_APPEND] >> metis_tac[]
QED

Finalise immutable_assign_empty_stmt_mem
