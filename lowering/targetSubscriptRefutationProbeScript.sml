Theory targetSubscriptRefutationProbe
Ancestors
  targetSubscriptUniversalProbe targetSubscriptProbe finite_map
  vyperTypeInvariants vyperTyping vyperTypeSystem
  vyperTypeCallStackSoundness vyperTypeCallGraphSoundness
  vyperLookupStorage vyperStorageFrame vyperStorageLayoutSafety
  vyperState vyperValue vyperStorageBackend vyperContext
  compileVyper placeTypingProps
  targetPlaceSim exprSim exprSimHyps compileEnv supportedExprTraverse
Libs
  pairLib

Definition clear_source_env_def:
  clear_source_env = probe_deep_env with toplevel_vtypes :=
    FEMPTY |+ ((NONE,"outer"),Type probe_deep_type)
End

Theorem clear_source_module_code:
  !src. get_module_code probe_clear_source_context src =
    if src = NONE then SOME probe_clear_source_code else NONE
Proof
  Cases >> EVAL_TAC
QED

Theorem clear_source_context_typed:
  context_well_typed probe_clear_source_context
Proof
  EVAL_TAC
QED

Theorem clear_source_supported:
  supported_program probe_clear_source_code
Proof
  EVAL_TAC >> simp[]
QED

Theorem clear_source_env_context:
  env_context_consistent clear_source_env probe_clear_source_context
Proof
  rw[env_context_consistent_def, fn_sigs_consistent_def,
     fn_sigs_live_def, fn_sigs_declared_complete_def,
     toplevel_vtypes_complete_def, bare_globals_complete_def,
     bare_global_assignable_complete_def, flag_members_complete_def,
     clear_source_env_def, probe_deep_env_def, clear_source_module_code] >>
  gvs[probe_clear_source_code_def, FLOOKUP_UPDATE, FUNION_FEMPTY_1,
      FUNION_FEMPTY_2] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def,
    fcpLib.INDEX_CONV ``dimindex (:256)``, vyperValueTheory.type_slot_size_def] >>
  gvs[AllCaseEqs()] >> EVAL_TAC >> simp[]
QED

Theorem clear_source_callable:
  !fn fm nr args dflts ret body.
    lookup_callable_function probe_clear_source_context.in_deploy fn
      probe_clear_source_code = SOME (fm,nr,args,dflts,ret,body) ==>
    fn = "shrink" /\ fm = Nonpayable /\ nr = F /\ args = [] /\
    dflts = [] /\ ret = BaseT (UintT 256) /\
    body = [Assign (BaseTarget (TopLevelNameTarget (NONE,"outer")))
       (Builtin probe_deep_type
         (MakeArray (SOME probe_word_outer_type) (Dynamic 1)) []);
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]
Proof
  rpt gen_tac >> Cases_on `fn = "shrink"` >> EVAL_TAC >> gvs[]
QED

Theorem clear_source_functions_typed:
  functions_well_typed probe_clear_source_context
Proof
  rewrite_tac[functions_well_typed_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[clear_source_module_code] >>
  drule clear_source_callable >> strip_tac >> gvs[] >>
  qexists_tac `clear_source_env with <|fn_sigs := fn_sigs;
    bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
    toplevel_vtypes := toplevel_vtypes; flag_members := flag_members|>` >>
  qpat_x_assum `toplevel_vtypes_complete _ _` mp_tac >>
  simp[toplevel_vtypes_complete_def,
       clear_source_module_code, probe_clear_source_code_def] >>
  strip_tac >>
  `IS_SOME (lookup_var_slot_from_layout probe_clear_source_context F NONE "outer")`
    by EVAL_TAC >>
  `FLOOKUP toplevel_vtypes (NONE,"outer") = SOME (Type probe_deep_type)` by
    (first_x_assum irule >> simp[]) >>
  `!id. FLOOKUP bare_globals (NONE,id) = NONE` by
    (gen_tac >> Cases_on `FLOOKUP bare_globals (NONE,id)` >> simp[] >>
     qpat_x_assum `!src id ty. FLOOKUP bare_globals _ = _ ==> _` drule >>
     CONV_TAC (computeLib.RESTR_EVAL_CONV [``FLOOKUP``]) >> simp[]) >>
  `!id. FLOOKUP bare_global_assignable (NONE,id) = NONE` by
    (gen_tac >> Cases_on `FLOOKUP bare_global_assignable (NONE,id)` >> simp[] >>
     qpat_x_assum `!src id ty. FLOOKUP bare_global_assignable _ = _ ==> _` drule >>
     CONV_TAC (computeLib.RESTR_EVAL_CONV [``FLOOKUP``]) >> simp[]) >>
  qpat_x_assum `FLOOKUP toplevel_vtypes (NONE,"outer") = _` mp_tac >>
  qpat_x_assum `!id. FLOOKUP bare_globals _ = NONE` mp_tac >>
  qpat_x_assum `!id. FLOOKUP bare_global_assignable _ = NONE` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``FLOOKUP``]) >>
  simp[probe_deep_type_def, probe_word_outer_type_def,
       wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``,
       vyperValueTheory.type_slot_size_def]
QED

Theorem clear_source_env_consistent:
  env_consistent clear_source_env probe_clear_source_context probe_deep_source_state
Proof
  simp[env_consistent_def, clear_source_env_context] >>
  conj_tac
  >- (simp[env_scopes_consistent_def, clear_source_env_def,
           probe_deep_env_def, probe_deep_source_state_def,
           vyperStateTheory.set_storage_backend_def,
           vyperStateTheory.bind_def, vyperStateTheory.get_accounts_def,
           vyperStateTheory.update_accounts_def, vyperStateTheory.empty_state_def,
           vyperStateTheory.lookup_scopes_def]) >>
  rw[env_immutables_consistent_def, clear_source_env_def,
     probe_deep_env_def, FLOOKUP_UPDATE, clear_source_module_code] >>
  gvs[AllCaseEqs()] >>
  gvs[probe_clear_source_code_def, vyperStateTheory.find_var_decl_by_name_def] >>
  EVAL_TAC >> simp[]
QED

Theorem clear_source_storage_var_info:
  !mid name tr off tv.
    storage_var_info probe_clear_source_context mid name = SOME (tr,off,tv) <=>
    mid = NONE /\ tr = F /\ name = "outer" /\ off = 0 /\
    tv = ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1)) (Dynamic 1)
Proof
  rpt gen_tac >> Cases_on `mid` >>
  simp[storage_var_info_def] >> EVAL_TAC >>
  Cases_on `name = "outer"` >> gvs[] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem clear_source_layout_safe:
  storage_layout_safe probe_clear_source_context
Proof
  rw[storage_layout_safe_def, well_formed_layout_def,
     probe_clear_source_declared_region, clear_source_storage_var_info,
     nonreentrant_slot_separated_def, probe_clear_source_context_def,
     probe_deep_context_def, vyperContextTheory.empty_evaluation_context_def] >>
  gvs[probe_deep_layout, ranges_disjoint_def, wordsTheory.dimword_def,
      fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem clear_source_storage_well_formed:
  contract_storage_well_formed probe_clear_source_context probe_deep_source_state
Proof
  rw[contract_storage_well_formed_def, well_formed_storage_def,
     storage_var_in_range_def, clear_source_storage_var_info,
     probe_clear_source_declared_region,
     vyperStorageBackendTheory.get_storage_backend_eq] >>
  gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``slots_in_range``]) >>
  EVAL_TAC >>
  ntac 4 (simp[wordsTheory.dimword_def,
    fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC)
QED

Theorem clear_source_inv:
  expr_sim_inv probe_deep_cenv probe_clear_source_context
    clear_source_env probe_deep_source_state
Proof
  simp[expr_sim_inv_def, clear_source_env_consistent,
       clear_source_context_typed, clear_source_functions_typed,
       clear_source_storage_well_formed, clear_source_layout_safe,
       clear_source_env_def, probe_deep_env_def, clear_source_module_code,
       probe_deep_source_typed, probe_deep_source_accounts_typed] >>
  conj_tac
  >- (CONV_TAC (computeLib.RESTR_EVAL_CONV [``probe_deep_cenv``]) >> simp[]) >>
  conj_tac
  >- (CONV_TAC (computeLib.RESTR_EVAL_CONV [``probe_deep_cenv``]) >> simp[]) >>
  conj_tac
  >- (simp[probe_deep_cenv_def, build_compile_env_ce_struct_fields,
           sfields_tenv_consistent_def] >> EVAL_TAC >> simp[]) >>
  conj_tac
  >- (simp[probe_deep_cenv_def, build_compile_env_ce_struct_fields] >>
      EVAL_TAC >> simp[]) >>
  conj_tac
  >- (simp[outcomes_accounts_typed_def, probe_deep_source_state_def,
           set_storage_backend_def, bind_def, return_def, get_accounts_def,
           update_accounts_def, empty_state_def]) >>
  conj_tac
  >- (simp[probe_deep_source_state_def, set_storage_backend_def,
           bind_def, return_def, get_accounts_def, update_accounts_def,
           empty_state_def]) >>
  conj_tac
  >- (simp[vyperTypeStoragePreservationTheory.oracle_storage_ok_def,
           probe_deep_source_state_def, set_storage_backend_def,
           bind_def, return_def, get_accounts_def, update_accounts_def,
           empty_state_def]) >>
  conj_tac
  >- (simp[popped_keys_indexed_def, probe_deep_source_state_def,
           set_storage_backend_def, bind_def, return_def, get_accounts_def,
           update_accounts_def, empty_state_def]) >>
  rw[place_map_tables_agree_on_defined_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> EVAL_TAC
QED

Theorem clear_source_call_safe:
  call_evaluation_safe probe_clear_source_context [(NONE,"shrink")]
Proof
  rw[call_evaluation_safe_def] >>
  qexistsl_tac [`[((NONE,"caller"),(NONE,"shrink"))]`,
                `(NONE,"caller")`, `[]`] >>
  simp[probe_clear_source_context_def, probe_deep_context_def,
       empty_evaluation_context_def, call_stack_follows_def,
       calls_follow_call_graph_def, call_edge_rel_def] >>
  conj_tac
  >- (qspecl_then [`[(NONE,"caller");(NONE,"shrink")] : nsid list`,
                    `[((NONE,"caller"),(NONE,"shrink"))]`] mp_tac
        (GEN_ALL call_graph_acyclic_correct) >> EVAL_TAC >> simp[]) >>
  rw[functions_follow_call_graph_def, get_module_code_def] >>
  gvs[AllCaseEqs()] >> EVAL_TAC >> simp[] >>
  gvs[vyperInterpreterTheory.lookup_callable_function_def,
      probe_clear_source_code_def, vyperInterpreterTheory.lookup_function_def,
      AllCaseEqs()] >> EVAL_TAC
QED

Theorem clear_source_outer_indices_pre:
  target_indices_pre probe_deep_cenv probe_clear_source_context clear_source_env
    (SubscriptTarget probe_clear_source_bt
      (Literal (BaseT (UintT 256)) (IntL 0)))
Proof
  simp[probe_clear_source_bt_def, target_indices_pre_def, expr_body_pre_def] >>
  `call_evaluation_safe probe_clear_source_context []` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `[(NONE,"shrink")]` >> simp[clear_source_call_safe]) >>
  simp[expr_has_evm_run_thm, expr_evm_run_root_def,
       vyperTypeCallGraphTheory.int_calls_expr_def, clear_source_call_safe,
       clear_source_module_code, clear_source_supported] >>
  rpt conj_tac >> rpt strip_tac >> EVAL_TAC >> simp[]
QED

Theorem clear_source_target_env_ok:
  target_env_ok probe_deep_cenv probe_clear_source_context
Proof
  rw[target_env_ok_def, clear_source_module_code] >>
  gvs[AllCaseEqs()] >>
  gvs[probe_clear_source_code_def, find_var_decl_by_name_def, AllCaseEqs()] >>
  EVAL_TAC
QED

Theorem clear_source_outer_target_pre:
  target_pre probe_deep_cenv probe_clear_source_context clear_source_env
    (SubscriptTarget probe_clear_source_bt
      (Literal (BaseT (UintT 256)) (IntL 0))) probe_deep_source_state
Proof
  simp[target_pre_def, clear_source_inv, clear_source_target_env_ok,
       clear_source_outer_indices_pre, immutable_root_def,
       target_root_def, probe_clear_source_bt_def, clear_source_module_code] >>
  EVAL_TAC
QED

Theorem clear_source_outer_type:
  type_place_target clear_source_env
    (SubscriptTarget probe_clear_source_bt
      (Literal (BaseT (UintT 256)) (IntL 0))) =
    SOME (Type (BaseT (UintT 256)))
Proof
  EVAL_TAC >> simp[subscript_vtype_def, is_int_type_def]
QED

Theorem clear_source_outer_compile:
  compile_get_target_ptr compile_expr probe_deep_cenv
    (SubscriptTarget probe_clear_source_bt
      (Literal (BaseT (UintT 256)) (IntL 0)))
    (initial_compile_state "entry") = probe_descendant_outer
Proof
  simp[probe_descendant_outer_def, probe_clear_source_bt_def]
QED

Theorem clear_source_outer_has_code:
  fn_has_code (initial_compile_state "entry") (SND probe_descendant_outer)
    probe_descendant_outer_caller
Proof
  rewrite_tac[fragExecTheory.fn_has_code_def] >> conj_tac
  >- (EVAL_TAC >> simp[]) >>
  qexists_tac `HD probe_descendant_outer_caller.fn_blocks` >> EVAL_TAC
QED

Theorem clear_source_outer_ids_distinct:
  fn_inst_ids_distinct probe_descendant_outer_caller
Proof
  EVAL_TAC
QED

Theorem clear_source_local_ptrs_reserved:
  local_ptrs_reserved probe_deep_cenv (initial_compile_state "entry")
Proof
  EVAL_TAC >> simp[]
QED

Definition clear_outer_machine_def:
  clear_outer_machine = (init_venom_state "entry") with
    vs_accounts := probe_deep_source_state.accounts
End

Theorem clear_outer_machine_position:
  ~clear_outer_machine.vs_halted /\
  clear_outer_machine.vs_current_bb = "entry" /\
  clear_outer_machine.vs_inst_idx = 0
Proof
  EVAL_TAC
QED

Theorem clear_outer_machine_state_rel:
  state_rel probe_descendant_outer_caller probe_deep_cenv
    probe_clear_source_context probe_deep_source_state clear_outer_machine
Proof
  rewrite_tac[state_rel_def] >> rpt conj_tac >> EVAL_TAC >> simp[] >>
  rpt conj_tac >> rpt gen_tac >>
  Cases_on `name = "outer"` >> gvs[find_var_decl_by_name_def] >>
  Cases_on `name = "donor"` >> gvs[find_var_decl_by_name_def] >> EVAL_TAC >>
  rpt strip_tac >> gvs[]
QED

Theorem clear_outer_machine_alloca_room:
  !k. alloca_room (probe_descendant_ctx k)
    probe_descendant_outer_caller clear_outer_machine
Proof
  gen_tac >> irule exprLoweringPropsTheory.alloca_room_fields >>
  qexists_tac `probe_deep_empty_donor_machine` >>
  simp[probe_descendant_ctx_alloca_room] >> EVAL_TAC
QED

Theorem clear_outer_machine_stmt_state_rel:
  !k. stmt_state_rel (probe_descendant_ctx k)
    probe_descendant_outer_caller probe_deep_cenv
    probe_clear_source_context probe_deep_source_state clear_outer_machine
Proof
  gen_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       clear_outer_machine_state_rel, clear_outer_machine_alloca_room] >>
  rpt conj_tac >> EVAL_TAC >> simp[]
QED

Theorem clear_outer_endpoint_stop:
  !k s. ~s.vs_halted /\
    s.vs_current_bb = (SND probe_descendant_outer).cs_current_bb /\
    s.vs_inst_idx = LENGTH (SND probe_descendant_outer).cs_current_insts ==>
    ?fuel t. run_from fuel (probe_descendant_ctx k)
      probe_descendant_outer_caller s = Halt t
Proof
  rpt gen_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_from``]) >> strip_tac >>
  qexists_tac `0` >>
  simp[fragExecTheory.run_from_def, probe_descendant_outer_caller_def,
       venomInstTheory.mk_raw_function_def,
       venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  simp[Once venomExecSemanticsTheory.exec_block_def,
       venomInstTheory.get_instruction_def] >>
  EVAL_TAC >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >> simp[]
QED


Theorem clear_outer_concrete_abort:
  !k. ?n a u. run_from n (probe_descendant_ctx k)
    probe_descendant_outer_caller clear_outer_machine = Abort a u
Proof
  gen_tac >> qexists_tac `1` >>
  simp[fragExecTheory.run_from_def, clear_outer_machine_position,
       probe_descendant_outer_caller_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  ntac 10 (simp[Once venomExecSemanticsTheory.exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV
      [``exec_block``, ``probe_descendant_ctx``]) >>
    simp[wordsTheory.WORD_OR_CLAUSES, wordsTheory.WORD_ADD_0,
         wordsTheory.WORD_MULT_CLAUSES, wordsTheory.dimword_def,
         fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  simp[Once venomExecSemanticsTheory.exec_block_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``exec_block``, ``step_inst``, ``probe_descendant_ctx``]) >>
  pure_rewrite_tac[GSYM venomInstTheory.mk_inst_def,
       numLib.num_CONV ``1``, clear_machine_invoke] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``exec_block``, ``probe_descendant_ctx``]) >>
  ntac 3 (simp[Once venomExecSemanticsTheory.exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV
      [``exec_block``, ``probe_descendant_ctx``]) >>
    simp[wordsTheory.WORD_OR_CLAUSES, wordsTheory.WORD_ADD_0,
         wordsTheory.WORD_MULT_CLAUSES, wordsTheory.dimword_def,
         fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  simp[Once venomExecSemanticsTheory.exec_block_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``exec_block``, ``probe_descendant_ctx``]) >>
  simp_tac (srw_ss() ++ wordsLib.WORD_ss) [] >>
  ntac 2 (simp[Once venomExecSemanticsTheory.exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV
      [``exec_block``, ``probe_descendant_ctx``]) >>
    simp[wordsTheory.WORD_OR_CLAUSES, wordsTheory.WORD_ADD_0,
         wordsTheory.WORD_MULT_CLAUSES]) >>
  simp_tac (srw_ss() ++ wordsLib.WORD_ss) [] >>
  ntac 2 (simp[Once venomExecSemanticsTheory.exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV
      [``exec_block``, ``probe_descendant_ctx``]) >>
    simp[wordsTheory.WORD_OR_CLAUSES, wordsTheory.WORD_ADD_0,
         wordsTheory.WORD_MULT_CLAUSES]) >>
  simp_tac (srw_ss() ++ wordsLib.WORD_ss) [] >>
  ntac 2 (simp[Once venomExecSemanticsTheory.exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV
      [``exec_block``, ``probe_descendant_ctx``]) >>
    simp[wordsTheory.WORD_OR_CLAUSES, wordsTheory.WORD_ADD_0,
         wordsTheory.WORD_MULT_CLAUSES]) >>
  simp_tac (srw_ss() ++ wordsLib.WORD_ss) [] >>
  ntac 2 (simp[Once venomExecSemanticsTheory.exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV
      [``exec_block``, ``probe_descendant_ctx``]) >>
    simp[wordsTheory.WORD_OR_CLAUSES, wordsTheory.WORD_ADD_0,
         wordsTheory.WORD_MULT_CLAUSES]) >>
  simp_tac (srw_ss() ++ wordsLib.WORD_ss) [] >>
  ntac 2 (simp[Once venomExecSemanticsTheory.exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV
      [``exec_block``, ``probe_descendant_ctx``]) >>
    simp[wordsTheory.WORD_OR_CLAUSES, wordsTheory.WORD_ADD_0,
         wordsTheory.WORD_MULT_CLAUSES]) >>
  simp_tac (srw_ss() ++ wordsLib.WORD_ss) [] >>
  ntac 2 (simp[Once venomExecSemanticsTheory.exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV
      [``exec_block``, ``probe_descendant_ctx``]) >>
    simp[wordsTheory.WORD_OR_CLAUSES, wordsTheory.WORD_ADD_0,
         wordsTheory.WORD_MULT_CLAUSES]) >>
  simp_tac (srw_ss() ++ wordsLib.WORD_ss) [] >>
  ntac 2 (simp[Once venomExecSemanticsTheory.exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV
      [``exec_block``, ``probe_descendant_ctx``]) >>
    simp[wordsTheory.WORD_OR_CLAUSES, wordsTheory.WORD_ADD_0,
         wordsTheory.WORD_MULT_CLAUSES]) >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >> simp[]
QED

Theorem clear_outer_no_halt:
  !fuel k t. run_from fuel (probe_descendant_ctx k)
    probe_descendant_outer_caller clear_outer_machine <> Halt t
Proof
  rpt gen_tac >> qspec_then `k` strip_assume_tac clear_outer_concrete_abort >>
  drule fragExecTheory.run_from_abort_no_halt >> simp[]
QED
