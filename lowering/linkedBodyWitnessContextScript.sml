(* The installed fixture's constructor and selected external entry contexts. *)
Theory linkedBodyWitnessContext
Ancestors
  e2eModsWitness e2eDeployModsDefs e2eModsDefs e2eDefs e2eWitnessCompute
  vyperTypeContract vyperTypeContractContext vyperContext vyperInterpreter
  bodySim bodyInvSplit bodyQualifiedStmtSupport exprSimHypsDefs compileUnit constSubst
  linkedBodyWitness linkedBodyEntryEnv supportedStmtTraverse
  vyperAST context alist list
Libs computeLib finite_mapLib intReduce

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset
val () = computeLib.add_funs [alistTheory.fmap_to_alist_FEMPTY,
                             integer_wordTheory.i2w_pos]

val constructor_context =
  ``deploy_evaluation_context_mods linked_witness_mods
      linked_witness_initial_machine linked_witness_deploy_tx``
val external_context =
  ``initial_evaluation_context linked_witness_am_call.sources
      linked_witness_am_call.layouts linked_witness_call_tx (SOME 2)``

val fixture_load = EVAL
  ``load_contract (SOME []) [] linked_witness_initial_machine
       linked_witness_deploy_tx linked_witness_mods linked_witness_exports``

val runtime_fields = map
  (SIMP_CONV (srw_ss())
    [linked_witness_am_call_def, next_source_machine_def,
     linked_witness_am_deploy_post_def, fixture_load])
  [``linked_witness_am_call.layouts``,
   ``linked_witness_am_call.sources``,
   ``linked_witness_am_call.exports``]

val entry_context_simps =
  [deploy_evaluation_context_mods_def, initial_evaluation_context_def,
   linked_witness_initial_machine_def, linked_witness_deploy_tx_def,
   linked_witness_call_tx_def, e2eWitnessComputeTheory.p23_deploy_tx_def,
   e2eWitnessComputeTheory.p23_call_tx_def,
   empty_call_txn_def, initial_machine_state_def,
   lookup_nonreentrant_slot_def, global_nonreentrant_slot_def, ALOOKUP_def] @
  runtime_fields

Theorem linked_witness_constructor_context:
  (^constructor_context).in_deploy /\
  ALOOKUP (^constructor_context).sources ((^constructor_context).txn).target =
    SOME linked_witness_mods /\
  (^constructor_context).stk = [(NONE,"__init__")] /\
  (^constructor_context).nonreentrant_slot = SOME global_nonreentrant_slot /\
  context_function_live ^constructor_context (NONE,"__init__") /\
  layouts_agree_mods linked_witness_mods linked_witness_exports
    linked_witness_initial_machine linked_witness_deploy_tx /\
  (?art. check_contract T (^constructor_context).layouts
    ((^constructor_context).txn).target linked_witness_mods = SOME art)
Proof
  mp_tac linked_witness_deploy_premises >>
  simp[deploy_typing_ok_mods_def, deploy_state_rel_mods_def] >>
  rpt strip_tac >>
  simp[initial_evaluation_context_def, deploy_evaluation_context_mods_def] >>
  simp entry_context_simps >>
  simp[context_function_live_def, function_live_def]
  >- (disj1_tac >>
      simp[linked_witness_mods_def, ALOOKUP_def, module_allocated_def,
           toplevel_allocated_def, lookup_var_slot_in_layouts_def])
  >- (qpat_assum `SOME _ = check_contract T _ _ linked_witness_mods`
        (fn checked =>
          exists_tac (optionSyntax.dest_some (lhs (concl checked))) >>
          ACCEPT_TAC (SIMP_RULE (srw_ss()) entry_context_simps checked)))
QED

Theorem linked_witness_external_context:
  ~(^external_context).in_deploy /\
  ALOOKUP (^external_context).sources ((^external_context).txn).target =
    SOME linked_witness_mods /\
  (^external_context).stk = [(SOME 2,"locked_get_x")] /\
  (^external_context).nonreentrant_slot = SOME global_nonreentrant_slot /\
  context_function_live ^external_context (SOME 2,"locked_get_x") /\
  layouts_agree_mods linked_witness_mods linked_witness_exports
    linked_witness_am_call linked_witness_call_tx /\
  (?art. check_contract F (^external_context).layouts
    ((^external_context).txn).target linked_witness_mods = SOME art) /\
  find_function_module linked_witness_am_call linked_witness_call_tx.target
    "locked_get_x" = SOME 2
Proof
  mp_tac linked_witness_call_premises >>
  simp[source_typing_ok_mods_def, call_state_rel_mods_def,
       source_deployment_rel_mods_def, linked_witness_exports_def] >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
  simp[initial_evaluation_context_def, find_function_module_def] >>
  simp entry_context_simps >>
  simp[context_function_live_def, function_live_def, linked_witness_exports_def] >>
  rpt conj_tac
  >- (disj1_tac >>
      simp[linked_witness_mods_def, ALOOKUP_def, module_allocated_def,
           toplevel_allocated_def, lookup_var_slot_in_layouts_def])
  >- (qpat_assum `SOME _ = check_contract F _ _ linked_witness_mods`
        (fn checked =>
          exists_tac (optionSyntax.dest_some (lhs (concl checked))) >>
          ACCEPT_TAC (SIMP_RULE (srw_ss()) entry_context_simps checked)))
QED

fun fixture_entry src fname =
  let
    val lookup = EVAL ``ALOOKUP linked_witness_mods ^src``
    val tops = optionSyntax.dest_some (rhs (concl lookup))
    fun matching_decl decl =
      case strip_comb decl of
        (head, [_, _, _, _, name, _, _, _, _]) =>
          same_const head ``FunctionDecl`` andalso aconv name fname
      | _ => false
    val decl = valOf (List.find matching_decl (#1 (listSyntax.dest_list tops)))
    val (_, [vis, mut, _, _, name, args, _, ret, body]) = strip_comb decl
    val env = ``build_compile_env_unit linked_witness_mods ^src
      ^vis ^mut ^name ^args ^ret ^body T``
  in (lookup, tops, decl, env, body) end

val (constructor_lookup, constructor_tops, constructor_decl,
     constructor_env, constructor_body) =
  fixture_entry ``NONE : num option`` ``"__init__"``
val (external_lookup, external_tops, external_decl,
     external_env, external_body) =
  fixture_entry ``SOME 2`` ``"locked_get_x"``

val () = computeLib.add_funs
  [const_name_root_mods_def, cx_const_name_mods_def, qualified_stmt_decls_ok_def]

Theorem linked_witness_constructor_body_checks:
  ALOOKUP linked_witness_mods NONE = SOME ^constructor_tops /\
  MEM ^constructor_decl ^constructor_tops /\
  subst_consts_stmts_mods (consts_env_mods linked_witness_mods)
    ^constructor_body = ^constructor_body /\
  stmts_exprs_ok ^constructor_env ^constructor_body
Proof
  simp[constructor_lookup] >> EVAL_TAC
QED

Theorem linked_witness_external_body_checks:
  ALOOKUP linked_witness_mods (SOME 2) = SOME ^external_tops /\
  MEM ^external_decl ^external_tops /\
  subst_consts_stmts_mods (consts_env_mods linked_witness_mods)
    ^external_body = ^external_body /\
  stmts_exprs_ok ^external_env ^external_body
Proof
  simp[external_lookup] >> EVAL_TAC
QED

Triviality linked_witness_entry_static_gate:
  ALOOKUP linked_witness_mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  (vis = Deploy \/ vis = External) /\ (vis = Deploy <=> cx.in_deploy) /\
  ALOOKUP cx.sources cx.txn.target = SOME linked_witness_mods /\
  cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
  layouts_agree_mods linked_witness_mods linked_witness_exports am tx /\
  cx.stk = [(src,name)] /\ context_function_live cx (src,name) /\
  check_contract cx.in_deploy cx.layouts cx.txn.target linked_witness_mods =
    SOME art /\
  subst_consts_stmts_mods (consts_env_mods linked_witness_mods) ss = ss /\
  stmts_exprs_ok (build_compile_env_unit linked_witness_mods src vis mut name
    args ret ss T) ss ==>
  ?ctx ce env'.
    contract_inv linked_witness_mods linked_witness_exports ctx ce cx /\
    module_body_inv linked_witness_mods src tops ce cx /\
    supported_stmts tops (args ++ supported_stmts_bindings T ss ++
      supported_stmts_bindings F ss) ss /\
    (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
      EXISTS (occurs_abi_decode_target target o SND) linked_witness_mods) /\
    type_stmts (function_entry_env art linked_witness_mods src vis args)
      ret ss = SOME env' /\
    stmts_exprs_ok ce ss /\
    call_evaluation_safe cx (int_calls_stmts ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vis = Deploy ==> cx.in_deploy` by simp[] >>
  drule_all_then strip_assume_tac linked_witness_entry_support >>
  qexistsl [`ctx`,
    `build_compile_env_unit linked_witness_mods src vis mut name args ret ss T
      with ce_target := ce.ce_target`, `env'`] >>
  simp[stmts_exprs_ok_entry_target] >>
  conj_tac
  >- (irule contract_inv_build_compile_env_unit >> simp[]) >>
  simp[module_body_inv_def, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY] >>
  qpat_assum `subst_consts_stmts_mods _ ss = ss`
    (fn subst => qpat_assum `type_stmts _ _ _ = SOME env'`
      (ACCEPT_TAC o PURE_REWRITE_RULE [subst]))
QED

fun static_gate src cx vis args ret body tops =
  ``?ctx ce art env'.
    check_contract (^cx).in_deploy (^cx).layouts ((^cx).txn).target
      linked_witness_mods = SOME art /\
    contract_inv linked_witness_mods linked_witness_exports ctx ce ^cx /\
    module_body_inv linked_witness_mods ^src ^tops ce ^cx /\
    supported_stmts ^tops (^args ++ supported_stmts_bindings T ^body ++
      supported_stmts_bindings F ^body) ^body /\
    (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ^body ==>
      EXISTS (occurs_abi_decode_target target o SND) linked_witness_mods) /\
    type_stmts (function_entry_env art linked_witness_mods ^src ^vis ^args)
      ^ret ^body = SOME env' /\
    stmts_exprs_ok ce ^body /\
    call_evaluation_safe ^cx (int_calls_stmts ^body)``

fun specialize_static_gate src cx decl tops =
  let
    val (_, [vis, mut, nr, raw, name, args, dflts, ret, body]) = strip_comb decl
    val goal = static_gate src cx vis args ret body tops
    val selected_gate = INST
      [``src : num option`` |-> src, ``cx : evaluation_context`` |-> cx,
       ``vis : function_visibility`` |-> vis, ``mut : function_mutability`` |-> mut,
       ``nr : bool`` |-> nr, ``raw : bool`` |-> raw, ``name : string`` |-> name,
       ``args : (string # type) list`` |-> args, ``dflts : expr list`` |-> dflts,
       ``ret : type`` |-> ret, ``ss : stmt list`` |-> body, ``tops : toplevel list`` |-> tops]
      linked_witness_entry_static_gate
  in (goal, selected_gate) end

val (constructor_gate, constructor_gate_rule) =
  specialize_static_gate ``NONE : num option`` constructor_context constructor_decl constructor_tops

val (external_gate, external_gate_rule) =
  specialize_static_gate ``SOME 2`` external_context external_decl external_tops

Theorem linked_witness_constructor_entry_gate:
  ^constructor_gate
Proof
  strip_assume_tac linked_witness_constructor_context >>
  strip_assume_tac linked_witness_constructor_body_checks >>
  rename1 `check_contract T _ _ _ = SOME checked_art` >>
  mp_tac (INST [``am : abstract_machine`` |-> ``linked_witness_initial_machine``,
               ``tx : call_txn`` |-> ``linked_witness_deploy_tx``,
               ``art : contract_type_artifact`` |-> ``checked_art : contract_type_artifact``]
          constructor_gate_rule) >>
  simp[] >>
  disch_then (qx_choose_then `ctx` (qx_choose_then `ce`
              (qx_choose_then `env'` strip_assume_tac))) >>
  qexistsl [`ctx`, `ce`, `env'`] >> simp[]
QED

Theorem linked_witness_external_entry_gate:
  ^external_gate
Proof
  strip_assume_tac linked_witness_external_context >>
  strip_assume_tac linked_witness_external_body_checks >>
  rename1 `check_contract F _ _ _ = SOME checked_art` >>
  mp_tac (INST [``am : abstract_machine`` |-> ``linked_witness_am_call``,
               ``tx : call_txn`` |-> ``linked_witness_call_tx``,
               ``art : contract_type_artifact`` |-> ``checked_art : contract_type_artifact``]
          external_gate_rule) >>
  simp[] >>
  disch_then (qx_choose_then `ctx` (qx_choose_then `ce`
              (qx_choose_then `env'` strip_assume_tac))) >>
  qexistsl [`ctx`, `ce`, `env'`] >> simp[]
QED
