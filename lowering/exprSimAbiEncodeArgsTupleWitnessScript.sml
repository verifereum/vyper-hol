Theory exprSimAbiEncodeArgsTupleWitness
Ancestors
  exprSimAbiEncodeArgsTupleSim compileVyper vyperCompiler
  vyperTypeInvariants vyperContext exprSimHypsDefs
  exprSimAbiEncodeArgsTupleSource

Definition tuple_witness_cx_def:
  tuple_witness_cx = empty_evaluation_context with
    <|sources := [(0w,[(NONE,tuple_tops)])]; stk := [(NONE,"caller")];
      txn := (empty_call_txn with <|block_number := 1; block_hashes := [0w]|>)|>
End

Definition tuple_witness_es_def:
  tuple_witness_es = empty_state with <|outcomes := SOME []; scopes := [FEMPTY]|>
End

Definition tuple_witness_env_def:
  tuple_witness_env : typing_env = <|
    current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY; type_defs := FEMPTY;
    fn_sigs := FEMPTY |+ ((NONE,"f"),
      <|param_types := []; num_defaults := 0; ret_ty := tuple_narrow|>);
    flag_members := FEMPTY; event_fields := FEMPTY |>
End

Definition tuple_witness_ce_def:
  tuple_witness_ce = build_compile_env tuple_tops External Nonpayable
    "caller" [] NoneT [] F
End

Theorem tuple_witness_context:
  get_module_code tuple_witness_cx NONE = SOME tuple_tops /\
  ~MEM (NONE,"f") tuple_witness_cx.stk /\
  context_well_typed tuple_witness_cx
Proof
  EVAL_TAC
QED

Theorem tuple_witness_env_consistent:
  env_consistent tuple_witness_env tuple_witness_cx tuple_witness_es
Proof
  rewrite_tac[env_consistent_def, env_context_consistent_def,
    env_scopes_consistent_def, env_immutables_consistent_def] >>
  EVAL_TAC >> rw[AllCaseEqs()] >> EVAL_TAC >> gvs[]
QED

Theorem tuple_witness_metadata:
  tuple_witness_ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  tuple_witness_ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow
Proof
  EVAL_TAC
QED

Theorem tuple_witness_inv:
  expr_sim_inv tuple_witness_ce tuple_witness_cx tuple_witness_env tuple_witness_es
Proof
  rewrite_tac[expr_sim_inv_def] >>
  simp[tuple_witness_env_consistent, tuple_witness_context] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> rw[] >> EVAL_TAC) >>
  conj_tac >- suspend "functions" >>
  suspend "remaining"
QED

Resume tuple_witness_inv[functions]:
  rewrite_tac[functions_well_typed_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `get_module_code _ _ = _` mp_tac >>
  EVAL_TAC >> rw[AllCaseEqs()] >> gvs[] >>
  qpat_x_assum `lookup_callable_function _ _ _ = _` mp_tac >>
  EVAL_TAC >> rw[AllCaseEqs()] >> gvs[] >>
  qexists_tac `tuple_witness_env with <|fn_sigs := fn_sigs;
    bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
    toplevel_vtypes := toplevel_vtypes; flag_members := flag_members|>` >>
  EVAL_TAC >> simp[wordsTheory.dimword_def,
    vyperValueTheory.type_slot_size_def, vfmConstantsTheory.word_size_def]
QED

Resume tuple_witness_inv[remaining]:
  simp[tuple_witness_env_def, bare_globals_layout_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> rw[AllCaseEqs()] >> EVAL_TAC >>
    gvs[vyperStateTheory.lookup_flag_def]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- suspend "method" >>
  suspend "storage"
QED

Resume tuple_witness_inv[method]:
  simp[tuple_witness_ce_def, build_compile_env_def,
    tuple_witness_cx_def, empty_evaluation_context_def,
    vyperContextTheory.get_tenv_def, tuple_tops_def, tuple_function_def,
    build_flag_info_def, allocate_args_def, empty_call_txn_def,
    vyperContextTheory.type_env_all_modules_def] >>
  simp[vyperContextTheory.type_env_def]
QED

Resume tuple_witness_inv[storage]:
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- suspend "contract_storage" >>
  conj_tac >- suspend "layout" >>
  conj_tac >- suspend "oracle" >>
  conj_tac >- (EVAL_TAC >> rw[AllCaseEqs()] >>
    gvs[vyperStateTheory.find_var_decl_by_name_def]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- suspend "place_maps" >>
  EVAL_TAC >> simp[]
QED

Resume tuple_witness_inv[contract_storage]:
  EVAL_TAC >> rw[AllCaseEqs()] >> EVAL_TAC >> gvs[]
QED

Resume tuple_witness_inv[layout]:
  EVAL_TAC >> rw[AllCaseEqs()] >> EVAL_TAC >> gvs[]
QED

Resume tuple_witness_inv[oracle]:
  EVAL_TAC >> rw[AllCaseEqs()] >> EVAL_TAC >> gvs[]
QED

Resume tuple_witness_inv[place_maps]:
  EVAL_TAC >> rw[AllCaseEqs()] >> EVAL_TAC >> gvs[]
QED

Finalise tuple_witness_inv

Theorem tuple_witness_body_pre:
  expr_body_pre tuple_witness_ce tuple_witness_cx tuple_witness_env tuple_abi tuple_witness_es
Proof
  rewrite_tac[expr_body_pre_def] >>
  simp[tuple_witness_inv] >>
  conj_tac >- (rewrite_tac[exprSimAbiEncodeArgsTupleProbeTheory.tuple_abi_def,
    exprSimAbiEncodeArgsTupleProbeTheory.tuple_call_def] >>
    irule exprSimAbiEncodeArgsTupleProbeTheory.tuple_abi_typing >>
    simp[tuple_witness_env_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    qexists_tac `<|param_types := []; num_defaults := 0; ret_ty := tuple_narrow|>` >> simp[]) >>
  suspend "body_interfaces"
QED

Resume tuple_witness_body_pre[body_interfaces]:
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- suspend "allocation" >>
  conj_tac >- suspend "call_safe" >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> rw[AllCaseEqs()] >> EVAL_TAC >> gvs[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  EVAL_TAC >> simp[]
QED

Resume tuple_witness_body_pre[call_safe]:
  EVAL_TAC >>
  qexists_tac `[((NONE,"caller"),(NONE,"f"))]` >> simp[] >>
  conj_tac
  >- (`transitive (call_edge_rel ([((NONE,"caller"),(NONE,"f"))] : (nsid # nsid) list))` by
        simp[relationTheory.transitive_def,
          vyperTypeCallGraphSoundnessTheory.call_edge_rel_def] >>
      drule relationTheory.transitive_TC_identity >> disch_then SUBST1_TAC >>
      simp[relationTheory.irreflexive_def,
        vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]) >>
  rw[AllCaseEqs()] >>
  qpat_x_assum `lookup_function _ _ _ _ = _` mp_tac >>
  EVAL_TAC >> rw[AllCaseEqs()] >> gvs[] >> EVAL_TAC
QED

Resume tuple_witness_body_pre[allocation]:
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Finalise tuple_witness_body_pre

Definition tuple_witness_sa_def:
  tuple_witness_sa = initial_compile_state "entry"
End

Definition tuple_witness_compiled_def:
  tuple_witness_compiled = compile_abi_encode_args compile_expr
    tuple_witness_ce [tuple_call] tuple_witness_sa
End

Definition tuple_witness_fn_def:
  tuple_witness_fn = mk_raw_function "caller"
    [<|bb_label := "entry";
       bb_instructions := (SND tuple_witness_compiled).cs_current_insts|>]
End

Definition tuple_witness_name_def:
  tuple_witness_name = internal_fn_label
    (tuple_witness_ce.ce_func_ids (nsid_to_string (NONE,"f")))
    (nsid_to_string (NONE,"f"))
    (tuple_witness_ce.ce_func_param_types (nsid_to_string (NONE,"f")))
    tuple_witness_ce.ce_is_ctor
End

Definition tuple_witness_ctx_def:
  tuple_witness_ctx = (mk_venom_context [] NONE) with ctx_functions :=
    [tuple_witness_fn; tuple_target_function tuple_witness_name]
End

Definition tuple_witness_s_def:
  tuple_witness_s = (init_venom_state "entry") with
    vs_block_ctx := empty_block_context with bc_number := 1w
End

Theorem tuple_witness_code:
  fn_has_code tuple_witness_sa (SND tuple_witness_compiled) tuple_witness_fn /\
  fn_inst_ids_distinct tuple_witness_fn /\
  local_ptrs_reserved tuple_witness_ce tuple_witness_sa
Proof
  EVAL_TAC >> simp[]
QED

Theorem tuple_witness_state_rel:
  stmt_state_rel tuple_witness_ctx tuple_witness_fn tuple_witness_ce
    tuple_witness_cx tuple_witness_es tuple_witness_s
Proof
  rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def,
    compileEnvTheory.state_rel_def] >>
  conj_tac >- suspend "base" >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- suspend "alloca_room" >>
  conj_tac >- suspend "fmp_room" >>
  EVAL_TAC >> rw[AllCaseEqs()] >> EVAL_TAC >> gvs[]
QED

Resume tuple_witness_state_rel[base]:
  EVAL_TAC >> rw[AllCaseEqs()] >> EVAL_TAC >> gvs[]
QED

Resume tuple_witness_state_rel[alloca_room]:
  `fn_directly_calls tuple_witness_ctx =
     (\a b. a = "caller" /\ b = tuple_witness_name)` by
    (simp[FUN_EQ_THM, fcgBridgeTheory.fn_directly_calls_scan] >>
     rpt gen_tac >> EVAL_TAC >>
     simp[AllCaseEqs(), LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
       EXISTS_OR_THM] >> EVAL_TAC >> simp[]) >>
  `transitive (fn_directly_calls tuple_witness_ctx)` by
    simp[relationTheory.transitive_def, tuple_witness_name_def,
      tuple_witness_ce_def, build_compile_env_def] >>
  drule relationTheory.transitive_TC_identity >> disch_then assume_tac >>
  simp[exprLoweringPropsTheory.alloca_room_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Resume tuple_witness_state_rel[fmp_room]:
  EVAL_TAC >> simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC >> simp[]
QED

Finalise tuple_witness_state_rel

Theorem tuple_witness_lookup:
  venomInst$lookup_function tuple_witness_name tuple_witness_ctx.ctx_functions =
    SOME (tuple_target_function tuple_witness_name)
Proof
  EVAL_TAC
QED

Theorem tuple_witness_cases:
  exprs_case F tuple_witness_ctx tuple_witness_fn tuple_witness_ce
    tuple_witness_cx [tuple_call]
Proof
  irule tuple_universal_cases_in_context >>
  simp[tuple_witness_metadata, GSYM tuple_witness_name_def, tuple_witness_context,
    tuple_witness_lookup]
QED

Theorem tuple_witness_all_premises:
  exprs_case F tuple_witness_ctx tuple_witness_fn tuple_witness_ce
    tuple_witness_cx [tuple_call] /\
  expr_body_pre tuple_witness_ce tuple_witness_cx tuple_witness_env
    (TypeBuiltin (BaseT (BytesT (Dynamic 320))) (AbiEncode T NONE)
      (TupleT [tuple_wide]) [tuple_call]) tuple_witness_es /\
  (F ==> int_calls_expr (TypeBuiltin (BaseT (BytesT (Dynamic 320))) (AbiEncode T NONE)
      (TupleT [tuple_wide]) [tuple_call]) = []) /\
  compile_abi_encode_args compile_expr tuple_witness_ce [tuple_call] tuple_witness_sa =
    (FST tuple_witness_compiled, SND tuple_witness_compiled) /\
  fn_has_code tuple_witness_sa (SND tuple_witness_compiled) tuple_witness_fn /\
  fn_inst_ids_distinct tuple_witness_fn /\
  local_ptrs_reserved tuple_witness_ce tuple_witness_sa /\
  stmt_state_rel tuple_witness_ctx tuple_witness_fn tuple_witness_ce
    tuple_witness_cx tuple_witness_es tuple_witness_s /\
  ~tuple_witness_s.vs_halted /\
  tuple_witness_s.vs_current_bb = tuple_witness_sa.cs_current_bb /\
  tuple_witness_s.vs_inst_idx = LENGTH tuple_witness_sa.cs_current_insts
Proof
  simp[tuple_witness_cases, GSYM exprSimAbiEncodeArgsTupleProbeTheory.tuple_abi_def, tuple_witness_body_pre,
    tuple_witness_code, tuple_witness_state_rel, tuple_witness_compiled_def] >>
  EVAL_TAC
QED
