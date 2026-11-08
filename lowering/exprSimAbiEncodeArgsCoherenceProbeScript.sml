Theory exprSimAbiEncodeArgsCoherenceProbe
Ancestors
  exprSimHypsDefs exprLowering vyperTypeSystem vyperAST
  abiTypeBoundProps

Definition coherence_arg_def:
  coherence_arg = Literal (BaseT (BytesT (Dynamic 64))) (BytesL [])
End

Definition coherence_encoder_def:
  coherence_encoder = TypeBuiltin (BaseT (BytesT (Dynamic 96)))
    (AbiEncode F NONE) (TupleT [BaseT (BytesT (Dynamic 64))]) [coherence_arg]
End

Theorem coherence_capacity_gap:
  lowered_value_type ce coherence_encoder = BaseT (BytesT (Dynamic 32)) /\
  abi_encode_size_ok env.type_defs F
    (TupleT [BaseT (BytesT (Dynamic 64))]) NONE 96 /\
  ~abi_encode_size_ok env.type_defs F
    (TupleT [BaseT (BytesT (Dynamic 64))]) NONE 32
Proof
  EVAL_TAC
QED

Theorem coherence_retyping_rejected:
  ~well_typed_expr env
    (TypeBuiltin (lowered_value_type ce coherence_encoder)
      (AbiEncode F NONE) (TupleT [BaseT (BytesT (Dynamic 64))]) [coherence_arg])
Proof
  simp[coherence_capacity_gap, well_typed_expr_def, type_builtin_result_ok_def] >>
  EVAL_TAC
QED

Theorem coherence_source_typing:
  well_typed_expr env coherence_encoder
Proof
  simp[coherence_encoder_def, coherence_arg_def, well_typed_expr_def,
       well_typed_type_builtin_args_def, type_builtin_result_ok_def,
       well_typed_literal_def, well_formed_type_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem coherence_body_pre:
  expr_sim_inv ce cx env es /\ call_evaluation_safe cx [] /\
  (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
    is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) ==>
  expr_body_pre ce cx env coherence_encoder es
Proof
  simp[expr_body_pre_def, coherence_source_typing] >> strip_tac >>
  simp[coherence_encoder_def, coherence_arg_def,
       vyperTypeCallGraphTheory.int_calls_expr_def] >> EVAL_TAC >> simp[]
QED

Definition coherence_cx_def:
  coherence_cx = empty_evaluation_context with stk := [(NONE, "probe")]
End

Definition coherence_env_def:
  coherence_env = <|current_src := NONE; var_types := FEMPTY;
    var_assignable := FEMPTY; bare_globals := FEMPTY;
    bare_global_assignable := FEMPTY; toplevel_vtypes := FEMPTY;
    type_defs := FEMPTY; fn_sigs := FEMPTY; flag_members := FEMPTY;
    event_fields := FEMPTY|>
End

Definition coherence_es_def:
  coherence_es = empty_state with <|scopes := [FEMPTY]; outcomes := SOME []|>
End

Definition coherence_ce_def:
  coherence_ce = (ARB:compile_env) with <|ce_vars := FEMPTY;
    ce_module_vars := FEMPTY; ce_struct_fields := FEMPTY;
    ce_method_id := (\name tys. w2n (calldata_method_id
      (function_selector name (vyper_to_abi_types FEMPTY tys))))|>
End

Theorem coherence_context_inhabited:
  expr_sim_inv coherence_ce coherence_cx coherence_env coherence_es
Proof
  simp[expr_sim_inv_def, coherence_ce_def, coherence_env_def] >>
  rpt conj_tac
  >- (simp[vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_context_consistent_def,
           vyperTypeInvariantsTheory.env_scopes_consistent_def,
           vyperTypeInvariantsTheory.env_immutables_consistent_def,
           coherence_cx_def, coherence_es_def] >>
      rpt conj_tac >> EVAL_TAC >> simp[])
  >- simp[vyperTypeInvariantsTheory.state_well_typed_def,
          vyperTypeInvariantsTheory.scope_well_typed_def, coherence_es_def,
          vyperStateTheory.empty_state_def] >>
  simp[coherence_es_def, vyperStateTheory.empty_state_def,
       coherence_cx_def, vyperContextTheory.empty_evaluation_context_def]
  >- (rw[vyperTypeInvariantsTheory.accounts_well_typed_def,
          vyperTypeInvariantsTheory.account_well_typed_def] >> EVAL_TAC)
  >- (simp[vyperTypeInvariantsTheory.context_well_typed_def] >> EVAL_TAC)
  >- simp[vyperTypeInvariantsTheory.functions_well_typed_def,
          vyperContextTheory.get_module_code_def] >>
  simp[vyperContextTheory.get_module_code_def, vyperContextTheory.get_tenv_def] >>
  EVAL_TAC >> simp[]
QED

Theorem coherence_empty_calls_safe:
  call_evaluation_safe coherence_cx []
Proof
  simp[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def,
       coherence_cx_def, vyperContextTheory.empty_evaluation_context_def] >>
  qexists `[]` >> EVAL_TAC >> simp[] >>
  irule vyperTypeCallGraphSoundnessTheory.edges_respect_rank_irreflexive >>
  simp[vyperTypeCallGraphTheory.edges_respect_rank_def]
QED

Theorem coherence_pre_inhabited:
  expr_body_pre coherence_ce coherence_cx coherence_env coherence_encoder coherence_es
Proof
  irule coherence_body_pre >>
  simp[coherence_context_inhabited, coherence_empty_calls_safe,
       coherence_cx_def, vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.get_tenv_def, gasContextTheory.cx_tops_def] >>
  EVAL_TAC >> simp[]
QED

Theorem abi_encode_lowered_well_typed_coherent_counterexample:
  expr_body_pre coherence_ce coherence_cx coherence_env coherence_encoder coherence_es /\
  ~well_typed_expr coherence_env
    (TypeBuiltin (lowered_value_type coherence_ce coherence_encoder)
      (AbiEncode F NONE) (TupleT [BaseT (BytesT (Dynamic 64))]) [coherence_arg])
Proof
  simp[coherence_pre_inhabited, coherence_retyping_rejected]
QED

Theorem abi_encode_lowered_well_typed_coherent_false:
  ~(!cenv cx env ann ensure mid target args es.
    expr_body_pre cenv cx env
      (TypeBuiltin ann (AbiEncode ensure mid) target args) es ==>
    well_typed_expr env
      (TypeBuiltin
        (lowered_value_type cenv
          (TypeBuiltin ann (AbiEncode ensure mid) target args))
        (AbiEncode ensure mid) target args))
Proof
  strip_tac >>
  mp_tac abi_encode_lowered_well_typed_coherent_counterexample >>
  simp[coherence_encoder_def] >> metis_tac[]
QED
