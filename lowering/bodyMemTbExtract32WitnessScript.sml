(* Concrete empty-module witnesses for the Extract32 probe. *)
Theory bodyMemTbExtract32Witness
Ancestors
  bodyMemTbExtract32Probe bodySim exprSimHypsDefs vyperTypeContract vyperMisc vyperState vyperInterpreter

Theorem extract32_empty_module_code:
  get_module_code
    (empty_evaluation_context with sources :=
      [(empty_evaluation_context.txn.target, [(NONE,[])])]) NONE = SOME []
Proof
  EVAL_TAC >> simp[]
QED

Theorem extract32_empty_module_tenv:
  get_tenv
    (empty_evaluation_context with sources :=
      [(empty_evaluation_context.txn.target, [(NONE,[])])]) = type_env []
Proof
  EVAL_TAC >> simp[]
QED

Theorem extract32_empty_source_invariant:
  expr_sim_inv
    (build_compile_env [] External View "probe" [] NoneT [] F)
    (empty_evaluation_context with sources :=
      [(empty_evaluation_context.txn.target, [(NONE,[])])])
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
       flag_members := FEMPTY; event_fields := FEMPTY |>
    (empty_state with <| scopes := [FEMPTY]; outcomes := SOME [] |>)
Proof
  rewrite_tac[expr_sim_inv_def] >> EVAL_TAC >>
  simp[lookup_flag_def, lookup_function_def, find_var_decl_by_name_def] >>
  simp[SF boolSimps.COND_elim_ss, find_var_decl_by_name_def]
QED

Theorem extract32_empty_source_pre_rejected:
  ~expr_body_pre
    (build_compile_env [] External View "probe" [] NoneT [] F)
    (empty_evaluation_context with sources :=
      [(empty_evaluation_context.txn.target, [(NONE,[])])])
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
       flag_members := FEMPTY; event_fields := FEMPTY |>
    (TypeBuiltin (BaseT (UintT 256)) Extract32 (BaseT (UintT 256))
      [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w));
       Literal (BaseT (UintT 256)) (IntL 0)])
    (empty_state with <| scopes := [FEMPTY]; outcomes := SOME [] |>)
Proof
  simp[expr_body_pre_def, extract32_empty_source_invariant,
       extract32_fixed32_well_typed, extract32_fixed32_widths,
       extract32_fixed32_alloc_limits] >> EVAL_TAC >> simp[]
QED

Theorem extract32_singleton_source_invariant:
  expr_sim_inv
    (build_compile_env [] External View "probe" [] NoneT [] F)
    (empty_evaluation_context with <| sources :=
      [(empty_evaluation_context.txn.target, [(NONE,[])])]; stk := [(NONE,"probe")] |>)
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
       flag_members := FEMPTY; event_fields := FEMPTY |>
    (empty_state with <| scopes := [FEMPTY]; outcomes := SOME [] |>)
Proof
  rewrite_tac[expr_sim_inv_def] >> EVAL_TAC >>
  simp[lookup_flag_def, lookup_function_def, find_var_decl_by_name_def] >>
  simp[SF boolSimps.COND_elim_ss, find_var_decl_by_name_def]
QED

Theorem extract32_singleton_source_pre:
  expr_body_pre
    (build_compile_env [] External View "probe" [] NoneT [] F)
    (empty_evaluation_context with <| sources :=
      [(empty_evaluation_context.txn.target, [(NONE,[])])]; stk := [(NONE,"probe")] |>)
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
       flag_members := FEMPTY; event_fields := FEMPTY |>
    (TypeBuiltin (BaseT (UintT 256)) Extract32 (BaseT (UintT 256))
      [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w));
       Literal (BaseT (UintT 256)) (IntL 0)])
    (empty_state with <| scopes := [FEMPTY]; outcomes := SOME [] |>)
Proof
  simp[expr_body_pre_def, extract32_singleton_source_invariant,
       extract32_fixed32_well_typed, extract32_fixed32_widths,
       extract32_fixed32_alloc_limits] >> EVAL_TAC >> simp[] >>
  qexists_tac `[]` >>
  simp[lookup_function_def, vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
       relationTheory.irreflexive_def] >>
  metis_tac[relationTheory.TC_CASES1,
            vyperTypeCallGraphSoundnessTheory.call_edge_rel_def, listTheory.MEM]
QED
