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

Theorem extract32_empty_runtime_exists:
  ?unit. lower_vyper_runtime_unit []
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> = SOME unit
Proof
  EVAL_TAC >> simp[]
QED

Theorem extract32_empty_runtime_body_inv:
  ?unit. lower_vyper_runtime_unit []
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> = SOME unit /\
    body_inv [] unit.cu_context
      (build_compile_env [] External View "probe" [] NoneT [] F)
      (empty_evaluation_context with <| sources :=
        [(empty_evaluation_context.txn.target, [(NONE,[])])];
        stk := [(NONE,"probe")] |>)
Proof
  strip_assume_tac extract32_empty_runtime_exists >>
  qexists_tac `unit` >> simp[body_inv_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (qexistsl_tac [`<| rpol_target := all_capabilities;
                        rpol_frontend_dispatch := Linear;
                        rpol_final_assembly := FAP_Optimize |>`, `unit`] >> simp[] >> EVAL_TAC) >>
  EVAL_TAC >> simp[]
QED

Theorem extract32_initial_state_rel_rejected:
  !func. ~state_rel func
    (build_compile_env [] External View "probe" [] NoneT [] F)
    (empty_evaluation_context with <| sources :=
      [(empty_evaluation_context.txn.target, [(NONE,[])])]; stk := [(NONE,"probe")] |>)
    (empty_state with <| scopes := [FEMPTY]; outcomes := SOME [] |>)
    (init_venom_state "probe")
Proof
  gen_tac >> rewrite_tac[compileEnvTheory.state_rel_def] >> EVAL_TAC >> simp[]
QED

Theorem extract32_empty_tx_env_rejected:
  ~compileEnv$tx_env_ok empty_evaluation_context.txn
Proof
  EVAL_TAC
QED

Theorem extract32_valid_tx_env:
  compileEnv$tx_env_ok (empty_evaluation_context.txn with
    <| block_number := 1; block_hashes := [0w] |>)
Proof
  EVAL_TAC
QED

Theorem extract32_valid_source_invariant:
  expr_sim_inv
    (build_compile_env [] External View "probe" [] NoneT [] F)
    (empty_evaluation_context with <| sources :=
      [(empty_evaluation_context.txn.target, [(NONE,[])])]; stk := [(NONE,"probe")];
      txn := empty_evaluation_context.txn with
        <| block_number := 1; block_hashes := [0w] |> |>)
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

Theorem extract32_valid_source_pre:
  expr_body_pre
    (build_compile_env [] External View "probe" [] NoneT [] F)
    (empty_evaluation_context with <| sources :=
      [(empty_evaluation_context.txn.target, [(NONE,[])])]; stk := [(NONE,"probe")];
      txn := empty_evaluation_context.txn with
        <| block_number := 1; block_hashes := [0w] |> |>)
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
       flag_members := FEMPTY; event_fields := FEMPTY |>
    (TypeBuiltin (BaseT (UintT 256)) Extract32 (BaseT (UintT 256))
      [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w));
       Literal (BaseT (UintT 256)) (IntL 0)])
    (empty_state with <| scopes := [FEMPTY]; outcomes := SOME [] |>)
Proof
  simp[expr_body_pre_def, extract32_valid_source_invariant,
       extract32_fixed32_well_typed, extract32_fixed32_widths,
       extract32_fixed32_alloc_limits] >> EVAL_TAC >> simp[] >>
  qexists_tac `[]` >>
  simp[lookup_function_def, vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
       relationTheory.irreflexive_def] >>
  metis_tac[relationTheory.TC_CASES1,
            vyperTypeCallGraphSoundnessTheory.call_edge_rel_def, listTheory.MEM]
QED

Theorem extract32_valid_runtime_body_inv:
  ?unit. lower_vyper_runtime_unit []
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> = SOME unit /\
    body_inv [] unit.cu_context
      (build_compile_env [] External View "probe" [] NoneT [] F)
      (empty_evaluation_context with <| sources :=
        [(empty_evaluation_context.txn.target, [(NONE,[])])];
        stk := [(NONE,"probe")]; txn := empty_evaluation_context.txn with
          <| block_number := 1; block_hashes := [0w] |> |>)
Proof
  strip_assume_tac extract32_empty_runtime_exists >>
  qexists_tac `unit` >> simp[body_inv_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (qexistsl_tac [`<| rpol_target := all_capabilities;
                        rpol_frontend_dispatch := Linear;
                        rpol_final_assembly := FAP_Optimize |>`, `unit`] >> simp[] >> EVAL_TAC) >>
  EVAL_TAC >> simp[]
QED

Theorem extract32_valid_initial_state_rel:
  !func. state_rel func
    (build_compile_env [] External View "probe" [] NoneT [] F)
    (empty_evaluation_context with <| sources :=
      [(empty_evaluation_context.txn.target, [(NONE,[])])]; stk := [(NONE,"probe")];
      txn := empty_evaluation_context.txn with
        <| block_number := 1; block_hashes := [0w] |> |>)
    (empty_state with <| scopes := [FEMPTY]; outcomes := SOME [] |>)
    (init_venom_state "probe" with vs_block_ctx :=
      empty_block_context with bc_number := 1w)
Proof
  gen_tac >> rewrite_tac[compileEnvTheory.state_rel_def] >> EVAL_TAC >> simp[]
QED

Theorem extract32_empty_runtime_no_mload:
  !unit func bb i.
    lower_vyper_runtime_unit []
      <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |> = SOME unit /\
    venomInst$lookup_function func.fn_name unit.cu_context.ctx_functions = SOME func /\
    lookup_block bb.bb_label func.fn_blocks = SOME bb /\
    MEM i bb.bb_instructions ==>
    i.inst_opcode <> MLOAD
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >>
  gvs[listTheory.INDEX_FIND_def, AllCaseEqs()]
QED

(* Even a partial fragment cannot introduce an MLOAD in this context. *)
Theorem extract32_empty_runtime_fragment_no_mload:
  lower_vyper_runtime_unit []
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> = SOME unit /\
  venomInst$lookup_function func.fn_name unit.cu_context.ctx_functions = SOME func /\
  fn_has_code sa sb func /\ MEM i sb.cs_current_insts ==>
  i.inst_opcode <> MLOAD
Proof
  strip_tac >> fs[fragExecTheory.fn_has_code_def] >>
  irule extract32_empty_runtime_no_mload >>
  qexistsl_tac [`bb`, `func`, `unit`] >> simp[] >>
  conj_tac
  >- (`!bbs lbl b. lookup_block lbl bbs = SOME b ==> b.bb_label = lbl`
        by (Induct_on `bbs` >> rw[venomInstTheory.lookup_block_def,
                                 listTheory.FIND_thm]) >>
      metis_tac[]) >>
  metis_tac[rich_listTheory.IS_PREFIX_MEM]
QED
