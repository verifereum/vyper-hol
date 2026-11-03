(* Full-caller feasibility diagnostics.  No falsehood is asserted here. *)
Theory extCallFrameCounterexample
Ancestors
  exprSimHyps exprSimLeaves extCallZeroReturnProbe compileVyper vfmState vfmContext fragExec compileEnv venomInst

Definition frame_call_def:
  frame_call =
    Call (TupleT [NoneT]) (ExtCall T T ("f",[],TupleT [NoneT]) [])
      [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w))] NONE
End

Definition frame_cenv_def:
  frame_cenv = build_compile_env [] External Nonpayable "probe" [] NoneT [] F
End

Definition frame_cx_def:
  frame_cx = empty_evaluation_context with stk := [(NONE,"probe")]
End

Definition frame_env_def:
  frame_env = <| current_src := NONE; var_types := FEMPTY;
    var_assignable := FEMPTY; bare_globals := FEMPTY;
    bare_global_assignable := FEMPTY; toplevel_vtypes := FEMPTY;
    type_defs := FEMPTY; fn_sigs := FEMPTY; flag_members := FEMPTY |>
End

Definition frame_outcome_def:
  frame_outcome = <| co_success := T; co_returnData := [];
    co_accounts := empty_accounts; co_tStorage := empty_transient_storage;
    co_logs := []; co_toDelete := [] |>
End

Definition frame_es_def:
  frame_es = empty_state with
    <| scopes := [FEMPTY]; outcomes := SOME [frame_outcome] |>
End

Definition frame_sa_def:
  frame_sa = (initial_compile_state "entry") with cs_next_id := 100
End

Definition frame_compiled_def:
  frame_compiled = compile_expr frame_cenv (TupleT [NoneT]) frame_call frame_sa
End

Theorem frame_call_typed:
  well_typed_expr frame_env frame_call
Proof
  qspec_then `frame_env` mp_tac (GEN_ALL nested_none_extcall_typing_probe) >>
  simp[frame_env_def, frame_call_def]
QED

Theorem frame_context_typed:
  context_well_typed frame_cx
Proof
  EVAL_TAC
QED

Theorem frame_env_consistent:
  env_consistent frame_env frame_cx frame_es
Proof
  EVAL_TAC >> simp[]
QED

Theorem frame_call_alloc_limits:
  alloc_limits_expr frame_cenv frame_call
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem frame_source_invariants:
  state_well_typed frame_es /\
  accounts_well_typed frame_es.accounts /\
  functions_well_typed frame_cx /\
  outcomes_accounts_typed frame_es.outcomes /\
  contract_storage_well_formed frame_cx frame_es /\
  storage_layout_safe frame_cx /\
  oracle_storage_ok frame_cx frame_es
Proof
  EVAL_TAC >> simp[empty_accounts_def, empty_account_state_def]
QED

Theorem frame_sim_inv:
  expr_sim_inv frame_cenv frame_cx frame_env frame_es
Proof
  simp[expr_sim_inv_def, frame_env_consistent, frame_context_typed,
       frame_source_invariants] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >> simp[]
QED

Theorem frame_body_pre:
  expr_body_pre frame_cenv frame_cx frame_env frame_call frame_es
Proof
  simp[expr_body_pre_def, frame_sim_inv, frame_call_typed,
       frame_call_alloc_limits] >> EVAL_TAC >> simp[] >>
  qexists_tac `[]` >> simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
                          relationTheory.irreflexive_def] >>
  simp[Once relationTheory.TC_CASES1,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED

Definition frame_sb_def:
  frame_sb = SND frame_compiled
End

Definition frame_func_def:
  frame_func = mk_raw_function "probe"
    (<| bb_label := frame_sb.cs_current_bb;
        bb_instructions := frame_sb.cs_current_insts ++
          [mk_inst frame_sb.cs_next_id RETURN [Lit 64w; Lit 32w] []] |> ::
      frame_sb.cs_blocks)
End

