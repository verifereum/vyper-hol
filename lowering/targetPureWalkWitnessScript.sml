(* Shared concrete fixture for the RawLog walk diagnostic. *)
Theory targetPureWalkWitness
Ancestors
  targetPureWalkProbe compileVyper stmtLowering loweringStateRelDefs
  loweringShapeDefs fragExec venomWf vyperTypeSystem

Definition w_cx_def:
  w_cx = empty_evaluation_context with <|
    sources := [(0w, [(NONE, [])])]; stk := [(NONE, "walk")] |>
End

Definition w_cenv_def:
  w_cenv = (build_compile_env [] External Nonpayable "walk" [] NoneT [] F)
    with <| ce_vars := FEMPTY |+ ("a", PtrVar (Var "local") 64);
            ce_var_type := (\id. if id = "a" then
              SOME (ArrayT (BaseT (UintT 256)) (Dynamic 1)) else NONE);
            ce_dynarray_capacity := (\id. if id = "a" then 1 else 0) |>
End

Definition w_env_def:
  w_env = <| current_src := NONE;
    var_types := FEMPTY |+ ("a", ArrayT (BaseT (UintT 256)) (Dynamic 1));
    var_assignable := FEMPTY |+ ("a", T);
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
    flag_members := FEMPTY; event_fields := FEMPTY |>
End

Definition w_es_def:
  w_es = empty_state with <|
    scopes := [FEMPTY |+ ("a", <| assignable := T;
      type := ArrayTV (BaseTV (UintT 256)) (Dynamic 1);
      value := ArrayV (DynArrayV [IntV 7]); popped := [] |>)];
    outcomes := SOME [] |>
End

Definition w_bt_def:
  w_bt = SubscriptTarget (NameTarget "a") raw_log_index
End

Definition w_vt_def:
  w_vt = BaseTV (UintT 256)
End

Definition w_sa_def:
  w_sa = <| cs_next_var := 1; cs_next_label := 0; cs_next_id := 0;
    cs_current_bb := "entry"; cs_current_insts := []; cs_blocks := [];
    cs_data_sections := [] |>
End

Definition w_op_def:
  w_op = FST (compile_get_target_ptr compile_expr w_cenv w_bt w_sa)
End
Definition w_sb_def:
  w_sb = SND (compile_get_target_ptr compile_expr w_cenv w_bt w_sa)
End
Definition w_func_def:
  w_func = mk_raw_function "walk" (all_blocks w_sb)
End
Definition w_ctx_def:
  w_ctx = mk_venom_context [w_func] (SOME "walk")
End

Definition w_s0_def:
  w_s0 = (init_venom_state "entry") with <|
    vs_vars := FEMPTY |+ ("local", 1024w);
    vs_memory := REPLICATE 1024 0w ++ word_to_bytes (1w:bytes32) T ++ word_to_bytes (7w:bytes32) T;
    vs_alloca_next := 2048;
    vs_fmp := 4096w; vs_initial_fmp := 4096w;
    vs_call_entry_fmp := 4096w |>
End

Theorem w_compilation:
  compile_get_target_ptr compile_expr w_cenv w_bt w_sa = (w_op, w_sb)
Proof
  simp[w_op_def, w_sb_def]
QED

Theorem w_code:
  fn_has_code w_sa w_sb w_func /\ fn_inst_ids_distinct w_func
Proof
  conj_tac
  >- (simp[fn_has_code_def, w_func_def, venomInstTheory.mk_raw_function_def,
           all_blocks_def, w_sa_def] >>
      conj_tac >- (EVAL_TAC >> simp[]) >>
      qexists_tac `<| bb_label := w_sb.cs_current_bb;
                     bb_instructions := w_sb.cs_current_insts |>` >>
      EVAL_TAC >> simp[]) >>
  EVAL_TAC
QED

Theorem w_reserved:
  local_ptrs_reserved w_cenv w_sa
Proof
  simp[w_cenv_def, local_ptrs_reserved_def, not_fresh_at_def, w_sa_def,
       build_compile_env_def, build_flag_info_def, allocate_args_def,
       finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_EMPTY] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem w_cursor:
  ~w_s0.vs_halted /\ w_s0.vs_current_bb = w_sa.cs_current_bb /\
  w_s0.vs_inst_idx = LENGTH w_sa.cs_current_insts
Proof
  simp[w_s0_def, w_sa_def, venomStateTheory.init_venom_state_def]
QED

(* Compact computed interface: consumers need not unfold the compiler to
   discover the finite fragment's size, labels, allocation sizes and opcodes. *)
Theorem w_fragment:
  FST w_op = Var "%16" /\
  w_sb.cs_next_var = 17 /\ w_sb.cs_next_id = 20 /\
  w_sb.cs_next_label = 0 /\ w_sb.cs_current_bb = "entry" /\
  w_sb.cs_blocks = [] /\ w_sb.cs_data_sections = [] /\
  MAP (\i. i.inst_id) w_sb.cs_current_insts = COUNT_LIST 20 /\
  MAP (\i. i.inst_opcode) w_sb.cs_current_insts =
    [ALLOCA; ALLOCA; MSTORE; MLOAD; ADD; LOG; ADD; ADD; MSTORE;
     ADD; MLOAD; MLOAD; LT; ISZERO; OR; ISZERO; ASSERT; ADD; MUL; ADD]
Proof
  EVAL_TAC
QED

Theorem w_entry_fields:
  w_s0.vs_vars = FEMPTY |+ ("local", 1024w) /\
  w_s0.vs_allocas = FEMPTY /\ w_s0.vs_alloca_next = 2048 /\
  w_s0.vs_fmp = 4096w /\ w_s0.vs_initial_fmp = 4096w /\
  w_s0.vs_call_entry_fmp = 4096w /\
  w_s0.vs_memory = REPLICATE 1024 0w ++
    word_to_bytes (1w:bytes32) T ++ word_to_bytes (7w:bytes32) T /\
  w_es.outcomes = SOME [] /\
  lookup_scopes "a" w_es.scopes = SOME <| assignable := T;
    type := ArrayTV (BaseTV (UintT 256)) (Dynamic 1);
    value := ArrayV (DynArrayV [IntV 7]); popped := [] |>
Proof
  simp[w_s0_def, venomStateTheory.init_venom_state_def,
       w_es_def, vyperStateTheory.empty_state_def, vyperStateTheory.lookup_scopes_def,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY]
QED
