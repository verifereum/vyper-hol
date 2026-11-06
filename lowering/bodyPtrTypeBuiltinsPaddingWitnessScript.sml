(* Witness fragments for the padding gate; not a target counterexample. *)
Theory bodyPtrTypeBuiltinsPaddingWitness
Ancestors
  bodyPtrTypeBuiltinsPartialRead valueEncodingProps valueEncodingProofs
  list words bodyPtrDefs valueEncoding ptrDiscipline finite_map
  compileVyper venomPolicyTypes venomCompilerTypes
  vyperState vyperInterpreter vyperTypeSystem exprSimHypsDefs vyperTyping
  vyperValue vyperTypeCallGraphSoundness relation bodySim
  venomState compileEnv vyperContext vyperCompiler exprLowering
  exprLoweringProps venomInst fragExec

Theorem outside_taint_window_equal:
  mem_agree_outside M mem mem' /\
  (!i. a <= i /\ i < a+n ==> i NOTIN M) ==>
  mem_bytes_at a n mem = mem_bytes_at a n mem'
Proof
  strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  `mem_bytes_at (a+x) 1 mem = mem_bytes_at (a+x) 1 mem'` by
    (gvs[mem_agree_outside_def] >> first_x_assum irule >>
     first_x_assum irule >> decide_tac) >>
  pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]
QED

Theorem padding_robust_bytes:
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV [b]) 0 mem /\
  mem_agree_outside {63} mem mem' ==>
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV [b]) 0 mem'
Proof
  strip_tac >>
  `mem_bytes_at 0 32 mem = mem_bytes_at 0 32 mem'` by
    (irule outside_taint_window_equal >> qexists_tac `{63}` >> simp[]) >>
  `mem_bytes_at 32 1 mem = mem_bytes_at 32 1 mem'` by
    (gvs[mem_agree_outside_def] >> first_x_assum irule >> simp[]) >>
  gvs[val_in_memory_def, mem_word_at_def, mem_bytes_at_def]
QED

Theorem padding_memory_example:
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV [0w:word8]) 0
    (REPLICATE 31 (0w:word8) ++ [1w;0w] ++ REPLICATE 31 0w)
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w]
QED

Theorem padding_memory_robust_example:
  !m. mem_agree_outside {63}
    (REPLICATE 31 (0w:word8) ++ [1w;0w] ++ REPLICATE 31 0w) m ==>
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV [0w:word8]) 0 m
Proof
  rpt strip_tac >> irule padding_robust_bytes >>
  goal_assum (drule_at Any) >> ACCEPT_TAC padding_memory_example
QED

(* These are actual ghost-entry obligations, still conditional on a semantic
   frame.  They do not assert inhabitation of body_inv or stmt_state_rel. *)
Theorem padding_ghost_entry:
  cenv.ce_vars = FEMPTY |+ (id, PtrVar (Var p) 64) /\
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = BaseTV (BytesT (Dynamic 1)) /\
  entry.value = BytesV [0w:word8] /\
  lookup_var p s = SOME 0w /\
  s.vs_memory = REPLICATE 31 (0w:word8) ++ [1w;0w] ++ REPLICATE 31 0w ==>
  ghost_inv NONE cenv cx es (FEMPTY |+ (p,(0,64)))
    (entry_taint with t_mem := {63}) s
Proof
  strip_tac >> simp[ghost_inv_def, return_buf_ptr_def, stor_taint_ok_def,
                    entry_taint_def, op_taint_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE] >>
  simp[ptr_covers_def, entry_taint_def, op_taint_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> irule padding_memory_robust_example >> simp[]
QED

Theorem padding_empty_runtime_exists:
  IS_SOME (lower_vyper_runtime_unit []
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> )
Proof
  EVAL_TAC >> simp[]
QED

(* Record abbreviations keep the concrete entry probe readable.  These do not
   replace any invariant or simulation judgment. *)
Definition padding_source_def:
  padding_source = empty_state with
    <| scopes := [FEMPTY |+ ("x",
         <| assignable := F; type := BaseTV (BytesT (Dynamic 1));
            value := BytesV [0w:word8]; popped := [] |>)];
       outcomes := SOME [] |>
End

Definition padding_env_def:
  padding_env =
    <| current_src := NONE;
       var_types := FEMPTY |+ ("x",BaseT (BytesT (Dynamic 1)));
       var_assignable := FEMPTY |+ ("x",F);
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
       flag_members := FEMPTY; event_fields := FEMPTY |>
End

Definition padding_cenv_def:
  padding_cenv =
    (build_compile_env [] External Pure "" [] NoneT [] F) with
      <| ce_vars := FEMPTY |+ ("x",PtrVar (Var "p") 64);
         ce_var_type := (\id. if id = "x" then SOME (BaseT (BytesT (Dynamic 1)))
                            else NONE) |>
End

Definition padding_context_def:
  padding_context tx = initial_evaluation_context
    [(tx.target,[(NONE,[])])] [] tx NONE
End

Theorem padding_source_invariant_probe:
  context_well_typed (padding_context tx) ==>
  expr_sim_inv padding_cenv (padding_context tx) padding_env padding_source
Proof
  EVAL_TAC >> simp[] >> strip_tac >>
  simp[AllCaseEqs(), lookup_flag_def, vyperInterpreterTheory.lookup_function_def,
       evaluate_type_def, value_has_type_def, well_formed_type_value_def] >>
  simp[type_slot_size_def, find_var_decl_by_name_def] >> EVAL_TAC >> simp[dimword_def]
QED

Theorem padding_convert_body_pre:
  context_well_typed (padding_context tx) ==>
  expr_body_pre padding_cenv (padding_context tx) padding_env
    (TypeBuiltin (BaseT (IntT 256)) Convert (BaseT (IntT 256))
       [Name (BaseT (BytesT (Dynamic 1))) "x"]) padding_source
Proof
  strip_tac >> simp[expr_body_pre_def, padding_source_invariant_probe] >>
  EVAL_TAC >> simp[dimword_def] >> qexists_tac `[]` >>
  simp[vyperInterpreterTheory.lookup_function_def, call_edge_rel_def, irreflexive_def] >>
  simp[Once TC_CASES1, call_edge_rel_def]
QED

Theorem padding_body_inv:
  lower_vyper_runtime_unit []
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> = SOME unit ==>
  body_inv [] unit.cu_context padding_cenv (padding_context tx)
Proof
  strip_tac >> simp[body_inv_def] >>
  conj_tac
  >- EVAL_TAC >>
  conj_tac
  >- (qexistsl_tac
        [`<| rpol_target := all_capabilities;
             rpol_frontend_dispatch := Linear;
             rpol_final_assembly := FAP_Optimize |>`, `unit`] >>
      simp[padding_context_def, initial_evaluation_context_def,
           padding_cenv_def, build_compile_env_def] >> EVAL_TAC) >>
  EVAL_TAC >> simp[]
QED

Definition padding_tx_def:
  padding_tx = empty_call_txn with <| block_number := 1; block_hashes := [0w] |>
End

Definition padding_machine_def:
  padding_machine = (init_venom_state "entry") with
    <| vs_memory := REPLICATE 31 (0w:word8) ++ [1w;0w] ++ REPLICATE 31 0w;
       vs_vars := FEMPTY |+ ("p",0w); vs_alloca_next := 64;
       vs_block_ctx := empty_block_context with bc_number := 1w |>
End

Theorem padding_machine_state_rel:
  state_rel func padding_cenv (padding_context padding_tx)
    padding_source padding_machine
Proof
  rewrite_tac[state_rel_def] >> conj_tac
  >- (EVAL_TAC >> simp[AllCaseEqs(), type_memory_size_def, val_wf_def,
                       val_in_memory_def] >> EVAL_TAC >> simp[w2n_n2w]) >>
  EVAL_TAC >> simp[AllCaseEqs()]
QED

Definition padding_expr_def:
  padding_expr = TypeBuiltin (BaseT (IntT 256)) Convert (BaseT (IntT 256))
    [Name (BaseT (BytesT (Dynamic 1))) "x"]
End

Definition padding_start_def:
  padding_start = initial_compile_state "entry"
End

Definition padding_end_def:
  padding_end = SND (lower_value compile_expr padding_cenv (BaseT (IntT 256))
                    padding_expr padding_start)
End

Definition padding_function_def:
  padding_function = mk_raw_function "probe"
    [<| bb_label := "entry"; bb_instructions := padding_end.cs_current_insts |>]
End

(* The empty-program context is inhabited, but cannot host this fragment:
   alloca_room requires the running function to belong to the runtime unit. *)
Theorem padding_empty_runtime_excludes_probe:
  lower_vyper_runtime_unit []
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> = SOME unit ==>
  ~stmt_state_rel unit.cu_context padding_function padding_cenv
    (padding_context padding_tx) padding_source padding_machine
Proof
  EVAL_TAC >> simp[dimword_def] >> strip_tac >> gvs[] >> EVAL_TAC >> simp[]
QED

(* Actual program embedding: the previous synthetic function cannot be inserted
   into an unrelated runtime context. *)
Definition padding_program_def:
  padding_program =
    [FunctionDecl Internal Pure F F "probe"
       [("x",BaseT (BytesT (Dynamic 1)))] [] (BaseT (IntT 256))
       [Return (SOME padding_expr)]]
End

Definition padding_policy_def:
  padding_policy =
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
End

Theorem padding_program_supported:
  supported_program padding_program
Proof
  EVAL_TAC >> simp[]
QED

Theorem padding_program_lowers:
  IS_SOME (lower_vyper_runtime_unit padding_program padding_policy)
Proof
  EVAL_TAC >> simp[dimword_def]
QED

Definition padding_runtime_def:
  padding_runtime = THE (lower_vyper_runtime_unit padding_program padding_policy)
End

Definition padding_runtime_label_def:
  padding_runtime_label = internal_fn_label
    (build_func_ids 0 padding_program "probe") "probe"
    [BaseT (BytesT (Dynamic 1))] F
End

Definition padding_runtime_function_def:
  padding_runtime_function = THE (venomInst$lookup_function padding_runtime_label
    padding_runtime.cu_context.ctx_functions)
End

Theorem padding_runtime_function_member:
  venomInst$lookup_function padding_runtime_function.fn_name
    padding_runtime.cu_context.ctx_functions = SOME padding_runtime_function
Proof
  EVAL_TAC >> simp[dimword_def] >> EVAL_TAC >> simp[]
QED

Theorem padding_runtime_opcodes:
  MAP (\i. i.inst_opcode) (fn_insts padding_runtime_function) =
    [PARAM; RETPC_PARAM; ALLOCA; MLOAD; ADD; MLOAD; ISZERO; ISZERO;
     MUL; SUB; MUL; SAR; RET]
Proof
  EVAL_TAC >> simp[dimword_def] >> EVAL_TAC >> simp[]
QED

Theorem padding_runtime_function_equation:
  padding_runtime_function = (mk_raw_function padding_runtime_label
    [<| bb_label := padding_runtime_label;
        bb_instructions :=
          [<| inst_id := 8; inst_opcode := PARAM; inst_operands := [Lit 0w]; inst_outputs := ["%5"] |>;
           <| inst_id := 9; inst_opcode := RETPC_PARAM; inst_operands := [Lit 1w]; inst_outputs := ["%6"] |>;
           <| inst_id := 10; inst_opcode := ALLOCA; inst_operands := [Lit 32w]; inst_outputs := ["%7"] |>;
           <| inst_id := 11; inst_opcode := MLOAD; inst_operands := [Var "%5"]; inst_outputs := ["%8"] |>;
           <| inst_id := 12; inst_opcode := ADD; inst_operands := [Var "%5";Lit 32w]; inst_outputs := ["%9"] |>;
           <| inst_id := 13; inst_opcode := MLOAD; inst_operands := [Var "%9"]; inst_outputs := ["%10"] |>;
           <| inst_id := 14; inst_opcode := ISZERO; inst_operands := [Var "%8"]; inst_outputs := ["%11"] |>;
           <| inst_id := 15; inst_opcode := ISZERO; inst_operands := [Var "%11"]; inst_outputs := ["%12"] |>;
           <| inst_id := 16; inst_opcode := MUL; inst_operands := [Var "%10";Var "%12"]; inst_outputs := ["%13"] |>;
           <| inst_id := 17; inst_opcode := SUB; inst_operands := [Lit 32w;Var "%8"]; inst_outputs := ["%14"] |>;
           <| inst_id := 18; inst_opcode := MUL; inst_operands := [Var "%14";Lit 8w]; inst_outputs := ["%15"] |>;
           <| inst_id := 19; inst_opcode := SAR; inst_operands := [Var "%15";Var "%13"]; inst_outputs := ["%16"] |>;
           <| inst_id := 20; inst_opcode := RET; inst_operands := [Var "%16";Var "%6"]; inst_outputs := [] |>] |>]) with
      fn_call_abi := <| ica_has_memory_return_buffer := SOME F;
                        ica_user_return_count := SOME 1 |>
Proof
  EVAL_TAC >> simp[dimword_def] >> EVAL_TAC >> simp[]
QED

(* The runtime diagnostic fixes the actual parameter and return-PC operands,
   and places the fragment after PARAM, RETPC_PARAM and the dead return ALLOCA. *)
Definition padding_actual_cenv_def:
  padding_actual_cenv =
    (build_compile_env padding_program Internal Pure "probe"
      [("x",BaseT (BytesT (Dynamic 1)))] (BaseT (IntT 256))
      [Return (SOME padding_expr)] F) with
      <| ce_vars := FEMPTY |+ ("x",PtrVar (Var "%5") 64);
         ce_return_pc := SOME (PtrVar (Var "%6") 0) |>
End

Definition padding_actual_start_def:
  padding_actual_start =
    (initial_compile_state padding_runtime_label) with
      <| cs_next_var := 8; cs_next_id := 11;
         cs_current_insts := TAKE 3 (fn_insts padding_runtime_function) |>
End

Definition padding_actual_end_def:
  padding_actual_end = SND (lower_value compile_expr padding_actual_cenv
     (BaseT (IntT 256)) padding_expr padding_actual_start)
End

(* padding_actual_start/cenv are candidates extracted from the checked runtime
   equation.  Their lower_value equation and the complete entry predicates
   remain to be checked; runtime membership alone is not a frame certificate. *)
