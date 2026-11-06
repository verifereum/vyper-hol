Theory bodyPtrPopFullFrameProbe
Ancestors
  supportedProgram vyperTypeContract vyperValue words compileEnv compileVyper
  venomCompilerTypes alist integer_word fragExec exprLowering
  bodySim vyperContext vyperState vyperStorageBackend vyperInterpreter
  exprSimHypsDefs vyperTypeInvariants
Libs finite_mapLib computeLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])

(* Concrete names keep the full-entry control experiment readable. These
   definitions name a supported source fixture, not an assumed frame. *)
Definition pop_full_frame_expr_def:
  pop_full_frame_expr =
    Pop (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"a"))
End
Definition pop_full_frame_tops_def:
  pop_full_frame_tops =
    [VariableDecl Private Storage "a"
       (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (SOME 0);
     FunctionDecl Internal Nonpayable F F "take" [] []
       (BaseT (UintT 256)) [Return (SOME pop_full_frame_expr)]]
End

Theorem pop_full_frame_supported:
  supported_program pop_full_frame_tops
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Definition pop_full_frame_cenv_def:
  pop_full_frame_cenv =
    (build_compile_env pop_full_frame_tops Internal Nonpayable "take" []
      (BaseT (UintT 256)) [Return (SOME pop_full_frame_expr)] F) with
      <| ce_is_ctor := F; ce_raw_return := F;
         ce_nonreentrant := (F,0,F,F) |>
End

Theorem pop_full_frame_allocs:
  fn_allocs_ok pop_full_frame_tops
    (Nonpayable,F,F,"take",[],([] : expr list),BaseT (UintT 256),
      [Return (SOME pop_full_frame_expr)])
Proof
  simp[fn_allocs_ok_def] >> EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Definition pop_full_frame_policy_def:
  pop_full_frame_policy = THE (resolve_o1_policy (o1_policy all_capabilities))
End

Theorem pop_full_frame_unit_exists:
  IS_SOME (lower_vyper_runtime_unit pop_full_frame_tops pop_full_frame_policy)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Definition pop_full_frame_unit_def:
  pop_full_frame_unit = THE
    (lower_vyper_runtime_unit pop_full_frame_tops pop_full_frame_policy)
End

Theorem pop_full_frame_unit_lowered:
  lower_vyper_runtime_unit pop_full_frame_tops pop_full_frame_policy =
    SOME pop_full_frame_unit
Proof
  metis_tac[pop_full_frame_unit_exists, pop_full_frame_unit_def,
            optionTheory.IS_SOME_EXISTS, optionTheory.THE_DEF]
QED

(* Project the actual lowered unit, rather than supplying an unrelated fn. *)
Definition pop_full_frame_context_def:
  pop_full_frame_context = pop_full_frame_unit.cu_context
End
Definition pop_full_frame_fn_def:
  pop_full_frame_fn = THE (venomInst$lookup_function
    "internal 0 take()_runtime" pop_full_frame_context.ctx_functions)
End

Theorem pop_full_frame_fn_lookup:
  venomInst$lookup_function "internal 0 take()_runtime"
    pop_full_frame_context.ctx_functions = SOME pop_full_frame_fn
Proof
  simp[pop_full_frame_fn_def, pop_full_frame_context_def,
       pop_full_frame_unit_def] >>
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

(* The expression starts after RETPC_PARAM and the return buffer ALLOCA. *)
Definition pop_full_frame_start_def:
  pop_full_frame_start = (initial_compile_state "internal 0 take()_runtime") with
    <| cs_next_var := 7; cs_next_id := 10;
       cs_current_insts := [mk_inst 8 RETPC_PARAM [Lit 0w] ["%5"];
                            mk_inst 9 ALLOCA [Lit 32w] ["%6"]] |>
End
Definition pop_full_frame_body_env_def:
  pop_full_frame_body_env = pop_full_frame_cenv with
    <| ce_return_pc := SOME (PtrVar (Var "%5") 0);
       ce_imm_alloca := NONE; ce_alloca_locals := T |>
End
Definition pop_full_frame_compiled_def:
  pop_full_frame_compiled = compile_expr pop_full_frame_body_env
    (BaseT (UintT 256)) pop_full_frame_expr pop_full_frame_start
End

Theorem pop_full_frame_fragment:
  fn_has_code pop_full_frame_start (SND pop_full_frame_compiled)
    pop_full_frame_fn
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_full_frame_blocks:
  pop_full_frame_fn.fn_blocks =
  [<| bb_label := "internal 0 take()_runtime";
      bb_instructions :=
       [mk_inst 8 RETPC_PARAM [Lit 0w] ["%5"];
        mk_inst 9 ALLOCA [Lit 32w] ["%6"];
        mk_inst 10 SLOAD [Lit 0w] ["%7"];
        mk_inst 11 ISZERO [Var "%7"] ["%8"];
        mk_inst 12 ISZERO [Var "%8"] ["%9"];
        mk_inst 13 ASSERT [Var "%9"] [];
        mk_inst 14 SUB [Var "%7"; Lit 1w] ["%10"];
        mk_inst 15 SSTORE [Lit 0w; Var "%10"] [];
        mk_inst 16 ADD [Lit 0w; Lit 1w] ["%11"];
        mk_inst 17 MUL [Var "%10"; Lit 1w] ["%12"];
        mk_inst 18 ADD [Var "%11"; Var "%12"] ["%13"];
        mk_inst 19 SLOAD [Var "%13"] ["%14"];
        mk_inst 20 RET [Var "%14"; Var "%5"] []] |>]
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_full_frame_ids:
  fn_inst_ids_distinct pop_full_frame_fn
Proof
  simp[venomWfTheory.fn_inst_ids_distinct_def, pop_full_frame_blocks,
       venomInstTheory.mk_inst_def]
QED

Theorem pop_full_frame_vars:
  pop_full_frame_body_env.ce_vars = FEMPTY
Proof
  simp[pop_full_frame_body_env_def, pop_full_frame_cenv_def,
       build_compile_env_def] >>
  simp[allocate_args_def, allocate_internal_special_vars_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem pop_full_frame_specials:
  ~pop_full_frame_body_env.ce_is_ctor /\
  pop_full_frame_body_env.ce_return_pc = SOME (PtrVar (Var "%5") 0) /\
  pop_full_frame_body_env.ce_imm_alloca = NONE
Proof
  simp[pop_full_frame_body_env_def, pop_full_frame_cenv_def]
QED

Theorem pop_full_frame_return_buf:
  pop_full_frame_body_env.ce_return_buf = NONE
Proof
  simp[pop_full_frame_body_env_def, pop_full_frame_cenv_def,
       build_compile_env_def, allocate_args_def,
       allocate_internal_special_vars_def, returns_stack_count_def,
       is_word_type_def] >>
  pairarg_tac >> simp[]
QED

Theorem pop_full_frame_reservations:
  local_ptrs_reserved pop_full_frame_body_env pop_full_frame_start /\
  ~pop_full_frame_body_env.ce_is_ctor /\
  (!x sz. pop_full_frame_body_env.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at pop_full_frame_start x) /\
  (!x sz. pop_full_frame_body_env.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at pop_full_frame_start x)
Proof
  simp[local_ptrs_reserved_def, pop_full_frame_vars,
       pop_full_frame_specials, pop_full_frame_return_buf] >>
  `"%5" = STRING #"%" (toString (5:num))` by EVAL_TAC >>
  pop_assum SUBST1_TAC >>
  simp[not_fresh_at_def, pop_full_frame_start_def,
       ASCIInumbersTheory.toString_inj]
QED

(* A source context with the declared storage root at slot zero. *)
Definition pop_full_frame_cx_def:
  pop_full_frame_cx = empty_evaluation_context with
    <| stk := [(NONE,"take")];
       sources := [(0w,[(NONE,pop_full_frame_tops)])];
       layouts := [(0w,([((NONE,"a"),0)],[]))] |>
End

Theorem pop_full_frame_module:
  get_module_code pop_full_frame_cx NONE = SOME pop_full_frame_tops
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_tenv:
  get_tenv pop_full_frame_cx = type_env pop_full_frame_tops
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_body_inv:
  body_inv pop_full_frame_tops pop_full_frame_context
    pop_full_frame_body_env pop_full_frame_cx
Proof
  simp[body_inv_def, pop_full_frame_supported, pop_full_frame_module,
       pop_full_frame_body_env_def, pop_full_frame_cenv_def,
       build_compile_env_ce_func_ids, build_compile_env_ce_func_info,
       build_compile_env_ce_func_param_types, build_compile_env_ce_func_return_type,
       build_compile_env_ce_struct_fields] >>
  conj_tac >-
   (qexistsl [`pop_full_frame_policy`, `pop_full_frame_unit`] >>
    simp[pop_full_frame_cx_def, empty_evaluation_context_def,
         pop_full_frame_unit_lowered, pop_full_frame_context_def,
         build_compile_env_def] >>
    rpt (pairarg_tac >> simp[]) >> EVAL_TAC) >>
  simp[pop_full_frame_tenv, pop_full_frame_cx_def, empty_evaluation_context_def] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  simp[build_compile_env_def, allocate_args_def,
       allocate_internal_special_vars_def, returns_stack_count_def,
       is_word_type_def] >>
  pairarg_tac >> simp[] >> EVAL_TAC
QED

(* Concrete length-one store and source typing environment for the control. *)
Definition pop_full_frame_storage_def:
  pop_full_frame_storage : bytes32 -> bytes32 = (0w =+ 1w) (K 0w)
End
Definition pop_full_frame_es_def:
  pop_full_frame_es = set_storage pop_full_frame_cx
    (empty_state with <|scopes := [FEMPTY]; outcomes := SOME []|>)
    F pop_full_frame_storage
End
Definition pop_full_frame_env_def:
  pop_full_frame_env = function_entry_env
    (build_contract_type_artifact F [(NONE,pop_full_frame_tops)])
    [(NONE,pop_full_frame_tops)] NONE Internal []
End

Theorem pop_full_frame_source_eval:
  eval_expr pop_full_frame_cx pop_full_frame_expr pop_full_frame_es =
    (INL (PlaceR (StoragePlace F 1w (BaseTV (UintT 256)))), set_storage pop_full_frame_cx pop_full_frame_es F ((0w =+ 0w) (K 0w)))
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC >>
  simp[FUN_EQ_THM, combinTheory.UPDATE_APPLY]
QED

