Theory bodySimAugPlaceComputationProbe
Ancestors
  vyperTypeSystem vyperTyping vyperInterpreter vyperState vyperStorage vyperValue vyperAST
  finite_map words compileEnv vyperCompiler stmtLowering venomExecSemantics venomState vfmState
Libs
  wordsLib

Definition aug_place_compute_inner_ty_def:
  aug_place_compute_inner_ty = ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Dynamic 1)
End
Definition aug_place_compute_ty_def:
  aug_place_compute_ty = ArrayT aug_place_compute_inner_ty (Dynamic 1)
End
Definition aug_place_compute_rhs_def:
  aug_place_compute_rhs = Builtin aug_place_compute_ty
    (MakeArray (SOME aug_place_compute_inner_ty) (Dynamic 1))
    [Builtin aug_place_compute_inner_ty
      (MakeArray (SOME (ArrayT (BaseT (UintT 256)) (Fixed 1))) (Dynamic 1)) []]
End
Definition aug_place_compute_body_def:
  aug_place_compute_body =
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"outer"))) aug_place_compute_rhs;
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]
End
Definition aug_place_compute_tops_def:
  aug_place_compute_tops =
    [VariableDecl Private Storage "outer" aug_place_compute_ty (SOME 0);
     FunctionDecl Internal Nonpayable F F "key" [] [] (BaseT (UintT 256))
       aug_place_compute_body]
End
Definition aug_place_compute_env_def:
  aug_place_compute_env = <|
    current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY |+ ((NONE,"outer"),Type aug_place_compute_ty);
    type_defs := type_env aug_place_compute_tops;
    fn_sigs := FEMPTY |+ ((NONE,"key"),
      <|param_types := []; num_defaults := 0; ret_ty := BaseT (UintT 256)|>);
    flag_members := FEMPTY |>
End
Theorem aug_place_compute_typed:
  IS_SOME (type_stmts aug_place_compute_env (BaseT (UintT 256)) aug_place_compute_body)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def]
QED

Definition aug_place_compute_cenv_def:
  aug_place_compute_cenv = <|
    ce_target := all_capabilities;
    ce_vars := FEMPTY;
    ce_module_vars := FEMPTY |+ ((NONE,"outer"),StorageLoc 0w);
    ce_storage_layout := FEMPTY; ce_module := NONE;
    ce_struct_fields := FEMPTY;
    ce_dynarray_capacity := K 0;
    ce_module_dynarray_capacity := (\n. if n = (NONE,"outer") then 1 else 0);
    ce_method_id := (\n ts. 0); ce_flag_member_id := (\n m. 0);
    ce_flag_n_members := K 0; ce_var_type := K NONE;
    ce_module_var_type := (\n. if n = (NONE,"outer") then SOME aug_place_compute_ty else NONE);
    ce_hashmap_info := K NONE; ce_event_info := K NONE;
    ce_type_env := type_env aug_place_compute_tops;
    ce_returns_count := 1; ce_return_buf := NONE; ce_return_pc := NONE;
    ce_ctor_exit_label := NONE; ce_is_external := F;
    ce_ret_enc_info := AbiPrimWord; ce_ret_dec_info := DecPrimWord NoClamp;
    ce_max_return_size := 32; ce_is_ctor := F; ce_imm_alloca := NONE;
    ce_func_info := K (0,0,[]); ce_func_param_types := K [];
    ce_func_ids := K 0; ce_nonreentrant := (F,0,F,F);
    ce_raw_return := F; ce_alloca_locals := T |>
End
Definition aug_place_compute_lowered_def:
  aug_place_compute_lowered = SND (compile_stmt aug_place_compute_cenv NoLoop
    (BaseT (UintT 256)) (HD aug_place_compute_body) (initial_compile_state "entry"))
End
Theorem aug_place_compute_copy_selected:
  MAP (\i. i.inst_opcode)
    (EL 1 aug_place_compute_lowered.cs_blocks).bb_instructions =
    [MUL; ADD; MLOAD; ADD; SSTORE; ADD; ASSIGN; JMP] /\
  MAP (\i. i.inst_opcode)
    (EL 5 aug_place_compute_lowered.cs_blocks).bb_instructions =
    [ALLOCA; MSTORE; ALLOCA; MSTORE; ADD; MCOPY; MLOAD; ASSIGN; JMP]
Proof
  EVAL_TAC
QED

Definition aug_place_compute_cx_def:
  aug_place_compute_cx = empty_evaluation_context with
    <| stk := [(NONE,"caller")];
       sources := [(0w,[(NONE,aug_place_compute_tops)])];
       layouts := [(0w,([((NONE,"outer"),0)],[]))] |>
End
Definition aug_place_compute_initial_def:
  aug_place_compute_initial = empty_state with accounts :=
    (0w =+ (empty_account_state with storage :=
       (0w =+ 1w) ((1w =+ 1w) ((2w =+ 7w) (K 0w))))) empty_accounts
End
Definition aug_place_compute_target_def:
  aug_place_compute_target = SubscriptTarget
    (SubscriptTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"outer"))
        (Literal (BaseT (UintT 256)) (IntL 0)))
      (Literal (BaseT (UintT 256)) (IntL 0)))
    (Call (BaseT (UintT 256)) (IntCall (NONE,"key")) [] NONE)
End
Theorem aug_place_compute_source_capture:
  let (r,s) = eval_target_place aug_place_compute_cx aug_place_compute_target
                aug_place_compute_initial in
    r = INL (StoragePlace F 2w (BaseTV (UintT 256))) /\
    get_storage aug_place_compute_cx s F 0w = 1w /\
    get_storage aug_place_compute_cx s F 1w = 0w /\
    read_place aug_place_compute_cx (StoragePlace F 2w (BaseTV (UintT 256))) s =
      (INL (IntV 7),s)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, wordsTheory.WORD_ADD_0, return_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, return_def] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def] >> EVAL_TAC >>
  simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def]
QED

Definition aug_place_compute_fn_def:
  aug_place_compute_fn = mk_raw_function "probe"
    (<| bb_label := aug_place_compute_lowered.cs_current_bb;
        bb_instructions := aug_place_compute_lowered.cs_current_insts ++
          [<|inst_id := 34; inst_opcode := STOP; inst_operands := []; inst_outputs := []|>] |>
      :: aug_place_compute_lowered.cs_blocks)
End
Definition aug_place_compute_backend_def:
  aug_place_compute_backend = (ARB:venom_state) with
    <| vs_memory := []; vs_vars := FEMPTY; vs_allocas := FEMPTY;
       vs_alloca_next := 0; vs_current_bb := "entry"; vs_inst_idx := 0;
       vs_halted := F; vs_prev_bb := NONE;
       vs_accounts := aug_place_compute_initial.accounts;
       vs_call_ctx := (ARB:call_context) with cc_address := 0w |>
End
Theorem aug_place_compute_backend_copy:
  case run_blocks 20 ARB aug_place_compute_fn aug_place_compute_backend of
    Halt s => sload 0w s = 1w /\ sload 1w s = 0w /\ sload 2w s = 0w
  | _ => F
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC >> simp[]
QED
