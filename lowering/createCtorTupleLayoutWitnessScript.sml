Theory createCtorTupleLayoutWitness
Ancestors
  exprSimAbiEncodeArgsTupleProbe
  exprLowering exprLoweringProps compileEnv context emitHelper
  venomExecSemantics venomInst venomState finite_map words
  abiEncoderWindow abiEncoderInput contractABI vyperTypeSystem

Overload ctor_tuple_start[local] =
  ``<| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |>``

(* A narrow internal-call result is copied using its wider annotation. *)
Theorem create_ctor_tuple_widened_code[local]:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow ==>
  (SND (compile_create_ctor_tuple compile_expr ce [tuple_call]
    ctor_tuple_start)).cs_current_insts =
    [mk_inst 0 ALLOCA [Lit 128w] ["%0"];
     mk_inst 1 INVOKE
       [Label (internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
          (nsid_to_string (NONE,"f"))
          (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor);
        Var "%0"] [];
     mk_inst 2 ALLOCA [Lit 192w] ["%1"];
     mk_inst 3 ADD [Var "%1"; Lit 0w] ["%2"];
     mk_inst 4 MCOPY [Var "%2"; Var "%0"; Lit 192w] []]
Proof
  strip_tac >>
  `toString (0:num) = "0" /\ toString (1:num) = "1" /\
   toString (2:num) = "2"` by EVAL_TAC >>
  simp[compile_create_ctor_tuple_def, compile_multi_vvs_def,
       Once compile_expr_def, compile_call_def,
       compile_stage_intcall_args_def, compile_extcall_store_values_def,
       unwrap_value_def, tuple_call_def, tuple_narrow_def, tuple_wide_def,
       vyperASTTheory.expr_type_def, type_memory_bytes_def, is_word_type_def,
       is_bytestring_type_def, base_ptr_def,
       compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def]
QED

Theorem create_ctor_tuple_widened_encoder[local]:
  type_to_abi_enc_info ce.ce_struct_fields ce
    (TupleT (MAP expr_type [tuple_call])) =
  AbiComplex [(AbiComplex [(AbiBytestring 64,32,96,T);
                           (AbiBytestring 64,32,96,T)],32,192,T)]
Proof
  simp[tuple_call_def, tuple_wide_def, vyperASTTheory.expr_type_def,
       type_to_abi_enc_info_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, type_memory_bytes_def]
QED

Theorem create_ctor_tuple_widened_window_length[local]:
  abi_encoder_window_input
    (AbiComplex [(AbiComplex [(AbiBytestring 64,32,96,T);
                              (AbiBytestring 64,32,96,T)],32,192,T)])
    (Tuple [Tuple [Bytes NONE; Bytes NONE]])
    (ListV [ListV [contractABI$BytesV [170w]; contractABI$BytesV [187w]]])
    128 cap mem ==>
  mem_word_at 224 mem = 1w
Proof
  simp[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def] >>
  strip_tac >>
  first_x_assum (qspecl_then [`1`, `AbiBytestring 64`, `32`, `96`, `T`] mp_tac) >>
  simp[abi_encoder_member_span_def, abi_encoder_window_bytes_iff] >>
  strip_tac >> simp[]
QED

Overload ctor_tuple_callee[local] =
  ``\name. mk_raw_function name
     [<| bb_label := "tuple_entry"; bb_instructions :=
       [mk_inst 0 PARAM [Lit 0w] ["p"];
        mk_inst 1 MSTORE [Var "p"; Lit 1w] [];
        mk_inst 2 ADD [Var "p"; Lit 32w] ["q"];
        mk_inst 3 MSTORE [Var "q"; Lit (n2w (170 * 2 ** 248))] [];
        mk_inst 4 ADD [Var "p"; Lit 64w] ["r"];
        mk_inst 5 MSTORE [Var "r"; Lit 1w] [];
        mk_inst 6 ADD [Var "p"; Lit 96w] ["z"];
        mk_inst 7 MSTORE [Var "z"; Lit (n2w (187 * 2 ** 248))] [];
        mk_inst 8 RET [Lit 0w] []] |>]``

(* Execute the helper itself, including its real internal-call instruction. *)
Theorem create_ctor_tuple_widened_execution[local]:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow ==>
  ?t.
    exec_block 1
      (ctx with ctx_functions :=
        [ctor_tuple_callee
          (internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
            (nsid_to_string (NONE,"f"))
            (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor)])
      <| bb_label := "entry";
         bb_instructions :=
           (SND (compile_create_ctor_tuple compile_expr ce [tuple_call]
             ctor_tuple_start)).cs_current_insts ++ [mk_inst 5 STOP [] []] |>
      (init_venom_state "entry") = Halt t /\
    lookup_var "%1" t = SOME 128w /\
    t.vs_alloca_next = 320 /\
    mem_word_at 224 t.vs_memory = n2w (187 * 2 ** 248)
Proof
  strip_tac >> drule_all create_ctor_tuple_widened_code >> strip_tac >>
  asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `ctor_tuple_callee name` >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC >>
  simp_tac bool_ss [] >> EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC
QED

Theorem create_ctor_tuple_widened_counterexample:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  FLOOKUP env.fn_sigs (NONE,"f") = SOME sig /\
  sig.ret_ty = tuple_narrow /\ sig.param_types = [] ==>
  well_typed_expr env tuple_call /\
  ?t.
    exec_block 1
      (ctx with ctx_functions :=
        [ctor_tuple_callee
          (internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
            (nsid_to_string (NONE,"f"))
            (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor)])
      <| bb_label := "entry";
         bb_instructions :=
           (SND (compile_create_ctor_tuple compile_expr ce [tuple_call]
             ctor_tuple_start)).cs_current_insts ++ [mk_inst 5 STOP [] []] |>
      (init_venom_state "entry") = Halt t /\
    lookup_var "%1" t = SOME 128w /\
    (!cap. ~abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce
        (TupleT (MAP expr_type [tuple_call])))
      (Tuple [Tuple [Bytes NONE; Bytes NONE]])
      (ListV [ListV [contractABI$BytesV [170w]; contractABI$BytesV [187w]]])
      128 cap t.vs_memory)
Proof
  strip_tac >> conj_tac
  >- (simp[tuple_call_def] >> irule tuple_call_typing >>
      goal_assum drule >> simp[]) >>
  drule_all create_ctor_tuple_widened_execution >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` strip_assume_tac)) >>
  qexists_tac `t` >> simp[create_ctor_tuple_widened_encoder] >>
  `n2w (187 * 2 ** 248) <> (1w:bytes32)` by
    (CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC) >>
  rpt strip_tac >> drule create_ctor_tuple_widened_window_length >> simp[]
QED
