Theory createCtorTupleLayoutWitness
Ancestors
  exprSimAbiEncodeArgsTupleProbe
  exprLowering exprLoweringProps compileEnv context emitHelper
  venomExecSemantics venomInst venomState finite_map words
  abiEncoder contractABI valueEncodingDefs vyperTypeSystem

Overload ctor_tuple_start[local] =
  ``<| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |>``

(* The wider annotation leaves the INVOKE's physical return slot at 128 bytes. *)
Theorem create_ctor_tuple_widened_rows[local]:
  omitted_defaults ce (nsid_to_string (NONE,"f")) 0 = [] /\
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow ==>
  compile_create_ctor_args compile_expr ce [tuple_call] ctor_tuple_start =
    ([LocatedValue tuple_narrow
        (base_ptr <| buf_operand := Var "%0"; buf_size := 128 |>)],
     ctor_tuple_start with <|
       cs_next_var := 1; cs_next_id := 2;
       cs_current_insts :=
         [mk_inst 0 ALLOCA [Lit 128w] ["%0"];
          mk_inst 1 INVOKE
            [Label (internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
               (nsid_to_string (NONE,"f"))
               (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor);
             Var "%0"] []] |>)
Proof
  strip_tac >>
  `toString (0:num) = "0"` by EVAL_TAC >>
  simp[compile_create_ctor_args_def, ext_call_arg_value_def,
       compile_snapshot_vv_def, expr_can_mutate_def, vv_type_def,
       Once compile_expr_def, compile_call_def,
       compile_stage_intcall_args_def,
       unwrap_value_def, tuple_call_def, tuple_narrow_def, tuple_wide_def,
       vyperASTTheory.expr_type_def, type_memory_bytes_def, is_word_type_def,
       is_bytestring_type_def, base_ptr_def, lowered_value_type_def,
       compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def]
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

(* Execute the lowered helper including its internal call and direct encoder. *)
Theorem create_ctor_tuple_widened_execution:
  omitted_defaults ce (nsid_to_string (NONE,"f")) 0 = [] /\
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  FLOOKUP env.fn_sigs (NONE,"f") = SOME sig /\
  sig.ret_ty = tuple_narrow /\ sig.param_types = [] ==>
  well_typed_expr env tuple_call /\
  ?dst len st t.
    compile_create_blueprint_args compile_expr ce F [] [tuple_call] ctor_tuple_start =
      ((dst,len),st) /\
    exec_block 1
      (ctx with ctx_functions :=
        [ctor_tuple_callee
          (internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
            (nsid_to_string (NONE,"f"))
            (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor)])
      <| bb_label := "entry";
         bb_instructions :=
           st.cs_current_insts ++ [mk_inst st.cs_next_id STOP [] []] |>
      (init_venom_state "entry") = Halt t /\
    eval_operand dst t = SOME 128w /\
    eval_operand len t = SOME 224w /\
    mem_bytes_at 128 224 t.vs_memory =
      enc (Tuple [Tuple [Bytes NONE; Bytes NONE]])
        (ListV [ListV [contractABI$BytesV [170w]; contractABI$BytesV [187w]]])
Proof
  strip_tac >> conj_tac
  >- (simp[tuple_call_def] >> irule tuple_call_typing >>
      goal_assum drule >> simp[]) >>
  drule_all create_ctor_tuple_widened_rows >> strip_tac >>
  `lowered_value_type ce tuple_call = tuple_narrow` by
    simp[tuple_call_def, lowered_value_type_def] >>
  simp[compile_create_blueprint_args_def, comp_bind_def, comp_return_def] >>
  qabbrev_tac `name =
    internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
      (nsid_to_string (NONE,"f"))
      (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor` >>
  PURE_REWRITE_TAC [tuple_narrow_def] >>
  CONV_TAC (BINDER_CONV (BINDER_CONV (BINDER_CONV (BINDER_CONV
    (LAND_CONV (LAND_CONV EVAL)))))) >>
  simp_tac (srw_ss()) [] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC >>
  simp_tac bool_ss [] >> EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC
QED
