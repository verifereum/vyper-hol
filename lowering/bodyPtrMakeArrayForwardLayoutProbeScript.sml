(* Forward widening is source-typed; this is not an execution witness. *)
Theory bodyPtrMakeArrayForwardLayoutProbe
Ancestors
  bodyPtrMakeArrayScalarReturnProbe vyperTypeSystem vyperValue option
  supportedProgram supportedExprs compileVyper exprLowering compileEnv supportedDecls supportedTypes supportedNames context
Libs finite_mapLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val B32 = ``BaseT (BytesT (Dynamic 32))``
val B64 = ``BaseT (BytesT (Dynamic 64))``
val N = ``TupleT [^B32; ^B32]``
val W = ``TupleT [^B64; ^B32]``
val emptyN = ``Builtin ^N (MakeArray NONE (Fixed 2))
  [Literal ^B32 (BytesL []); Literal ^B32 (BytesL [])]``
val callW = ``Call ^W (IntCall (NONE,"empty_narrow")) [] NONE``
val tops = ``[
  FunctionDecl Internal Pure F F "empty_narrow" [] ([] : expr list) ^N
    [Return (SOME ^emptyN)];
  FunctionDecl External Pure F F "read_empty" [] ([] : expr list) ^W
    [Return (SOME ^callW)]]``
val pkg = ``package_external_fn ^tops F (assign_nkeys ^tops 0)
  (Pure,F,F,"read_empty",[],([] : expr list),^W,
   [Return (SOME ^callW)])``

Theorem forward_return_widens:
  !tenv. type_widens_to tenv ^N ^W
Proof
  simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def, evaluate_type_def, type_slot_size_def, wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem forward_return_support_gates:
  supported_value_type ^tops ^N /\
  supported_value_type ^tops ^W /\
  IS_SOME (supported_function_decl ^tops (NONE,"empty_narrow") Internal) /\
  supported_function_return ^tops Internal ^N /\
  supported_return_layout ^N (Return (SOME ^emptyN)) /\
  supported_return_layout ^W (Return (SOME ^callW))
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem forward_return_call_annotation:
  expr_type ^callW = ^W
Proof
  EVAL_TAC
QED

Theorem forward_return_packaged_call_layout:
  lowered_value_type (FST (SND ^pkg)) ^callW = ^N
Proof
  simp[lowered_value_type_def, package_external_fn_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       build_compile_env_ce_func_return_type] >> EVAL_TAC
QED

Theorem forward_return_call_typing:
  FLOOKUP env.fn_sigs (NONE,"empty_narrow") = SOME sig /\
  sig.ret_ty = ^N /\ sig.param_types = [] ==>
  well_typed_expr env ^callW
Proof
  strip_tac >> simp[Once well_typed_expr_def, forward_return_widens,
                    well_formed_type_def, evaluate_type_def, type_slot_size_def, wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem forward_return_layout_sizes:
  type_memory_bytes cenv ^N = 128 /\
  type_memory_bytes cenv ^W = 160 /\
  type_memory_bytes cenv ^B32 = 64 /\
  type_memory_bytes cenv ^B64 = 96
Proof
  simp[type_memory_bytes_def]
QED

Theorem forward_return_supported_program:
  supported_program ^tops
Proof
  simp[supported_program_def, supported_declaration_headers_def,
       supported_declaration_header_def, forward_return_support_gates,
       supported_function_return_def, supported_place_type_def,
       supported_nested_type_def, supported_scalar_type_def,
       supported_string_type_def, supported_word_type_def,
       supported_declaration_names_def, supported_function_names_def,
       supported_event_names_def, supported_function_header_names_def,
       supported_function_bindings_def, supported_selectors_distinct_def,
       classify_functions_def, classify_function_def, build_selectors_def] >>
  rpt conj_tac >> EVAL_TAC
QED

(* The consumer's source type is N, not W. The tuple recursion advances
   source by 64 bytes and destination by 96 bytes after the first field.
   In contrast expr_post (loweringPosts) describes expr_type = W, whereas
   ptr_buf_ok (bodyPtrDefs) covers lowered_value_type = N. No implication
   from that W representation and N coverage to clean N headers at the
   same child endpoint has been established. This ledger is not a callee
   execution witness or a counterexample to make_array_expr_ptr_ok. *)
Theorem forward_return_typed_dispatch:
  acyclic_struct_metadata cenv.ce_struct_fields ==>
  compile_store_memory cenv src dst ^W ^N =
  compile_typed_copy_fields cenv dst src [^B64; ^B32] [^B32; ^B32] 0 0
Proof
  strip_tac >> simp[compile_store_memory_def,
    Once compile_store_memory_typed_def, is_word_type_def,
    is_bytestring_type_def]
QED
