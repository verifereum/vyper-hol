Theory vyperCalldataSliceTest
Ancestors
  arithmetic integer list words
  jsonToVyper jsonToVyperExpr jsonAST vyperAST vyperContext vyperValue
  vyperValueOperation vyperState vyperInterpreter vyperSmallStep
  vyperTypeSystem vyperTypeBuiltins vyperTypeContract
Libs
  vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/check_contract/calldata_slice.json"];

Theorem calldata_slice_compile_time_length_test:
  calldata_slice_length (JE_Int 4 ty) = SOME 4 /\
  calldata_slice_length (JE_Folded original (JE_Int 4 ty)) = SOME 4 /\
  calldata_slice_length (JE_Int 0 ty) = NONE /\
  calldata_slice_length (JE_Int (-1) ty) = NONE /\
  calldata_slice_length (JE_Int (&(2n ** 256)) ty) = NONE /\
  calldata_slice_length (JE_Name "length" tc src ty) = NONE
Proof
  simp[calldata_slice_length_def]
QED

Theorem calldata_slice_source_shape_test:
  is_calldata_slice_call (JE_Name "slice" tc src fn_ty)
    [JE_Attribute (JE_Name "msg" mtc msrc mty)
       "data" atc bn btc asrc dty; start; len] /\
  ~is_calldata_slice_call (JE_Name "slice" tc src fn_ty)
    [JE_Attribute (JE_Name "msg" mtc msrc mty)
       "sender" atc bn btc asrc dty; start; len] /\
  ~is_calldata_slice_call (JE_Name "slice" tc src fn_ty) []
Proof
  simp[is_calldata_slice_call_def]
QED

Theorem calldata_slice_start_translation_test:
  translate_expr ctx
    (JE_Call (JE_Name "slice" tc src fn_ty)
      [JE_Attribute (JE_Name "msg" mtc msrc mty)
         "data" atc bn btc asrc dty; start; JE_Int 4 lty]
      [] ret_ty call_src) =
  Builtin (BaseT (BytesT (Dynamic 4))) (CalldataSlice 4)
    [translate_expr ctx start]
Proof
  simp[Once translate_expr_def, is_calldata_len_call_def,
       is_calldata_slice_call_def, calldata_slice_bound_def,
       calldata_slice_length_def] >>
  simp[Once translate_expr_def] >> simp[Once translate_expr_def]
QED

Theorem calldata_slice_zero_marker_typing_test:
  ~well_typed_builtin_app ty (CalldataSlice 0) ts /\
  ~well_typed_builtin_app (BaseT (BytesT (Dynamic 4))) (CalldataSlice 4) [] /\
  ~well_typed_builtin_app (BaseT (BytesT (Dynamic 3))) (CalldataSlice 4)
    [BaseT (UintT 256)] /\
  ~well_typed_builtin_app (BaseT (BytesT (Dynamic 4))) (CalldataSlice 4)
    [BaseT BoolT]
Proof
  simp[well_typed_builtin_app_def]
QED

(* Exported by pinned Vyper cd74ce4f: literal, folded Name, folded BinOp. *)
val fixture = vyperCheckContractFrontendLib.check_contract_result
  {in_deploy = false, address = ``0w : address``,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     "fixtures/check_contract/calldata_slice.json",
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     "fixtures/check_contract/calldata_slice.json"};
val function_tm = prim_mk_const {Thy = "vyperAST", Name = "FunctionDecl"};
val functions = find_terms (fn tm =>
  case strip_comb tm of (head, args) =>
    aconv head function_tm andalso length args = 9) (#modules fixture);
val expected_slice = ``Builtin (BaseT (BytesT (Dynamic 4))) (CalldataSlice 4)
  [Name (BaseT (UintT 256)) "start"]``;
val () = if length functions = 3 andalso
    List.all (fn func => not (null (find_terms (aconv expected_slice) func))) functions
  then () else raise Fail "pinned literal/folded calldata slices were not preserved";

val data_expr = ``JE_Attribute
  (JE_Name "msg" NONE JMissingSource JT_None)
  "data" NONE NONE NONE JMissingSource JT_None``;
val start_expr = ``JE_Int 0 (JT_Integer 256 F)``;
val length_expr = ``JE_Int 4 (JT_Integer 256 F)``;
fun translate_slice args kwargs = rhs (concl (bossLib.EVAL
  ``translate_expr (0, NONE, [], [], [], [])
    (JE_Call (JE_Name "slice" NONE JMissingSource JT_None)
      ^args ^kwargs (JT_Bytes 4) JMissingSource)``));
fun check_slice_expr expression =
  vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = false, address = ``0w : address``,
       layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
       modules = ``[(NONE,
         [FunctionDecl External View F F "slice_data" [] []
           (BaseT (BytesT (Dynamic 4))) [Return (SOME ^expression)]])]
         : (num option # toplevel list) list``});
val valid_expression = translate_slice
  ``[^data_expr; ^start_expr; ^length_expr]`` ``[] : json_keyword list``;
val () = if optionSyntax.is_some (rhs (concl (check_slice_expr valid_expression)))
  then () else raise Fail "valid translated calldata slice rejected";
val wrong_start_expression = translate_slice
  ``[^data_expr; JE_Bool T; ^length_expr]`` ``[] : json_keyword list``;
val () = if optionSyntax.is_none (rhs (concl (check_slice_expr wrong_start_expression)))
  then () else raise Fail "contract checker accepted non-uint256 calldata start";
val invalid_calls = [
  (``[^data_expr; ^start_expr]``, ``[] : json_keyword list``),
  (``[^data_expr; ^start_expr; ^length_expr; JE_Bool T]``, ``[] : json_keyword list``),
  (``[^data_expr; ^start_expr; ^length_expr]``, ``[JKeyword "length" ^length_expr]``),
  (``[^data_expr; ^start_expr; JE_Int 0 (JT_Integer 256 F)]``, ``[] : json_keyword list``),
  (``[^data_expr; ^start_expr; JE_Int (-1) (JT_Integer 256 F)]``, ``[] : json_keyword list``),
  (``[^data_expr; ^start_expr; JE_Name "length" NONE JMissingSource (JT_Integer 256 F)]``,
   ``[] : json_keyword list``)];
val marker = ``Builtin (BaseT (BytesT (Dynamic 0))) (CalldataSlice 0) []``;
val () = app (fn (args, kwargs) => let
  val expression = translate_slice args kwargs
in
  if aconv expression marker andalso
     optionSyntax.is_none (rhs (concl (check_slice_expr expression))) then ()
  else raise Fail "malformed calldata slice did not translate to a rejected marker"
end) invalid_calls;

(* Full selector/ABI/trailing bytes, with exact-end inclusion and no padding. *)
Theorem calldata_slice_content_test:
  evaluate_calldata_slice [1w; 2w; 3w; 4w; 10w; 11w; 99w] (IntV 0) 4 =
    INL (BytesV [1w; 2w; 3w; 4w]) /\
  evaluate_calldata_slice [1w; 2w; 3w; 4w; 10w; 11w; 99w] (IntV 4) 3 =
    INL (BytesV [10w; 11w; 99w]) /\
  evaluate_calldata_slice [1w; 2w; 3w; 4w; 10w; 11w; 99w] (IntV 6) 1 =
    INL (BytesV [99w]) /\
  evaluate_calldata_slice [1w; 2w; 3w; 4w; 10w; 11w; 99w] (IntV 6) 2 =
    INR (RuntimeError "evaluate_slice range") /\
  evaluate_calldata_slice [] (IntV 0) 1 = INR (RuntimeError "evaluate_slice range")
Proof
  EVAL_TAC
QED

Theorem calldata_slice_overflow_test:
  evaluate_calldata_slice bs (IntV (&(2n ** 256) - 1)) 1 =
    INR (RuntimeError "calldata slice overflow") /\
  evaluate_calldata_slice bs (IntV &(2n ** 256)) 4 =
    INR (RuntimeError "calldata slice overflow")
Proof
  EVAL_TAC
QED

Theorem calldata_slice_malformed_arity_test:
  evaluate_builtin cx acc ty (CalldataSlice n) [] = INR (TypeError "builtin") /\
  evaluate_builtin cx acc ty (CalldataSlice n) [sv; lv] = INR (TypeError "builtin")
Proof
  simp[evaluate_builtin_def]
QED

(* For an arbitrary, possibly side-effectful start expression, evaluation occurs
   before bounds checking and the resulting state is retained without edits. *)
Theorem calldata_slice_eval_start_state_test:
  eval_expr cx start st = (INL (Value sv), st') /\
  evaluate_calldata_slice cx.txn.calldata sv n = INL v ==>
  eval_expr cx (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [start]) st =
    (INL (Value v), st')
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, builtin_args_length_ok_def, type_check_def,
       assert_def, ignore_bind_def, bind_def] >>
  simp[Once evaluate_def, bind_def, materialise_def, return_def] >>
  simp[Once evaluate_def, bind_def, return_def, get_accounts_def,
       evaluate_builtin_def, lift_sum_def]
QED

Theorem calldata_slice_eval_range_error_state_test:
  eval_expr cx start st = (INL (Value sv), st') /\
  evaluate_calldata_slice cx.txn.calldata sv n = INR err ==>
  eval_expr cx (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [start]) st =
    (INR (Error err), st')
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, builtin_args_length_ok_def, type_check_def,
       assert_def, ignore_bind_def, bind_def] >>
  simp[Once evaluate_def, bind_def, materialise_def, return_def] >>
  simp[Once evaluate_def, bind_def, return_def, get_accounts_def,
       evaluate_builtin_def, lift_sum_def, raise_def]
QED

Theorem calldata_slice_cps_start_state_test:
  eval_expr cx start st = (INL (Value sv), st') /\
  evaluate_calldata_slice cx.txn.calldata sv n = INL v ==>
  fromtvk (cont (eval_expr_cps cx
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [start]) st DoneK)) =
    (INL (Value v), st')
Proof
  simp[GSYM eval_expr_eq_cont_cps] >>
  ACCEPT_TAC calldata_slice_eval_start_state_test
QED
