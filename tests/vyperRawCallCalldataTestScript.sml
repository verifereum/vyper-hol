Theory vyperRawCallCalldataTest
Ancestors
  arithmetic list words
  jsonToVyper jsonToVyperExpr jsonAST vyperAST vyperContext vyperValue
  vyperValueOperation vyperState vyperInterpreter vyperSmallStep
  vyperTypeSystem vyperTypeContract
Libs
  vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/check_contract/raw_call_calldata.json"];

Theorem raw_call_calldata_source_shape_test:
  is_raw_call_calldata_call (JE_Name "raw_call" tc src fn_ty)
    [target; JE_Attribute (JE_Name "msg" mtc msrc mty)
       "data" atc bn btc asrc dty] /\
  ~is_raw_call_calldata_call (JE_Name "raw_call" tc src fn_ty)
    [target; JE_Attribute (JE_Name "msg" mtc msrc mty)
       "sender" atc bn btc asrc dty] /\
  ~is_raw_call_calldata_call (JE_Name "raw_call" tc src fn_ty) [target] /\
  ~is_raw_call_calldata_call (JE_Name "raw_call" tc src fn_ty)
    [target; data; extra]
Proof
  simp[is_raw_call_calldata_call_def] >> strip_tac >>
  drule is_raw_call_calldata_call_length >> simp[]
QED

(* Pinned cd74ce4f exports INF bytes metadata on msg.data and folded
   constants/BinOps on flags. The contract checker must accept all variants. *)
val fixture_input =
  {in_deploy = false, address = ``0w : address``,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     "fixtures/check_contract/raw_call_calldata.json",
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     "fixtures/check_contract/raw_call_calldata.json"};
val fixture = vyperCheckContractFrontendLib.check_contract_result fixture_input;
val target_e = ``Name (BaseT AddressT) "target"``;
val zero_e = ``Literal (BaseT (UintT 256)) (IntL 0)``;
val expected_calls = [
  ``Call NoneT (RawCallCalldataTarget
    <|rcf_max_outsize := 0; rcf_is_delegate := F; rcf_is_static := F;
      rcf_revert_on_failure := T|>)
    [^target_e; Name (BaseT (UintT 256)) "amount"] NONE``,
  ``Call (BaseT (BytesT (Dynamic 4))) (RawCallCalldataTarget
    <|rcf_max_outsize := 4; rcf_is_delegate := F; rcf_is_static := T;
      rcf_revert_on_failure := T|>) [^target_e; ^zero_e] NONE``,
  ``Call (BaseT BoolT) (RawCallCalldataTarget
    <|rcf_max_outsize := 0; rcf_is_delegate := F; rcf_is_static := F;
      rcf_revert_on_failure := F|>) [^target_e; ^zero_e] NONE``,
  ``Call (TupleT [BaseT BoolT; BaseT (BytesT (Dynamic 4))]) (RawCallCalldataTarget
    <|rcf_max_outsize := 4; rcf_is_delegate := F; rcf_is_static := F;
      rcf_revert_on_failure := F|>) [^target_e; ^zero_e] NONE``];
val () = app (fn expected =>
  if not (null (find_terms (aconv expected) (#modules fixture))) then ()
  else raise Fail "pinned raw_call calldata operands/flags were not preserved") expected_calls;

(* Decoder folding is confined to compile-time flags on this exact form.
   Even expressions carrying folded metadata remain runtime operands for
   target, value and gas, and for the entire ordinary bytes-input call. *)
val runtime_json = "{\"ast_type\":\"BinOp\",\"left\":{\"ast_type\":\"Int\",\"value\":2},\"op\":{\"ast_type\":\"Add\"},\"right\":{\"ast_type\":\"Int\",\"value\":2},\"folded_value\":{\"ast_type\":\"Int\",\"value\":4}}";
val data_json = "{\"ast_type\":\"Attribute\",\"value\":{\"ast_type\":\"Name\",\"id\":\"msg\"},\"attr\":\"data\"}";
val bool_json = "{\"ast_type\":\"NameConstant\",\"value\":true,\"folded_value\":{\"ast_type\":\"NameConstant\",\"value\":false}}";
fun decode_call source = let
  val ast = JSONDecode.decodeString jsonASTLib.annotated_ast
    ("{\"ast\":{\"body\":[{\"ast_type\":\"FunctionDef\",\"name\":\"test\",\"decorator_list\":[]," ^
     "\"args\":{\"ast_type\":\"arguments\",\"args\":[]},\"func_type\":{\"argument_types\":[],\"return_type\":null}," ^
     "\"body\":[{\"ast_type\":\"Expr\",\"value\":" ^ source ^ "}]}]}}")
  val call_tm = prim_mk_const {Thy = "jsonAST", Name = "JE_Call"}
in
  case find_terms (fn tm => let val (head, args) = strip_comb tm in
    aconv head call_tm andalso length args = 5 end) ast of
    [call] => call
  | _ => raise Fail "decoder regression did not contain one call"
end;
fun decode_raw_call data extra = decode_call
  ("{\"ast_type\":\"Call\",\"func\":{\"ast_type\":\"Name\",\"id\":\"raw_call\"},\"args\":[" ^
   runtime_json ^ "," ^ data ^ extra ^ "],\"keywords\":[" ^
   "{\"arg\":\"max_outsize\",\"value\":" ^ runtime_json ^ "}," ^
   "{\"arg\":\"value\",\"value\":" ^ runtime_json ^ "}," ^
   "{\"arg\":\"gas\",\"value\":" ^ runtime_json ^ "}," ^
   "{\"arg\":\"revert_on_failure\",\"value\":" ^ bool_json ^ "}]}");
val runtime_e = ``JE_BinOp (JE_Int 2 JT_None) JBop_Add (JE_Int 2 JT_None) JT_None``;
val source_data_e = ``JE_Attribute (JE_Name "msg" NONE JMissingSource JT_None)
  "data" NONE NONE NONE JMissingSource JT_None``;
val plain_kwargs = ``[JKeyword "max_outsize" ^runtime_e;
  JKeyword "value" ^runtime_e; JKeyword "gas" ^runtime_e;
  JKeyword "revert_on_failure" (JE_Bool T)]``;
val folded_kwargs = ``[JKeyword "max_outsize" (JE_Folded ^runtime_e (JE_Int 4 JT_None));
  JKeyword "value" ^runtime_e; JKeyword "gas" ^runtime_e;
  JKeyword "revert_on_failure" (JE_Folded (JE_Bool T) (JE_Bool F))]``;
fun expected_decoded args kwargs = ``JE_Call
  (JE_Name "raw_call" NONE JMissingSource JT_None) ^args ^kwargs JT_None JMissingSource``;
val () = app (fn (actual, expected) =>
  if aconv actual expected then ()
  else raise Fail "raw_call decoder changed runtime operands/ordinary path or lost folded flags")
  [(decode_raw_call data_json "", expected_decoded ``[^runtime_e; ^source_data_e]`` folded_kwargs),
   (decode_raw_call runtime_json "", expected_decoded ``[^runtime_e; ^runtime_e]`` plain_kwargs),
   (decode_raw_call data_json ("," ^ runtime_json),
    expected_decoded ``[^runtime_e; ^source_data_e; ^runtime_e]`` plain_kwargs)];

fun check_raw_call args flags =
  vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = false, address = ``0w : address``,
       layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
       modules = ``[(NONE, [FunctionDecl External Nonpayable F F "forward" [] []
         NoneT [Expr (Call NoneT (RawCallCalldataTarget ^flags) ^args NONE)]])]
         : (num option # toplevel list) list``});
val flags = ``<|rcf_max_outsize := 0; rcf_is_delegate := F; rcf_is_static := F;
  rcf_revert_on_failure := T|>``;
val addr_e = rhs (concl (EVAL ``Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w))``));
val () = if optionSyntax.is_some (rhs (concl (check_raw_call ``[^addr_e; ^zero_e]`` flags)))
  then () else raise Fail "valid calldata raw_call rejected";
val () = app (fn args =>
  if optionSyntax.is_none (rhs (concl (check_raw_call args flags))) then ()
  else raise Fail "malformed calldata raw_call accepted")
  [``[] : expr list``, ``[^addr_e]``, ``[^addr_e; ^zero_e; ^zero_e]``,
   ``[^zero_e; ^zero_e]``, ``[^addr_e; Literal (BaseT BoolT) (BoolL T)]``];
val () = if optionSyntax.is_none (rhs (concl (check_raw_call
    ``[^addr_e; ^zero_e]`` ``^flags with rcf_is_delegate := T``))) then ()
  else raise Fail "delegate calldata raw_call accepted";

(* Arbitrary side effects: target runs first, value sees its resulting state;
   execution receives the original transaction input without stripping a selector
   or trailing bytes and begins in the post-value state. *)
Theorem raw_call_calldata_operand_order_test:
  eval_expr cx target st = (INL (Value target_v), target_st) /\
  eval_expr cx value_e target_st = (INL (Value amount_v), value_st) /\
  dest_AddressV target_v = SOME to /\ dest_NumV amount_v = SOME amount ==>
  eval_expr cx (Call ty (RawCallCalldataTarget flags) [target; value_e] drv) st =
    eval_raw_call cx flags to cx.txn.calldata amount value_st
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def, materialise_def, return_def] >>
  simp[Once evaluate_def, bind_def, materialise_def, return_def] >>
  simp[Once evaluate_def, return_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, lift_option_type_def]
QED

Theorem raw_call_bytes_operand_order_test:
  eval_expr cx target st = (INL (Value target_v), target_st) /\
  eval_expr cx data_e target_st = (INL (Value (BytesV data)), data_st) /\
  eval_expr cx value_e data_st = (INL (Value amount_v), value_st) /\
  dest_AddressV target_v = SOME to /\ dest_NumV amount_v = SOME amount ==>
  eval_expr cx (Call ty (RawCallTarget flags) [target; data_e; value_e] drv) st =
    eval_raw_call cx flags to data amount value_st
Proof
  rpt strip_tac >> simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def, materialise_def, return_def] >>
  simp[Once evaluate_def, bind_def, materialise_def, return_def] >>
  simp[Once evaluate_def, bind_def, materialise_def, return_def] >>
  simp[Once evaluate_def, return_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, lift_option_type_def, dest_BytesV_def]
QED

Theorem raw_call_calldata_target_exception_test:
  eval_expr cx target st = (INR exc, target_st) ==>
  eval_expr cx (Call ty (RawCallCalldataTarget flags) [target; value_e] drv) st =
    (INR exc, target_st)
Proof
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def]
QED

Theorem raw_call_calldata_bad_target_state_test:
  eval_exprs cx es st = (INL [BoolV b; amount_v], operand_st) ==>
  eval_expr cx (Call ty (RawCallCalldataTarget flags) es drv) st =
    (INR (Error (TypeError "raw_call target")), operand_st)
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, lift_option_type_def, return_def, raise_def, dest_AddressV_def]
QED

Theorem raw_call_calldata_bad_value_state_test:
  eval_exprs cx es st = (INL [target_v; BoolV b], operand_st) /\
  dest_AddressV target_v = SOME to ==>
  eval_expr cx (Call ty (RawCallCalldataTarget flags) es drv) st =
    (INR (Error (TypeError "raw_call value")), operand_st)
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, lift_option_type_def, return_def, raise_def, dest_NumV_def]
QED

Theorem raw_call_calldata_malformed_arity_state_test:
  eval_exprs cx es st = (INL vs, operand_st) /\ LENGTH vs <> 2 ==>
  eval_expr cx (Call ty (RawCallCalldataTarget flags) es drv) st =
    (INR (Error (TypeError "raw_call calldata args")), operand_st)
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, raise_def]
QED

(* All existing output/revert/static variants use the same original bytes. *)
Theorem raw_call_calldata_original_input_test:
  ~flags.rcf_is_delegate /\
  cx.txn.calldata = [1w; 2w; 3w; 4w; 10w; 11w; 99w] /\
  run_ext_call cx.txn.target to cx.txn.calldata
    (if flags.rcf_is_static then NONE else SOME amount)
    st.accounts st.tStorage (vyper_to_tx_params cx.txn) =
      SOME (success, retdata, accounts', transient', logs') ==>
  eval_raw_call cx flags to cx.txn.calldata amount st =
    (if flags.rcf_revert_on_failure then
       if success then INL (Value (if flags.rcf_max_outsize = 0 then NoneV
         else BytesV (TAKE flags.rcf_max_outsize retdata)))
       else INR (Error (RuntimeError "raw_call reverted"))
     else INL (Value (if flags.rcf_max_outsize = 0 then BoolV success
       else ArrayV (TupleV [BoolV success;
         BytesV (TAKE flags.rcf_max_outsize retdata)]))),
     st with <|accounts := accounts'; tStorage := transient'; logs := st.logs ++ logs'|>)
Proof
  rpt strip_tac >>
  Cases_on `flags.rcf_revert_on_failure` >> Cases_on `success` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  gvs[eval_raw_call_def, bind_def, ignore_bind_def, type_check_def, check_def,
       assert_def, get_accounts_def, get_transient_storage_def, lift_option_def,
       update_accounts_def, update_transient_def, append_logs_def, return_def, raise_def]
QED

Theorem raw_call_calldata_recursive_cps_agreement_test:
  fromtvk (cont (eval_expr_cps cx
    (Call ty (RawCallCalldataTarget flags) es drv) st DoneK)) =
  eval_expr cx (Call ty (RawCallCalldataTarget flags) es drv) st
Proof
  simp[GSYM eval_expr_eq_cont_cps]
QED
