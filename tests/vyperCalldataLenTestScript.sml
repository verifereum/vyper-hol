Theory vyperCalldataLenTest
Ancestors
  jsonToVyperExpr vyperAST jsonAST vyperContext vyperState
  vyperInterpreter vyperSmallStep vyperTypeSystem vyperTypeBuiltins
  vyperTypeContract
Libs
  vyperCheckContractLib

(* The special form does not require a bounded bytes annotation for msg.data. *)
Theorem translate_calldata_len_test:
  translate_expr ctx
    (JE_Call (JE_Name "len" tc src fn_ty)
      [JE_Attribute (JE_Name "msg" msg_tc msg_src msg_ty)
        "data" attr_tc base_name base_tc attr_src data_ty]
      [] ret_ty call_src) =
  Builtin (BaseT (UintT 256)) CalldataLen []
Proof
  simp[Once translate_expr_def, is_calldata_len_call_def]
QED

(* Neither other attributes nor malformed arities/keywords are special forms. *)
Theorem calldata_len_source_shape_test:
  ~is_calldata_len_call (JE_Name "len" NONE JMissingSource JT_None) [] [] /\
  ~is_calldata_len_call (JE_Name "len" NONE JMissingSource JT_None)
    [JE_Attribute (JE_Name "msg" NONE JMissingSource JT_None)
      "sender" NONE NONE NONE JMissingSource JT_None] [] /\
  ~is_calldata_len_call (JE_Name "len" NONE JMissingSource JT_None)
    [JE_Attribute (JE_Name "msg" NONE JMissingSource JT_None)
      "data" NONE NONE NONE JMissingSource JT_None; JE_Bool T] [] /\
  ~is_calldata_len_call (JE_Name "len" NONE JMissingSource JT_None)
    [JE_Attribute (JE_Name "msg" NONE JMissingSource JT_None)
      "data" NONE NONE NONE JMissingSource JT_None]
    [JKeyword "extra" (JE_Bool T)]
Proof
  simp[is_calldata_len_call_def]
QED

Theorem ordinary_len_translation_test:
  make_builtin_call ty "len" args kwargs ret_ty = Builtin ty Len args
Proof
  simp[make_builtin_call_def]
QED

(* Complete raw calldata is observed: selector, ABI bytes, and trailing bytes. *)
Theorem calldata_len_selector_and_trailing_test:
  evaluate_builtin
    (cx with txn := cx.txn with calldata :=
      [a; b; c; d] ++ abi_bytes ++ trailing_bytes)
    acc (BaseT (UintT 256)) CalldataLen [] =
  INL (IntV &(4 + LENGTH abi_bytes + LENGTH trailing_bytes))
Proof
  simp[evaluate_builtin_def]
QED

Theorem calldata_len_empty_test:
  evaluate_builtin (cx with txn := cx.txn with calldata := [])
    acc (BaseT (UintT 256)) CalldataLen [] = INL (IntV 0)
Proof
  simp[evaluate_builtin_def]
QED

Theorem calldata_len_malformed_values_test:
  evaluate_builtin cx acc ty CalldataLen (v::vs) =
    INR (TypeError "builtin")
Proof
  simp[evaluate_builtin_def]
QED

Theorem calldata_len_typing_test:
  well_typed_builtin_app ty CalldataLen ts <=>
    ty = BaseT (UintT 256) /\ ts = []
Proof
  simp[well_typed_builtin_app_def, EQ_IMP_THM]
QED

Theorem calldata_len_malformed_typing_test:
  ~well_typed_builtin_app (BaseT (UintT 256)) CalldataLen [arg_ty] /\
  ~well_typed_builtin_app (BaseT (UintT 8)) CalldataLen [] /\
  ~well_typed_builtin_app (BaseT BoolT) CalldataLen []
Proof
  simp[well_typed_builtin_app_def]
QED

(* Contract-checker computation covers the new constructor too. *)
fun check_len_contract ty args = let
  val modules = ``[(NONE,
    [FunctionDecl External View F F "data_len" [] [] ^ty
      [Return (SOME (Builtin ^ty CalldataLen ^args))]])]
    : (num option # toplevel list) list``
in
  vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = false, address = ``0w : address``, modules = modules,
       layouts = ``[] : (address # (storage_layout # storage_layout)) list``})
end;

val valid_len_contract =
  check_len_contract ``BaseT (UintT 256)`` ``[] : expr list``;
val () = if optionSyntax.is_some (rhs (concl valid_len_contract)) then ()
  else raise Fail "contract checker rejected calldata length";

val wrong_len_type =
  check_len_contract ``BaseT (UintT 8)`` ``[] : expr list``;
val extra_len_argument = check_len_contract ``BaseT (UintT 256)``
  ``[Literal (BaseT (UintT 256)) (IntL 0)]``;
val () = app (fn checked =>
  if optionSyntax.is_none (rhs (concl checked)) then ()
  else raise Fail "contract checker accepted malformed calldata length")
  [wrong_len_type, extra_len_argument];

(* The recursive evaluator reads the context without changing any state. *)
Theorem calldata_len_eval_test:
  eval_expr cx (Builtin (BaseT (UintT 256)) CalldataLen []) st =
    (INL (Value (IntV &(LENGTH cx.txn.calldata))), st)
Proof
  simp[Once evaluate_def, builtin_args_length_ok_def,
       type_check_def, assert_def, ignore_bind_def, bind_def] >>
  simp[Once evaluate_def, return_def, bind_def, get_accounts_def,
       lift_sum_def, evaluate_builtin_def]
QED

Theorem calldata_len_malformed_eval_test:
  eval_expr cx (Builtin (BaseT (UintT 256)) CalldataLen (e::es)) st =
    (INR (Error (TypeError "Builtin args")), st)
Proof
  simp[Once evaluate_def, builtin_args_length_ok_def,
       type_check_def, assert_def, ignore_bind_def, bind_def]
QED

(* Exercise the CPS path and its already-proved recursive equivalence. *)
Theorem calldata_len_cps_test:
  fromtvk (cont (eval_expr_cps cx
    (Builtin (BaseT (UintT 256)) CalldataLen []) st DoneK)) =
    (INL (Value (IntV &(LENGTH cx.txn.calldata))), st)
Proof
  simp[GSYM eval_expr_eq_cont_cps, calldata_len_eval_test]
QED
