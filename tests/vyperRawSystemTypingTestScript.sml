Theory vyperRawSystemTypingTest
Ancestors
  vyperTypeSystem vyperTypeContract vyperAST vyperValue finite_map list
  jsonToVyper jsonAST
Libs
  wordsLib vyperCheckContractLib vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/check_contract/raw_log_folded_topics.json"];

Theorem raw_log_rejects_named_topics:
  !env data.
    ~well_typed_expr env
      (Call NoneT RawLog
        [Name (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic 4)) "topics";
         data] NONE)
Proof
  simp[well_typed_expr_def]
QED

Theorem raw_log_rejects_fixed_data_other_than_bytes32:
  !env topics.
    ~well_typed_expr env
      (Call NoneT RawLog
        [topics; Name (BaseT (BytesT (Fixed 1))) "data"] NONE)
Proof
  simp[well_typed_expr_def, expr_type_def]
QED

Theorem raw_log_rejects_fixed_topic_arrays:
  !env n topics data.
    ~well_typed_expr env
      (Call NoneT RawLog
        [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Fixed n))
           (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Fixed n)) topics;
         data] NONE)
Proof
  simp[well_typed_expr_def, expr_type_def]
QED

Theorem raw_log_fixed_topics_contract_rejected:
  check_contract F [] (0w : address)
    [(NONE, [FunctionDecl External Nonpayable F F "f" [] [] NoneT
      [Expr (Call NoneT RawLog
        [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Fixed 1))
           (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Fixed 1))
           [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w))];
         Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])] NONE)]])]
  = NONE
Proof
  CONV_TAC (LAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem raw_revert_rejects_fixed_data:
  !env.
    ~well_typed_expr env
      (Call NoneT RawRevert
        [Name (BaseT (BytesT (Fixed 32))) "data"] NONE)
Proof
  simp[well_typed_expr_def, expr_type_def]
QED

Theorem raw_log_accepts_literal_empty_topics:
  !env data.
    well_typed_expr env data /\
    (expr_type data = BaseT (BytesT (Fixed 32)) \/
     ?n. expr_type data = BaseT (BytesT (Dynamic n))) ==>
    well_typed_expr env
      (Call NoneT RawLog
        [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic 4))
           (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic 4)) [];
         data] NONE)
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def, expr_type_def,
       well_formed_type_def, evaluate_type_def, compatible_bound_def,
       bound_at_most_def, builtin_operands_ok_def, type_slot_size_def] >>
  simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []
QED

Theorem raw_log_accepts_literal_nonempty_topics:
  !env.
    well_typed_expr
      (env with var_types := FEMPTY |+
        ("topic", BaseT (BytesT (Fixed 32))) |+
        ("data", BaseT (BytesT (Dynamic 1))))
      (Call NoneT RawLog
        [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic 4))
           (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic 4))
           [Name (BaseT (BytesT (Fixed 32))) "topic"];
         Name (BaseT (BytesT (Dynamic 1))) "data"] NONE)
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def, expr_type_def,
       well_formed_type_def, evaluate_type_def, compatible_bound_def,
       bound_at_most_def, FLOOKUP_UPDATE, builtin_operands_ok_def,
       type_slot_size_def] >> simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []
QED

Theorem raw_revert_accepts_dynamic_data:
  !env.
    well_typed_expr
      (env with var_types := FEMPTY |+ ("data", BaseT (BytesT (Dynamic 1))))
      (Call NoneT RawRevert
        [Name (BaseT (BytesT (Dynamic 1))) "data"] NONE)
Proof
  simp[well_typed_expr_def, expr_type_def, FLOOKUP_UPDATE]
QED

(* Pinned 9362e36b preserves the original Subscript together with its
   reduced List. The frontend must use the reduced list for raw_log. *)
val folded_topics_fixture = vyperCheckContractFrontendLib.check_contract_result
  {in_deploy = false, address = ``0w : address``,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     "fixtures/check_contract/raw_log_folded_topics.json",
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     "fixtures/check_contract/raw_log_folded_topics.json"};
val expected_folded_call = ``Call NoneT RawLog
  [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic 4))
     (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic 4))
     [Literal (BaseT (BytesT (Fixed 32)))
        (BytesL [18w; 18w; 18w; 18w; 18w; 18w; 18w; 16w;
                 33w; 40w; 1w; 41w; 18w; 18w; 18w; 18w;
                 18w; 18w; 18w; 16w; 18w; 18w; 18w; 18w;
                 18w; 18w; 18w; 18w; 18w; 18w; 18w; 18w])];
   Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])] NONE``;
val () = case find_terms (aconv expected_folded_call)
    (#modules folded_topics_fixture) of
    [_] => ()
  | _ => raise Fail "folded raw_log frontend witness lost its topic or data";
val _ = save_thm ("raw_log_folded_list_frontend_accepted",
  #theorem folded_topics_fixture);
