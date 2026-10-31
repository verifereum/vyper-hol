(* Custom-error declaration, typing, ABI payload, and execution regressions. *)
Theory vyperCustomErrorTest
Ancestors
  vyperTypeContract vyperSmallStep[ignore_grammar] extCallOracle
  vyperCallOutcome[ignore_grammar] vfmState[ignore_grammar]
  vfmExecution[ignore_grammar] vyperState vyperContext vyperABI vyperAST
  vyperValue list finite_map words vfmTypes
Libs
  cv_transLib wordsLib

Definition custom_error_uint_def:
  custom_error_uint = BaseT (UintT 256)
End

Definition simple_error_payload_def:
  simple_error_payload = [252w; 217w; 54w; 177w] : word8 list
End

Definition ordered_error_payload_def:
  ordered_error_payload =
    [62w; 186w; 110w; 78w] ++
    REPLICATE 31 0w ++ [1w] ++ REPLICATE 31 0w ++ [2w] : word8 list
End

Definition fancy_error_payload_def:
  fancy_error_payload =
    [230w; 32w; 47w; 173w] ++
    REPLICATE 31 0w ++ [64w] ++
    REPLICATE 31 0w ++ [3w] ++
    REPLICATE 31 0w ++ [2w] ++ [104w; 105w] ++ REPLICATE 30 0w : word8 list
End
val () = cv_auto_trans custom_error_uint_def;
val () = cv_auto_trans simple_error_payload_def;
val () = cv_auto_trans ordered_error_payload_def;
val () = cv_auto_trans fancy_error_payload_def;


Theorem zero_argument_custom_error_payload:
  build_custom_error_data FEMPTY "Simple" [] [] = SOME simple_error_payload
Proof
  CONV_TAC cv_eval
QED

Theorem static_custom_error_payload:
  build_custom_error_data FEMPTY "Ordered"
    [custom_error_uint; custom_error_uint] [IntV 1; IntV 2] =
    SOME ordered_error_payload
Proof
  CONV_TAC cv_eval
QED

Theorem dynamic_custom_error_payload:
  build_custom_error_data FEMPTY "Fancy"
    [BaseT (StringT 16); custom_error_uint] [StringV "hi"; IntV 3] =
    SOME fancy_error_payload
Proof
  CONV_TAC cv_eval
QED

Definition one_expr_def:
  one_expr = Literal custom_error_uint (IntL 1)
End

Definition two_expr_def:
  two_expr = Literal custom_error_uint (IntL 2)
End

Theorem custom_error_keyword_declaration_order:
  order_custom_error_args
    [("a",custom_error_uint); ("b",custom_error_uint)]
    (CustomError (NONE,"Ordered") [] [("a",one_expr); ("b",two_expr)]) =
    SOME [one_expr; two_expr] /\
  order_custom_error_args
    [("a",custom_error_uint); ("b",custom_error_uint)]
    (CustomError (NONE,"Ordered") [] [("b",two_expr); ("a",one_expr)]) = NONE /\
  order_custom_error_args
    [("a",custom_error_uint); ("b",custom_error_uint)]
    (CustomError (NONE,"Ordered") [] [("a",one_expr)]) = NONE /\
  order_custom_error_args
    [("a",custom_error_uint); ("b",custom_error_uint)]
    (CustomError (NONE,"Ordered") [] [("a",one_expr); ("c",two_expr)]) = NONE /\
  order_custom_error_args
    [("a",custom_error_uint); ("b",custom_error_uint)]
    (CustomError (NONE,"Ordered") [] [("a",one_expr); ("a",two_expr)]) = NONE /\
  order_custom_error_args
    [("a",custom_error_uint); ("b",custom_error_uint)]
    (CustomError (NONE,"Ordered") [one_expr] [("b",two_expr)]) = NONE
Proof
  EVAL_TAC
QED

Definition custom_error_program_def:
  custom_error_program name args =
    [(NONE,
      [ErrorDecl "Ordered" [("a",custom_error_uint); ("b",custom_error_uint)];
       FunctionDecl External Nonpayable F F "run" [] [] NoneT
         [Raise (RaiseCustomError (CustomError (NONE,name) args []))]])]
End

Theorem custom_error_contract_checker:
  IS_SOME (check_contract F [] 0w
    (custom_error_program "Ordered" [one_expr; two_expr])) /\
  check_contract F [] 0w
    (custom_error_program "Missing" [one_expr; two_expr]) = NONE /\
  check_contract F [] 0w
    (custom_error_program "Ordered" [one_expr]) = NONE /\
  check_contract F [] 0w
    (custom_error_program "Ordered"
      [one_expr; Literal (BaseT BoolT) (BoolL T)]) = NONE
Proof
  EVAL_TAC >> simp[]
QED

Definition custom_error_call_def:
  custom_error_call target =
    Call custom_error_uint (ExtCall T F ("f",[],custom_error_uint) [])
      [Literal (BaseT AddressT)
        (BytesL (REPLICATE 19 0w ++ [target]))] NONE
End

Definition custom_error_outcome_def:
  custom_error_outcome n =
    <|co_success := T;
      co_returnData := REPLICATE 31 0w ++ [n2w n];
      co_accounts := empty_accounts;
      co_tStorage := empty_transient_storage;
      co_logs := [];
      co_toDelete := []|>
End

Definition custom_error_context_def:
  custom_error_context = empty_evaluation_context with
    sources := [(0w,[(NONE,
      [ErrorDecl "Ordered"
        [("a",custom_error_uint); ("b",custom_error_uint)]])])]
End

Definition custom_error_state_def:
  custom_error_state = empty_state with
    outcomes := SOME [custom_error_outcome 1; custom_error_outcome 2]
End

Definition custom_error_body_def:
  custom_error_body =
    [Raise (RaiseCustomError
      (CustomError (NONE,"Ordered")
        [custom_error_call 9w; custom_error_call 10w] []))]
End

Definition custom_error_execution_observations_def:
  custom_error_execution_observations res ⇔
    FST res = INR (Error (RevertData ordered_error_payload)) /\
    MAP (\request. request.cr_target) (SND res).requests = [9w; 10w] /\
    (SND res).outcomes = SOME [] /\
    (SND res).logs = []
End
val () = cv_auto_trans custom_error_call_def;
val () = cv_auto_trans custom_error_outcome_def;
val () = cv_auto_trans custom_error_context_def;
val () = cv_auto_trans custom_error_state_def;
val () = cv_auto_trans custom_error_body_def;
val () = cv_auto_trans custom_error_execution_observations_def;


Definition custom_error_cps_execution_test_def:
  custom_error_cps_execution_test =
    custom_error_execution_observations
      (vyperSmallStep$fromk (vyperSmallStep$cont
        (vyperSmallStep$eval_stmts_cps custom_error_context custom_error_body
          custom_error_state vyperSmallStep$DoneK)))
End
val () = cv_trans custom_error_cps_execution_test_def;

Theorem custom_error_arguments_left_to_right_once:
  custom_error_cps_execution_test
Proof
  CONV_TAC cv_eval
QED
(* An error declared in an imported module, raised by its qualified name. *)
Definition imported_error_context_def:
  imported_error_context = empty_evaluation_context with
    sources := [(0w,[(NONE,[]);
      (SOME 1,
        [ErrorDecl "Ordered"
          [("a",custom_error_uint); ("b",custom_error_uint)]])])]
End

Definition imported_error_body_def:
  imported_error_body =
    [Raise (RaiseCustomError
      (CustomError (SOME 1,"Ordered") [one_expr; two_expr] []))]
End
val () = cv_auto_trans imported_error_context_def;
val () = cv_auto_trans imported_error_body_def;

Definition imported_error_cps_test_def:
  imported_error_cps_test =
    (FST (vyperSmallStep$fromk (vyperSmallStep$cont
      (vyperSmallStep$eval_stmts_cps imported_error_context imported_error_body
        empty_state vyperSmallStep$DoneK))) =
     INR (Error (RevertData ordered_error_payload)))
End
val () = cv_trans imported_error_cps_test_def;

Theorem imported_custom_error_payload:
  imported_error_cps_test
Proof
  CONV_TAC cv_eval
QED

Theorem custom_error_recursive_cps_exact_agreement:
  custom_error_execution_observations
    (vyperInterpreter$eval_stmts custom_error_context custom_error_body
      custom_error_state)
Proof
  once_rewrite_tac[eval_stmts_eq_cont_cps]
  \\ once_rewrite_tac[GSYM custom_error_cps_execution_test_def]
  \\ ACCEPT_TAC custom_error_arguments_left_to_right_once
QED

