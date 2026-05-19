Theory evalCompiler
Ancestors compileVyper concretizeMemLocDefs alist integer_word
Libs finite_mapLib computeLib wordsLib

val () = the_compset := add_finite_map_compset(!the_compset)
val () = the_compset := computeLib.add_thms [fmap_to_alist_FEMPTY] (!the_compset)
val () = the_compset := computeLib.add_thms [i2w_pos] (!the_compset)

val () = Globals.max_print_depth := 20

Definition compile_vyper_lengths_def:
  compile_vyper_lengths (tops : toplevel list)
                        pipeline dispatch_strategy =
    case compile_vyper tops pipeline dispatch_strategy of
      NONE => NONE
    | SOME (deploy_bs, runtime_bs) =>
        SOME (LENGTH deploy_bs, LENGTH runtime_bs)
End

Definition noop_program_def:
  noop_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) NoneT [Pass]]
End

Definition return_uint_program_def:
  return_uint_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]]
End

Definition return_arg_program_def:
  return_arg_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Name (BaseT (UintT 256)) "x"))]]
End

Definition local_uint_program_def:
  local_uint_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 1));
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition add_arg_program_def:
  add_arg_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Builtin (BaseT (UintT 256)) (Bop Add)
             [Name (BaseT (UintT 256)) "x";
              Literal (BaseT (UintT 256)) (IntL 1)]))]]
End

Definition two_external_program_def:
  two_external_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))];
     FunctionDecl External Nonpayable F F "bar"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 2)))]]
End

Definition storage_read_program_def:
  storage_read_program =
    [VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))]]
End

Definition storage_write_program_def:
  storage_write_program =
    [VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "stored")))
          (Literal (BaseT (UintT 256)) (IntL 5));
        Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))]]
End

Definition hashmap_read_program_def:
  hashmap_read_program =
    [HashMapDecl Private F "stored" (BaseT (UintT 256))
       (Type (BaseT (UintT 256))) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       [("k", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Subscript (BaseT (UintT 256))
             (TopLevelName NoneT (NONE, "stored"))
             (Name (BaseT (UintT 256)) "k")))]]
End

Definition hashmap_write_program_def:
  hashmap_write_program =
    [HashMapDecl Private F "stored" (BaseT (UintT 256))
       (Type (BaseT (UintT 256))) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       [("k", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Assign (BaseTarget
          (SubscriptTarget (TopLevelNameTarget (NONE, "stored"))
             (Name (BaseT (UintT 256)) "k")))
          (Literal (BaseT (UintT 256)) (IntL 5));
        Return (SOME
          (Subscript (BaseT (UintT 256))
             (TopLevelName NoneT (NONE, "stored"))
             (Name (BaseT (UintT 256)) "k")))]]
End

Definition if_bool_program_def:
  if_bool_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT BoolT)] ([] : expr list) (BaseT (UintT 256))
       [If (Name (BaseT BoolT) "x")
          [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]
          [Return (SOME (Literal (BaseT (UintT 256)) (IntL 2)))]]]
End

Definition if_join_program_def:
  if_join_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT BoolT)] ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 1));
        If (Name (BaseT BoolT) "x")
          [Assign (BaseTarget (NameTarget "y"))
             (Literal (BaseT (UintT 256)) (IntL 2))]
          [Assign (BaseTarget (NameTarget "y"))
             (Literal (BaseT (UintT 256)) (IntL 3))];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition for_pass_program_def:
  for_pass_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 2)))
          0
          [Pass];
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]]
End

Definition for_accum_program_def:
  for_accum_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 2)))
          0
          [Assign (BaseTarget (NameTarget "y"))
             (Builtin (BaseT (UintT 256)) (Bop Add)
                [Name (BaseT (UintT 256)) "y";
                 Name (BaseT (UintT 256)) "i"])];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition for_continue_program_def:
  for_continue_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 3)))
          0
          [If (Builtin (BaseT BoolT) (Bop Eq)
                 [Name (BaseT (UintT 256)) "i";
                  Literal (BaseT (UintT 256)) (IntL 1)])
              [Continue]
              [];
           Assign (BaseTarget (NameTarget "y"))
             (Builtin (BaseT (UintT 256)) (Bop Add)
                [Name (BaseT (UintT 256)) "y";
                 Name (BaseT (UintT 256)) "i"])];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition for_break_program_def:
  for_break_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 3)))
          0
          [If (Builtin (BaseT BoolT) (Bop Eq)
                 [Name (BaseT (UintT 256)) "i";
                  Literal (BaseT (UintT 256)) (IntL 2)])
              [Break]
              [];
           Assign (BaseTarget (NameTarget "y"))
             (Builtin (BaseT (UintT 256)) (Bop Add)
                [Name (BaseT (UintT 256)) "y";
                 Name (BaseT (UintT 256)) "i"])];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition internal_call_program_def:
  internal_call_program =
    [FunctionDecl Internal Nonpayable F F "bar"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 7)))];
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Call (BaseT (UintT 256)) (IntCall (NONE, "bar"))
             ([] : expr list) NONE))]]
End

Definition internal_call_arg_program_def:
  internal_call_arg_program =
    [FunctionDecl Internal Nonpayable F F "bar"
       [("y", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Builtin (BaseT (UintT 256)) (Bop Add)
             [Name (BaseT (UintT 256)) "y";
              Literal (BaseT (UintT 256)) (IntL 1)]))];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Call (BaseT (UintT 256)) (IntCall (NONE, "bar"))
             [Name (BaseT (UintT 256)) "x"] NONE))]]
End

Theorem empty_result_lengths:
  compile_vyper_lengths ([] : toplevel list)
    concretize_context_eval Linear = SOME (53, 34)
Proof
  EVAL_TAC
QED

Theorem noop_result_lengths:
  compile_vyper_lengths noop_program
    concretize_context_eval Linear = SOME (82, 63)
Proof
  EVAL_TAC
QED

Theorem return_uint_result_lengths:
  compile_vyper_lengths return_uint_program
    concretize_context_eval Linear = SOME (89, 70)
Proof
  EVAL_TAC
QED

Theorem return_arg_result_lengths:
  compile_vyper_lengths return_arg_program
    concretize_context_eval Linear = SOME (107, 88)
Proof
  EVAL_TAC
QED

Theorem local_uint_result_lengths:
  compile_vyper_lengths local_uint_program
    concretize_context_eval Linear = SOME (95, 76)
Proof
  EVAL_TAC
QED

Theorem add_arg_result_lengths:
  compile_vyper_lengths add_arg_program
    concretize_context_eval Linear = SOME (121, 102)
Proof
  EVAL_TAC
QED

Theorem two_external_result_lengths:
  compile_vyper_lengths two_external_program
    concretize_context_eval Linear = SOME (129, 110)
Proof
  EVAL_TAC
QED

Theorem storage_read_result_lengths:
  compile_vyper_lengths storage_read_program
    concretize_context_eval Linear = SOME (91, 72)
Proof
  EVAL_TAC
QED

Theorem storage_write_result_lengths:
  compile_vyper_lengths storage_write_program
    concretize_context_eval Linear = SOME (95, 76)
Proof
  EVAL_TAC
QED

Theorem hashmap_read_result_lengths:
  compile_vyper_lengths hashmap_read_program
    concretize_context_eval Linear = SOME (123, 104)
Proof
  EVAL_TAC
QED

Theorem hashmap_write_result_lengths:
  compile_vyper_lengths hashmap_write_program
    concretize_context_eval Linear = SOME (143, 124)
Proof
  EVAL_TAC
QED

Theorem if_bool_result_lengths:
  compile_vyper_lengths if_bool_program
    concretize_context_eval Linear = SOME (137, 118)
Proof
  EVAL_TAC
QED

Theorem if_join_result_lengths:
  compile_vyper_lengths if_join_program
    concretize_context_eval Linear = SOME (155, 136)
Proof
  EVAL_TAC
QED

Theorem for_pass_result_lengths:
  compile_vyper_lengths for_pass_program
    concretize_context_eval Linear = SOME (131, 112)
Proof
  EVAL_TAC
QED

Theorem for_accum_result_lengths:
  compile_vyper_lengths for_accum_program
    concretize_context_eval Linear = SOME (157, 138)
Proof
  EVAL_TAC
QED

Theorem for_continue_result_lengths:
  compile_vyper_lengths for_continue_program
    concretize_context_eval Linear = SOME (182, 163)
Proof
  EVAL_TAC
QED

Theorem for_break_result_lengths:
  compile_vyper_lengths for_break_program
    concretize_context_eval Linear = SOME (182, 163)
Proof
  EVAL_TAC
QED

Theorem internal_call_result_lengths:
  compile_vyper_lengths internal_call_program
    concretize_context_eval Linear = SOME (96, 77)
Proof
  EVAL_TAC
QED

Theorem internal_call_arg_result_lengths:
  compile_vyper_lengths internal_call_arg_program
    concretize_context_eval Linear = SOME (114, 95)
Proof
  EVAL_TAC
QED
