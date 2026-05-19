Theory evalCompiler
Ancestors compileVyper concretizeMemLocDefs alist integer_word
Libs finite_mapLib computeLib wordsLib

val () = the_compset := add_finite_map_compset(!the_compset)
val () = the_compset := computeLib.add_thms [fmap_to_alist_FEMPTY] (!the_compset)
val () = the_compset := computeLib.add_thms [i2w_pos] (!the_compset)

val () = Globals.max_print_depth := 20

Definition compile_vyper_eval_lengths_def:
  compile_vyper_eval_lengths fuel (tops : toplevel list)
                             pipeline dispatch_strategy =
    case compile_vyper_eval fuel tops pipeline dispatch_strategy of
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

Theorem empty_result_lengths:
  compile_vyper_eval_lengths 16 ([] : toplevel list)
    (concretize_context_fuel 4) Linear = SOME (36, 20)
Proof
  EVAL_TAC
QED

Theorem noop_result_lengths:
  compile_vyper_eval_lengths 16 noop_program
    (concretize_context_fuel 4) Linear = SOME (30, 14)
Proof
  EVAL_TAC
QED

(* These return-value examples compute through the current ABI-size equations
   in compileEnv, whose termination is still cheat-tagged. Keep them as exact
   build-time checks until those definitions have clean termination proofs. *)
fun assert_eval_result name tm expected =
  let
    val th = EVAL tm
    val got = boolSyntax.rhs (concl th)
  in
    if Term.aconv got expected then th
    else raise Fail (name ^ ": expected " ^ term_to_string expected ^
                     ", got " ^ term_to_string got)
  end

val return_uint_result_lengths =
  assert_eval_result "return_uint_result_lengths"
    ``compile_vyper_eval_lengths 16 return_uint_program
        (concretize_context_fuel 4) Linear``
    ``SOME (37, 21) : (num # num) option``

val return_arg_result_lengths =
  assert_eval_result "return_arg_result_lengths"
    ``compile_vyper_eval_lengths 16 return_arg_program
        (concretize_context_fuel 4) Linear``
    ``SOME (55, 39) : (num # num) option``

val local_uint_result_lengths =
  assert_eval_result "local_uint_result_lengths"
    ``compile_vyper_eval_lengths 16 local_uint_program
        (concretize_context_fuel 4) Linear``
    ``SOME (43, 27) : (num # num) option``

val add_arg_result_lengths =
  assert_eval_result "add_arg_result_lengths"
    ``compile_vyper_eval_lengths 16 add_arg_program
        (concretize_context_fuel 4) Linear``
    ``SOME (69, 53) : (num # num) option``
