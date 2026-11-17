(* Verified evaluation support for the bytecode stack checker. *)
Theory stackBoundCompute
Ancestors
  stackBoundDefs cv_std vfmOperation vfmContext byte divides
Libs
  cv_transLib wordsLib

val _ = cv_auto_trans parse_code_def;
val _ = cv_auto_trans bytecode_stack_io_def;
val _ = cv_auto_trans bytecode_jump_targets_def;
val _ = cv_auto_trans bytecode_stack_successors_def;
val _ = cv_auto_trans bytecode_stack_closure_def;
val _ = cv_auto_trans bytecode_stack_check_def;

Theorem bytecode_stack_check_empty:
  bytecode_stack_check 1 0 []
Proof
  CONV_TAC cv_eval
QED

Theorem bytecode_stack_check_push_limit:
  ~bytecode_stack_check 4 1 [0x5Fw; 0x5Fw; 0x00w]
Proof
  CONV_TAC cv_eval
QED
