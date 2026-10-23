Theory vyperPrimitiveAudit
Ancestors
  vfmExecution

val () = List.app (fn (n, th) =>
  if String.isSubstring "run_call" n orelse
     String.isSubstring "dispatch_precompiles" n orelse
     String.isSubstring "step_call" n orelse
     String.isSubstring "step_create" n orelse
     String.isSubstring "proceed_" n orelse
     String.isSubstring "handle_" n orelse
     String.isSubstring "self_destruct" n
  then print (n ^ ": " ^ thm_to_string th ^ "\n") else ())
  (DB.thms "vfmExecution");

val () = List.app (fn (n, th) =>
  if String.isSuffix "_def" n then
    print ("EXECDEF " ^ n ^ ": " ^ thm_to_string th ^ "\n") else ())
  (List.filter (fn (n, th) =>
     List.exists (fn key => String.isSubstring key (thm_to_string th))
       ["update_accounts", "set_rollback", "set_original", "pop_and_incorporate",
        "dispatch_precompiles", "push_context", "step ", "precompile_"])
    (DB.thms "vfmExecution"));
val () = List.app (fn (n, th) =>
  if List.exists (fn key => String.isSubstring key n)
      ["pop_and_incorporate", "push_context", "set_original", "set_rollback", "update_accounts"]
  then print ("CONTEXT " ^ n ^ ": " ^ thm_to_string th ^ "\n") else ())
  (DB.thms "vfmContext");
val () = List.app (fn (n, th) =>
  if String.isSubstring "OWHILE" n then
    print ("WHILE " ^ n ^ ": " ^ thm_to_string th ^ "\n") else ())
  (DB.thms "While");

val () = List.app (fn (n, th) =>
  if List.exists (fn key => n = key)
      ["step_inst_def", "pop_context_def", "set_last_accounts_def",
       "get_original_def", "transfer_value_def", "increment_nonce_def",
       "step_sstore_def", "step_tstore_def"]
  then print ("LEAF " ^ n ^ ": " ^ thm_to_string th ^ "\n") else ())
  (DB.thms "vfmExecution");
val () = print ("ALL EXECUTION DEFINITIONS: " ^
  String.concatWith ", " (List.map #1 (List.filter
     (fn (n, _) => String.isSuffix "_def" n) (DB.thms "vfmExecution"))) ^ "\n");
