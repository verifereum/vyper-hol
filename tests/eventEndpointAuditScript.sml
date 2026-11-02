(* Admission checks at the public event and Log boundaries only. *)
Theory eventEndpointAudit
Ancestors
  vyperEventSoundness checkedLogEmptyExecution checkedLogData checkedLogDataExecution

val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("Unclosed event endpoint: " ^ name)
  end)
  [("checked_log_encoding_success", vyperEventSoundnessTheory.checked_log_encoding_success),
   ("indexed_only_log", checkedLogEmptyExecutionTheory.checked_compile_log_empty_execution),
   ("packed_log", checkedLogDataTheory.checked_compile_saved_log_data),
   ("full_log", checkedLogDataExecutionTheory.checked_compile_log_data_execution)];
