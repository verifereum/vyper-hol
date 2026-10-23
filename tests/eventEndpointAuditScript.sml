(* Diagnostic only: report actual saved oracle provenance, no theorem aliases. *)
Theory eventEndpointAudit
Ancestors
  e2eCorrectness e2eDefs vyperTypeSoundness vyperEventSoundness

fun report (thy,name) =
  let val th = DB.fetch thy name
      val (ors,axs) = Tag.dest_tag (Thm.tag th)
  in print ("EVENT ENDPOINT " ^ thy ^ "." ^ name ^
       " oracles=[" ^ String.concatWith "," ors ^ "] axioms=" ^
       Int.toString (length axs) ^ " hypotheses=" ^
       Int.toString (length (Thm.hyp th)) ^ "\n") end;
val _ = List.app report
 [("e2eCorrectness","vyper_call_correct"),
  ("e2eCorrectness","e2e_vyper_to_evm"),
  ("e2eCorrectness","e2e_deploy_correctness"),
  ("vyperLoweringCorrect","lower_vyper_runtime_unit_correct"),
  ("vyperLoweringCorrect","lower_vyper_runtime_unit_source_unit_ok"),
  ("vyperLoweringCorrect","lower_vyper_runtime_unit_memory_ok"),
  ("o1PipelineCorrect","run_venom_pipeline_correct"),
  ("o1PipelineCorrect","run_venom_pipeline_output_shape"),
  ("o1PipelineCorrect","o1_pipeline_memory_obligations"),
  ("codegenCorrectness","codegen_correct"),
  ("vyperTypeEvalSoundness","eval_all_type_sound_mutual"),
  ("exprLoweringProps","compile_expr_correct"),
  ("stmtLoweringProps","compile_stmt_correct"),
  ("stmtLoweringProps","compile_stmts_correct"),
  ("abiEncoderProps","compile_abi_encode_to_buf_correct")];
val _ = List.app (fn thy => List.app (fn (n,_) => report (thy,n))
  (DB.theorems thy))
 ["vyperTypeSoundness", "vyperTypeContractSoundness", "vyperTypeInitialState",
  "vyperTypeStmtSoundness", "vyperTypeCallSoundness", "vyperEventSoundness",
  "e2eDefs"];

(* These selected event/type endpoints really are closed, not just buildable.
   The broader compiler endpoints above intentionally remain report-only. *)
val _ = List.app (fn thy => List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn tag => tag = "DISK_THM") ors then ()
     else raise Fail ("Unclosed event/type endpoint: " ^ thy ^ "." ^ name)
  end) (DB.theorems thy))
 ["vyperTypeSoundness", "vyperTypeContractSoundness", "vyperTypeInitialState",
  "vyperTypeStmtSoundness", "vyperTypeCallSoundness", "vyperEventSoundness",
  "e2eDefs"];

