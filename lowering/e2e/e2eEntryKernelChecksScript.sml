(* Focused saved-object receipt and substantive exact-schema consumer. *)
Theory e2eEntryKernelChecks
Ancestors
  e2eEntryChecks e2eProducerChecks e2eProducers e2eEntry
  e2eDefs codegenCorrectness vyperLoweringCorrect unitTransformDefs
  o1PipelineCorrect stackPlanGen contextCodegenRel unitShapeDefs

val _ = Parse.hide "cp";

fun check_saved (thy,n) = let
  val th = DB.fetch thy n
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  val _ = if null (Thm.hyp th) andalso null axioms andalso
      List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail (thy ^ "." ^ n ^ ": not kernel-closed/unadmitted")
  in print ("TASK053_DB_RECEIPT " ^ thy ^ "." ^ n ^
    " hyp=0 axioms=[] oracles=[" ^ String.concatWith "," oracles ^ "]\n") end;

val () = List.app (fn thy => List.app
  (fn (n,_) => check_saved (thy,n)) (DB.thms thy))
  ["e2eEntry", "e2eProducers", "e2eEntryChecks", "e2eProducerChecks"];

val () = List.app (fn (thy,n) => print
  ("TASK053_EXACT_SCHEMA " ^ thy ^ "." ^ n ^ "\n" ^
    term_to_string (Thm.concl (DB.fetch thy n)) ^ "\n"))
  [("e2eEntry", "entry_venom_state_def"),
   ("e2eProducers", "o1_pipeline_codegen_obligations"),
   ("e2eProducers", "entry_venom_state_initial_venom_state_rel"),
   ("e2eProducers", "entry_venom_state_o1_initial_state_ok"),
   ("e2eProducers", "entry_venom_state_initial_ctx_rel")];

(* Exact four-contract consumer, not a theorem-name-only receipt. *)
Theorem entry_producers_exact_schema:
  (!rpolicy unit out cp Inv.
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    unit_shape_ok out.po_unit /\
    codegen_memory_obligations Inv out.po_unit.cu_context cp ==>
    codegen_context_obligations Inv out.po_unit.cu_context cp) /\
  (!tops prog am tx es cp.
    call_state_rel tops (assemble prog) am tx es ==>
    initial_venom_state_rel am tx (entry_venom_state prog cp es)) /\
  (!prog cp es. o1_initial_state_ok (entry_venom_state prog cp es)) /\
  (!tops prog am tx es u cp.
    call_state_rel tops (assemble prog) am tx es /\ unit_shape_ok u ==>
    initial_ctx_rel cp prog u.cu_context (entry_venom_state prog cp es) es)
Proof
  rpt conj_tac >|
    [ACCEPT_TAC o1_pipeline_codegen_obligations,
     ACCEPT_TAC entry_venom_state_initial_venom_state_rel,
     ACCEPT_TAC entry_venom_state_o1_initial_state_ok,
     ACCEPT_TAC entry_venom_state_initial_ctx_rel]
QED

val () = check_saved ("e2eEntryKernelChecks", "entry_producers_exact_schema");
