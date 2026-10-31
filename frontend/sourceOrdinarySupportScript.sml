(* #543 gate discharge at the clean ordinary frontend boundary. Backend-only
   tuple-base/ABI restrictions remain explicit in source_program_remainder. *)
Theory sourceOrdinarySupport
Ancestors
  sourceOrdinaryProgram sourceProgramSupport sourceSyntax vyperTypeContract alist

Theorem source_ordinary_checked_remainder:
  source_ordinary_check fuel trust policies keys contexts program claims layouts address =
    SM_Ok (retained,art) /\
  ALOOKUP (retained_executable retained) src = SOME tops /\
  module_allocated layouts address src tops ==>
  (source_program_remainder tops <=> supported_program tops)
Proof
  strip_tac >> drule source_ordinary_check_equations >> strip_tac >>
  drule_all checked_program_remainder >> simp[]
QED

Theorem source_ordinary_checked_supported_program:
  source_ordinary_check fuel trust policies keys contexts program claims layouts address =
    SM_Ok (retained,art) /\
  ALOOKUP (retained_executable retained) src = SOME tops /\
  module_allocated layouts address src tops /\
  source_program_remainder tops ==>
  supported_program tops
Proof
  metis_tac[source_ordinary_checked_remainder]
QED

(* The same exact modules are checked and passed to the actual backend callback;
   no MethodId/Exp gate is supplied separately by the caller. *)
Theorem source_ordinary_compiled_supported_program:
  source_ordinary_compile compiler fuel trust policies keys contexts program claims layouts address =
    SM_Ok (retained,art,bytes) /\
  ALOOKUP (retained_executable retained) src = SOME tops /\
  module_allocated layouts address src tops /\
  source_program_remainder tops ==>
  retained_source retained = program /\
  check_contract T layouts address (retained_executable retained) = SOME art /\
  compiler (retained_executable retained) = SOME bytes /\
  supported_program tops
Proof
  strip_tac >> drule source_ordinary_compile_equations >> strip_tac >> simp[] >>
  drule_all checked_program_remainder >> simp[]
QED

val () = List.app (fn (name,th) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
  else raise Fail ("ordinary support kernel audit: " ^ name) end)
  (DB.thms "sourceOrdinarySupport");
