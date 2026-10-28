(* Public original-source checking + transparent remainder, using the
   replacement support lemma exported by sourceModuleCompile. *)
Theory sourceProgramIntegrationTest
Ancestors
  sourceModuleCompile sourceProgramSupportTest sourceProgramSupport
  sourceModuleElaborate sourceModuleDefs sourceSyntax sourceConstAST
  vyperAST vyperContext finite_map
Libs
  sourceModuleFrontendLib

Definition source_support_power_program_def:
  source_support_power_program = SourceProgram (SourceModule
    [SD_Function "f" [SX_Name "external"]
      [SourceArg "a" (SOME (SCA_Name ["uint256"]))] []
      (SOME (SCA_Name ["uint256"]))
      [SS_Return (SOME (SX_Binary SCB_Pow (SX_Name "a")
        (SX_Literal (SCL_Int 2))))]]) []
End

Definition source_support_power_trust_def:
  source_support_power_trust = <| smt_ids := [(["main"],NONE)];
    smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [] |>
End

val checked_power = sourceModuleFrontendLib.check
  {fuel=``30:num``,trust=``source_support_power_trust``,
   policies=``[(["main"],SourceModulePolicy F F)]``,keys=``[["main"]]``,
   program=``source_support_power_program``}
  {layouts=``[(0w:address,([]:storage_layout,[]:storage_layout))]``,address=``0w:address``};
val source_support_power_check_phase =
  save_thm ("source_support_power_check_phase", #composition checked_power);
val elaboration = save_thm ("source_support_power_elaboration_phase",
  #equation (#elaboration checked_power));

Theorem source_support_power_elaboration:
  source_module_elaborate 30 source_support_power_trust
    [(["main"],SourceModulePolicy F F)] [["main"]] source_support_power_program =
  SM_Ok (SourceRetained source_support_power_program [(NONE,source_support_power_tops)])
Proof
  CONV_TAC (LAND_CONV (REWR_CONV elaboration)) >>
  EVAL_TAC
QED

(* This proof uses the public replacement lemma, not direct evaluation of
   supported_program. The checker and the remainder discharge distinct roles. *)
Theorem source_support_power_public_replacement:
  ?retained art.
    source_module_check 30 source_support_power_trust
      [(["main"],SourceModulePolicy F F)] [["main"]] source_support_power_program
      [(0w:address,([]:storage_layout,[]:storage_layout))] (0w:address) =
        SM_Ok (retained,art) /\
    retained_source retained = source_support_power_program /\
    retained_executable retained = [(NONE,source_support_power_tops)] /\
    source_program_remainder source_support_power_tops /\
    supported_program source_support_power_tops
Proof
  mp_tac source_support_power_check_phase >> strip_tac >>
  drule source_module_check_equations >> strip_tac >>
  gvs[source_support_power_elaboration] >>
  simp[retained_source_def, retained_executable_def,
       power_program_remainder_nonvacuous] >>
  drule source_module_checked_supported_program >>
  simp_tac std_ss [retained_executable_def, GSYM source_support_power_tops_def,
                   power_program_remainder_nonvacuous]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source program integration kernel audit: " ^ name) end)
  (DB.thms "sourceProgramIntegrationTest");
