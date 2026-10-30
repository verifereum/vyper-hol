Theory sourceModuleCompile
Ancestors
  sourceModuleElaborate sourceModuleDefs sourceSyntax compileVyper
  vyperTypeContract vyperAST list sourceProgramSupport

(* compile_vyper's raw API currently takes ONE toplevel list, not a module
   registry. Do not erase module identities by flattening imported declarations.
   Multi-module source checking is supported; that backend boundary is explicit. *)
Definition source_module_compile_def:
  source_module_compile fuel trust keys program layouts address finalizer policy =
    source_module_bind (source_module_check_simple fuel trust keys program layouts address)
      (\(retained,art). case retained_executable retained of
        [(NONE,tops)] =>
          (case compile_vyper finalizer policy tops of
            NONE => SM_Error (SME_Declaration "backend-compilation")
          | SOME bytes => SM_Ok (retained,art,bytes))
      | _ => SM_Error (SME_Declaration "backend-module-linking"))
End

Theorem source_module_compile_equations:
  source_module_compile fuel trust keys program layouts address finalizer policy =
    SM_Ok (retained,art,bytes) ==>
  source_module_elaborate_simple fuel trust keys program = SM_Ok retained /\
  retained_source retained = program /\
  check_contract T layouts address (retained_executable retained) = SOME art /\
  ?tops. retained_executable retained = [(NONE,tops)] /\
         compile_vyper finalizer policy tops = SOME bytes
Proof
  simp[source_module_compile_def] >>
  Cases_on `source_module_check_simple fuel trust keys program layouts address` >>
  simp[source_module_bind_def] >>
  rename1 `source_module_check_simple fuel trust keys program layouts address = SM_Ok checked` >>
  PairCases_on `checked` >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule source_module_check_simple_equations >> simp[]
QED

(* The check is on the original source program and its retained executable;
   no ready/supported_program assumption is supplied by the caller. *)
Theorem source_module_checked_supported_program:
  source_module_check fuel trust policies keys program layouts address =
    SM_Ok (retained,art) /\
  retained_executable retained = [(NONE,tops)] /\
  source_program_remainder tops ==> supported_program tops
Proof
  strip_tac >> drule source_module_check_equations >> strip_tac >>
  gvs[] >> drule checked_remainder_supported_program >> simp[]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source module compiler kernel audit: " ^ name) end)
  (DB.thms "sourceModuleCompile");
