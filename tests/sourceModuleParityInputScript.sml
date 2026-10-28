(* Source-driven acceptance matrix: the 36 pinned-valid whole programs must
   elaborate AND check in deployment mode. Only method_id_var is pin-invalid.
   No successful source rejection is counted as acceptance. *)
Theory sourceModuleParityInput
Ancestors
  sourceModuleFrontendLibTest sourceModuleCompile sourceModuleElaborate
  sourceModuleDefs sourceSyntax vyperAST finite_map compileVyper
Libs sourceModuleParityLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract/source_syntax",
  "../lowering/defs/bytecode/folded-value-witnesses.txt",
  "../lowering/defs/bytecode/folded-value-parity-fixtures.txt"];

val () = app (fn name => let
  val phase = sourceModuleParityLib.certified_phase name
  val _ = save_thm (name ^ "_source", phase)
  in if name = "method_id_var" then
    ignore (save_thm (name ^ "_compile_reject",
      simpLib.SIMP_CONV (srw_ss())
        [sourceModuleCompileTheory.source_module_compile_def,
         sourceModuleElaborateTheory.source_module_check_simple_def,phase,
         sourceModuleDefsTheory.source_module_bind_def]
        (sourceModuleParityLib.compile name)))
  else let
    val check = sourceModuleParityLib.certified_check name
    val () = if same_const (#1 (strip_comb (rhs (concl check)))) ``SM_Ok`` then ()
      else raise Fail ("pin-valid source rejected: " ^ name)
    val _ = save_thm (name ^ "_checked",check)
    val _ = save_thm (name ^ "_exact_checked_modules",
      MATCH_MP sourceModuleElaborateTheory.source_module_check_simple_equations check)
    in print ("SOURCE_PARITY_ACCEPT " ^ name ^ "\n") end
  end) sourceModuleParityLib.names;
val () = sourceModuleParityLib.audit "sourceModuleParityInput";
