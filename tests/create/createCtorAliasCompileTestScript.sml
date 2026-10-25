(* Checked HOL compilation of a constructor argument aliasing witness. *)
Theory createCtorAliasCompileTest
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["constructor-alias/oracle"]
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])

val compiled = memoryStoreWitnessLib.evaluate
  "constructor-alias/oracle" "ctor_alias"
val _ = save_thm ("create_ctor_alias_compiled", #evaluation compiled)
val runtime = #2 (pairSyntax.dest_pair
  (optionSyntax.dest_some (rhs (concl (#evaluation compiled)))))

Definition create_ctor_alias_runtime_def:
  create_ctor_alias_runtime = ^runtime
End
val () = cv_auto_trans create_ctor_alias_runtime_def;

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createCtorAliasCompileTest");
