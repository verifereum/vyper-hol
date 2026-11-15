(* One checked compiler evaluation per theory keeps regression replay bounded. *)
Theory createProxyCompileTest
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../../bytecode/create-builtins/oracle"]
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])

val compiled = memoryStoreWitnessLib.evaluate
  "../../bytecode/create-builtins/oracle" "cp01_proxy"
val _ = save_thm ("create_proxy_compiled", #evaluation compiled)
val runtime = #2 (pairSyntax.dest_pair
  (optionSyntax.dest_some (rhs (concl (#evaluation compiled)))))

Definition create_proxy_runtime_def:
  create_proxy_runtime = ^runtime
End
val () = cv_auto_trans create_proxy_runtime_def;
