Theory vyperMembershipNotinMemSarrayTest
Ancestors compileVyper concretizeMemLocDefs codegenReadyCompute alist byte integer_word option vyperTypeSystem
Libs vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib membershipParityLib finite_mapLib wordsLib

(* Hash and stage the independent inputs, including in exported source builds. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/membership"];

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY,i2w_pos])

val () = membershipParityLib.prepare_compile "notin_mem_sarray"

Theorem notin_mem_sarray_matches_python:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    ^(membershipParityLib.program "notin_mem_sarray") =
    SOME ^(membershipParityLib.oracle "notin_mem_sarray")
Proof
  EVAL_TAC
QED
