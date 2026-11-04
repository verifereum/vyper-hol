Theory vyperMembershipParityTest
Ancestors compileVyper concretizeMemLocDefs alist byte integer_word option vyperTypeSystem
Libs vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib membershipParityLib finite_mapLib wordsLib

(* Hash and stage the independent inputs, including in exported source builds. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/membership"];

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY,i2w_pos])

val () = membershipParityLib.prepare_compile "in_lit_list"

Theorem in_lit_list_matches_python:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    ^(membershipParityLib.program "in_lit_list") =
    SOME ^(membershipParityLib.oracle "in_lit_list")
Proof
  EVAL_TAC
QED

val () = membershipParityLib.prepare_compile "notin_lit_list3"
val () = membershipParityLib.prepare_compile "in_mem_dynarray"
val () = membershipParityLib.prepare_compile "in_storage_dynarray"
val () = membershipParityLib.prepare_compile "eq_string_lit_same"
val () = membershipParityLib.prepare_compile "eq_bytes_storage_both"

Theorem notin_lit_list3_matches_python:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    ^(membershipParityLib.program "notin_lit_list3") =
    SOME ^(membershipParityLib.oracle "notin_lit_list3")
Proof
  EVAL_TAC
QED

Theorem in_mem_dynarray_matches_python:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    ^(membershipParityLib.program "in_mem_dynarray") =
    SOME ^(membershipParityLib.oracle "in_mem_dynarray")
Proof
  EVAL_TAC
QED

Theorem in_storage_dynarray_matches_python:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    ^(membershipParityLib.program "in_storage_dynarray") =
    SOME ^(membershipParityLib.oracle "in_storage_dynarray")
Proof
  EVAL_TAC
QED

Theorem eq_string_lit_same_matches_python:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    ^(membershipParityLib.program "eq_string_lit_same") =
    SOME ^(membershipParityLib.oracle "eq_string_lit_same")
Proof
  EVAL_TAC
QED

Theorem eq_bytes_storage_both_matches_python:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    ^(membershipParityLib.program "eq_bytes_storage_both") =
    SOME ^(membershipParityLib.oracle "eq_bytes_storage_both")
Proof
  EVAL_TAC
QED
