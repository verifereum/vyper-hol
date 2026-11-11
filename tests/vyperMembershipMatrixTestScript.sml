(* Distinct boundary cases beyond the six core parity fixtures. *)
Theory vyperMembershipMatrixTest
Ancestors vyperMembershipParityTest compileVyper concretizeMemLocDefs alist byte integer_word option
Libs membershipParityLib evalCompilerBytecodeLib vyperCheckContractFrontendLib jsonASTLib finite_mapLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/membership"];

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY,i2w_pos])
val controls = ["in_flag", "notin_flag", "notin_mem_sarray",
  "ne_bytes_var", "in_empty_list"]
val () = List.app membershipParityLib.prepare_compile controls
val programs = listSyntax.mk_list (map membershipParityLib.program controls,
  ``:toplevel list``)
val outputs = listSyntax.mk_list (map membershipParityLib.oracle controls,
  ``:word8 list # word8 list``)

Theorem task_controls_match_python:
  MAP (compile_vyper (K SOME) (o1_policy all_capabilities)) ^programs =
  MAP SOME ^outputs
Proof
  EVAL_TAC
QED

(* Keep one real-codegen rejection at the aggregate-element boundary. *)
fun checker name deploy = let
  val i = membershipParityLib.input name
in vyperCheckContractLib.mk_check_contract
  {in_deploy=deploy,address= #address i,modules= #modules i,layouts= #layouts i}
end

Theorem nonword_witnesses_rejected_runtime:
  ^(checker "in_nested_array" false) = NONE
Proof
  CONV_TAC (LAND_CONV vyperCheckContractLib.check_contract_conv) >> REFL_TAC
QED

Theorem nonword_witnesses_rejected_deploy:
  ^(checker "in_nested_array" true) = NONE
Proof
  CONV_TAC (LAND_CONV vyperCheckContractLib.check_contract_conv) >> REFL_TAC
QED

val () = List.app (fn theory => List.app (fn (name,th) =>
  let val oracles = #1 (Tag.dest_tag (Thm.tag th))
  in if List.all (fn x => x = "DISK_THM") oracles then ()
     else raise Fail ("oracle tag on " ^ theory ^ "." ^ name) end)
  (DB.thms theory)) ["vyperMembershipParityTest","vyperMembershipMatrixTest"]
