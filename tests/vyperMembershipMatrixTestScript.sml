(* Full independently pinned task matrix, beyond the six permanent fixtures. *)
Theory vyperMembershipMatrixTest
Ancestors vyperMembershipParityTest compileVyper concretizeMemLocDefs alist byte integer_word option
Libs membershipParityLib evalCompilerBytecodeLib vyperCheckContractFrontendLib jsonASTLib finite_mapLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/membership"];

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY,i2w_pos])
val controls = ["eq_string_storage_lhs_mem","eq_string_var","in_bytes4_list",
  "in_calldata_sarray","in_dynarray_arg","in_flag","in_lit_list2","in_lit_zero",
  "in_mem_sarray","in_sarray_zero","in_storage_sarray","list_in_lit",
  "ne_bytes_lit_same","ne_bytes_var","notin_flag","notin_lit_list",
  "notin_mem_sarray","notin_storage_dynarray"]
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

val residuals = ["eq_string_storage","in_empty_list","in_sarray_default"]
val () = List.app membershipParityLib.prepare_compile residuals
val residual_programs = listSyntax.mk_list
  (map membershipParityLib.program residuals, ``:toplevel list``)
val residual_outputs = listSyntax.mk_list
  (map membershipParityLib.oracle residuals, ``:word8 list # word8 list``)

Theorem externally_owned_residual_observations:
  MAP (\(tops,bytes).
    compile_vyper (K SOME) (o1_policy all_capabilities) tops = SOME bytes)
    (ZIP (^residual_programs,^residual_outputs)) = [T;F;F]
Proof
  EVAL_TAC
QED

(* The three real-codegen rejections must also be rejected by HOL, in both modes. *)
fun checker name deploy = let
  val i = membershipParityLib.input name
in vyperCheckContractLib.mk_check_contract
  {in_deploy=deploy,address= #address i,modules= #modules i,layouts= #layouts i}
end

Theorem nonword_witnesses_rejected_runtime:
  ^(checker "in_string_list" false) = NONE /\
  ^(checker "in_struct_dynarray" false) = NONE /\
  ^(checker "in_nested_array" false) = NONE
Proof
  rpt conj_tac >> CONV_TAC (LAND_CONV vyperCheckContractLib.check_contract_conv) >> REFL_TAC
QED

Theorem nonword_witnesses_rejected_deploy:
  ^(checker "in_string_list" true) = NONE /\
  ^(checker "in_struct_dynarray" true) = NONE /\
  ^(checker "in_nested_array" true) = NONE
Proof
  rpt conj_tac >> CONV_TAC (LAND_CONV vyperCheckContractLib.check_contract_conv) >> REFL_TAC
QED

val () = List.app (fn theory => List.app (fn (name,th) =>
  let val oracles = #1 (Tag.dest_tag (Thm.tag th))
  in if List.all (fn x => x = "DISK_THM") oracles then ()
     else raise Fail ("oracle tag on " ^ theory ^ "." ^ name) end)
  (DB.thms theory)) ["vyperMembershipParityTest","vyperMembershipMatrixTest"]

Theorem residual_compilation_succeeds:
  EVERY IS_SOME
    (MAP (compile_vyper (K SOME) (o1_policy all_capabilities)) ^residual_programs)
Proof
  EVAL_TAC
QED

(* Diagnostics, not proof: independent expectations are used only after
   normalization. Kernel theorems above establish the exact verdicts. *)
fun report_residual name = let
  val tops = membershipParityLib.program name
  val actual = optionSyntax.dest_some (rhs (concl (EVAL
    ``compile_vyper (K SOME) (o1_policy all_capabilities) ^tops``)))
  val expected = rhs (concl (EVAL (membershipParityLib.oracle name)))
  fun lists tm = let val (a,b) = pairSyntax.dest_pair tm
    in (#1 (listSyntax.dest_list a),#1 (listSyntax.dest_list b)) end
  val (ad,ar) = lists actual
  val (ed,er) = lists expected
  fun first_diff i ([],[]) = "none"
    | first_diff i (a::aa,b::bb) =
        if aconv boolSyntax.T (rhs (concl (EVAL ``^a = ^b``)))
        then first_diff (i+1) (aa,bb) else Int.toString i
    | first_diff i _ = Int.toString i
  fun sizes (a,b) = Int.toString (length a) ^ "/" ^ Int.toString (length b)
in print ("RESIDUAL " ^ name ^ " deploy hol/python=" ^ sizes(ad,ed) ^
  " first_diff=" ^ first_diff 0 (ad,ed) ^ " runtime hol/python=" ^ sizes(ar,er) ^
  " first_diff=" ^ first_diff 0 (ar,er) ^ "\n") end
val () = List.app report_residual residuals
