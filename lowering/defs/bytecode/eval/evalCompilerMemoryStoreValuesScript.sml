(* Independent checked-frontend bytecode witnesses for memory stores. *)
Theory evalCompilerMemoryStoreValues
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option sourceModuleDefs sourceModuleEnv sourceConstBuiltinCompute
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib sourceModuleLoaderLib sourceOrdinaryClaimsLib sourceOrdinaryProgramLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../memory-stores"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../memory-stores/oracle"

(* This fixture needs explicit source normalization, not the legacy raw
   runtime MethodId. Pair genuine pre-erasure syntax with the UNCHANGED oracle
   annotations. Only layouts and runtime contexts are inherited, never bodies. *)
fun source_program source_path annotated_path = let
  val original = sourceModuleLoaderLib.load_file source_path
  val capture = JSONDecode.decodeFile JSONDecode.raw source_path
  val original_json = JSONDecode.decode
    (JSONDecode.field "annotated_ast" JSONDecode.raw) capture
  val annotated = JSONDecode.decodeFile JSONDecode.raw annotated_path
  val paired = sourceOrdinaryClaimsLib.pair_program original original_json annotated
  val trust = ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
    smt_type_defs := FEMPTY; smt_slots := [] |>``
  val storage = JSONDecode.decodeFile jsonASTLib.storage_layout annotated_path
  val layout = rhs (concl (EVAL
    ``jsonToVyper$extract_storage_layout [] ^storage``))
  val layouts = ``[(0w:address,^layout)]``
  val contexts = sourceOrdinaryProgramLib.inherited_contexts paired trust
  (* Kernel-checked evaluation of arbitrary original strings, not a selector
     table or an interpretation of folded_value. *)
  val () = computeLib.upd_compset (computeLib.add_conv
    (``sourceConstBuiltin$source_const_keccak``,1,cv_transLib.cv_eval))
  val checked = vyperCheckContractFrontendLib.check_contract_result
    {fuel=``80:num``,address=``0w:address``,paired=paired,
     inherited={trust=trust,layouts=layouts,contexts=contexts}}
  (* The ordinary API checks deployment. Keep the independent runtime check
     on the exact same normalized modules, as for every legacy witness. *)
  val _ = vyperCheckContractLib.check_contract
    {in_deploy=false,address= #address checked,
     modules= #modules checked,layouts= #layouts checked}
in
  case #1 (listSyntax.dest_list (#modules checked)) of
    [entry] => #2 (pairSyntax.dest_pair entry)
  | _ => raise Fail "expected one checked source module"
end

val method_id_lit_tops = source_program
  "../memory-stores/source/method_id_lit.json"
  "../memory-stores/oracle/method_id_lit.json"
val method_id_lit_term = memoryStoreWitnessLib.compile_term method_id_lit_tops
val method_id_lit = {term=method_id_lit_term,evaluation=EVAL method_id_lit_term}

val a01_str_local_reassign = memoryStoreWitnessLib.evaluate fixture_root "a01_str_local_reassign"
Theorem a01_str_local_reassign_matches_python_oracle:
  ^(#term a01_str_local_reassign) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "a01_str_local_reassign")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation a01_str_local_reassign))) >> EVAL_TAC
QED

val a02_bytes_local_from_arg = memoryStoreWitnessLib.evaluate fixture_root "a02_bytes_local_from_arg"
Theorem a02_bytes_local_from_arg_matches_python_oracle:
  ^(#term a02_bytes_local_from_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "a02_bytes_local_from_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation a02_bytes_local_from_arg))) >> EVAL_TAC
QED

val a11_local_string_from_intcall = memoryStoreWitnessLib.evaluate fixture_root "a11_local_string_from_intcall"
Theorem a11_local_string_from_intcall_matches_python_oracle:
  ^(#term a11_local_string_from_intcall) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "a11_local_string_from_intcall")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation a11_local_string_from_intcall))) >> EVAL_TAC
QED

val c03_annassign_empty_dynarray = memoryStoreWitnessLib.evaluate fixture_root "c03_annassign_empty_dynarray"
Theorem c03_annassign_empty_dynarray_matches_python_oracle:
  ^(#term c03_annassign_empty_dynarray) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c03_annassign_empty_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c03_annassign_empty_dynarray))) >> EVAL_TAC
QED

val c04_annassign_empty_bytes = memoryStoreWitnessLib.evaluate fixture_root "c04_annassign_empty_bytes"
Theorem c04_annassign_empty_bytes_matches_python_oracle:
  ^(#term c04_annassign_empty_bytes) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c04_annassign_empty_bytes")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c04_annassign_empty_bytes))) >> EVAL_TAC
QED

val a12_local_dynarray_from_arg = memoryStoreWitnessLib.evaluate fixture_root "a12_local_dynarray_from_arg"
Theorem a12_local_dynarray_from_arg_matches_python_oracle:
  ^(#term a12_local_dynarray_from_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "a12_local_dynarray_from_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation a12_local_dynarray_from_arg))) >> EVAL_TAC
QED

val c06_assign_empty_storage_dynarray = memoryStoreWitnessLib.evaluate fixture_root "c06_assign_empty_storage_dynarray"
Theorem c06_assign_empty_storage_dynarray_matches_python_oracle:
  ^(#term c06_assign_empty_storage_dynarray) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c06_assign_empty_storage_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c06_assign_empty_storage_dynarray))) >> EVAL_TAC
QED

val a09_local_array_from_storage = memoryStoreWitnessLib.evaluate fixture_root "a09_local_array_from_storage"
Theorem a09_local_array_from_storage_matches_python_oracle:
  ^(#term a09_local_array_from_storage) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "a09_local_array_from_storage")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation a09_local_array_from_storage))) >> EVAL_TAC
QED

val long_string_literal = memoryStoreWitnessLib.evaluate fixture_root "long_string_literal"
Theorem long_string_literal_matches_python_oracle:
  ^(#term long_string_literal) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "long_string_literal")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation long_string_literal))) >> EVAL_TAC
QED

val long_bytes_literal = memoryStoreWitnessLib.evaluate fixture_root "long_bytes_literal"
Theorem long_bytes_literal_matches_python_oracle:
  ^(#term long_bytes_literal) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "long_bytes_literal")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation long_bytes_literal))) >> EVAL_TAC
QED

val storage_one_word_array = memoryStoreWitnessLib.evaluate fixture_root "storage_one_word_array"
Theorem storage_one_word_array_matches_python_oracle:
  ^(#term storage_one_word_array) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "storage_one_word_array")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation storage_one_word_array))) >> EVAL_TAC
QED

val enc_in_assign = memoryStoreWitnessLib.evaluate fixture_root "enc_in_assign"
Theorem enc_in_assign_matches_python_oracle:
  ^(#term enc_in_assign) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "enc_in_assign")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation enc_in_assign))) >> EVAL_TAC
QED

Theorem method_id_lit_matches_python_oracle:
  ^(#term method_id_lit) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "method_id_lit")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation method_id_lit))) >> EVAL_TAC
QED
