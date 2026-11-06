(* Independent checked-frontend bytecode witnesses for slice output buffers
   (#561, a07-06).
   TOP-LEVEL: slice_msg_data_matches_python_oracle,
              slice_msg_data_var_matches_python_oracle,
              slice_bytes_var_matches_python_oracle,
              slice_storage_bytes_matches_python_oracle,
              slice_string_lit_matches_python_oracle. *)
Theory evalCompilerSliceBuffers
Ancestors compileVyper vyperCompiler supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../slice-buffers"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../slice-buffers/oracle"

(* slice(msg.data, 0, 4): the output buffer is 32 + ceil32(4) bytes,
   allocated before CALLDATASIZE. *)
val slice_msg_data = memoryStoreWitnessLib.evaluate fixture_root "slice_msg_data"
Theorem slice_msg_data_matches_python_oracle:
  ^(#term slice_msg_data) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "slice_msg_data")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation slice_msg_data))) >> EVAL_TAC
QED

(* slice(msg.data, s, 8) with a variable start. *)
val slice_msg_data_var = memoryStoreWitnessLib.evaluate fixture_root "slice_msg_data_var"
Theorem slice_msg_data_var_matches_python_oracle:
  ^(#term slice_msg_data_var) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "slice_msg_data_var")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation slice_msg_data_var))) >> EVAL_TAC
QED

(* control: memory Bytes source, variable start and length. *)
val slice_bytes_var = memoryStoreWitnessLib.evaluate fixture_root "slice_bytes_var"
Theorem slice_bytes_var_matches_python_oracle:
  ^(#term slice_bytes_var) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "slice_bytes_var")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation slice_bytes_var))) >> EVAL_TAC
QED

(* control: storage Bytes source. *)
val slice_storage_bytes = memoryStoreWitnessLib.evaluate fixture_root "slice_storage_bytes"
Theorem slice_storage_bytes_matches_python_oracle:
  ^(#term slice_storage_bytes) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "slice_storage_bytes")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation slice_storage_bytes))) >> EVAL_TAC
QED

(* control: String source, literal start and length. *)
val slice_string_lit = memoryStoreWitnessLib.evaluate fixture_root "slice_string_lit"
Theorem slice_string_lit_matches_python_oracle:
  ^(#term slice_string_lit) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "slice_string_lit")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation slice_string_lit))) >> EVAL_TAC
QED

(* The HOL typed AST permits a struct variable named msg.  Its data field
   is memory, even though its syntax also satisfies is_msg_data.  Real
   transaction calldata uses the separate CalldataSlice constructor. *)
Definition slice_struct_field_expr_def:
  slice_struct_field_expr =
    Builtin (BaseT (BytesT (Dynamic 40))) (Slice 40)
      [Attribute (BaseT (BytesT (Dynamic 40)))
         (Name (StructT (NONE, "S")) "msg") "data";
       Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL 1)]
End

Definition slice_struct_field_insts_def:
  slice_struct_field_insts =
    let cenv = build_compile_env
      [StructDecl "S" [("data", BaseT (BytesT (Dynamic 40)))]]
      External Pure "entry" [("msg", StructT (NONE, "S"))]
      (BaseT (BytesT (Dynamic 40)))
      [Return (SOME slice_struct_field_expr)] F in
    (SND (compile_expr cenv (BaseT (BytesT (Dynamic 40)))
      slice_struct_field_expr
      (vyperCompiler$initial_compile_state "entry"))).cs_current_insts
End

Theorem slice_struct_field_copies_memory:
  EXISTS (\i. i.inst_opcode = MCOPY) slice_struct_field_insts /\
  ~EXISTS (\i. i.inst_opcode = CALLDATACOPY) slice_struct_field_insts
Proof
  EVAL_TAC
QED
