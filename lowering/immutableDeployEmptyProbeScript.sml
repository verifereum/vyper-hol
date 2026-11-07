(* Empty-struct boundary audit. These facts are not a counterexample to stmt_frag. *)
Theory immutableDeployEmptyProbe
Ancestors
  immutableDeployOperandTransfer supportedDecls supportedTypes
  stmtLowering vyperTypeSystem vyperTypeEnv valueEncoding
  venomState venomMemDefs venomExecSemantics context finite_map compileEnv
  vyperInterpreter state_transformer venomMemProofs immutableRelation stmtReasonMemory
Libs monadsyntax

Theorem empty_struct_immutable_supported_probe:
  supported_immutable_type
    [StructDecl "Empty" [];
     VariableDecl Private Immutable "dst" (StructT (NONE,"Empty")) NONE]
    (NONE,"dst") = SOME (StructT (NONE,"Empty"))
Proof
  EVAL_TAC
QED

Theorem empty_struct_evaluated_probe:
  evaluate_type (FEMPTY |+ ((NONE,"Empty"),StructArgs []))
    (StructT (NONE,"Empty")) = SOME (StructTV []) /\
  type_memory_size (StructTV []) = 0
Proof
  EVAL_TAC
QED

Theorem empty_struct_rhs_typed_probe:
  well_typed_expr
    (env with type_defs := FEMPTY |+ ((NONE,"Empty"),StructArgs []))
    (StructLit (StructT (NONE,"Empty")) (NONE,"Empty") [])
Proof
  simp[well_typed_expr_def, well_formed_type_def] >> EVAL_TAC
QED

Theorem empty_struct_compile_word_probe:
  compile_assign_value ce (Lit 0w) LocCode (Lit 32w) F NONE
    (StructT (NONE,"Empty")) (StructT (NONE,"Empty")) NONE 0 sa =
  comp_bind (emit_op MLOAD [Lit 32w])
    (\loaded. compile_imm_store_word ce.ce_imm_alloca (Lit 0w) loaded) sa
Proof
  simp[compile_assign_value_def, is_bytestring_type_def,
       comp_bind_def, comp_return_def]
QED

Theorem empty_struct_store_corrupts_neighbor_probe:
  mload 0 (mstore 0 1w (s with vs_memory := [])) = 1w /\
  mload 0 (istore 0
    (mload 32 (mstore 0 1w (s with vs_memory := [])))
    (mstore 0 1w (s with vs_memory := []))) = 0w
Proof
  `!off w t. mload off (istore off w t) = w` by
    (rpt gen_tac >>
     pure_rewrite_tac[mload_def, immutable_istore_byte_address] >>
     pure_rewrite_tac[GSYM mload_def] >>
     simp[mload_mstore_same_proof]) >>
  simp[mload_mstore_same_proof, mload_mstore_apart] >>
  EVAL_TAC >> simp[]
QED
