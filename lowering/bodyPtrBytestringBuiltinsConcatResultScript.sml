(* Typed result packaging for Concat. *)
Theory bodyPtrBytestringBuiltinsConcatResult
Ancestors
  bodyPtrBytestringBuiltinsConcatSuffix bodyPtrEnvBuiltinsBoundary
  exprSimConcatResult exprSimHyps exprSimProps exprLowering
  compileEnv loweringPosts bodyPtrDefs words list arithmetic vfmConstants

Theorem concat_buffer_capacity:
  ann = BaseT (BytesT (Dynamic n)) \/ ann = BaseT (StringT n) ==>
  type_memory_bytes ce (lowered_value_type ce (Builtin ann (Concat n) args)) <=
    concat_alloc_size (MAP expr_type args)
Proof
  strip_tac >> gvs[lowered_value_type_def, concat_buffer_type_def,
    type_memory_bytes_def, concat_alloc_size_def, MAP_MAP_o,
    combinTheory.o_DEF, word_size_def] >>
  simp[MAX_DEF]
QED
