(* Execution-boundary probes, not a strengthened Call judgment.
   In particular none of these claims whole-callee header cleanliness. *)
Theory bodyPtrMakeArrayCallExecutionProbe
Ancestors
  intCallLookup supportedExprs stmtLowering context ptrSafeRun
  compileEnv finite_map words

(* The supported-expression gate does not reject this widened tuple annotation.
   Function declaration lookup and full supported_program remain separate gates. *)
Theorem widened_tuple_call_supported:
  IS_SOME (supported_function_decl tops id Internal) ==>
  supported_expr tops
    (Call (TupleT [BaseT (BytesT (Dynamic 32)); ArrayT (BaseT (UintT 256)) (Dynamic 1)])
      (IntCall id) [] NONE)
Proof
  simp[supported_expr_def, supported_effect_expr_def, supported_pure_expr_def]
QED

(* The actual memory-return instruction generator invokes the same-layout
   store when the returned expression already has the declared wide type.
   It does not store the narrow call-site type into the return buffer. *)
Theorem memory_return_wide_store:
  compile_internal_return cenv (SOME src) rpc 0
    (TupleT [BaseT (BytesT (Dynamic 64)); ArrayT (BaseT (UintT 256)) (Dynamic 1)])
    (TupleT [BaseT (BytesT (Dynamic 64)); ArrayT (BaseT (UintT 256)) (Dynamic 1)])
    elems (SOME dst) =
  do compile_copy_memory dst src
       (type_memory_bytes cenv
         (TupleT [BaseT (BytesT (Dynamic 64)); ArrayT (BaseT (UintT 256)) (Dynamic 1)]));
     emit_inst RET [rpc] []
  od
Proof
  simp[compile_internal_return_def, compile_store_memory_def,
       is_word_type_def, is_bytestring_type_def]
QED

(* This is the exact same-execution memory-taint obligation that remains after
   successful operational call selection. No independently chosen endpoint is
   substituted for ghost_blocks. *)
Theorem invoke_memory_taint_boundary:
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs ==>
  (SND (ghost_step fuel ctx PG G tn inst s)).t_mem =
  (SND (ghost_blocks fuel ctx callee (MAP (op_prov G) ops)
     FEMPTY (tn with t_var := FEMPTY) cs)).t_mem
Proof
  strip_tac >> simp[Once ghost_defs]
QED
