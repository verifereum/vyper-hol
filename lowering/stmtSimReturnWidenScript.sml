(*
 * Returns whose value type widens to the declared return type
 *
 * type_stmt admits `return e` when expr_type e widens to the return type
 * (type_widens_to: a bytestring or dynamic array of a smaller bound,
 * elementwise).  An internal memory return uses compile_store_memory,
 * which converts layouts with compile_store_memory_typed.  A compatible
 * bounded external ABI return can encode directly at the source layout.
 * See externalReturnValuedFull for the proof of that path.
 *
 * TOP-LEVEL:
 *   stack_return_widens_eq — a stack-returned type only widens from itself
 *)

Theory stmtSimReturnWiden
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  list rich_list finite_map
  fragExec  exprSimAlloc exprSimCopy exprSimStorageCopy
  intCallReturnMem intCallResult typedMemoryCopy exprSimTypedAlloc valueCopy valueCopyBytes
  loweringSlice localPtrsProps stmtSimReturn
  stmtLowering exprLowering emitHelper exprLoweringProps context compileEnv loweringStateRelDefs
  typedCopyDomain valueEncoding vyperTypeSystem vyperState vyperTyping
  venomExecSemantics venomInst venomState

Theorem stack_word_fits_eq[local]:
  (!sty ty. arg_type_fits sty ty /\ is_word_type ty ==> sty = ty) /\
  (!stys tys. arg_types_fit stys tys /\ EVERY is_word_type tys ==>
     stys = tys)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, is_word_type_def] >> gvs[]
QED

(* Word members widen only from themselves, so stack returns need no
   conversion. *)
Theorem stack_return_widens_eq:
  !sft tenv sty ty.
    0 < returns_stack_count sft ty /\ type_widens_to tenv sty ty ==>
    sty = ty
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[returns_stack_count_def, tuple_like_stack_count_def] >>
  rpt strip_tac >> gvs[COND_RAND, COND_RATOR, COND_EXPAND] >>
  metis_tac[typed_copy_word_widening, typed_copy_struct_widening,
            typed_copy_tuple_widening, cj 2 stack_word_fits_eq]
QED
