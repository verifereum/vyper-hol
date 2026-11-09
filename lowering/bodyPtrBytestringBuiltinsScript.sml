(*
 * Bytestring builtins: slice, concat, uint2str, calldata slice.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   bytestring_builtin_expr_ptr_ok
 *)
Theory bodyPtrBytestringBuiltins
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list
  bodyPtrBytestringBuiltinsCalldataCase bodyPtrBytestringBuiltinsConcatCase
  bodyPtrBytestringBuiltinsSliceCase bodyPtrBytestringBuiltinsUintCase

val _ = Parse.hide "body";

Theorem bytestring_builtin_expr_ptr_ok:
  !cx ty bt es.
    ((?n. bt = CalldataSlice n) \/ (?n. bt = Concat n) \/ (?n. bt = Slice n) \/
     (?n. bt = Uint2Str n)) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC
  >~ [`CalldataSlice`]
  >- (irule calldata_slice_body_expr_ptr_ok >> first_assum ACCEPT_TAC)
  >~ [`Concat`]
  >- (irule concat_body_expr_ptr_ok >> first_assum ACCEPT_TAC)
  >~ [`Slice`]
  >- (irule slice_body_expr_ptr_ok >> first_assum ACCEPT_TAC)
  >~ [`Uint2Str`]
  >- (irule uint2str_body_expr_ptr_ok >> first_assum ACCEPT_TAC)
QED
