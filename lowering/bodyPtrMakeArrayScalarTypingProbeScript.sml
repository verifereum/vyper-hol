(* Source-typing diagnostic for the exact scalar-bytes fixture.
   This tests the direction of widening, not compiler execution. *)
Theory bodyPtrMakeArrayScalarTypingProbe
Ancestors
  bodyPtrMakeArrayScalarReturnProbe memoryLocalRhsProps exprSimHypsDefs
  vyperTypeSystem

val B32 = ``BaseT (BytesT (Dynamic 32))``
val B64 = ``BaseT (BytesT (Dynamic 64))``
val W = ``TupleT [^B64; ^B32]``
val N = ``TupleT [^B32; ^B32]``
val callN = ``Call ^N (IntCall (NONE,"empty_wide")) [] NONE``

Theorem scalar_return_narrowing_rejected:
  !tenv. ~type_widens_to tenv ^W ^N
Proof
  simp[type_widens_to_def, arg_type_fits_def]
QED

Theorem scalar_return_call_typing_rejected:
  FLOOKUP env.fn_sigs (NONE,"empty_wide") = SOME sig /\
  sig.ret_ty = ^W ==>
  ~well_typed_expr env ^callN
Proof
  strip_tac >> simp[Once well_typed_expr_def,
                    scalar_return_narrowing_rejected]
QED

Theorem scalar_return_body_pre_rejected:
  FLOOKUP env.fn_sigs (NONE,"empty_wide") = SOME sig /\
  sig.ret_ty = ^W ==>
  ~expr_body_pre cenv cx env ^callN es
Proof
  strip_tac >> drule_all scalar_return_call_typing_rejected >>
  simp[expr_body_pre_def]
QED
