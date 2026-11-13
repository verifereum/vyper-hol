(*
 * Seam of bodyPtrTypeBuiltins: extract32(src, off).
 *
 * TOP-LEVEL:
 *   extract32_body_expr_ptr_ok
 *)
Theory bodyPtrTypeBuiltinsSeamExtract32
Ancestors
  bodyPtrTypeBuiltinsExtract32Sim exprSimExtract32Source
  vyperTypeSystem exprSimHypsDefs
  bodyPtrTypeBuiltinsIndexEntry bodyPtrTypeBuiltinsSavedOperand
  bodyPtrTypeBuiltinsBounds bodyPtrTypeBuiltinsTransport
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* S1's proof of this case is exprSimExtract32's compile_extract32_case
   (exprSimExtract32Source/Ready/Read/Run/Tail/Post/Assembly...), proved on
   this base; extract32_body_pre_shape gives the operand shape.  Typing
   (well_typed_type_builtin_args) admits only a dynamic Bytes[m] source
   and an unsigned offset, so fixed-bytes sources never reach here.  The
   main obligation is that the source's bytes stay untainted while the
   offset is evaluated (ghost_kept over the offset's run).  The lowering reads the source's length word, checks the bounds,
   MLOADs 32 bytes at the offset and clamps to the result type. *)
Theorem extract32_body_expr_ptr_ok:
  !cx ann typ es.
    (type_builtin_args_length_ok Extract32 (LENGTH es) ==>
     body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin ann Extract32 typ es)
Proof
  rpt gen_tac >> strip_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule extract32_body_pre_shape >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [src;off]` by
    (first_x_assum irule >> simp[type_builtin_args_length_ok_def]) >>
  `?m. expr_type src = BaseT (BytesT (Dynamic m)) /\ is_uint_type (expr_type off)` by
    (qpat_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[NoAsms, expr_body_pre_def, well_typed_expr_def, well_typed_type_builtin_args_def] >>
     strip_tac >> gvs[]) >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty
     (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) es'` by
    (irule extract32_ready_expr_vv_sim_ptr >> goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[] >> irule expr_sim_ptr_of_vv >> metis_tac[]
QED
