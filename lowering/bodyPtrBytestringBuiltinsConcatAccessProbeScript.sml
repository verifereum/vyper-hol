(* Conditional access audit; source/frame reachability is a separate obligation. *)
Theory bodyPtrBytestringBuiltinsConcatAccessProbe
Ancestors bodyPtrBytestringBuiltinsConcatCapacityProbe ptrSafeRun
  codegenRel contextCodegenRel venomInst venomExecSemantics finite_map words
  ptrDiscipline venomState memLocDefs

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:8)``,
   fcpLib.INDEX_CONV ``dimindex(:256)``];

Theorem concat_overhang_access_failure:
  !lo G fn s id dst value w b.
    ~in_revert_forward fn s /\
    lookup_var dst s = SOME (n2w (b + 33)) /\
    eval_operand value s = SOME w /\
    FLOOKUP G dst = SOME (b,64) /\
    b + 33 < dimword (:256) ==>
    ~access_ok lo G fn (mk_inst id MSTORE [Var dst;value] []) s
Proof
  rpt strip_tac >>
  gvs[access_ok_def, source_memory_write_ranges_def,
      fixed_source_write_range_def, mk_inst_def, eval_operand_def,
      mem_write_ops_def, op_prov_def]
QED

Theorem concat_overhang_ptr_inst_failure:
  !D lo fuel ctx G tn fn s id dst value w b.
    ~in_revert_forward fn s /\
    lookup_var dst s = SOME (n2w (b + 33)) /\
    eval_operand value s = SOME w /\
    FLOOKUP G dst = SOME (b,64) /\
    b + 33 < dimword (:256) ==>
    ~ptr_inst_ok D lo fuel ctx fn G tn
      (mk_inst id MSTORE [Var dst;value] []) s
Proof
  rpt strip_tac >>
  drule_all concat_overhang_access_failure >>
  gvs[ptr_inst_ok_def] >> metis_tac[]
QED
