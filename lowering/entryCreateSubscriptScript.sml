Theory entryCreateSubscript
Ancestors
  entryCreateEffectFocus exprSimTuple exprSimMapKey exprSimPlaces
  exprLoweringProps emitHelperProps exprSimAbiGasBridge
  createSizeCutCode venomInst compileEnv fragExec list

(* The tuple index is a literal, and has no separate compiled interval. *)
Theorem create_subscript_tuple_layout:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = TupleT tys /\ place_type ce obj = ValPT (TupleT tys) ==>
  expr_body_pre ce cx env obj es /\
  ?ity k bvv sm dst.
    idx = Literal ity (IntL (&k)) /\ k < LENGTH tys /\ EL k tys = ann /\
    compile_expr ce ty obj sa = (bvv,sm) /\
    emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset ce tys (vv_loc bvv)
                                      (literal_int_index idx)))] sm = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst (vv_loc bvv))
Proof
  strip_tac >> drule_all tuple_pre_base >> strip_tac >>
  drule_all compile_expr_tuple_subscript >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem create_subscript_tuple_suffix_code:
  emit_op ADD [baseop; Lit off] sm = (dst,sb) ==>
  create_cut_code {} sm sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sm sb)
Proof
  strip_tac >> conj_tac
  >- (`create_cut_code {} sm (SND (emit_op ADD [baseop; Lit off] sm))` by
        simp[create_cut_code_emit_op, create_cut_targets_def] >>
      qpat_assum `emit_op _ _ _ = _` (fn th => fs[th])) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  fs[same_blocks_def, frag_code_def, emitted_blocks_def, mk_inst_def,
     DROP_LENGTH_NIL]
QED
