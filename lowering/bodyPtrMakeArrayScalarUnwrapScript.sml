(* Actual scalar unwrap branches share the clean word/destination interface.
   No scalar source-buffer coverage is required or exported. *)
Theory bodyPtrMakeArrayScalarUnwrap
Ancestors
  bodyPtrMakeArrayUnwrapIdentity bodyPtrMakeArrayScalarSemantics
  bodyPtrMakeArrayMemoryWord bodyPtrMakeArrayMloadFrame
  bodyPtrMakeArrayExternalWord bodyPtrMakeArrayWordClean
  bodyPtrDefs loweringPosts context compileEnv venomState

Theorem scalar_stack_unwrap_endpoint:
  unwrap_value ce (StackValue t arg) sm = (op,sb) /\
  vv_post ctx fn ce cx e es sa sm s0 es' tv (StackValue t arg) s /\
  read_result cx tv es' = (INL v,es') /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  ptr_vv_ok cx (expr_type e) tv (StackValue t arg) es' G tn s /\
  ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d ce cx es' G tn s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  ptr_covers G tn dst s n ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    expr_post ctx fn ce cx e es sa sb s0 es' v op sf /\
    eval_operand op sf = SOME (typed_val_to_w256 ty v) /\
    op_taint tnf op = {} /\
    ptr_val_ok cx (expr_type e) v op Gf tnf sf /\
    ghost_inv d ce cx es' Gf tnf sf /\
    ghost_kept ce es sa G0 tn0 s0 Gf tnf /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var dst sf = lookup_var dst s /\
    ptr_covers Gf tnf dst sf n
Proof
  strip_tac >> drule_all unwrap_stack_ptr_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G`, `tn`, `s`] >>
  gvs[ptr_val_ok_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED
