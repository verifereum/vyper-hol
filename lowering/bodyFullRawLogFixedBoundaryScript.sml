(* Fixed RawLog compiler and scratch-resource boundaries. *)
Theory bodyFullRawLogFixedBoundary
Ancestors
  bodySimFull bodyPtrDefs exprLowering gasShadowState
  exprSimDefs loweringPosts compileEnv venomState list finite_map
Libs
  pairLib

Theorem raw_log_fixed_layout:
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  compile_call compile_expr cenv ret_ty ty RawLog [topics; data] dflt sa =
    (vv, sb) ==>
  ?ops s1 buf s2 value s3 s4.
    compile_multi_exprs compile_expr cenv (raw_log_topic_exprs topics) sa =
      (ops, s1) /\
    compile_alloc_buffer 32 s1 = (buf, s2) /\
    lower_value compile_expr cenv (expr_type data) data s2 = (value, s3) /\
    emit_void MSTORE [buf.buf_operand; value] s3 = ((), s4) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++
      [Lit 32w; buf.buf_operand]) [] s4 = ((), sb) /\
    vv = StackValue ret_ty (Lit 0w)
Proof
  strip_tac >>
  qpat_x_assum `compile_call _ _ _ _ RawLog _ _ _ = _` mp_tac >>
  simp[compile_call_def] >> rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[]
QED

(* The scratch ALLOCA precedes the fixed data child.  Its output is old
   at the child's entry, so the joint post keeps both its value and its
   pointer ghost.  No premise about the child's implementation is used. *)
Theorem raw_log_fixed_scratch_post:
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  compile_alloc_buffer 32 sm = (buf, sa) /\
  buf.buf_operand = Var p /\
  not_fresh_at sa p /\
  expr_post H ctx func cenv cx data es sa sb s0 ee v data_op s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  ptr_covers G0 tn0 p s0 32 /\
  FLOOKUP s0.vs_allocas aid = SOME (b, 32) ==>
  ptr_covers G tn p s 32 /\
  FLOOKUP s.vs_allocas aid = SOME (b, 32)
Proof
  simp[ptr_covers_def, ghost_kept_at_def, expr_post_def] >>
  rpt strip_tac >> metis_tac[]
QED

(* Pair the fixed continuation after topics, without imposing a canonical
   parameter ghost or replaying the topic compilation. *)
Theorem raw_log_fixed_continuation_shadow:
  gas_shadow_compiles (compile_alloc_buffer 32) (compile_alloc_buffer 32) /\
  gas_shadow_compiles (lower_value compile_expr cenv (expr_type data) data)
    (lower_value compile_expr cenv (expr_type data) (gas_shadow_expr data)) /\
  gas_shadow_state sm shadow_sm /\
  compile_alloc_buffer 32 sm = (buf, sa) /\
  lower_value compile_expr cenv (expr_type data) data sa = (value, sb) /\
  emit_void MSTORE [buf.buf_operand; value] sb = ((), sc) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++
    [Lit 32w; buf.buf_operand]) [] sc = ((), sd) ==>
  ?shadow_sa shadow_sb shadow_sc shadow_sd.
    compile_alloc_buffer 32 shadow_sm = (buf, shadow_sa) /\
    lower_value compile_expr cenv (expr_type data) (gas_shadow_expr data)
      shadow_sa = (value, shadow_sb) /\
    emit_void MSTORE [buf.buf_operand; value] shadow_sb = ((), shadow_sc) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++
      [Lit 32w; buf.buf_operand]) [] shadow_sc = ((), shadow_sd) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_state sc shadow_sc /\ gas_shadow_state sd shadow_sd
Proof
  strip_tac >>
  Cases_on `compile_alloc_buffer 32 shadow_sm` >>
  rename1 `compile_alloc_buffer 32 shadow_sm = (sbuf, shadow_sa)` >>
  `sbuf = buf /\ gas_shadow_state sa shadow_sa` by
    (qpat_x_assum `gas_shadow_compiles (compile_alloc_buffer _) _`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sm`, `shadow_sm`] mp_tac) >> simp[]) >>
  gvs[] >>
  Cases_on `lower_value compile_expr cenv (expr_type data)
    (gas_shadow_expr data) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr data) shadow_sa =
    (svalue, shadow_sb)` >>
  `svalue = value /\ gas_shadow_state sb shadow_sb` by
    (qpat_x_assum `gas_shadow_compiles (lower_value _ _ _ _) _`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  Cases_on `emit_void MSTORE [buf.buf_operand; svalue] shadow_sb` >>
  rename1 `emit_void _ _ shadow_sb = (u, shadow_sc)` >>
  `gas_shadow_state sc shadow_sc` by
    (mp_tac (Q.INST [`opc` |-> `MSTORE`, `ops` |-> `[buf.buf_operand; svalue]`]
       gas_shadow_compiles_emit_void) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sb`, `shadow_sb`] mp_tac) >> simp[]) >>
  Cases_on `emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++
    [Lit 32w; buf.buf_operand]) [] shadow_sc` >>
  rename1 `emit_inst _ _ _ shadow_sc = (u', shadow_sd)` >>
  `gas_shadow_state sd shadow_sd` by
    (mp_tac (Q.INST [`opc` |-> `LOG`, `ops` |-> `Lit (n2w (LENGTH ops)) :: REVERSE ops ++
       [Lit 32w; buf.buf_operand]`, `outs` |-> `[]`] gas_shadow_compiles_emit_inst) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sc`, `shadow_sc`] mp_tac) >> simp[]) >>
  Cases_on `u` >> Cases_on `u'` >> gvs[] >>
  qexistsl_tac [`shadow_sc`, `shadow_sd`] >> simp[]
QED
