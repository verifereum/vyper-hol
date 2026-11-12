Theory placeRelayoutStaticExit
Ancestors
  placeRelayoutContinuation placeStaticCopyExit
  placeStoreStorage exprSimHyps
  placeDestinationBounds allocaSiteResource allocLimitsProps loweringPosts
  stmtSimDefs exprSimProps venomMemDefs exprLoweringProps fragExec loweringHalt
  emitHelperProps venomInst venomState venomExecSemantics

Theorem owned_target_relayout_store_static_exit:
  compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
    (type_memory_bytes cenv dty) sb = ((),sf) /\
  compile_get_target_ptr cfn cenv bt sa = ((dst,SOME loc,SOME (ValPT dty)),sb) /\
  target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type dty)
    (dst,SOME loc,SOME (ValPT dty)) s /\
  expr_val_own cenv cx sty si sj es v op s0 /\
  sj.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id <= sb.cs_next_id /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s0.vs_memory /\ eval_operand op s0 = SOME sw /\
  (!x. op = Var x ==> not_fresh_at sa x /\ not_fresh_at sb x) /\
  (!l. op <> Label l) /\ 0 < type_memory_size stv /\
  expr_sim_inv cenv cx env ee /\ acyclic_struct_metadata cenv.ce_struct_fields /\
  assign_alloc_ok cenv bt e /\ lowered_value_type cenv e = sty /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  local_ptrs_reserved cenv sb /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  cx.txn.is_static /\ (loc = LocStorage \/ loc = LocTransient) ==>
  ?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[target_post_def] >>
  fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]
QED
