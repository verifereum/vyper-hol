(* Clean stack-word packaging shared by deterministic expression suffixes. *)
Theory bodyPtrHashBuiltinsWordSummary
Ancestors bodyPtrHashBuiltinsSummary bodyPtrDefs exprSimDefs
  gasSummaryComposePtr

Theorem hash_word_endpoint_summary:
  (!tail. source (ee with gas_obs := tail) =
    (INL tv, ef with gas_obs := tail)) /\ ef.gas_obs = [] /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
  vv_post ctx fn cenv cx e es sa sb s0 ef tv (StackValue ann op) u /\
  u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv d cenv cx ef Gf tf u /\ is_word_type (expr_type e) /\
  read_result cx tv ef = (INL v,ef) /\
  op_taint tf op = {} /\ op_prov Gf op = NONE /\
  ghost_kept cenv es sa G0 tn0 s0 Gf tf ==>
  ?marks. gas_summary_ptr_at D (ctx,fn) PG marks source (ee,s,G,tn)
    (\res ef G' tn' t. ?tv. res = INL tv /\
      vv_post ctx fn cenv cx e es sa sb s0 ef tv (StackValue ann op) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ef G' tn' t /\
      ptr_vv_ok cx (expr_type e) tv (StackValue ann op) ef G' tn' t /\
      (!t' op'. StackValue ann op = StackValue t' op' /\
        ~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op' G' t) /\
      (!t' p. StackValue ann op = LocatedValue t' p /\
        p.ptr_location = LocMemory ==> ptr_buf_ok cenv e p.ptr_operand G' t) /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn') R
Proof
  strip_tac >> qexists_tac `[]` >> irule hash_zero_mark_summary >>
  first_assum (irule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`INL tv`, `ef`] >> simp[] >>
  simp[ptr_vv_ok_def] >> irule ptr_val_ok_word >> simp[]
QED
