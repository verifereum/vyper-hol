(* Successful-post transport preserves the actual counted execution. *)
Theory exprSimExtract32TailBoundary
Ancestors
  exprSimExtract32TailLift gasOutcome gasSummary
  exprSimDefs loweringPosts builtinBytes vyperAST vyperState

Theorem extract32_outcome_post_conseq:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!res ee t. Q res ee t ==> Q' res ee t) ==>
  gas_outcome memory tops (ctx,func) source (es,s) Q' R
Proof
  pure_rewrite_tac[gas_outcome_def, gas_summary_at_def] >> metis_tac[]
QED

Theorem extract32_tail_ready_any_post:
  expr_post ctx func cenv cx src es sa sm s0 es1 (BytesV bs) src_op s1 /\
  expr_post ctx func cenv cx off es1 sm st3 s1 es2 (IntV i) off_op s2 /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv st3 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= st3.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  extract32_result_base_ok bt /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
              BytesT (Fixed k) => k <= 32 | _ => T) /\
  is_word_type (BaseT bt) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt) /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s2.vs_memory /\
  LENGTH bs < dimword (:256) /\ Num i < dimword (:256) /\
  p + 32 + LENGTH bs < dimword (:256) /\
  eval_operand len s2 = SOME (n2w (LENGTH bs)) /\
  eval_operand dp s2 = SOME (n2w (p + 32)) /\
  eval_operand off_op s2 = SOME (n2w (Num i)) /\
  (!z. len = Var z ==> not_fresh_at st3 z) /\
  (!z. dp = Var z ==> not_fresh_at st3 z) /\
  (!z. off_op = Var z ==> not_fresh_at st3 z) /\
  compile_extract32_load len dp off_op st3 = (raw,st4) /\
  compile_clamp_basetype raw (BaseT bt) st4 = (op,sb) /\
  fn_has_code st3 sb func /\ es2.gas_obs = [] /\
  ~s2.vs_halted /\ s2.vs_current_bb = st3.cs_current_bb /\
  s2.vs_inst_idx = LENGTH st3.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (lift_sum (evaluate_type_builtin cx Extract32 (BaseT bt)
       [expr_type src;expr_type off] [BytesV bs;IntV i])) (\v. return (Value v)))
    (es2,s2)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off])
        es sa sb s0 ee tv (StackValue ty op) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all extract32_tail_ready_any >>
  disch_then (qspec_then `ty` assume_tac) >>
  irule extract32_outcome_post_conseq >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
