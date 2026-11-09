(* Reachability-sensitive counted sequencing for slice operands. *)
Theory bodyMemSliceContinue
Ancestors
  bodyMemSliceTerminal rawCallArgumentMemory exprSimSliceOrdinaryContinue
  exprSimMemDefs exprSimHypsDefs exprSimProps exprSimWordArgs

Theorem slice_two_read_outcome_seq_mem:
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_mem ctx func cenv cx ty start ec /\
  (!gs v ee. bind (eval_expr cx start) (read_result cx) (ec with gas_obs := gs) =
      (INL v,ee) /\ ee.gas_obs = [] ==>
    expr_sim_mem ctx func cenv cx ty len ee /\
    gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok ee) /\
  gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok ec /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\
  stmt_state_rel ctx func cenv cx ec u /\ alloca_history func u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!e1 e2 t r i k gs1 gs2.
    bind (eval_expr cx start) (read_result cx) (ec with gas_obs := gs1) =
      (INL (IntV (&i)),e1) /\
    bind (eval_expr cx len) (read_result cx) (e1 with gas_obs := gs2) =
      (INL (IntV (&k)),e2) /\ e1.gas_obs = [] /\ e2.gas_obs = [] /\
    expr_post ctx func cenv cx start ec sc sd u e1 (IntV (&i)) sop t /\
    expr_post ctx func cenv cx len e1 sd se t e2 (IntV (&k)) lop r /\
    expr_store_bound cx (expr_type start) (IntV (&i)) sop t /\
    expr_store_bound cx (expr_type len) (IntV (&k)) lop r /\
    stmt_state_rel ctx func cenv cx e1 t /\ stmt_state_rel ctx func cenv cx e2 r /\
    expr_sim_inv cenv cx env e1 /\
    MAP FDOM ec.scopes = MAP FDOM e1.scopes /\
    MAP FDOM e1.scopes = MAP FDOM e2.scopes /\
    i < dimword (:256) /\ k < dimword (:256) /\
    eval_operand sop t = SOME (n2w i) /\ eval_operand lop r = SOME (n2w k) /\
    r.vs_current_bb = se.cs_current_bb /\ r.vs_inst_idx = LENGTH se.cs_current_insts /\
    alloca_history func r /\ u.vs_alloca_next <= r.vs_alloca_next /\ ~r.vs_halted ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (finish_slice (IntV (&i):value) (IntV (&k):value) : evaluation_state -> eval_result evaluation_result)
      (e2,r) Q (\res ee rr. expr_exit res rr)) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        finish_slice sv lv od) (ec,u) Q (\res ee rr. expr_exit res rr)
Proof
  strip_tac >> irule raw_call_mem_value_bind >> simp[] >>
  conj_tac >- (rpt gen_tac >> Cases_on `r` >> Cases_on `exc` >>
    simp[exprSimDefsTheory.expr_exit_def] >>
    rename1 `Error err` >> Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  qexistsl_tac [`cenv`, `sop`, `sc`, `sd`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all slice_uint_read_post >> strip_tac >> gvs[] >>
  `expr_sim_mem ctx func cenv cx ty len ee /\
   gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok ee` by metis_tac[] >>
  `expr_body_pre cenv cx env len ee` by gvs[expr_body_pre_def] >>
  `stmt_state_rel ctx func cenv cx ee t` by metis_tac[expr_post_state] >>
  irule raw_call_mem_value_bind >> simp[] >>
  conj_tac >- (rpt gen_tac >> Cases_on `r` >> Cases_on `exc` >>
    simp[exprSimDefsTheory.expr_exit_def] >>
    rename1 `Error err` >> Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  qexistsl_tac [`cenv`, `lop`, `sd`, `se`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all slice_uint_read_post >> strip_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- metis_tac[expr_post_state] >>
  qexistsl_tac [`ee`, `gs`, `gs'`, `t`] >> simp[]
QED
