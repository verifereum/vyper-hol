(* Counted address evaluation for external-code slices. *)
Theory bodyMemSliceExtcodeAddress
Ancestors
  rawCallArgumentMemory exprSimSliceExtcodeContinue exprSimMemDefs
  exprSimHypsDefs exprSimProps exprSimSource

Theorem slice_address_read_outcome_mem:
  expr_type addr = BaseT AddressT /\ expr_body_pre cenv cx env addr es /\
  expr_sim_mem ctx func cenv cx ty addr es /\
  lower_value compile_expr cenv ty addr sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!ee t bs gs.
    bind (eval_expr cx addr) (read_result cx) (es with gas_obs := gs) =
      (INL (BytesV bs),ee) /\
    expr_post ctx func cenv cx addr es sa sb s ee (BytesV bs) op t /\
    expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    LENGTH bs = 20 /\ ~t.vs_halted /\ ee.gas_obs = [] /\
    eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (finish_slice (BytesV bs) : evaluation_state -> eval_result evaluation_result)
      (ee,t) Q (\res ee r. expr_exit res r)) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx addr) (read_result cx)) finish_slice) (es,s)
    Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr cx addr) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  irule raw_call_mem_value_bind >> simp[] >>
  conj_tac >- (rpt gen_tac >> Cases_on `r` >> Cases_on `exc` >>
    simp[exprSimDefsTheory.expr_exit_def] >>
    rename1 `Error err` >> Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  qexistsl_tac [`cenv`, `op`, `sa`, `sb`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all slice_address_read_post >> strip_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `gs` >> simp[]
QED
