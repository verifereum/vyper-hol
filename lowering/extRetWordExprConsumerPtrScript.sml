Theory extRetWordExprConsumerPtr
Ancestors
  extRetWordConsumerPtr extRetWordInputsPtr typedCopyPtr bodyPtrDefs
  fragGasPathPtr stmtLowering compileEnv fragExec venomInst venomState
  loweringPosts vyperInterpreter vyperState

Theorem external_return_word_expr_outcome_ptr:
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) P
    (\res ee gt r. expr_exit res r) /\
  compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x,st') /\
  fn_has_code st st' func /\ ~block_is_terminated st /\
  (!y. op = Var y ==> not_fresh_at st y) /\ ~ctx_has_dalloca ctx /\
  (!res ee G1 tn1 t. P res ee G1 tn1 t ==> ?v.
    res = INL v /\ expr_post ctx func cenv cx e es sa st s ee v op t /\
    ~t.vs_halted /\ t.vs_current_bb = st.cs_current_bb /\
    t.vs_inst_idx = LENGTH st.cs_current_insts /\
    ghost_inv d cenv cx ee G1 tn1 t /\
    ptr_val_ok cx (expr_type e) v op G1 tn1 t) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_stmt cx (Return (SOME e))) (es,s,G,tn) Q
    (\res ee gt r. !tail.
      stmt_exit_ptr (\v es gt r. T) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)
    external_return_word_outcome_ptr >>
  disch_then irule >> simp[] >>
  qexists_tac `P` >> simp[] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all expr_post_ptr_return_inputs >> strip_tac >>
  drule_all external_return_word_allocation_inputs >> strip_tac >>
  metis_tac[]
QED
