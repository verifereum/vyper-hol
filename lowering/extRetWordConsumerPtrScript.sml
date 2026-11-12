Theory extRetWordConsumerPtr
Ancestors
  extRetSomeComposePtr extRetCountedPtr bodyPtrDefs fragGasPathPtr
  stmtLowering compileEnv fragExec ptrDiscipline abiBuiltinAllocation
  finite_map words venomExecSemantics venomInst venomState vyperInterpreter
  vyperState

Theorem external_return_word_outcome_ptr:
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) P
    (\res ee gt r. expr_exit res r) /\
  compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x,st') /\
  fn_has_code st st' func /\ ~block_is_terminated st /\
  (!y. op = Var y ==> not_fresh_at st y) /\ ~ctx_has_dalloca ctx /\
  (!res ee G1 tn1 t. P res ee G1 tn1 t ==>
    ?v w base. res = INL v /\ ~t.vs_halted /\
      t.vs_current_bb = st.cs_current_bb /\
      t.vs_inst_idx = LENGTH st.cs_current_insts /\
      eval_operand op t = SOME w /\ op_taint tn1 op = {} /\
      stor_taint_ok cx tn1 t /\
      FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 t).vs_allocas
        st.cs_next_id = SOME (base,32) /\ base < dimword (:256)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_stmt cx (Return (SOME e))) (es,s,G,tn) Q
    (\res ee gt r. !tail.
      stmt_exit_ptr (\v es gt r. T) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> Cases_on `x` >> irule external_return_some_outcome_ptr >>
  qexists_tac `P` >> reverse conj_tac
  >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `v` >> simp[] >>
  irule compile_external_return_word_gas_path_ptr >>
  simp[] >> metis_tac[]
QED
