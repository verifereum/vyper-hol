(* Shared counted expression judgments and their result domains. *)
Theory exprSimDefs
Ancestors
  loweringStateRelDefs
  loweringPosts gasOutcome gasContext exprLowering compileEnv loweringSlice
  vyperInterpreter vyperState venomState venomExecSemantics unitMemInv

Definition halt_exit_def:
  halt_exit H cx (ee:evaluation_state) (res : 'a + exception) r <=>
    (res = INR HaltException ==> ?s. r = Halt s /\ halt_rel H cx ee s)
End

Definition expr_exit_def:
  (expr_exit (INR (Error (RuntimeError m))) (Abort a s) <=> T) /\
  (expr_exit (INR (Error (RevertData d))) (Abort a s) <=> a = Revert_abort) /\
  (expr_exit (INR (AssertException str)) (Abort a s) <=>
     a = Revert_abort \/ (a = ExHalt_abort /\ str = "UNREACHABLE")) /\
  (expr_exit (INR HaltException) (Halt s) <=> s.vs_returndata = []) /\
  (expr_exit _ _ <=> F)
End

Definition expr_res_ok_def:
  expr_res_ok (res : value + exception) <=>
    (?v. res = INL v) \/ (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str)) \/
    res = INR HaltException
End

Definition expr_sim_def:
  expr_sim ctx func cenv cx ty e es <=>
    !st0 sa sb op s0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 ∧
        storage_well_formed_on cx es (FST H)) ∧ ~s0.vs_halted ∧
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) cx st0
        (bind (eval_expr cx e) (read_result cx)) (es, s0)
        (\H res ee t. ?v. res = INL v /\
          expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
End

Definition expr_vv_res_ok_def:
  expr_vv_res_ok (res : eval_result + exception) <=>
    (?v. res = INL (Value v)) \/ (?p. res = INL (PlaceR p)) \/
    (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str)) \/
    res = INR HaltException
End

Definition expr_read_res_ok_def:
  expr_read_res_ok cx es res <=>
    (?r v. res = INL r /\ read_result cx r es = (INL v,es)) \/
    (?exc. res = INR exc /\
           expr_res_ok (INR exc : value + exception))
End

Definition expr_vv_sim_def:
  expr_vv_sim ctx func cenv cx ty e es <=>
    !st0 sa sb vv s0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 ∧
        storage_well_formed_on cx es (FST H)) ∧ ~s0.vs_halted ∧
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) cx st0 (eval_expr cx e) (es, s0)
        (\H res ee t. ?tv. res = INL tv /\
          vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
End

Theorem expr_exit_INL[simp]:
  !x r. ~expr_exit (INL x) r
Proof
  Cases_on `r` >> simp[expr_exit_def]
QED

Theorem expr_exit_success_map:
  !f r. expr_exit (case r of INL v => INL (f v) | INR ex => INR ex) =
        expr_exit r
Proof
  rpt gen_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `r` >- simp[] >>
  rename1 `INR ex` >> Cases_on `ex` >>
  Cases_on `x` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

(* The DALLOCA no-wrap fact the sims assume at a run's start s0 holds at
   its success states too: what is reachable from such a state was reached
   from s0 (completed sub-runs, loop rounds and INVOKE returns included).
   A sim that runs a second fragment from the first one's end uses this to
   supply that fragment's antecedent. *)
Theorem gas_outcome_no_wrap_post:
  !memory tops ctx func cx st0 source es s0 Q R.
    gas_outcome memory tops (ctx,func) cx st0 source (es,s0) Q R /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==>
                 dalloca_no_wrap inst s) ==>
    gas_outcome memory tops (ctx,func) cx st0 source (es,s0)
      (\H res ee t. Q H res ee t /\
         !fn inst s. frag_reachable ctx func t fn inst s ==>
                     dalloca_no_wrap inst s) R
Proof
  cheat
QED
