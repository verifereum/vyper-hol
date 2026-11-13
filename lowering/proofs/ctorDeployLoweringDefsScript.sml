(* Definitions shared by the pieces of deploy_unit_execution_correct (the
 * constructor's S1, ctorDeployLowering).  They name the facts the pieces
 * exchange; none of them is a correctness claim.
 *
 * deploy_ctor_start: the source state es0 where the constructor body starts
 *   in load_contract, with outcomes NONE: the selected constructor, its
 *   bound arguments, the machine am_c after constant evaluation, then the
 *   value transfer and the reentrancy lock.
 * deploy_ctor_finish: what load_contract returns from the body's result res
 *   and end state st.  Only a fall-through and a valueless return finish
 *   normally; the other exceptions are the result.
 * deploy_ctor_code: the code compile_generate_deploy emits for a contract
 *   with a constructor, named at the points the proof needs: the body
 *   start sa, its end sb, the fall-through jump to sj, the exit block
 *   st_exit, the unlock to st_epilogue and the epilogue to st_final, all in
 *   the deploy unit's function func.
 *)
Theory ctorDeployLoweringDefs
Ancestors
  ctorDeployDefs e2eDeployDefs fragExec compileVyper moduleLowering
  stmtLowering compileEnv vyperInterpreter vyperState

Definition deploy_ctor_start_def:
  deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) <=>
    ?args env imms.
      lookup_function NONE tx.function_name Deploy tops =
        SOME (mut, nr, args, [], NoneT, body) /\
      LENGTH tx.args = LENGTH args /\
      bind_arguments (type_env_all_modules [(NONE, tops)]) args tx.args =
        SOME env /\
      initial_immutables (type_env_all_modules [(NONE, tops)])
        [(NONE, tops)] = SOME imms /\
      evaluate_all_constants (deploy_evaluation_context tops am tx)
        (am with <| immutables updated_by CONS (tx.target, imms);
                    exports updated_by CONS (tx.target, []) |>)
        tx.target [(NONE, tops)] = SOME am_c /\
      ignore_bind (send_call_value mut (deploy_evaluation_context tops am tx))
        (lock_if_nr (deploy_evaluation_context tops am tx) nr
           (is_view_mut mut))
        (initial_state am_c [env] with <| outcomes := NONE; requests := [] |>) =
        (INL (), es0)
End

Definition deploy_ctor_finish_def:
  deploy_ctor_finish tops tx cx nr mut (am_c : abstract_machine)
    (res : unit + exception) st =
    if res = INL () \/ res = INR (ReturnException NoneV) then
      case unlock_if_nr cx nr (is_view_mut mut) st of
        (INL (), st') =>
          INL (finalize_pending_deletions
                 (abstract_machine_from_state am_c.sources am_c.exports
                    am_c.layouts st' with
                    sources updated_by CONS (tx.target, [(NONE, tops)])),
               st'.requests)
      | (INR e, _) => INR e
    else INR (OUTR res)
End

Definition deploy_ctor_code_def:
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body, cenv, nr, nkey, ut, imm, exit_lbl,
     sa, sb, sj, st_exit, st_epilogue, st_final, func) <=>
    ?exts ints fb cf cenv0 pos_args is_payable ret cap st_pay st1 cenv1 st2
     st3 old_bb.
      lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
      classify_functions tops = (exts, ints, fb, SOME cf) /\
      set_constructor_package_target rpolicy.rpol_target
        (package_constructor tops T (K global_nonreentrant_slot) cf) =
        (cenv0, pos_args, is_payable, nr, nkey, ut, body, ret) /\
      cap = imm_len tops /\
      (if is_payable then comp_return ()
       else comp_bind (emit_op CALLVALUE [])
              (\cv. comp_bind (emit_op ISZERO [cv])
                      (\no_val. emit_void ASSERT [no_val])))
        (initial_compile_state "__deploy") = ((), st_pay) /\
      (if cap > 0 then
         comp_bind (compile_fixed_region_with_id cap)
           (\r. comp_return (SND r).buf_operand)
       else comp_return (Lit 0w)) st_pay = (imm, st1) /\
      compile_register_constructor_args
        (cenv0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
        pos_args 0 0 st1 = (cenv1, st2) /\
      (if nr then compile_nonreentrant_lock nkey ut F else comp_return ())
        st2 = ((), st3) /\
      fresh_label "ctor_exit" st3 = (exit_lbl, sa) /\
      cenv = cenv1 with ce_ctor_exit_label := SOME exit_lbl /\
      compile_stmts cenv NoLoop NoneT body sa = ((), sb) /\
      (if block_is_terminated sb then comp_return ()
       else emit_inst JMP [Label exit_lbl] []) sb = ((), sj) /\
      new_block exit_lbl sj = (old_bb, st_exit) /\
      (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
        st_exit = ((), st_epilogue) /\
      compile_constructor_epilogue (LENGTH runtime_bc) cap imm st_epilogue =
        ((), st_final) /\
      MEM func dunit.cu_context.ctx_functions /\
      func.fn_name = "__deploy" /\ fn_inst_ids_distinct func /\
      fn_has_code (initial_compile_state "__deploy") sa func /\
      fn_has_code sa sb func /\ fn_has_code sb sj func /\
      fn_has_code st_exit st_final func
End
