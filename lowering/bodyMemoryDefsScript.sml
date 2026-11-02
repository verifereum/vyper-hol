(* Memory-safe body judgments.  Caller-owned return buffers survive entry
   into a fresh callee allocation map, so their identity and capacity are
   carried separately from the callee's allocation sites. *)
Theory bodyMemoryDefs
Ancestors
  bodySim stmtSim exprSim exprSimHyps fragExecMem memSafeRun allocaHistory compileEnv
  exprLowering exprLoweringProps context venomState venomExecSemantics
  vyperInterpreter vyperTypeSystem vyperTypeCallGraph list finite_map words

(* The size in ce_return_buf describes a pointer slot.  Capacity below is
   the actual caller allocation, supplied by the declared return layout. *)
Definition return_buf_frame_def:
  (return_buf_frame NONE (cenv : compile_env) sa s <=>
    cenv.ce_return_buf = NONE) /\
  (return_buf_frame (SOME (bw : bytes32, capacity)) cenv sa s <=>
    ?x slot_size.
      cenv.ce_return_buf = SOME (PtrVar (Var x) slot_size) /\
      lookup_var x s = SOME bw /\ not_fresh_at sa x /\
      w2n bw + capacity <= s.vs_alloca_next)
End

Theorem return_buf_frame_frame:
  !d cenv cenv' sa sb s s'.
    return_buf_frame d cenv sa s /\
    cenv'.ce_return_buf = cenv.ce_return_buf /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
           lookup_var x s' = SOME w) /\
    s.vs_alloca_next <= s'.vs_alloca_next ==>
    return_buf_frame d cenv' sb s'
Proof
  rpt gen_tac >> Cases_on `d`
  >- simp[return_buf_frame_def] >>
  rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
  rw[return_buf_frame_def] >>
  qexistsl_tac [`x`, `slot_size`] >> simp[] >>
  fs[not_fresh_at_def] >> rpt strip_tac >>
  qpat_x_assum `!n. sa.cs_next_var <= n ==> _`
    (qspec_then `n` mp_tac) >> simp[]
QED

Theorem return_buf_frame_jump_to:
  !d cenv sa l s.
    return_buf_frame d cenv sa (jump_to l s) <=>
    return_buf_frame d cenv sa s
Proof
  rpt gen_tac >> Cases_on `d`
  >- simp[return_buf_frame_def] >>
  rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
  simp[return_buf_frame_def, lookup_var_def, jump_to_def]
QED

(* Frontier monotonicity also preserves caller buffers absent from the
   callee's allocation map.  The other expression postconditions are S1's. *)
Definition expr_sim_mem_def:
  expr_sim_mem ctx func cenv cx ty e es <=>
    !sa sb op res es' s0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      (do result <- eval_expr cx e; read_result cx result od) es = (res, es') /\
      expr_res_ok res /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
      frag_exec_mem ctx sa sb
        (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
             alloca_history func s)
        (\s. ?v. res = INL v /\
          expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
          s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
        (expr_exit res)
End

Definition expr_vv_sim_mem_def:
  expr_vv_sim_mem ctx func cenv cx ty e es <=>
    !sa sb vv res es' s0.
      compile_expr cenv ty e sa = (vv, sb) /\
      eval_expr cx e es = (res, es') /\ expr_vv_res_ok res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec_mem ctx sa sb
        (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
             alloca_history func s)
        (\s. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
          s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
        (expr_exit res)
End

(* The buffer frame applies at concrete entries and at every continuing
   landing, including break and continue.  Terminal exits carry their own
   memory-safe run witness. *)
Definition stmt_frag_mem_def:
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (m : compile_env compiler) es res es' <=>
    !sa sb s0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
      return_buf_frame d cenv sa s0 /\
      ~block_is_terminated sa /\ stmt_res_ok lctx res /\
      stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
      ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      (?s cenv''.
         stmt_lands lctx sb res s /\ ~s.vs_halted /\
         (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
         cenv_top_ext cenv cenv'' es'.scopes /\
         stmt_state_rel ctx func cenv'' cx es' s /\ alloca_history func s /\
         (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                lookup_var x s = SOME w) /\
         (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP s.vs_allocas aid = SOME b) /\
         return_buf_frame d cenv'' sb s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\
         !fuel r. run_from fuel ctx func s = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func s0 = r /\
                    (mem_safe_run fuel ctx func s ==>
                     mem_safe_run fuel' ctx func s0)) \/
      (?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
                stmt_exit RetQ es' res r /\ mem_safe_run fuel ctx func s0)
End

Definition frame_ret_ok_mem_def:
  frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty <=>
    !cenv' env lctx eo es res es'.
      same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
      IS_SOME (type_stmt env ret_ty (Return eo)) /\
      call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
      (!e ty. eo = SOME e ==>
              expr_sim_mem ctx func cenv' cx ty e es /\
              expr_vv_sim_mem ctx func cenv' cx ty e es) /\
      eval_stmt cx (Return eo) es = (res, es') ==>
      stmt_frag_mem d ctx func cx lctx RetQ cenv'
        (stmt_env cenv' lctx ret_ty (Return eo)) es res es'
End

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_MEMORY_FRAME_AUDIT OK\n"
     else raise Fail "body memory frame inherited admission"
  end) [return_buf_frame_frame, return_buf_frame_jump_to,
        mem_safe_run_all_fuel, frag_exec_mem_complete];
