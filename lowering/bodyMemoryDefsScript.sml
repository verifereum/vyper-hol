(* Memory-safe body judgments.  Caller-owned return buffers survive entry
   into a fresh callee allocation map, so their identity and capacity are
   carried separately from the callee's allocation sites. *)
Theory bodyMemoryDefs
Ancestors
  exprSimMemDefs stmtSimDefs
  loweringPosts
  bodySim stmtSim exprSim exprSimHyps fragExecMem memSafeRun allocaHistory compileEnv
  exprLowering exprLoweringProps context venomState venomExecSemantics
  vyperInterpreter vyperTypeSystem vyperTypeCallGraph list finite_map words

(* The size in ce_return_buf describes a pointer slot.  Capacity below is
   the actual caller allocation, supplied by the declared return layout. *)

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


(* The buffer frame applies at concrete entries and at every continuing
   landing, including break and continue.  Terminal exits carry their own
   memory-safe run witness. *)

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
