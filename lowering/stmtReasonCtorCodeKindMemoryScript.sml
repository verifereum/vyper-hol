(* The revert encoder's run from a string reason compiled to a pointer into
   the immutables (reason_code_vv) inside a constructor, where unwrap_value
   copies the message out of the immutables' memory region rather than out
   of code.  Admitted: the memory simulation runs only runtime bodies, so
   this leaf is expected to close by contradiction once the body judgments
   carry ~cx.in_deploy. *)
Theory stmtReasonCtorCodeKindMemory
Ancestors
  stmtReasonMemory exprReasonOperand stmtSimReasonExpr stmtSimReason loweringPosts
  fragGasPathMem exprLowering compileEnv vyperInterpreter

Theorem reason_ctor_code_revert_path_mem:
  !ctx func cenv cx se es sa vv sm sb s0 ee tv t str n.
    reason_code_vv vv /\ cenv.ce_is_ctor /\
    expr_type se = BaseT (StringT n) /\
    type_memory_bytes cenv (BaseT (StringT n)) < 2 ** 64 /\
    compile_expr cenv (expr_type se) se sa = (vv, sm) /\
    compile_revert_with_reason cenv vv (expr_type se)
      (type_memory_bytes cenv (expr_type se)) sm = ((), sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    vv_post ctx func cenv cx se es sa sm s0 ee tv vv t /\
    read_result cx tv ee = (INL (StringV str), ee) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func t 0 (Abort Revert_abort u)
Proof
  cheat
QED
