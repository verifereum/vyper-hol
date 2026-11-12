Theory bodyPtrCodeSliceExternalJoin
Ancestors
  bodyPtrCodeSliceExternalAllocated bodyPtrCodeSliceExternalTail
  bodyPtrDefs compileEnv venomState words list vyperState exprSimSource gasSummaryComposePtr

(* Public continuation boundary; the concrete tail is already discharged in
   ExternalAllocated, so consumers need no semantic-tail hypothesis. *)
Theorem external_code_continue_outcome_ptr:
  compile_slice_out_buf sz sa = ((Var out,Var dst),sb) /\
  lower_value compile_expr cenv ty a sb = (aop,sc) /\
  compile_slice_extcode aop sop lop (Var out) (Var dst) sc = (r,sd) /\
  fn_has_code sa sd fn /\ fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  expr_type a = BaseT AddressT /\ expr_body_pre cenv cx env a es /\
  expr_sim_ptr d ctx PG fn cenv cx ty a es /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G0 tn0 s /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  op_taint tn0 sop = {} /\ op_taint tn0 lop = {} /\
  op_prov G0 sop = NONE /\ op_prov G0 lop = NONE /\
  (!op. MEM op [sop;lop] ==>
    (?w. op = Lit w) \/ (?x. op = Var x /\ not_fresh_at sa x)) /\
  (!x. aop = Var x ==> not_fresh_at sc x) /\
  (!x j. cenv.ce_return_buf = SOME (PtrVar (Var x) j) ==> not_fresh_at sa x) /\
  (!x j. cenv.ce_return_pc = SOME (PtrVar (Var x) j) ==> not_fresh_at sa x) /\
  i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  32+n <= sz /\ sz < dimword (:256) /\
  type_memory_bytes cenv (lowered_value_type cenv result) <= sz /\
  32+32*word_size n <= sz /\ expr_type result = BaseT (BytesT (Dynamic n)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (do av <- bind (eval_expr cx a) (read_result cx);
        code_acc <- get_accounts;
        code_v <- lift_sum (evaluate_builtin cx code_acc ct (Acc Code) [expr_type a] [av]);
        slice_acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx slice_acc (expr_type result) (Slice n)
                      tys [code_v;IntV (&i);IntV (&k)]);
        return (Value v) od) (es,s,G0,tn0)
    (\res ee G tn t. ?tv. res = INL tv /\
      vv_post ctx fn cenv cx result es sa sd s ee tv
        (LocatedValue (expr_type result) (mk_ptr (Var out) LocMemory)) t /\
      t.vs_current_bb = sd.cs_current_bb /\ t.vs_inst_idx = LENGTH sd.cs_current_insts /\
      ghost_inv d cenv cx ee G tn t /\ ghost_kept cenv es sa G0 tn0 s G tn /\
      ptr_vv_ok cx (expr_type result) tv
        (LocatedValue (expr_type result) (mk_ptr (Var out) LocMemory)) ee G tn t /\
      ptr_buf_ok cenv result (Var out) G t)
    (\res ee gt rr. expr_exit res rr)
Proof
  strip_tac >> drule_all external_code_allocated_continue_given_tail >> simp[]
QED
