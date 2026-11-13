(* Public pointer-safe custom-error argument store loop. *)
Theory stmtSimCustomErrorPtrStore
Ancestors
  stmtSimCustomErrorPtrStoreLoop stmtSimCustomErrorPtrStoreHead

Theorem custom_error_store_args_sim_ptr:
  !args ce cx env off sa sb es tvs func inst x b asz s0 ctx tys tops d PG G tn.
  tys = MAP expr_type args /\
  compile_custom_error_store_args ce args tys (Var x) off sa = ((),sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  body_inv tops ctx ce cx /\ ~ce.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
  expr_sim_inv ce cx env es /\
  (!e ee. MEM e args /\ expr_sim_inv ce cx env ee ==> expr_body_pre ce cx env e ee) /\
  body_exprs_ptr_ok cx args /\ EVERY (supported_pure_expr tops) args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!ee. expr_sim_inv ce cx env ee ==> not_local_ptr ce ee.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\ ptr_covers G tn x s0 asz /\
  off + type_memory_size_list tvs <= asz /\ b+asz < dimword (:256) /\
  stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G tn s0 /\
  (!n lo sz i. local_region ce es.scopes s0 n lo sz /\ lo <= i /\ i < lo+sz ==>
    ~(b <= i /\ i < b+asz)) /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z. ce.ce_imm_alloca = SOME (Var z) ==> not_fresh_at sa z) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) tops (ctx,func) PG (eval_exprs cx args) (es,s0,G,tn)
    (\res ee Gf tf r. ?vs.
      res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~r.vs_halted /\
      expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee r /\
      ghost_inv d ce cx ee Gf tf r /\
      ptr_covers Gf tf x r asz /\ lookup_var x r = SOME (n2w b) /\
      FLOOKUP r.vs_allocas inst.inst_id = SOME (b,asz) /\
      (!mem. mem_agree_outside tf.t_mem r.vs_memory mem ==>
        tuple_in_memory vs tvs (b+off) mem) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!z. not_fresh_at sa z ==> FLOOKUP Gf z = FLOOKUP G z /\
        op_taint tf (Var z) = op_taint tn (Var z)) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP r.vs_allocas aid = SOME entry) /\
      (!i. b <= i /\ i < b+asz /\ ~(b+off <= i /\ i < b+off+type_memory_size_list tvs) ==>
        mem_bytes_at i 1 r.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
        (i IN tf.t_mem ==> i IN tn.t_mem)))
    (\res ee gt exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  match_mp_tac custom_error_store_args_sim_ptr_conditional >>
  rpt gen_tac >> strip_tac >>
  drule_all custom_error_store_head_path_ptr >> simp[]
QED
