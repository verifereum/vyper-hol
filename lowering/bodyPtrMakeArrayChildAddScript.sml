(* The actual destination instruction, at the child evaluation endpoint. *)
Theory bodyPtrMakeArrayChildAdd
Ancestors
  bodyPtrMakeArrayEmission bodyPtrMakeArrayAdd bodyPtrMakeArrayAddFrame bodyPtrMakeArrayAddCoverage
  bodyPtrDefs loweringPosts venomState venomExecSemantics ptrDiscipline compileEnv context

Theorem literal_child_add_endpoint:
  !base cap.
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var out,sn) /\
  fn_has_code sm sn func /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (base,cap) /\
  base + cap <= dimword(:256) /\ off < capacity /\ off+n <= capacity /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv es' G tn s /\
  (!t op. vv = StackValue t op /\ ~is_word_type (expr_type e) ==>
    ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\
  (!p. vv_operand vv = Var p ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce esi si G0 tn0 s0 G tn ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sn.cs_current_bb /\
    z.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post ctx func ce cx e esi si sn s0 es' raw vv z /\
    ptr_vv_ok cx (expr_type e) raw vv es' H tm z /\
    (!t op. vv = StackValue t op /\ ~is_word_type (expr_type e) ==>
      ptr_buf_ok ce e op H z) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand H z) /\
    z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
    tm.t_mem = tn.t_mem /\
    ghost_inv d ce cx es' H tm z /\
    ghost_kept ce esi si G0 tn0 s0 H tm /\
    ptr_covers H tm out z n
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all emit_op_fetch_boundary >> strip_tac >> fs[] >>
  qexistsl [`(update_var out (a+n2w off) s) with
               vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst sm.cs_next_id ADD
       [Var root; Lit (n2w off)] [out]) (update_var out (a+n2w off) s)`,
    `step_taint (mk_inst sm.cs_next_id ADD
       [Var root; Lit (n2w off)] [out]) s (update_var out (a+n2w off) s) tn`] >>
  conj_tac
  >- (irule emit_clean_binop_ptr_path >>
      simp[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[] >>
  conj_tac >- (irule emit_binop_vv_post >> metis_tac[]) >>
  conj_tac >- (irule binop_source_ptr_vv_ok >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule binop_source_ptr_buf_ok >>
      simp[] >> gvs[vv_operand_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule binop_source_ptr_buf_ok >>
      simp[] >> gvs[vv_operand_def] >> metis_tac[]) >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  conj_tac >- (irule emit_binop_ghost_inv >> metis_tac[]) >>
  conj_tac >- (irule emit_binop_ghost_kept >> metis_tac[]) >>
  drule add_destination_coverage >>
  simp[arithmeticTheory.ADD_COMM] >>
  disch_then (qspecl_then [`off`, `n`, `PG`, `sm.cs_next_id`, `out`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED
