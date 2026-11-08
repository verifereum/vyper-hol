(* Uniform bytes child: runtime copying advances by the declared field slot. *)
Theory bodyPtrStructLitUniformBytesEndpoint
Ancestors bodyPtrStructLitUniformChildUnwrap bodyPtrStructLitBytesCoverage
  bodyPtrMakeArrayConsOutcome bodyPtrMakeArrayConsLayout
  bodyPtrMakeArrayConsInvariant bodyPtrMakeArrayPositiveBytes
  exprLoweringProps exprOperandVar freshWrites fragExec emitHelperProps
  compileEnv loweringPosts fragGasPathPtr

Theorem structlit_uniform_cons_bytes_endpoint:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf esi si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ value_has_type tv v /\ k = type_memory_bytes ce (expr_type e) /\
  off+k <= capacity /\ post_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ is_bytestring_type (expr_type e) /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~s.vs_halted /\ lookup_var root s = SOME (n2w addr) /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (addr,capacity) /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv es' G tn s /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce esi si G0 tn0 s0 G tn ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es' sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
    literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_cons_compiler_stages >> strip_tac >>
  drule literal_loop_frame_allocation >> strip_tac >>
  drule_all literal_annotation_slot >> strip_tac >>
  drule_all literal_bytes_runtime_slot >> strip_tac >>
  qmatch_asmsub_abbrev_tac `val_store_size tv v = n` >>
  `0 < k /\ n <= k /\ n < dimword(:256)` by
    (gvs[Abbr `n`, wordsTheory.dimword_def] >> decide_tac) >>
  `stmt_state_rel ctx func ce cx esi s0` by metis_tac[literal_loop_frame_runtime] >>
  `off < capacity /\ op_taint tn (Var root) = {}` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> decide_tac) >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_var <= su.cs_next_var /\
   si.cs_next_id <= su.cs_next_id /\ su.cs_next_var <= sb.cs_next_var /\
   su.cs_next_id <= sb.cs_next_id` by gvs[ci_mono_def] >>
  `n+off <= capacity` by decide_tac >>
  drule structlit_uniform_child_add_unwrap >> simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all literal_loop_frame_materialized >> strip_tac >>
  `w2n (n2w addr + n2w off : bytes32) = addr+off` by
    (simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `?a. eval_operand op z = SOME a /\ op_taint tm op = {}` by
    (gvs[bodyPtrDefsTheory.ptr_val_ok_def, expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `?src. op = Var src /\ lookup_var src z = SOME a /\ ptr_covers H tm src z n` by
    (drule_all structlit_bytes_source_coverage >> simp[]) >>
  `!p. vv_operand vv = Var p ==> not_fresh_at sn p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  `not_fresh_at su src` by
    (drule compiler_unwrap_value_var >>
     disch_then (qspec_then `src` mp_tac) >> simp[] >>
     Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  `not_fresh_at su dst` by metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  `(!p. not_fresh_at fr p ==> not_fresh_at su p) /\
   (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at su p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at su p)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
      arithmeticTheory.LESS_EQ_TRANS]) >>
  `?z' H' tm'.
    gas_path_ptr D 0 ctx func PG H tm z 0 H' tm' (OK z') /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es' sb H' tm' z' (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
    literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm' z'` by
    (irule literal_bytes_loop_store >> simp[] >>
     qexistsl [`a`, `n2w addr + n2w off`, `dst`, `su`, `src`,
       `lowered_value_type ce e`, `expr_type e`] >> gvs[Abbr `n`]) >>
  qexistsl [`z'`, `H'`, `tm'`] >> gvs[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD]
QED
