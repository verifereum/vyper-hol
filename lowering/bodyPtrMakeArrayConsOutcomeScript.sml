(* Compiler-stage facts for the annotation-typed operational cons.
   The one-child source ends after read_result; no tail is evaluated here. *)
Theory bodyPtrMakeArrayConsOutcome
Ancestors
  bodyPtrMakeArrayConsSource bodyPtrMakeArrayConsLayout bodyPtrMakeArrayConsBind
  bodyPtrMakeArrayConsInvariant bodyPtrMakeArrayChildUnwrap bodyPtrMakeArrayZeroWidth
  bodyPtrMakeArrayPositiveFrame bodyPtrMakeArrayPositiveBytes bodyPtrMakeArrayPositiveWord
  exprLoweringProps exprOperandVar fragExec emitHelperProps compileEnv loweringPosts fragGasPathPtr

Theorem literal_cons_compiler_stages:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa ==>
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sb /\
  ci_mono sa sn /\ ci_mono sa su /\ ci_mono sa sb /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_has_code sn su func /\ fn_has_code su sb func /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
  local_ptrs_reserved ce su /\
  (!p. vv_operand vv = Var p ==> not_fresh_at sm p) /\
  not_fresh_at sn dst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa sm` by
    (mp_tac (cj 1 compile_expr_ci_mono) >>
     disch_then (qspecl_then [`ce`, `expr_type e`, `e`, `sa`] mp_tac) >> simp[]) >>
  `ci_mono sm sn` by
    (qspecl_then [`ADD`, `[Var root; Lit (n2w off)]`, `sm`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sn su` by
    (qspecl_then [`ce`, `vv`, `sn`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `ci_mono su sb` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono sa sn /\ ci_mono sa su /\ ci_mono sa sb /\
   cs_extends sm sb /\ cs_extends sn sb` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code sm sn func /\ fn_has_code sn sb func /\
   fn_has_code sn su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su` by
    metis_tac[compiler_ci_mono_reserved] >>
  `!p. vv_operand vv = Var p ==> not_fresh_at sm p` by
    metis_tac[cj 1 compiler_compile_var] >>
  simp[] >> drule emitted_insts_emit_op >> simp[not_fresh_at_def] >> metis_tac[]
QED

(* Snapshot instantiation for the operational theorem (still to be proved):
   ees = the literal expression's source input, sf = its target input, and
   fr = its compile_expr entry state before allocation.  These are the
   es,s0,sa quantified in expr_vv_sim_ptr_def, which supplies
   stmt_state_rel ctx func ce cx ees sf independently of the current loop
   endpoint.  literal_alloca_ghost_endpoint (AllocationFrame) consumes that
   same initial relation and returns ghost_kept relative to es,sa,s.
   Cons recursion must retain the initial relation as an explicit fixed
   hypothesis; it is not inferred backwards from literal_loop_frame.
   The marked child's source input may instead have gas_obs replaced;
   ConsSource supplies that input without changing the fixed snapshot. *)

(* Zero-width operational branch: the child has already run, but ADD and
   unwrap still run on that very endpoint before the prefix is extended. *)
Theorem literal_cons_zero_endpoint:
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
  val_wf tv v /\ type_memory_bytes ce (expr_type e) = 0 /\
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~s.vs_halted /\ lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv es' G tn s /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce esi si G0 tn0 s0 G tn ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es' sb H tm z (cells ++ [(tv,v,addr+off,0)]) off /\
    literal_prefix_ok (cells ++ [(tv,v,addr+off,0)]) tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_cons_compiler_stages >> strip_tac >>
  `stmt_state_rel ctx func ce cx esi s0` by metis_tac[literal_loop_frame_runtime] >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_var <= sb.cs_next_var /\
   si.cs_next_id <= sb.cs_next_id` by gvs[ci_mono_def] >>
  drule_all literal_zero_child_materialize >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `val_footprint tv v = 0` by
    (drule_all literal_annotation_slot >> strip_tac >>
     `val_footprint tv v <= 0` by metis_tac[] >> decide_tac) >>
  `?a mem. val_in_memory tv v a mem` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  qexistsl [`z`, `H`, `tm`] >> simp[] >>
  drule_all literal_zero_frame_extend >> simp[]
QED

Theorem literal_cons_zero_outcome_ptr:
  expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  expr_body_pre ce cx env e es /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = 0 /\ lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee H tm z. ?v. res = INL v /\ value_has_type tv v /\
      literal_loop_frame ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ [(tv,v,addr+off,0)]) off /\
      literal_prefix_ok (cells ++ [(tv,v,addr+off,0)]) tm z)
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_cons_compiler_stages >> strip_tac >>
  drule literal_loop_frame_runtime >> strip_tac >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyPtrDefsTheory.expr_vv_sim_ptr_def] >>
  disch_then drule_all >> strip_tac >>
  irule literal_result_bind_outcome_ptr >>
  qexists `\raw ee H tm z.
    vv_post ctx func ce cx e es si sm s0 ee raw vv z /\
    z.vs_current_bb = sm.cs_current_bb /\ z.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d ce cx ee H tm z /\ ptr_vv_ok cx (expr_type e) raw vv ee H tm z /\
    (!t arg. vv = StackValue t arg /\ ~is_word_type (expr_type e) ==>
      ptr_buf_ok ce e arg H z) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand H z) /\
    ghost_kept ce es si G0 tn0 s0 H tm` >>
  conj_tac >- suspend "normal" >> suspend "child"
QED

Resume literal_cons_zero_outcome_ptr[child]:
  drule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >> disch_then irule >>
  simp[] >> rpt strip_tac >>
  Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def] >>
  metis_tac[]
QED

Resume literal_cons_zero_outcome_ptr[normal]:
  rpt gen_tac >> strip_tac >> fs[] >>
  `ee with gas_obs := [] = ee` by
    (simp[vyperStateTheory.evaluation_state_component_equality]) >>
  drule literal_marked_child_materialises >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `eval_expr cx e marked = _` >>
  `literal_loop_frame ctx func ce cx d root aid addr capacity
     ees fr sf Gf tnf marked si G0 tn0 s0 cells off` by
    (gvs[Abbr `marked`, literal_loop_frame_def, bodyPtrDefsTheory.ghost_inv_def,
        bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]) >>
  `ghost_kept ce marked si G0 tn0 s0 G tn` by
    (gvs[Abbr `marked`, bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]) >>
  `expr_body_pre ce cx env e marked` by simp[Abbr `marked`] >>
  `lookup_var root t = SOME (n2w addr)` by
    (gvs[literal_loop_frame_def, vv_post_def] >> metis_tac[]) >>
  `op_taint tn (Var root) = {}` by
    (gvs[literal_loop_frame_def, bodyPtrDefsTheory.ghost_kept_def,
         bodyPtrDefsTheory.ptr_covers_def, ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryComposePtrTheory.gas_marked_exec_ptr_def] >>
     metis_tac[gas_path_ptr_erase, fragGasPathTheory.gas_path_normal]) >>
  `!ty arg. vv = StackValue ty arg ==> ptr_buf_ok ce e arg G t` by metis_tac[] >>
  drule_at (Pat `eval_expr _ _ _ = _`) literal_cons_zero_endpoint >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  qexists `[]` >> disj1_tac >>
  qexistsl [`INL v'`, `ee`, `H`, `tm`, `OK z`] >> simp[]

QED
Finalise literal_cons_zero_outcome_ptr

Theorem literal_cons_flat_endpoint:
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
  val_wf tv v /\ k = type_memory_bytes ce (expr_type e) /\ 0 < k /\
  off+k <= capacity /\ lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
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
  `stmt_state_rel ctx func ce cx esi s0` by metis_tac[literal_loop_frame_runtime] >>
  `off < capacity /\ op_taint tn (Var root) = {}` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> decide_tac) >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_var <= su.cs_next_var /\
   si.cs_next_id <= su.cs_next_id /\ su.cs_next_var <= sb.cs_next_var /\
   su.cs_next_id <= sb.cs_next_id` by gvs[ci_mono_def] >>
  `k+off <= capacity` by decide_tac >>
  drule literal_child_add_unwrap >> simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all literal_loop_frame_materialized >> strip_tac >>
  drule_all literal_annotation_slot >> strip_tac >>
  `k < dimword(:256)` by (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  `w2n (n2w addr + n2w off : bytes32) = addr+off` by
    (simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `?src a. op = Var src /\ lookup_var src z = SOME a /\ ptr_covers H tm src z k` by
    (gvs[bodyPtrDefsTheory.ptr_buf_ok_def, expr_post_def, expr_val_rel_def,
         bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_covers_def,
         venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  gvs[] >>
  `val_footprint tv v <= type_memory_size tv /\ type_memory_size tv+off <= capacity` by
    (conj_tac >- metis_tac[] >> decide_tac) >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) literal_flat_loop_store >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`z'`, `H`, `tm'`] >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD]
QED

