(* Compiler-stage facts for the annotation-typed operational cons.
   The one-child source ends after read_result; no tail is evaluated here. *)
Theory bodyPtrMakeArrayConsOutcome
Ancestors
  bodyPtrMakeArrayConsSource bodyPtrMakeArrayConsLayout bodyPtrMakeArrayConsBind
  bodyPtrMakeArrayConsInvariant bodyPtrMakeArrayChildUnwrap bodyPtrMakeArrayZeroWidth
  bodyPtrMakeArrayPositiveFrame bodyPtrMakeArrayPositiveBytes bodyPtrMakeArrayPositiveWord
  exprLoweringProps exprOperandVar fragExec emitHelperProps compileEnv

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
