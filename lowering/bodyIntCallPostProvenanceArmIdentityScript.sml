(* Pointer-retaining conditional arms keep the selected F-mode endpoint. *)
Theory bodyIntCallPostProvenanceArmIdentity
Ancestors
  bodyIntCallMemoryView bodyIntCallProducerInterface exprSimUnwrapProps exprSimUnwrap
  exprLowering fragGasPath gasSummary fragGasMode exprSimIfExpWidenedAdapter

Theorem ifexp_arm_identity_compile:
  (is_word_type ty \/ same_memory_layout ce at ty) /\
  ((?a. vv = StackValue a op) \/
   (?a p. vv = LocatedValue a p /\ p.ptr_location = LocMemory /\
          ~is_word_type a /\ op = p.ptr_operand)) ==>
  compile_ifexp_arm ce ty at vv sm = (op,sm)
Proof
  strip_tac >> gvs[compile_ifexp_arm_def, unwrap_value_def,
                   compileEnvTheory.comp_return_def]
QED

Theorem ifexp_arm_identity_post:
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  ((?a. vv = StackValue a op) \/
   (?a p. vv = LocatedValue a p /\ p.ptr_location = LocMemory /\
          ~is_word_type a /\ op = p.ptr_operand)) ==>
  expr_post ctx func ce cx e es sa sm s0 ee v op s
Proof
  strip_tac >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) vv s` by
    metis_tac[vv_post_read_result] >>
  gvs[] >> metis_tac[expr_post_of_vv_post_stack, expr_post_of_vv_post_memory]
QED

(* Both reads are explicit source compatibility: ownership is transported
   only for the value actually returned by conditional_result. *)
Theorem ifexp_arm_identity_continuation:
  (is_word_type ty \/ same_memory_layout ce at ty) /\
  ((?a. vv = StackValue a op) \/
   (?a p. vv = LocatedValue a p /\ p.ptr_location = LocMemory /\
          ~is_word_type a /\ op = p.ptr_operand)) /\
  compile_ifexp_arm ce ty at vv sm = (out,sb) /\
  ty = expr_type e /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  intcall_vv_provenance ce cx ty sa sm ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  conditional_result cx raw ee = (INL tv,ee) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  sb = sm /\ out = op /\
  gas_marked_exec F (ctx,func) (conditional_result cx raw)
    (ee,s) [] (INL tv) ee (OK s) /\
  expr_post ctx func ce cx e es sa sb s0 ee v out s /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  intcall_vv_provenance ce cx ty sa sb ee tv
    (if is_word_type ty then StackValue ty out
     else LocatedValue ty (mk_ptr out LocMemory)) s
Proof
  strip_tac >> (qpat_x_assum `ty = expr_type e` SUBST_ALL_TAC >>
  `compile_ifexp_arm ce (expr_type e) at vv sm = (op,sm)` by
    (irule ifexp_arm_identity_compile >> simp[]) >>
  `expr_post ctx func ce cx e es sa sm s0 ee v op s` by
    (irule ifexp_arm_identity_post >> metis_tac[]) >>
  gvs[] >> simp[] >> conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def] >> conj_tac
      >- (drule conditional_result_gas_obs >> simp[]) >>
      irule (cj 1 gas_path_rules) >> simp[]) >>
  Cases_on `is_word_type (expr_type e)` >> gvs[intcall_vv_provenance_word] >>
  irule intcall_vv_provenance_memory_view >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> gvs[])
QED
