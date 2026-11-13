Theory internalReturnEndpointFrameMem
Ancestors
  internalReturnEndpointMetadataMem internalReturnCompoundEndpointMem
  intCallReturnDirectBranchesMem internalReturnBoundaryCommonMem ctorReturnFrame exprSimProps stmtSimProps
  exprOperandVar stmtSimReturn valueEncodingTyping fragExecMem
  loweringPosts exprLoweringProps exprSimDefs loweringStateRelDefs
  venomExecSemantics bodyMemoryDefs intCallReturnMem venomState vyperState

Theorem internal_return_endpoint_frames_mem:
  expr_post ctx func ce cx e es sa sm s0 ee v op t /\
  lower_value compile_expr ce ty e sa = (op,sm) /\
  ret_pc_ok ce sa s0 /\ return_buf_frame rb ce sa s0 /\
  s0.vs_alloca_next <= t.vs_alloca_next ==>
  ret_pc_ok ce sm t /\ return_buf_frame rb ce sm t
Proof
  strip_tac >> conj_tac
  >- (irule ret_pc_ok_frame >> qexistsl_tac [`ce`, `s0`, `sa`] >>
      fs[expr_post_def] >> metis_tac[cj 2 compile_expr_grows]) >>
  irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s0`, `sa`] >>
  fs[expr_post_def] >> metis_tac[cj 2 compile_expr_grows]
QED

Theorem internal_return_endpoint_post_frame_mem:
  same_frame ce ce' /\
  frag_exec_mem ctx sa sb P Q (intret_mem_q func ce' cx tv bw v (ee with scopes := [])) ==>
  frag_exec_mem ctx sa sb P Q (intret_mem_q func ce cx tv bw v (ee with scopes := []))
Proof
  strip_tac >> irule frag_exec_mem_conseq >>
  qexistsl_tac [`P`, `Q`, `intret_mem_q func ce' cx tv bw v (ee with scopes := [])`] >>
  simp[] >> rpt strip_tac >>
  fs[intret_mem_q_def] >> metis_tac[internal_return_post_frame]
QED

Theorem internal_return_equal_endpoint_mem:
  lower_value compile_expr ce ty e sa = (op,sm) /\
  compile_return_unlock ce sm = ((),su) /\ ce.ce_returns_count = 0 /\
  ~is_word_type ty /\
  compile_internal_return ce (SOME op) (Var rpc) 0 ty ty elems
    (SOME (Var bp)) su = ((),sb) /\
  ce.ce_imm_alloca = NONE /\
  ret_pc_ok ce sm t /\ ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ce.ce_return_buf = SOME (PtrVar (Var bp) bsz) /\
  return_buf_frame (SOME (bw,type_memory_size tv)) ce sm t /\
  local_ptrs_reserved ce sa /\
  expr_post ctx func ce cx e es sa sm s0 ee v op t /\
  post_value_type ce e = ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ expr_store_bound cx ty v op t /\
  (!sw. eval_operand op t = SOME sw ==> type_memory_size tv = 0 \/
    w2n sw + type_memory_size tv <= t.vs_alloca_next) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  w2n bw + type_memory_size tv + 64 < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)) ==>
  frag_exec_mem ctx sm sb (\s. s = t) (\s. F)
    (intret_mem_q func ce cx tv bw v (ee with scopes := []))
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at sm x` by metis_tac[compile_lower_value_var] >>
  `not_fresh_at sm rpc /\ not_fresh_at sm bp /\
   (?pc. eval_operand (Var rpc) t = SOME pc) /\
   eval_operand (Var bp) t = SOME bw /\
   w2n bw + type_memory_size tv <= t.vs_alloca_next` by
    gvs[ret_pc_ok_def, return_buf_frame_def, eval_operand_def] >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ce`, `cx`, `ee`, `ty`, `ty`,
    `tv`, `tv`, `v`, `op`, `Var rpc`, `elems`, `Var bp`, `sm`, `su`, `sb`, `bw`]
    compile_internal_return_compatible_epilogue_mem) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (irule o MATCH_MP frag_exec_mem_weaken) >> simp[] >>
  fs[expr_post_def, stmt_state_rel_def] >>
  conj_tac >- (irule state_rel_scopes_nil >> first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`t`, `ee`] >>
  simp[local_region_def, lookup_scopes_def]
QED
