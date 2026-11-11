(* Bytestring internal returns at a successful expression endpoint. *)
Theory internalReturnBytestringMem
Ancestors
  intCallReturnDirectBranchesMem returnValueTyped vyperTypeArgFits
  valueEncodingTyping exprOperandVar exprSimProps stmtSimReturn
  loweringPosts exprLoweringProps fragExecMem stmtLowering valueCopy
  typedMemoryCopy loweringStateRelDefs stmtSimReturnWiden valueCopyBytes
  venomExecSemantics venomState vyperState

Theorem internal_return_bytestring_suffix_mem:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v, ee') /\
  type_widens_to (get_tenv cx) (expr_type e) ty /\
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  lower_value compile_expr ce ty e sa = (op,sm) /\
  local_ptrs_reserved ce sa /\
  compile_internal_return ce (SOME op) (Var rpc) 0 ty
    (lowered_value_type ce e) elems (SOME (Var bp)) sm = ((),sb) /\
  ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ce.ce_return_buf = SOME (PtrVar (Var bp) bsz) /\
  ret_pc_ok ce sm t /\ return_buf_frame (SOME (bw,type_memory_size tv)) ce sm t /\
  expr_post ctx func ce cx e es sa sm s0 ee v op t /\
  expr_store_bound cx (expr_type e) v op t /\
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
  drule_all return_value_typed >> strip_tac >>
  `value_has_type tv v` by
    (drule_all type_widens_to_value_has_type >> simp[]) >>
  `is_bytestring_type (expr_type e)` by metis_tac[typed_copy_bytestring_source] >>
  `compile_internal_return ce (SOME op) (Var rpc) 0 ty ty elems
     (SOME (Var bp)) sm = ((),sb)` by
    (qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_internal_return_def, compile_store_memory_bytestring_src]) >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    metis_tac[compile_lower_value_var] >>
  `not_fresh_at sm rpc /\ not_fresh_at sm bp /\
   (?pc. eval_operand (Var rpc) t = SOME pc) /\
   eval_operand (Var bp) t = SOME bw /\
   w2n bw + type_memory_size tv <= t.vs_alloca_next` by
    gvs[ret_pc_ok_def, return_buf_frame_def, eval_operand_def] >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  drule_at (Pat `compile_internal_return _ _ _ _ _ _ _ _ _ = _`)
    compile_internal_return_equal_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `ee`, `tv`, `v`, `bw`] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
  disch_then (irule o MATCH_MP frag_exec_mem_weaken) >> simp[] >>
  rpt strip_tac >>
  `expr_val_rel cx ty v op t` by
    (irule return_bytestring_expr_rel >> fs[expr_post_def] >>
     qexistsl_tac [`tv'`, `expr_type e`] >> simp[]) >>
  `expr_store_bound cx ty v op t` by
    (irule return_bytestring_store_bound >> metis_tac[]) >>
  simp[] >>
  fs[expr_post_def, stmt_state_rel_def] >>
  conj_tac >- (irule state_rel_scopes_nil >> first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`t`, `ee`] >>
  simp[local_region_def, lookup_scopes_def]
QED
