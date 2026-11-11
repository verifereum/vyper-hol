(* Counted word stores to existing locals, with internal-call resources. *)
Theory bodyIntCallFamStmtMutationAugLocalStore
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtMutationResource bodyIntCallAssembly stmtSimAssignPath
  stmtSimAssignStore stmtSimDeclPath stmtSimDeclStore emitHelperProps
  valueEncodingProps compileEnv exprLoweringProps venomMemDefs venomState
  vyperLookup exprSimHypsDefs

Theorem intcall_local_word_mstore_resources:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ store_lays_out etv entry.type v /\
  ee = es with scopes :=
    pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest /\
  expr_sim_inv ce fp.jc_cx env ee /\
  local_ptrs_reserved ce sb /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) ==>
  intcall_joint_res fp ce env ee sb
    (mstore (w2n w) (typed_val_to_w256 etv v) s with vs_inst_idx := idx)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   expr_sim_inv ce fp.jc_cx env es /\ local_ptrs_reserved ce sa` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `32 <= sz` by
    (fs[stmt_state_rel_def,state_rel_def,local_ptrs_rel_def,store_lays_out_def] >>
     res_tac >> gvs[]) >>
  `local_region ce es.scopes s id (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `!a k. fp.jc_prot a k ==> regions_disjoint a k (w2n w) sz` by
    metis_tac[intcall_local_region_protected] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee
      (mstore (w2n w) (typed_val_to_w256 etv v) s)` by
    (gvs[] >> irule stmt_state_rel_write_local_store >> metis_tac[]) >>
  `!a k. fp.jc_prot a k ==>
     mem_bytes_at a k (mstore (w2n w) (typed_val_to_w256 etv v) s).vs_memory =
     mem_bytes_at a k s.vs_memory` by
    (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
     first_x_assum drule >> simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `!n b k. local_region ce ee.scopes s n b k ==>
            local_region ce es.scopes s n b k` by
    metis_tac[expr_inv_local_regions_transport] >>
  irule intcall_joint_res_mutation >> simp[stmt_state_rel_inst_idx] >>
  rpt conj_tac
  >- fs[intcall_joint_res_def,intcall_expr_res_def]
  >- (fs[intcall_joint_res_def,intcall_expr_res_def,mstore_def,
        intCallFrameTheory.allocas_above_def] >> metis_tac[])
  >- fs[intcall_joint_res_def]
  >- fs[intcall_joint_res_def,intcall_expr_res_def]
  >> qexistsl [`env`,`es`,`s`,`sa`] >>
  simp[mstore_def,lookup_var_def,eval_operand_def,local_region_def] >>
  metis_tac[]
QED

Theorem intcall_local_word_store_path:
  emit_void MSTORE [Var p; op] sa = ((),sb) /\
  fn_has_code sa sb fp.jc_func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ store_lays_out etv entry.type v /\
  eval_operand op s = SOME (typed_val_to_w256 etv v) /\
  ee = es with scopes :=
    pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest /\
  expr_sim_inv ce fp.jc_cx env ee /\
  local_ptrs_reserved ce sb /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_joint_res fp ce env ee sb u /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. lookup_var x u = lookup_var x s) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0
    (OK (mstore (w2n w) (typed_val_to_w256 etv v) s with
          vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emit_mstore_marked_path >> metis_tac[]) >>
  `intcall_joint_res fp ce env ee sb
    (mstore (w2n w) (typed_val_to_w256 etv v) s with
          vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule intcall_local_word_mstore_resources >> metis_tac[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emitHelperTheory.emit_void_def,compileEnvTheory.comp_bind_def,
        compileEnvTheory.fresh_id_def,compileEnvTheory.comp_ignore_bind_def,
        compileEnvTheory.comp_return_def,compileEnvTheory.emit_def] >>
  qexists `mstore (w2n w) (typed_val_to_w256 etv v) s with
          vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[mstore_def,lookup_var_def]
QED
