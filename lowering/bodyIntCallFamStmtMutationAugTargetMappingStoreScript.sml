(* Second scratch word, after the allocating prefix has established ownership. *)
Theory bodyIntCallFamStmtMutationAugTargetMappingStore
Ancestors
  bodyIntCallFamStmtMutationAugTargetMappingOps
  bodyIntCallFamStmtMutationAugTargetMapping bodyIntCallJointAggCore
  bodyIntCallJointContract exprSimMapKey emitHelperProps loweringShapeRules
  venomState compileEnv exprLoweringProps exprSimCopy stmtSimAugAssignPlaceMemory
  fragGasMode loweringStateRelDefs

Theorem intcall_scratch_second_word:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s0 /\
  intcall_expr_cont fp ce env es sa s0 es si s /\
  emit_op ADD [Var p; Lit 32w] si = (ptr_op,sm) /\
  emit_void MSTORE [ptr_op; key] sm = ((),sb) /\
  fn_has_code si sm fp.jc_func /\ fn_has_code sm sb fp.jc_func /\
  lookup_var p s = SOME w /\ not_fresh_at si p /\
  (!v. key = Var v ==> not_fresh_at si v) /\ eval_operand key s = SOME wd /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,64) /\
  sa.cs_next_id <= inst.inst_id /\ MEM inst (fn_insts fp.jc_func) /\
  inst.inst_opcode = ALLOCA /\ fp.jc_lo <= w2n w /\
  w2n w + 64 < dimword (:256) /\ sa.cs_next_var <= si.cs_next_var /\
  sa.cs_next_id <= si.cs_next_id /\
  (!n a z. local_region ce es.scopes s n a z ==>
     regions_disjoint (w2n w) 64 a z) /\
  (!n a z. local_region ce es.scopes s0 n a z ==>
     regions_disjoint (w2n w) 64 a z) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_expr_cont fp ce env es sa s0 es sb u /\
      eval_operand (Var p) u = SOME w /\
      mem_word_at (w2n w + 32) u.vs_memory = wd /\
      (!a z. regions_disjoint a z (w2n w+32) 32 ==>
        mem_bytes_at a z u.vs_memory = mem_bytes_at a z s.vs_memory)
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es si s /\ ~s.vs_halted /\
   s.vs_current_bb = si.cs_current_bb /\
   s.vs_inst_idx = LENGTH si.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule_at (Pat `emit_op ADD _ _ = _`) intcall_mapping_add_run >>
  simp[eval_operand_def] >> disch_then drule_all >> strip_tac >>
  rename1 `eval_operand ptr_op t = SOME (w+32w)` >>
  `intcall_expr_cont fp ce env es sa s0 es sm
      (t with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `w2n (w+32w) = w2n w+32` by simp[wordsTheory.word_add_def] >>
  drule emit_op_facts >> strip_tac >> gvs[] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory` by
    gvs[venom_state_component_equality] >>
  `local_ptrs_reserved ce si` by fs[intcall_expr_res_def] >>
  `(!n a z. local_region ce es.scopes
       (t with vs_inst_idx := LENGTH sm.cs_current_insts) n a z ==>
       regions_disjoint (w2n w) 64 a z)` by
    (simp[local_region_def, lookup_var_def] >>
     metis_tac[copy_buffer_local_region_frame, local_region_def, lookup_var_def]) >>
  `eval_operand key (t with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME wd` by
    (irule aug_place_saved_operand >> goal_assum (drule_at Any) >>
     fs[intcall_expr_cont_def] >> metis_tac[]) >>
  `FLOOKUP (t with vs_inst_idx := LENGTH si.cs_current_insts + 1).vs_allocas
     inst.inst_id = SOME (w2n w,64)` by simp[] >>
  drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ sm _`) intcall_scratch_mstore >>
  disch_then (drule_at (Pat `emit_void _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  simp[eval_operand_def, lookup_var_def] >>
  disch_then (qspecl_then [`wd`, `w+32w`] mp_tac) >>
  (impl_tac >- (gvs[eval_operand_def, lookup_var_def] >> metis_tac[])) >> strip_tac >>
  rename1 `mem_word_at (w2n (w+32w)) landed.vs_memory = wd` >>
  qexists `landed` >> simp[] >> conj_tac
  >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  `eval_operand (Var p) landed = SOME w` by
    (qpat_x_assum `!q. eval_operand q landed = _` (qspec_then `Var p` mp_tac) >>
     gvs[eval_operand_def]) >>
  gvs[eval_operand_def, lookup_var_def]
QED
