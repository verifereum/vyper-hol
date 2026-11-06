Theory bodyPtrIfExpAllocResources
Ancestors
  bodyPtrIfExpAllocSource bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocStep
  bodyPtrIfExpAllocSeparation
  bodyPtrDefs exprSimVVFrame loweringPosts compileEnv exprLoweringProps
  ptrDiscipline venomState venomInst loweringHalt finite_map exprLowering context

Theorem compile_alloc_buffer_vv_source_frame:
  !D d ctx fn PG G0 tn0 G tn cenv cx e es sa sb s0 es' tv vv s n buf sc.
    vv_post ctx fn cenv cx e es sa sb s0 es' tv vv s /\
    ghost_inv d cenv cx es' G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
    n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    fn_inst_ids_distinct fn /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
    ptr_vv_ok cx (expr_type e) tv vv es' G tn s /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
        ptr_buf_ok cenv e op G s) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G s) ==>
    ?out G1 tn1 t.
      buf.buf_operand = Var out /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
      ptr_covers G1 tn1 out t n /\
      ghost_inv d cenv cx es' G1 tn1 t /\
      ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
      vv_post ctx fn cenv cx e es sa sc s0 es' tv vv t /\
      ptr_vv_ok cx (expr_type e) tv vv es' G1 tn1 t /\
      (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
          ptr_buf_ok cenv e op G1 t) /\
      (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G1 t) /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
      t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      lookup_var out t = SOME (n2w (buffer_allocation_base s sb.cs_next_id)) /\
      buffer_allocation_base s sb.cs_next_id + n < dimword (:256)
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx fn cenv cx es' s` by gvs[vv_post_def] >>
  drule_all compile_alloc_buffer_counted >>
  disch_then (qspecl_then [`D`, `PG`, `G`, `tn`] strip_assume_tac) >>
  `!x. vv_operand vv = Var x ==> x <> out` by
    (drule compile_alloc_buffer_parts >> strip_tac >> metis_tac[]) >>
  drule_all compile_alloc_buffer_vv_post >> strip_tac >>
  `vv_at cenv cx (expr_type e) sa sb es' tv vv s` by gvs[vv_post_def] >>
  drule_all alloca_step_source_vv >> disch_then (qspec_then `PG` assume_tac) >>
  drule_all compile_alloc_buffer_ghost_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule_all compile_alloc_buffer_kept_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  `lookup_var out u = SOME (n2w (buffer_allocation_base s sb.cs_next_id))` by
    (drule_all ifexp_alloca_step_base >> simp[]) >>
  `buffer_allocation_base s sb.cs_next_id + n < dimword (:256)` by
    (drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[] >>
     drule_all ifexp_alloca_base_bound >> simp[]) >>
  qexistsl_tac [`out`, `G1`, `tn1`, `t`] >> simp[lookup_var_def] >>
  conj_tac >- suspend "ghost_position" >>
  conj_tac >- suspend "stack_buffer" >>
  conj_tac >- suspend "located_buffer" >>
  suspend "control"
QED

Resume compile_alloc_buffer_vv_source_frame[ghost_position]:
  qpat_x_assum `ghost_inv _ _ _ _ _ _ u` mp_tac >>
  rpt (pop_assum kall_tac) >> Cases_on `d`
  >- (simp[ghost_inv_def, ptr_covers_def, stor_taint_ok_def, lookup_var_def,
           return_buf_ptr_def] >> strip_tac >> simp[]) >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  simp[ghost_inv_def, return_buf_ptr_def, ptr_covers_def,
       stor_taint_ok_def, lookup_var_def] >> strip_tac >> simp[]
QED

Resume compile_alloc_buffer_vv_source_frame[stack_buffer]:
  rpt strip_tac >> irule alloca_step_source_buffer >>
  gvs[vv_operand_def] >> qexists_tac `s` >> simp[]
QED
Resume compile_alloc_buffer_vv_source_frame[located_buffer]:
  rpt strip_tac >> irule alloca_step_source_buffer >>
  gvs[vv_operand_def] >> qexists_tac `s` >> simp[]
QED
Resume compile_alloc_buffer_vv_source_frame[control]:
  drule_all alloca_step_contracts >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >> gvs[lookup_var_def]
QED
Finalise compile_alloc_buffer_vv_source_frame
