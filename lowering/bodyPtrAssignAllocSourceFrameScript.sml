Theory bodyPtrAssignAllocSourceFrame
Ancestors bodyPtrIfExpAllocResources bodyPtrIfExpStorageStart
  bodyPtrIfExpAllocStep bodyPtrIfExpAllocSeparation
  bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocSource exprSimVVFrame
  exprSimIfExpWidenedAdapter exprSimProps loweringPosts compileEnv
  loweringStateRelDefs bodyPtrDefs ptrDiscipline venomState venomInst
  loweringHalt finite_map exprLowering context exprLoweringProps allocationPtr

Theorem assign_vv_post_alloc_map_frame[local]:
  vv_post ctx fn cenv cx e es sa sb s0 ee raw vv s /\
  stmt_state_rel ctx fn cenv cx ee q /\ q.vs_memory = s.vs_memory /\
  contract_storage q = contract_storage s /\
  contract_transient q = contract_transient s /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  (!n b sz. local_region cenv ee.scopes q n b sz <=>
            local_region cenv ee.scopes s n b sz) /\
  sb.cs_next_id <= sc.cs_next_id ==>
  vv_post ctx fn cenv cx e es sa sc s0 ee raw vv q
Proof
  strip_tac >>
  `vv_holds cenv cx (post_value_type cenv e) raw vv ee q` by
    (irule vv_holds_vars_frame >> simp[] >> qexists `s` >> gvs[vv_post_def]) >>
  `vv_at cenv cx (post_value_type cenv e) sa sc ee raw vv q` by
    (irule vv_at_alloc_map_frame >> simp[] >>
     qexistsl [`s`, `sb`] >> gvs[vv_post_def]) >>
  `(post_value_type cenv e <> expr_type e ==>
    vv_own cenv cx (post_value_type cenv e) sa sc ee raw vv q)` by
    (strip_tac >> irule vv_own_alloc_mono_frame >> simp[] >>
     qexistsl [`s`, `sb`] >> gvs[vv_post_def]) >>
  `locals_kept cenv es ee s0 q` by
    (irule locals_kept_mem_tail >> qexists `s` >> gvs[vv_post_def]) >>
  `~expr_has_effect e ==> pure_frame cenv fn es sa s0 q` by
    (strip_tac >> irule pure_frame_mem_tail >> qexists `s` >> gvs[vv_post_def]) >>
  gvs[vv_post_def] >> conj_tac
  >- (Cases_on `vv` >> gvs[vv_storage_live_def, vv_operand_def]) >>
  rpt strip_tac >> metis_tac[]
QED

Theorem assign_alloc_buffer_vv_post[local]:
  vv_post ctx fn cenv cx e es sa sb s0 ee raw vv s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
  buf.buf_operand = Var out /\ n < dimword (:256) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  vv_post ctx fn cenv cx e es sa sc s0 ee raw vv u
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx ee s` by gvs[vv_post_def] >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    (irule alloca_step_operand_preserved >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!name b sz. local_region cenv ee.scopes u name b sz <=>
                local_region cenv ee.scopes s name b sz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >> conj_tac
         >- (qexists `fn` >> gvs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl [`sa`, `ee.scopes`, `u`] >> simp[]) >>
     strip_tac >> irule local_region_frame_fwd >>
     qexistsl [`s`, `sa`, `ee.scopes`] >> simp[]) >>
  drule_all alloca_step_contracts >> strip_tac >>
  irule assign_vv_post_alloc_map_frame >> simp[] >>
  qexistsl [`s`, `sb`] >> simp[]
QED

Theorem compile_alloc_buffer_vv_source_fresh_frame:
  vv_post ctx fn cenv cx e es sa sb s0 ee tv vv s /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\ fn_inst_ids_distinct fn /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\ fresh_vars_wrt sb s ==>
  ?out G1 tn1 t.
    buf.buf_operand = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
    ptr_covers G1 tn1 out t n /\ ghost_inv d cenv cx ee G1 tn1 t /\
    ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
    vv_post ctx fn cenv cx e es sa sc s0 ee tv vv t /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee G1 tn1 t /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op G1 t) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G1 t) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    lookup_var out t = SOME (n2w (buffer_allocation_base s sb.cs_next_id)) /\
    buffer_allocation_base s sb.cs_next_id + n < dimword (:256) /\
    MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    FLOOKUP t.vs_allocas sb.cs_next_id = SOME (buffer_allocation_base s sb.cs_next_id,n) /\
    fresh_vars_wrt sc t
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx ee s` by gvs[vv_post_def] >>
  drule_all compile_alloc_buffer_counted >>
  disch_then (qspecl_then [`D`, `PG`, `G`, `tn`] strip_assume_tac) >>
  `fresh_vars_wrt sc t` by metis_tac[ifexp_alloc_start_fresh] >>
  `!x. vv_operand vv = Var x ==> x <> out` by
    (drule compile_alloc_buffer_parts >> strip_tac >> metis_tac[]) >>
  drule_all assign_alloc_buffer_vv_post >> strip_tac >>
  `vv_at cenv cx (post_value_type cenv e) sa sb ee tv vv s` by gvs[vv_post_def] >>
  drule_all alloca_step_source_vv >> disch_then (qspec_then `PG` assume_tac) >>
  drule_all compile_alloc_buffer_ghost_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule_all compile_alloc_buffer_kept_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  `lookup_var out t = SOME (n2w (buffer_allocation_base s sb.cs_next_id))` by
    (drule_all ifexp_alloca_step_base >> simp[lookup_var_def]) >>
  `buffer_allocation_base s sb.cs_next_id + n < dimword (:256)` by
    (drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[] >>
     drule_all ifexp_alloca_base_bound >> simp[]) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn)` by
    (drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[]) >>
  `FLOOKUP t.vs_allocas sb.cs_next_id = SOME (buffer_allocation_base s sb.cs_next_id,n)` by
    (drule_all ifexp_alloca_step_site >> simp[]) >>
  qexistsl [`out`, `G1`, `tn1`, `t`] >> simp[lookup_var_def] >>
  conj_tac >- suspend "ghost_position" >>
  conj_tac >- suspend "stack_buffer" >>
  conj_tac >- suspend "located_buffer" >>
  drule_all alloca_step_contracts >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >> gvs[lookup_var_def]
QED

Resume compile_alloc_buffer_vv_source_fresh_frame[ghost_position]:
  qpat_x_assum `ghost_inv _ _ _ _ _ _ u` mp_tac >>
  rpt (pop_assum kall_tac) >> Cases_on `d`
  >- (simp[ghost_inv_def, ptr_covers_def, stor_taint_ok_def, lookup_var_def,
           return_buf_ptr_def] >> strip_tac >> simp[]) >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  simp[ghost_inv_def, return_buf_ptr_def, ptr_covers_def,
       stor_taint_ok_def, lookup_var_def] >> strip_tac >> simp[]
QED
Resume compile_alloc_buffer_vv_source_fresh_frame[stack_buffer]:
  rpt strip_tac >> irule alloca_step_source_buffer >>
  gvs[vv_operand_def] >> qexists `s` >> simp[]
QED
Resume compile_alloc_buffer_vv_source_fresh_frame[located_buffer]:
  rpt strip_tac >> irule alloca_step_source_buffer >>
  gvs[vv_operand_def] >> qexists `s` >> simp[]
QED
Finalise compile_alloc_buffer_vv_source_fresh_frame
