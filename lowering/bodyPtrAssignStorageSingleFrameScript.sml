Theory bodyPtrAssignStorageSingleFrame
Ancestors bodyPtrIfExpStorageSingle bodyPtrBytestringBuiltinsAllocation
  bodyPtrIfExpMaterializeSingle bodyPtrIfExpMaterializeWord
  bodyPtrIfExpStorageAllocation bodyPtrIfExpAllocSource
  bodyPtrIfExpMaterializeFrame loweringHalt loweringStateRelDefs
  compileEnv venomState venomInst finite_map ptrDiscipline

Theorem assign_storage_single_frame:
  post_value_type ce e = expr_type e /\
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw (LocatedValue tag pp) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue tag pp) ee G tn s /\
  (pp.ptr_location = LocStorage \/ pp.ptr_location = LocTransient) /\
  (type_memory_bytes ce (expr_type e)+31) DIV 32 = 1 /\
  compile_ensure_in_memory pp.ptr_operand pp.ptr_location
    (type_memory_bytes ce (expr_type e)) 1 is_ctor imm sb = (dst,sd) /\
  fn_has_code sb sd fn /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  type_memory_bytes ce (expr_type e) < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  fresh_vars_wrt sb s ==>
  ?out d ty t G' tn'.
    dst = Var out /\ eval_operand dst t = SOME d /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==> val_in_memory ty v (w2n d) m) /\
    ptr_covers G' tn' out t (type_memory_bytes ce (expr_type e)) /\
    ghost_inv rty ce cx ee G' tn' t /\ ghost_kept ce es sa G0 tn0 s0 G' tn' /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
      off+sz <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= off) /\
    (!name pos len. local_region ce es.scopes s0 name pos len ==>
      pos+len <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= pos) /\
    (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!b len. b+len <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_transient = s.vs_transient /\ t.vs_data_section = s.vs_data_section /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (~is_word_type (expr_type e) ==> expr_post ctx fn ce cx e es sa sd s0 ee v dst t) /\
    (!x. not_fresh_at sb x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  bodyPtrStorageSingleProofLib.start ifexp_storage_single_code >> suspend "execute"
QED

Resume assign_storage_single_frame[execute]:
  bodyPtrStorageSingleProofLib.execute ifexp_storage_load_step >> suspend "finish"
QED

Resume assign_storage_single_frame[finish]:
  bodyPtrStorageSingleProofLib.frames >> suspend "post"
QED

Resume assign_storage_single_frame[post]:
  bodyPtrStorageSingleProofLib.robust ifexp_storage_single_robust >> suspend "ordinary"
QED

Resume assign_storage_single_frame[ordinary]:
  bodyPtrStorageSingleProofLib.ordinary >> suspend "semantic"
QED

Resume assign_storage_single_frame[semantic]:
  markerLib.RESUME_TAC >> bodyPtrStorageSingleProofLib.semantic >> suspend "expr_post"
QED

Resume assign_storage_single_frame[expr_post]:
  markerLib.RESUME_TAC >> bodyPtrStorageSingleProofLib.post >> suspend "ghost_frame"
QED

Resume assign_storage_single_frame[ghost_frame]:
  `!x. not_fresh_at sb x ==> x <> out` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `compile_alloc_buffer _ sb = _` mp_tac >>
     qpat_x_assum `buf.buf_operand = Var out` mp_tac >>
     qpat_x_assum `not_fresh_at sb x` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  `!x. not_fresh_at sb x ==> FLOOKUP Gb x = FLOOKUP G x /\
    op_taint tb (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `Gb`, Abbr `tb`] >>
     metis_tac[alloca_old_register_ghost_frame]) >>
  `MEM opc [SLOAD;TLOAD;DLOAD]` by
    (qpat_x_assum `MEM opc [SLOAD;TLOAD]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  `eval_operand pp.ptr_operand r = SOME p` by simp[Abbr `r`] >>
  `tn1 = tb with t_var := tb.t_var |+ (out',
     if opc = SLOAD then key_taint tb.t_stor p
     else if opc = TLOAD then key_taint tb.t_trans p else {})` by
    (qpat_x_assum `tn1 = _` SUBST1_TAC >>
     simp[ifexp_materialize_load_taint]) >>
  `!x. not_fresh_at sb x ==> FLOOKUP G2 x = FLOOKUP G x /\
    op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> out'` by metis_tac[] >>
     `G2 = G1 /\ tn2.t_var = tn1.t_var` by
       (qpat_x_assum `G2 = _` SUBST1_TAC >>
        qpat_x_assum `tn2 = _` SUBST1_TAC >>
        simp[step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
          mk_inst_def, store_taint_def, adopt_reset_def, imm_taint_def, DRESTRICT_UNIV]) >>
     qpat_x_assum `G2 = G1` SUBST1_TAC >>
     qpat_x_assum `G1 = _` SUBST1_TAC >>
     qpat_x_assum `tn2.t_var = tn1.t_var` mp_tac >>
     qpat_x_assum `tn1 = tb with t_var := _` mp_tac >>
     qpat_x_assum `x <> out'` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sb x ==> FLOOKUP Gb x = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_x_assum `not_fresh_at sb x` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[step_prov_def, set_prov_def, mk_inst_def,
         FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
     Cases_on `out_prov PG Gb
       (mk_inst cs.cs_next_id opc [pp.ptr_operand] [out'])
       (update_var out' w r)` >>
     gvs[mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  bodyPtrStorageSingleProofLib.assemble
QED

Finalise assign_storage_single_frame
