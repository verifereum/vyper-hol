Theory bodyFullBopRestWordTailFrame
Ancestors
  bodyPtrBopInElementLoad bodyFullGhostFrame bodyFullUnwrapRun
  exprSimVVFrame tupleTypedLoad bodySimFull exprLoweringProps
  loweringStateRelDefs exprSimProps bodyPtrMakeArrayCopyStateFrame bodyPtrDefs
  bodyPtrBopInLoopContract loweringPosts freshWrites compileEnv venomState
  exprLowering bodyPtrBopInLoopLayout bodyPtrBopInBoundedLayout venomInst

Theorem rest_word_membership_tail_vv_frame[local]:
  compile_var_array_membership cenv needleop vv aty is_in sm = (out,ct) /\
  vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
  membership_loop_frame sm (gu:(string, num # num) fmap) tu u gt tt t /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) ==>
  vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv t
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) u` by
    metis_tac[membership_loop_frame_operand] >>
  `!n b sz. local_region cenv ee.scopes t n b sz <=>
             local_region cenv ee.scopes u n b sz` by
    (simp[local_region_def] >>
     fs[local_ptrs_reserved_def, membership_loop_frame_def] >> metis_tac[]) >>
  `t.vs_memory = u.vs_memory /\ t.vs_allocas = u.vs_allocas /\
   contract_storage t = contract_storage u /\
   contract_transient t = contract_transient u` by
    (fs[membership_loop_frame_def] >>
     qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     simp[contract_storage_def, contract_transient_def]) >>
  `stmt_state_rel H ctx fn cenv cx ee t` by suspend "state" >>
  `vv_holds cenv cx (post_value_type cenv e) tv vv ee t` by
    (irule vv_holds_vars_frame >> qexists_tac `u` >> fs[vv_post_def]) >>
  `vv_at cenv cx (post_value_type cenv e) sa sm ee tv vv t` by
    (irule vv_at_vars_frame >> qexistsl_tac [`u`,`sm`] >> fs[vv_post_def]) >>
  `post_value_type cenv e <> expr_type e ==>
   vv_own cenv cx (post_value_type cenv e) sa sm ee tv vv t` by
    (strip_tac >> irule vv_own_vars_frame >> qexistsl_tac [`u`,`sm`] >>
     fs[vv_post_def]) >>
  `locals_kept cenv es ee s0 t` by
    (irule locals_kept_mem_tail >> qexists_tac `u` >> fs[vv_post_def]) >>
  `pure_frame cenv fn es sa s0 t <=> pure_frame cenv fn es sa s0 u` by
    metis_tac[pure_frame_state_cong] >>
  `vv_storage_live H cx vv ee t = vv_storage_live H cx vv ee u` by
    suspend "storage" >>
  fs[vv_post_def] >> rpt strip_tac >>
  fs[membership_loop_frame_def] >> metis_tac[]
QED

Resume rest_word_membership_tail_vv_frame[state]:
  `stmt_state_rel H ctx fn cenv cx ee (u with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >>
     fs[vv_post_def, local_ptrs_reserved_def, membership_loop_frame_def,
        lookup_var_def] >> metis_tac[]) >>
  fs[membership_loop_frame_def] >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
  `u with <|vs_vars := t.vs_vars; vs_prev_bb := t.vs_prev_bb;
      vs_current_bb := t.vs_current_bb; vs_inst_idx := t.vs_inst_idx|> =
   (u with vs_vars := t.vs_vars) with <|vs_prev_bb := t.vs_prev_bb;
      vs_current_bb := t.vs_current_bb; vs_inst_idx := t.vs_inst_idx|>` by simp[] >>
  asm_rewrite_tac[literal_stmt_state_rel_cursor]
QED
Resume rest_word_membership_tail_vv_frame[storage]:
  Cases_on `vv` >> fs[contextTheory.vv_operand_def]
QED
Finalise rest_word_membership_tail_vv_frame

Theorem rest_word_membership_tail_ptr_frame[local]:
  compile_var_array_membership cenv needleop vv aty is_in sm = (out,ct) /\
  membership_loop_frame sm gu tu u gt tt t /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ptr_vv_ok cx ty tv vv ee gu tu u ==>
  ptr_vv_ok cx ty tv vv ee gt tt t
Proof
  strip_tac >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) u /\
   op_prov gt (vv_operand vv) = op_prov gu (vv_operand vv) /\
   op_taint tt (vv_operand vv) = op_taint tu (vv_operand vv)` by
    metis_tac[membership_loop_frame_operand] >>
  `!ty v. ptr_mem_ok cx ty v (vv_operand vv) gu tu u ==>
           ptr_mem_ok cx ty v (vv_operand vv) gt tt t` by
    metis_tac[membership_frame_ptr_mem_ok] >>
  Cases_on `vv`
  >- (fs[ptr_vv_ok_def, ptr_val_ok_def, contextTheory.vv_operand_def] >>
      metis_tac[]) >>
  fs[ptr_vv_ok_def, contextTheory.vv_operand_def] >>
  conj_tac >- metis_tac[] >>
  fs[membership_loop_frame_def] >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem rest_word_membership_exit_no_alloca[local]:
  compile_var_array_membership cenv needleop vv aty is_in sm = (out,ct) /\
  fn_has_code sm ct fn ==>
  !bb k inst. lookup_block ct.cs_current_bb fn.fn_blocks = SOME bb /\
    k < LENGTH ct.cs_current_insts /\ get_instruction bb k = SOME inst ==>
    inst.inst_opcode <> ALLOCA
Proof
  simp[compile_var_array_membership_def, comp_bind_def] >>
  pairarg_tac >>
  Cases_on `aty` >> simp[] >>
  rpt strip_tac >>
  gvs[SRULE [] bodyPtrBopInLoopLayoutTheory.membership_loop_layout,
      SRULE [] bodyPtrBopInBoundedLayoutTheory.membership_bounded_loop_layout] >>
  Cases_on `is_in` >>
  fs[fragExecTheory.fn_has_code_def] >>
  gvs[listTheory.isPREFIX, AllCaseEqs(), get_instruction_def, mk_inst_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  Cases_on `b` >>
  gvs[SRULE [] bodyPtrBopInLoopLayoutTheory.membership_loop_layout,
      SRULE [] bodyPtrBopInBoundedLayoutTheory.membership_bounded_loop_layout,
      listTheory.isPREFIX, mk_inst_def]
QED

Theorem rest_word_membership_tail_full_frame:
  compile_var_array_membership cenv needleop vv aty is_in sm = (out,ct) /\
  fn_has_code sm ct fn /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. needleop = Var x \/ vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!H. guard H ==>
    t.vs_current_bb = ct.cs_current_bb /\
    t.vs_inst_idx = LENGTH ct.cs_current_insts /\
    membership_loop_frame sm (gu H) (tu H) u (gt H) (tt H) t /\
    alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv u /\
    ghost_inv_at (DF H) lo d cenv cx ee (gu H) (tu H) u /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee (gu H) (tu H) u /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
               eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside (tu H).t_mem u.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)) /\
    (!vt op. vv = StackValue vt op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op (gu H) u) /\
    (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand (gu H) u) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 (gu H) (tu H)) ==>
  !H. guard H ==>
    alloca_history fn t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv t /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
    ghost_inv_at (DF H) lo d cenv cx ee (gt H) (tt H) t /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee (gt H) (tt H) t /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
               eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside (tt H).t_mem t.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)) /\
    (!vt op. vv = StackValue vt op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op (gt H) t) /\
    (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand (gt H) t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 (gt H) (tt H) /\
    eval_operand needleop t = eval_operand needleop u /\
    op_prov (gt H) needleop = op_prov (gu H) needleop /\
    op_taint (tt H) needleop = op_taint (tu H) needleop
Proof
  strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) u /\
   op_prov (gt H) (vv_operand vv) = op_prov (gu H) (vv_operand vv) /\
   op_taint (tt H) (vv_operand vv) = op_taint (tu H) (vv_operand vv)` by
    metis_tac[membership_loop_frame_operand] >>
  `t.vs_memory = u.vs_memory /\ t.vs_allocas = u.vs_allocas /\
   t.vs_alloca_next = u.vs_alloca_next /\ (tt H).t_mem = (tu H).t_mem` by
    (fs[membership_loop_frame_def] >>
     qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  rpt conj_tac
  >- suspend "history"
  >- simp[]
  >- metis_tac[rest_word_membership_tail_vv_frame]
  >- suspend "bound"
  >- suspend "ghost"
  >- metis_tac[rest_word_membership_tail_ptr_frame]
  >- metis_tac[]
  >- suspend "stackbuf"
  >- suspend "locatedbuf"
  >- suspend "kept"
  >> metis_tac[membership_loop_frame_operand]
QED

Resume rest_word_membership_tail_full_frame[history]:
  drule rest_word_membership_exit_no_alloca >>
  disch_tac >>
  fs[allocaHistoryTheory.alloca_history_def] >> metis_tac[]
QED
Resume rest_word_membership_tail_full_frame[bound]:
  Cases_on `vv` >>
  fs[exprSimMemDefsTheory.vv_store_bound_def, contextTheory.vv_operand_def] >>
  metis_tac[]
QED
Resume rest_word_membership_tail_full_frame[ghost]:
  irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`gu H`,`ee`,`u`,`sa`,`tu H`] >>
  fs[membership_loop_frame_def] >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[] >>
  metis_tac[]
QED
Resume rest_word_membership_tail_full_frame[stackbuf]:
  rpt strip_tac >> gvs[contextTheory.vv_operand_def] >>
  Cases_on `op` >> fs[ptr_buf_ok_def, ptrDisciplineTheory.op_prov_def] >>
  metis_tac[]
QED
Resume rest_word_membership_tail_full_frame[locatedbuf]:
  rpt strip_tac >> gvs[contextTheory.vv_operand_def] >>
  Cases_on `p.ptr_operand` >> fs[ptr_buf_ok_def, ptrDisciplineTheory.op_prov_def] >>
  metis_tac[]
QED
Resume rest_word_membership_tail_full_frame[kept]:
  irule ghost_kept_at_clean_suffix >>
  qexistsl_tac [`gu H`,`tu H`] >>
  fs[membership_loop_frame_def] >> metis_tac[]
QED
Finalise rest_word_membership_tail_full_frame
