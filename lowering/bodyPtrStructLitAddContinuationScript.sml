Theory bodyPtrStructLitAddContinuation
Ancestors bodyPtrStructLitCountedAdd bodyPtrStructLitSourceFrame
  bodyPtrStructLitFieldStore
  bodyPtrStructLitFreshGhost bodyPtrStructLitPostAdd exprOperandVar
  exprLoweringProps emitHelperProps freshWrites context compileEnv
  bodyPtrDefs venomState emitHelper bodyPtrStructLitRawChild
  exprLowering fragExec exprSimAggregateLayout

Theorem raw_child_add_source_frame:
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  local_ptrs_reserved ce sb /\
  emit_op ADD [Var p; Lit off] sc = (Var dst,sm) /\
  vv_post ctx fn ce cx e es sb sc t ee tv vv s ==>
  vv_post ctx fn ce cx e es sb sm t ee tv vv
    (update_var dst w s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule vv_post_update_var_pc >> simp[] >>
  qexists `sc` >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sc x` by
    metis_tac[compiler_compile_var] >>
  gvs[not_fresh_at_def]
QED

Theorem ptr_buf_ok_operand_frame:
  ptr_buf_ok ce e op G s /\
  eval_operand op s' = eval_operand op s /\
  (!x. op = Var x ==> FLOOKUP G' x = FLOOKUP G x) ==>
  ptr_buf_ok ce e op G' s'
Proof
  simp[ptr_buf_ok_def] >> metis_tac[]
QED

Theorem ptr_buf_ok_fresh_add:
  ptr_buf_ok ce e op G s /\ (!x. op = Var x ==> x <> dst) ==>
  ptr_buf_ok ce e op
    (step_prov PG G (mk_inst id ADD [left;right] [dst]) (update_var dst w s))
    (update_var dst w s)
Proof
  strip_tac >> irule ptr_buf_ok_operand_frame >>
  qexistsl [`G`, `s`] >> simp[] >>
  metis_tac[fresh_add_operand_frame]
QED

Theorem raw_child_add_output_separation:
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  local_ptrs_reserved ce sb /\
  emit_op ADD [Var p; Lit off] sc = (Var dst,sm) ==>
  (!x. not_fresh_at sb x ==> x <> dst) /\
  (!x. vv_operand vv = Var x ==> x <> dst) /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
     x <> dst)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sc x` by
    metis_tac[compiler_compile_var] >>
  gvs[not_fresh_at_def, local_ptrs_reserved_def] >> rpt conj_tac >>
  rpt strip_tac >> res_tac >> gvs[]
QED

Theorem raw_child_add_ghost_frame:
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  local_ptrs_reserved ce sb /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  emit_op ADD [Var p; Lit off] sc = (Var dst,sm) /\
  ghost_inv d ce cx ee G tn s ==>
  ghost_inv d ce cx ee
    (step_prov PG G (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst])
      (update_var dst w s))
    (step_taint (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst]) s
      (update_var dst w s) tn)
    (update_var dst w s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all raw_child_add_output_separation >> strip_tac >>
  irule ghost_inv_fresh_add_pc >> simp[] >> metis_tac[]
QED

Theorem raw_child_add_kept_frame:
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  local_ptrs_reserved ce sb /\
  emit_op ADD [Var p; Lit off] sc = (Var dst,sm) /\
  ghost_kept ce es sb G0 tn0 t G tn ==>
  ghost_kept ce es sb G0 tn0 t
    (step_prov PG G (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst])
      (update_var dst w s))
    (step_taint (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst]) s
      (update_var dst w s) tn)
Proof
  strip_tac >> drule_all raw_child_add_output_separation >> strip_tac >>
  irule field_add_ghost_kept >> simp[] >> metis_tac[]
QED

Theorem raw_child_add_value_frame:
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  local_ptrs_reserved ce sb /\
  emit_op ADD [Var p; Lit off] sc = (Var dst,sm) /\
  ptr_vv_ok cx (expr_type e) tv vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
     ptr_buf_ok ce e op G s) /\
  (!ty q. vv = LocatedValue ty q /\ q.ptr_location = LocMemory ==>
     ptr_buf_ok ce e q.ptr_operand G s) ==>
  !w PG.
  ptr_vv_ok cx (expr_type e) tv vv ee
    (step_prov PG G (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst])
      (update_var dst w s))
    (step_taint (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst]) s
      (update_var dst w s) tn)
    (update_var dst w s with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
     ptr_buf_ok ce e op
       (step_prov PG G (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst])
         (update_var dst w s))
       (update_var dst w s with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!ty q. vv = LocatedValue ty q /\ q.ptr_location = LocMemory ==>
     ptr_buf_ok ce e q.ptr_operand
       (step_prov PG G (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst])
         (update_var dst w s))
       (update_var dst w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all raw_child_add_output_separation >> strip_tac >>
  rpt gen_tac >> conj_tac
  >- (`!G' tn' u k. ptr_vv_ok cx (expr_type e) tv vv ee G' tn'
          (u with vs_inst_idx := k) = ptr_vv_ok cx (expr_type e) tv vv ee G' tn' u` by
        (Cases_on `vv` >>
         simp[ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def,
              ptr_covers_def, eval_operand_def, lookup_var_def]) >>
      asm_rewrite_tac[] >> irule ptr_vv_ok_fresh_add >> simp[] >> metis_tac[]) >>
  `!op G' u k. ptr_buf_ok ce e op G' (u with vs_inst_idx := k) =
                 ptr_buf_ok ce e op G' u` by
    simp[ptr_buf_ok_def, eval_operand_def, lookup_var_def] >>
  asm_rewrite_tac[] >> conj_tac >> rpt strip_tac >>
  irule ptr_buf_ok_fresh_add >> simp[] >>
  gvs[vv_operand_def] >> metis_tac[]
QED

Theorem raw_child_emitted_add_continuation:
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  local_ptrs_reserved ce sb /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  ghost_inv d ce cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
     ptr_buf_ok ce e op G s) /\
  (!ty q. vv = LocatedValue ty q /\ q.ptr_location = LocMemory ==>
     ptr_buf_ok ce e q.ptr_operand G s) /\
  ghost_kept ce es sb G0 tn0 t G tn /\
  not_fresh_at sb p /\ ptr_covers G0 tn0 p t N /\
  emit_op ADD [Var p; Lit off] sc = (Var dst,sm) /\
  fn_has_code sc sm fn /\ not_fresh_at sc p /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?a s1 G1 tn1.
    lookup_var p s = SOME a /\
    s1 = (update_var dst (a+off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G1 = step_prov PG G (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst])
      (update_var dst (a+off) s) /\
    tn1 = step_taint (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst]) s
      (update_var dst (a+off) s) tn /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1) /\
    vv_post ctx fn ce cx e es sb sm t ee tv vv s1 /\
    ghost_inv d ce cx ee G1 tn1 s1 /\
    ptr_vv_ok cx (expr_type e) tv vv ee G1 tn1 s1 /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
       ptr_buf_ok ce e op G1 s1) /\
    (!ty q. vv = LocatedValue ty q /\ q.ptr_location = LocMemory ==>
       ptr_buf_ok ce e q.ptr_operand G1 s1) /\
    ghost_kept ce es sb G0 tn0 t G1 tn1 /\
    ptr_covers G1 tn1 p s1 N /\ ~s1.vs_halted /\
    s1.vs_current_bb = sm.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> drule_all raw_child_emitted_add_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all raw_child_add_value_frame >>
  disch_then (qspecl_then [`a+off`, `PG`] strip_assume_tac) >>
  drule_all raw_child_add_source_frame >>
  disch_then (qspec_then `a+off` assume_tac) >>
  drule_all raw_child_add_ghost_frame >>
  disch_then (qspecl_then [`a+off`, `PG`] assume_tac) >>
  drule_all raw_child_add_kept_frame >>
  disch_then (qspecl_then [`a+off`, `s`, `PG`] assume_tac) >>
  qexists `a` >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_return_def, fresh_var_def,
      fresh_id_def, comp_ignore_bind_def, emit_def, update_var_def]
QED

Theorem structlit_first_add_suffix:
  compile_struct_lit compile_expr ce ty ((fname,e)::rest) buf off sb = (r,sd) /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  emit_op ADD [buf; Lit (n2w off)] sc = (dst,sm) ==>
  cs_extends sm sd
Proof
  simp[Once compile_struct_lit_def, LET_THM, comp_bind_def] >> strip_tac >>
  `ci_mono sm (SND
    (comp_bind (unwrap_value ce vv)
      (\v. comp_ignore_bind
        (compile_store_memory ce v dst
          (case ALOOKUP (get_struct_fields ce.ce_struct_fields
            (case ty of StructT n => nsid_to_string n | _ => "")) fname of
             SOME (fty,sz) => fty | NONE => expr_type e)
          (lowered_value_type ce e))
        (compile_struct_lit compile_expr ce ty rest buf
          (off + (case ALOOKUP (get_struct_fields ce.ce_struct_fields
            (case ty of StructT n => nsid_to_string n | _ => "")) fname of
             SOME (fty,sz) => sz | NONE => 32)))) sm))` by
    (ho_match_mp_tac ci_mono_bind >> conj_tac
     >- simp[ci_mono_unwrap_value] >>
     rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
     >- simp[ci_mono_compile_store_memory] >>
     gen_tac >> irule ci_mono_compile_struct_lit_cfn >>
     simp[cj 1 compile_expr_ci_mono]) >>
  gvs[comp_bind_def, ci_mono_def]
QED

Theorem structlit_first_add_code:
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  emit_op ADD [buf.buf_operand; Lit (n2w 0)] sc = (dst,sm) /\
  fn_has_code sa sd fn ==>
  fn_has_code sc sm fn
Proof
  strip_tac >> drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  `cs_extends sm sd` by (irule structlit_first_add_suffix >> metis_tac[]) >>
  `cs_extends sc sm` by
    (drule emitted_insts_emit_op >> simp[] >> strip_tac >>
     gvs[emit_op_def, comp_bind_def, comp_return_def, fresh_var_def,
         fresh_id_def, comp_ignore_bind_def, emit_def, cs_extends_def]) >>
  `cs_extends sa sc` by
    (`cs_extends sb sc` by metis_tac[cj 1 compile_expr_grows] >>
     `cs_extends sa sb` by
       (qspecl_then [`SUM (MAP (SND o SND)
          (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))`, `sa`]
          mp_tac ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
     metis_tac[cs_extends_trans]) >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED
