(* The word store starts after unwrap, not immediately after the ADD. *)
Theory bodyPtrStructLitFirstWordStore
Ancestors bodyPtrStructLitMemoryIntegration bodyPtrStructLitNonmemoryIntegration
  bodyPtrStructLitWordCapacity bodyPtrStructLitFieldStore
  exprSimAggregateLayout exprLoweringProps exprLowering context compileEnv
  emitHelperProps emitHelper fragExec loweringPosts bodyPtrDefs fragGasSeqPtr
  gasSummaryComposePtr ghostPcTransportPtr ptrSafeRun venomState
  typedCopyLoopHeaderPtr ptrDiscipline

Theorem structlit_first_store_suffix:
  compile_struct_lit compile_expr ce ty ((fname,e)::rest) buf off sb = (r,sd) /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  emit_op ADD [buf; Lit (n2w off)] sc = (dst,sm) /\
  unwrap_value ce vv sm = (v,su) /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields
    (case ty of StructT n => nsid_to_string n | _ => "")) fname = SOME (fty,sz) /\
  compile_store_memory ce v dst fty (lowered_value_type ce e) su = ((),sv) ==>
  cs_extends sv sd
Proof
  simp[Once compile_struct_lit_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def] >> strip_tac >>
  `ci_mono sv (SND (compile_struct_lit compile_expr ce ty rest buf (off+sz) sv))`
    by (irule ci_mono_compile_struct_lit_cfn >> simp[cj 1 compile_expr_ci_mono]) >>
  gvs[ci_mono_def]
QED

Theorem word_store_instruction:
  compile_store_memory ce value dst fty sty su = ((),sv) /\
  is_word_type fty /\ fn_has_code su sv fn ==>
  sv.cs_current_bb = su.cs_current_bb /\
  sv.cs_current_insts = su.cs_current_insts ++
    [mk_inst su.cs_next_id MSTORE [dst;value] []] /\
  ?bb. lookup_block su.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH su.cs_current_insts) =
      SOME (mk_inst su.cs_next_id MSTORE [dst;value] [])
Proof
  strip_tac >>
  `emit_void MSTORE [dst;value] su = ((),sv)` by gvs[compile_store_memory_def] >>
  `sv.cs_current_bb = su.cs_current_bb` by
    gvs[emit_void_def, comp_bind_def, comp_return_def, fresh_id_def,
        emit_def, comp_ignore_bind_def] >>
  drule emitted_insts_emit_void >> strip_tac >> simp[] >>
  drule_all fn_has_code_same_block >> strip_tac >> qexists `bb` >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem structlit_first_store_code:
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  emit_op ADD [buf.buf_operand; Lit (n2w 0)] sc = (dst,sm) /\
  unwrap_value ce vv sm = (v,su) /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) fname =
    SOME (fty,sz) /\
  compile_store_memory ce v dst fty (lowered_value_type ce e) su = ((),sv) /\
  fn_has_code sa sd fn ==>
  fn_has_code su sv fn
Proof
  strip_tac >> drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [root.buf_operand; Lit 0w] sc = (dst,sm)` >>
  `cs_extends sv sd` by
    (drule structlit_first_store_suffix >> simp[] >>
     disch_then drule >> simp[] >> disch_then drule >> simp[] >>
     disch_then drule >> simp[]) >>
  `cs_extends su sv` by
    (qspecl_then [`ce`, `v`, `dst`, `fty`, `lowered_value_type ce e`, `su`]
      mp_tac ci_mono_compile_store_memory >> simp[ci_mono_def]) >>
  `cs_extends sm su` by
    (qspecl_then [`ce`, `vv`, `sm`] mp_tac ci_mono_unwrap_value >>
     simp[ci_mono_def]) >>
  `cs_extends sc sm` by
    (qspecl_then [`ADD`, `[root.buf_operand; Lit (n2w 0)]`, `sc`]
      mp_tac ci_mono_emit_op >> simp[ci_mono_def]) >>
  `cs_extends sb sc` by metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends sa sb` by
    (qspecl_then [`SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))`, `sa`]
      mp_tac ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `cs_extends sa su /\ cs_extends su sd` by metis_tac[cs_extends_trans] >>
  `fn_has_code su sd fn` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

Theorem word_store_normal_continuation:
  compile_store_memory ce value (Var dst) fty sty su = ((),sv) /\
  is_word_type fty /\ is_word_type (expr_type e) /\
  fn_has_code su sv fn /\ ~ctx_has_dalloca ctx /\
  gas_path_ptr D lo ctx fn PG Gi tni initial k G tn (OK s) /\
  expr_post ctx fn ce cx e es sa su s0 ee v value s /\
  ptr_val_ok cx (expr_type e) v value G tn s /\
  ghost_kept ce es sf G0 tn0 t G tn /\
  ptr_covers G tn dst s 32 /\
  s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?a w. lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G
      (step_taint (mk_inst su.cs_next_id MSTORE [Var dst;value] []) s
        (mstore (w2n a) w s) tn)
      (OK (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ghost_kept ce es sf G0 tn0 t G
      (step_taint (mk_inst su.cs_next_id MSTORE [Var dst;value] []) s
        (mstore (w2n a) w s) tn) /\
    (mstore (w2n a) w s).vs_current_bb = sv.cs_current_bb /\
    SUC s.vs_inst_idx = LENGTH sv.cs_current_insts
Proof
  strip_tac >> drule_all word_store_instruction >> strip_tac >>
  `~s.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `op_taint tn value = {}` by gvs[ptr_val_ok_def] >>
  `?w. eval_operand value s = SOME w` by gvs[expr_post_def, expr_val_rel_def] >>
  `?a. lookup_var dst s = SOME a` by gvs[ptr_covers_def] >>
  qexistsl [`a`, `w`] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >> conj_tac
  >- (irule covered_word_store_counted >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (drule_all word_store_ghost_kept >> simp[ptrDisciplineTheory.step_prov_def,
       ptrDisciplineTheory.set_prov_def, venomInstTheory.mk_inst_def,
       finite_mapTheory.DRESTRICT_UNIV] >> metis_tac[]) >>
  simp[venomStateTheory.mstore_def]
QED

Theorem structlit_first_word_destination_coverage:
  expr_body_pre ce cx env (StructLit ann nsid ((fname,e)::rest)) es /\
  is_word_type (expr_type e) /\
  ptr_covers G tn root s
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) /\
  lookup_var root s = SOME a /\ root <> dst /\ dst <> load /\
  sa = (update_var dst (a+0w) s with vs_inst_idx := SUC s.vs_inst_idx) /\
  Ga = step_prov PG G (mk_inst id ADD [Var root; Lit 0w] [dst])
    (update_var dst (a+0w) s) /\
  tna = step_taint (mk_inst id ADD [Var root; Lit 0w] [dst]) s
    (update_var dst (a+0w) s) tn /\
  (!r sz. r <> load /\ ptr_covers Ga tna r sa sz ==>
    ptr_covers G1 tn1 r s1 sz) ==>
  ptr_covers G1 tn1 dst s1 32
Proof
  strip_tac >>
  `32 <= SUM (MAP (SND o SND)
    (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))` by
    (drule structlit_word_field_capacity >> simp[] >> metis_tac[]) >>
  `ptr_covers Ga tna dst sa 32` by
    (gvs[] >> simp[] >> irule typed_copy_loop_dynamic_offset_covers >>
     simp[venomStateTheory.eval_operand_def, wordsTheory.w2n_lt] >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  metis_tac[]
QED

(* Common consumer of the normal memory/nonmemory unwrap results. The universal
   frame below is exported by both first-word wrappers, not an access premise. *)
Theorem structlit_first_word_store_continuation:
  expr_body_pre ce cx env (StructLit ann nsid ((fname,e)::rest)) es /\
  is_word_type (expr_type e) /\ is_word_type fty /\
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (buf,sb) /\
  buf.buf_operand = Var root /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  emit_op ADD [buf.buf_operand; Lit (n2w 0)] sc = (Var dst,sm) /\
  unwrap_value ce vv sm = (Var load,su) /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) fname =
    SOME (fty,sz) /\
  compile_store_memory ce (Var load) (Var dst) fty (lowered_value_type ce e)
    su = ((),sv) /\ fn_has_code sa sd fn /\
  ptr_covers G tn root s
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) /\
  lookup_var root s = SOME a /\ root <> dst /\ dst <> load /\
  u = (update_var dst (a+0w) s with vs_inst_idx := SUC s.vs_inst_idx) /\
  Ga = step_prov PG G (mk_inst sc.cs_next_id ADD [Var root; Lit 0w] [dst])
    (update_var dst (a+0w) s) /\
  tna = step_taint (mk_inst sc.cs_next_id ADD [Var root; Lit 0w] [dst]) s
    (update_var dst (a+0w) s) tn /\
  gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
    (ee,u,Ga,tna) [] (INL v) ee G1 tn1 (OK s1) /\
  expr_post ctx fn ce cx e es sb su t ee v (Var load) s1 /\
  ptr_val_ok cx (expr_type e) v (Var load) G1 tn1 s1 /\
  ghost_kept ce es sb G0 tn0 t G1 tn1 /\
  (!r n. r <> load /\ ptr_covers Ga tna r u n ==>
    ptr_covers G1 tn1 r s1 n) /\
  s1.vs_current_bb = su.cs_current_bb /\
  s1.vs_inst_idx = LENGTH su.cs_current_insts /\ ~ctx_has_dalloca ctx ==>
  ?b w. lookup_var dst s1 = SOME b /\ eval_operand (Var load) s1 = SOME w /\
    gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G1
      (step_taint (mk_inst su.cs_next_id MSTORE [Var dst;Var load] []) s1
        (mstore (w2n b) w s1) tn1)
      (OK (mstore (w2n b) w s1 with vs_inst_idx := SUC s1.vs_inst_idx)) /\
    ghost_kept ce es sb G0 tn0 t G1
      (step_taint (mk_inst su.cs_next_id MSTORE [Var dst;Var load] []) s1
        (mstore (w2n b) w s1) tn1) /\
    (mstore (w2n b) w s1).vs_current_bb = sv.cs_current_bb /\
    SUC s1.vs_inst_idx = LENGTH sv.cs_current_insts
Proof
  strip_tac >>
  `fn_has_code su sv fn` by (irule structlit_first_store_code >> metis_tac[]) >>
  `ptr_covers G1 tn1 dst s1 32` by
    (gvs[] >> drule structlit_first_word_destination_coverage >> simp[] >>
     disch_then drule >> simp[] >> disch_then drule >> simp[] >>
     disch_then drule >> simp[] >> disch_then drule >> simp[]) >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE[gas_marked_exec_ptr_def]) >>
  irule word_store_normal_continuation >> simp[] >> metis_tac[]
QED
