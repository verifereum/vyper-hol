(* MakeArray-specific input boundaries for the joint child/store path. *)
Theory bodyFullMakeArrayInputs
Ancestors
  exprSimVVFrame exprOperandVar exprLowering loweringStateRelDefs
  venomState venomInst bodyPtrDefs abiEncodeMaterialize exprSimHyps
  valueCopyBytes bodyPtrMakeArrayAddFrame decoderGhostFramePtr exprSimMemDefs

val _ = Parse.hide "base";

Theorem make_array_add_original_post:
  !H ctx func ce cx e es sa sm s0 ee tv vv s buf off dst sn w.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    local_ptrs_reserved ce sa /\
    sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    eval_operand buf s = SOME w /\
    vv_post H ctx func ce cx e es sa sm s0 ee tv vv s ==>
    vv_post H ctx func ce cx e es sa sm s0 ee tv vv
      (update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s)
Proof
  rpt strip_tac >>
  irule vv_post_update_var >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `sm` >>
  simp[not_fresh_at_def] >>
  metis_tac[compiler_compile_var, not_fresh_at_def]
QED

Theorem make_array_physical_store_input:
  expr_body_pre ce cx env e es /\
  ~is_word_type (expr_type e) /\
  ~is_word_type (post_value_type ce e) /\
  ptr_val_ok cx (post_value_type ce e) v (Var xs) G tn z /\
  ptr_buf_ok ce e (Var xs) G z /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME lt /\
  value_has_type lt v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size lt /\
  eval_operand (Var xs) z = SOME sw ==>
  (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
         val_in_memory lt v (w2n sw) mem) /\
  (type_memory_size lt <> 0 ==> ptr_covers G tn xs z (type_memory_size lt))
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
     val_in_memory pt v (w2n sw) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (`arg_type_fits (lowered_value_type ce e) (expr_type e)` by
        metis_tac[expr_body_pre_lowered_fits] >>
      drule_all materialize_post_lowered_classify >> strip_tac
      >- gvs[] >>
      rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`post_value_type ce e`, `lowered_value_type ce e`,
                    `get_tenv cx`, `pt`] >> simp[]) >>
  strip_tac >> gvs[ptr_buf_ok_def, ptr_val_ok_def, ptr_covers_def,
                   venomStateTheory.eval_operand_def] >> metis_tac[]
QED

Theorem make_array_add_value_inputs:
  out = STRING #"%" (toString sm.cs_next_var) /\
  ai = mk_inst sm.cs_next_id ADD [Var q; Lit (n2w off)] [out] /\
  au = update_var out (n2w base + n2w off) t /\
  at = au with vs_inst_idx := SUC t.vs_inst_idx /\
  Ga = step_prov PG G ai au /\ tna = step_taint ai t au tn /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee tv vv t /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn t /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
     ptr_buf_ok ce e op G t) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok ce e p.ptr_operand G t) ==>
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee tv vv at /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee Ga tna at /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
     ptr_buf_ok ce e op Ga at) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok ce e p.ptr_operand Ga at) /\
  eval_operand (vv_operand vv) at = eval_operand (vv_operand vv) t /\
  at.vs_alloca_next = t.vs_alloca_next /\ at.vs_memory = t.vs_memory /\
  tna.t_mem = tn.t_mem
Proof
  strip_tac >>
  qpat_x_assum `tna = step_taint _ _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `Ga = step_prov _ _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `at = _ with vs_inst_idx := _` SUBST_ALL_TAC >>
  qpat_x_assum `au = update_var _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `ai = mk_inst _ _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `out = STRING _ _` SUBST_ALL_TAC >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `!x. vv_operand vv = Var x ==> x <> out` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[exprOperandVarTheory.compiler_compile_var] >>
     fs[Abbr `out`,not_fresh_at_def] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `step_prov PG G ai au` >>
  qabbrev_tac `at = au with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `Ga = step_prov PG G ai au` >>
  qabbrev_tac `tna = step_taint ai t au tn` >>
  `tna.t_mem = tn.t_mem /\ tna.t_stor = tn.t_stor /\
   tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
   (!x. x <> out ==> FLOOKUP Ga x = FLOOKUP G x /\
      op_taint tna (Var x) = op_taint tn (Var x))` by
    simp[Abbr `Ga`,Abbr `tna`,Abbr `ai`,Abbr `au`,
         typedCopyPtrTheory.copy_len_binop_ghost_frame,
         decoderGhostFramePtrTheory.step_taint_nonmemory_frame,venomInstTheory.mk_inst_def] >>
  `eval_operand (vv_operand vv) at = eval_operand (vv_operand vv) t` by
    (Cases_on `vv_operand vv` >>
     simp[Abbr `at`,Abbr `au`,venomStateTheory.eval_operand_def,
          venomStateTheory.update_var_def,venomStateTheory.lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `at.vs_alloca_next = t.vs_alloca_next /\ at.vs_memory = t.vs_memory /\
   at.vs_accounts = t.vs_accounts /\ at.vs_transient = t.vs_transient /\
   at.vs_call_ctx = t.vs_call_ctx` by
    simp[Abbr `at`,Abbr `au`,venomStateTheory.update_var_def] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (Cases_on `vv` >>
      gvs[contextTheory.vv_operand_def,exprSimMemDefsTheory.vv_store_bound_def] >>
      metis_tac[])
  >- (simp[Abbr `Ga`,Abbr `tna`,Abbr `ai`,Abbr `au`,Abbr `at`] >>
      irule bodyPtrMakeArrayAddFrameTheory.binop_source_ptr_vv_ok >> simp[] >> metis_tac[])
  >- (rpt strip_tac >>
      simp[Abbr `Ga`,Abbr `ai`,Abbr `au`,Abbr `at`] >>
      irule bodyPtrMakeArrayAddFrameTheory.binop_source_ptr_buf_ok >>
      simp[] >> metis_tac[contextTheory.vv_operand_def])
  >- (rpt strip_tac >>
      simp[Abbr `Ga`,Abbr `ai`,Abbr `au`,Abbr `at`] >>
      irule bodyPtrMakeArrayAddFrameTheory.binop_source_ptr_buf_ok >>
      simp[] >> metis_tac[contextTheory.vv_operand_def])
QED

