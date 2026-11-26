(* The array is consumed by the search. Only the Bool and the caller's
   frame are needed at the parent endpoint. *)
Theory bodyMembershipArrayPostMods
Ancestors
  bodyFullPostsMods bodyForRangeScalarFrameMods bodyFullUnwrapRun
  bodyPtrBopInElementLoad bodyPtrBopInLoopContract bodyPtrBopInLoopLayout
  bodyPtrBopInBoundedLayout bodyPtrMakeArrayCopyStateFrame
  exprSimProps exprSimWordArgs wordArgsPtr freshWrites loweringPosts
  bodyPtrDefs exprSimMemDefs vyperTypeSystem venomInst rich_list
  exprLowering compileEnv list fragExec allocaHistory loweringStateRelDefs
  venomState exprLoweringProps vyperAST vyperValue valueEncoding

Theorem membership_exit_no_alloca[local]:
  compile_var_array_membership cenv x vv (ArrayT ety bd) is_in sm = (out,ct) ==>
  EVERY (\i. i.inst_opcode <> ALLOCA) ct.cs_current_insts
Proof
  Cases_on `bd` >> simp[compile_var_array_membership_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  gvs[SRULE [] membership_loop_layout, SRULE [] membership_bounded_loop_layout] >>
  Cases_on `is_in` >> gvs[mk_inst_def]
QED

Theorem membership_exit_history[local]:
  compile_var_array_membership cenv x vv (ArrayT ety bd) is_in sm = (out,ct) /\
  fn_has_code sm ct func /\ alloca_history func u /\
  q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts /\
  q.vs_allocas = u.vs_allocas ==> alloca_history func q
Proof
  strip_tac >> drule membership_exit_no_alloca >> simp[EVERY_EL] >> strip_tac >>
  fs[fn_has_code_def, IS_PREFIX_APPEND, alloca_history_def] >>
  simp[] >> rpt strip_tac >> gvs[get_instruction_def, EL_APPEND1] >>
  first_x_assum drule >> simp[]
QED

Theorem membership_landing_state[local]:
  stmt_state_rel H ctx func cenv cx fin u /\ local_ptrs_reserved cenv sm /\
  membership_loop_frame sm G2 tn2 u G tn q ==>
  stmt_state_rel H ctx func cenv cx fin q
Proof
  strip_tac >> fs[membership_loop_frame_def] >>
  `stmt_state_rel H ctx func cenv cx fin (u with vs_vars := q.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[] >>
     fs[local_ptrs_reserved_def,lookup_var_def] >> metis_tac[]) >>
  qpat_assum `q = _` (fn th => once_rewrite_tac[th]) >>
  `u with <|vs_vars := q.vs_vars; vs_prev_bb := q.vs_prev_bb;
             vs_current_bb := q.vs_current_bb; vs_inst_idx := q.vs_inst_idx|> =
   (u with vs_vars := q.vs_vars) with
     <|vs_prev_bb := q.vs_prev_bb; vs_current_bb := q.vs_current_bb;
       vs_inst_idx := q.vs_inst_idx|>` by simp[] >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  pure_rewrite_tac[literal_stmt_state_rel_cursor] >> first_assum ACCEPT_TAC
QED

Theorem membership_array_post_mods:
  compile_var_array_membership cenv x vv (ArrayT ety bd) (bop = In) sm = (out,ct) /\
  fn_has_code sm ct func /\
  expr_post_mods H ctx func cenv cx e1 es sa s1 s0 mid needle x t /\
  vv_post_mods H ctx func cenv cx e2 mid s1 sm t fin tv vv u /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\
  ghost_inv_at_mods (DF H) lo d cenv cx fin G2 tn2 u /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ t.vs_alloca_next <= u.vs_alloca_next /\
  membership_loop_frame sm G2 tn2 u G tn q /\
  q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts /\
  eval_operand out q = SOME (bool_to_word b) /\ op_prov G out = NONE /\
  op_taint tn out = {} ==>
  let e = Builtin (BaseT BoolT) (Bop bop) [e1;e2] in
    expr_post_mods H ctx func cenv cx e es sa ct s0 fin (BoolV b) out q /\
    expr_store_bound cx (post_value_type cenv e) (BoolV b) out q /\
    q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts /\
    alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    s0.vs_alloca_next <= q.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx fin G tn q /\
    ptr_val_ok cx (post_value_type cenv e) (BoolV b) out G tn q /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e out G q) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `q.vs_memory = u.vs_memory /\ q.vs_data_section = u.vs_data_section /\
   q.vs_allocas = u.vs_allocas /\ q.vs_alloca_next = u.vs_alloca_next /\
   q.vs_call_ctx = u.vs_call_ctx /\ q.vs_accounts = u.vs_accounts /\
   q.vs_transient = u.vs_transient /\ q.vs_immutables = u.vs_immutables` by
    (fs[membership_loop_frame_def] >>
     qpat_assum `q = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `alloca_history func q` by
    (drule_all membership_exit_history >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp q)` by
    (drule membership_loop_frame_allocas_below_fmp >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  simp[post_value_type_def, expr_type_def, is_word_type_def,
       expr_store_bound_word, ptr_val_ok_word] >>
  conj_tac >- suspend "post" >>
  conj_tac >- suspend "ghost" >>
  suspend "kept"
QED

Resume membership_array_post_mods[post]:
  fs[expr_post_mods_def] >>
  `stmt_state_rel H ctx func cenv cx fin u /\
   immutable_frame_mods func cenv cx fin u /\
   storage_well_formed_on cx fin (FST H) /\ wb_frame cenv mid fin s1 t u` by
    (qhdtm_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- suspend "ordinary" >>
  irule immutable_frame_mods_exterior_frame >>
  qpat_assum `immutable_frame_mods func cenv cx fin u` (irule_at Any) >>
  qpat_assum `local_ptrs_reserved cenv sm` (irule_at Any) >>
  fs[membership_loop_frame_def]
QED

Resume membership_array_post_mods[ordinary]:
  `wb_frame cenv es mid sa s0 t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `wb_frame cenv es fin sa s0 u` by
    (drule_all wb_frame_trans >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx fin q` by
    (drule_all membership_landing_state >> simp[]) >>
  fs[expr_post_def,post_value_type_def,expr_type_def,expr_val_at_def,is_word_type_def,
     wb_frame_def,membership_loop_frame_def] >>
  conj_tac
  >- (Cases_on `b` >> fs[expr_val_rel_def,evaluate_type_def,typed_val_to_w256_def,
          val_to_w256_def,venomExecSemanticsTheory.bool_to_word_def,is_word_type_def]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (drule_all locals_kept_mem_tail >> simp[]) >>
  simp[expr_has_effect_thm] >> strip_tac >>
  `pure_frame cenv func mid s1 t u` by fs[vv_post_mods_def] >>
  `pure_frame cenv func es sa s0 t` by simp[] >>
  `pure_frame cenv func es sa s0 u` by
    (drule_all pure_frame_trans >> simp[]) >>
  metis_tac[pure_frame_state_cong]
QED

Resume membership_array_post_mods[ghost]:
  irule ghost_inv_at_mods_exterior_frame >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ fin G2 tn2 u` (irule_at Any) >>
  qpat_assum `local_ptrs_reserved cenv sm` (irule_at Any) >>
  fs[membership_loop_frame_def] >> metis_tac[]
QED

Resume membership_array_post_mods[kept]:
  `wb_frame cenv es mid sa s0 t` by
    (fs[expr_post_mods_def] >> irule expr_post_frame >> goal_assum (drule_at Any)) >>
  drule_all ghost_kept_at_wb_trans >> strip_tac >>
  irule ghost_kept_at_clean_suffix >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` (irule_at Any) >>
  fs[membership_loop_frame_def] >> metis_tac[]
QED

Finalise membership_array_post_mods
