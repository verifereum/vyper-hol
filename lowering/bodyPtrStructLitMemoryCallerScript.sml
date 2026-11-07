(* Memory-word read premises derived from semantic pointer robustness. *)
Theory bodyPtrStructLitMemoryCaller
Ancestors
  bodyPtrStructLitMemoryRead representationCleanPtr exprSimProps
  bodyPtrDefs exprLowering vyperABI contractABI vyperValue vyperTyping
  loweringPosts finite_map venomState compileEnv ptrDiscipline
  bodyPtrStructLitMemoryUnwrap ptrSafeRun venomInst

Theorem word_type_abi_static:
  is_word_type ty ==> ~is_dynamic (vyper_to_abi_type env ty)
Proof
  Cases_on `ty` >> simp[is_word_type_def, vyper_to_abi_type_def,
                        is_dynamic_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, vyper_base_to_abi_type_def, is_dynamic_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def, vyper_base_to_abi_type_def, is_dynamic_def]
QED

Theorem ptr_mem_ok_word_read:
  ptr_mem_ok cx ty v op G tn s /\ op_taint tn op = {} /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\ is_word_type ty /\ value_has_type tv v ==>
  (?src. op = Var src /\ ptr_covers G tn src s 32) /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
  `~is_dynamic (vyper_to_abi_type (get_tenv cx) ty)` by
    metis_tac[word_type_abi_static] >>
  `val_footprint tv v = 32` by metis_tac[static_val_footprint] >>
  conj_tac
  >- (gvs[ptr_mem_ok_def, ptr_covers_def] >>
      qexists `w` >>
      qspecl_then [`tv`, `v`] assume_tac val_footprint_le_store_size >>
      gvs[eval_operand_def] >> decide_tac) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem` by
    (gvs[ptr_mem_ok_def] >> metis_tac[]) >>
  metis_tac[robust_val_in_memory_static_clean]
QED

Theorem memory_word_unwrap_ptr_continuation:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\ is_word_type ty /\
  ptr_vv_ok cx ty tv (LocatedValue ty p) ee G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v) /\
  unwrap_value cenv (LocatedValue ty p) sm = (Var out,sb) /\
  fn_has_code sm sb fn /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\ not_local_ptr cenv ee.scopes out /\
  ghost_inv d cenv cx ee G tn s /\
  (!name entry r sz. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_buf = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_pc = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  ghost_kept cenv es sf G0 tn0 initial G tn /\ ~not_fresh_at sf out ==>
  ?v G1 tn1 s1. read_result cx tv ee = (INL v,ee) /\
    gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee G1 tn1 (OK s1) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v (Var out) s1 /\
    ptr_val_ok cx ty v (Var out) G1 tn1 s1 /\
    ghost_inv d cenv cx ee G1 tn1 s1 /\
    ghost_kept cenv es sf G0 tn0 initial G1 tn1 /\
    s1.vs_current_bb = sb.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!r sz. r <> out /\ ptr_covers G tn r s sz ==>
      ptr_covers G1 tn1 r s1 sz) /\
    (!x. x <> out ==> lookup_var x s1 = lookup_var x s)
Proof
  strip_tac >> drule_all vv_post_memory_word_read >> strip_tac >>
  `ptr_mem_ok cx ty v p.ptr_operand G tn s /\
   op_taint tn p.ptr_operand = {} /\ value_has_type tvt v` by
    (gvs[ptr_vv_ok_def] >> metis_tac[]) >>
  drule_all ptr_mem_ok_word_read >> strip_tac >>
  `lookup_var src s = SOME a` by gvs[eval_operand_def] >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++
    [mk_inst sm.cs_next_id MLOAD [Var src] [out]] /\
   ~not_fresh_at sm out` by
    (drule_all memory_word_unwrap_code >> simp[]) >>
  qexistsl [`v`,
    `step_prov PG G (mk_inst sm.cs_next_id MLOAD [Var src] [out])
      (update_var out (mload (w2n a) s) s)`,
    `step_taint (mk_inst sm.cs_next_id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn`,
    `update_var out (mload (w2n a) s) s with vs_inst_idx := SUC s.vs_inst_idx`] >>
  drule_at (Pat `ghost_inv _ _ _ _ _ _ _`) memory_word_unwrap_continuation >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED
