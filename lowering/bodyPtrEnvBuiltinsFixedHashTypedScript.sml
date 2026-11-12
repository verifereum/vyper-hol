(* Typing validates the scratch hash size; the compiler wrapper hides IDs. *)
Theory bodyPtrEnvBuiltinsFixedHashTyped
Ancestors bodyPtrEnvBuiltinsFixedHashCompile exprSimHash bodyPtrDefs
  exprSimDefs exprSimProps loweringPosts valueEncoding vyperAST vyperValue
  vyperTyping compileEnv venomState words finite_map list builtinHashing

Theorem fixed_hash_typed_counted:
  expr_post ctx fn cenv cx e es sa sm s0 es' (BytesV bs) arg s /\
  ptr_val_ok cx (expr_type e) (BytesV bs) arg G tn s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Fixed m))) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\
  compile_method_id_hash (expr_type e) arg sm = (op,sh) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  fn_inst_ids_distinct fn /\
  ghost_inv d cenv cx es' G tn s /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ fn_has_code sm sh fn /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sh) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sh.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 32))) result op G' tn' t /\
    ghost_inv d cenv cx es' G' tn' t /\ ghost_kept cenv es' sm G tn s G' tn'
Proof
  strip_tac >>
  `m <= 32` by gvs[evaluate_type_def, AllCaseEqs()] >>
  drule_at (Pat `expr_type _ = _`) hash_fixed_post_view >>
  disch_then drule_all >> strip_tac >>
  `stmt_state_rel ctx fn cenv cx es' s` by fs[expr_post_def] >>
  `op_taint tn arg = {}` by gvs[ptr_val_ok_def, is_word_type_def] >>
  gvs[compile_method_id_hash_def] >>
  drule_at (Pat `compile_keccak256_bytesm _ _ _ = _`) fixed_hash_compile_counted >>
  disch_then irule >> simp[] >> metis_tac[]
QED
