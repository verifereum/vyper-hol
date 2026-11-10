(* Typed operands provide the exact read range used by memory hashing. *)
Theory bodyPtrEnvBuiltinsMemoryHashTyped
Ancestors bodyPtrEnvBuiltinsMemoryHashCompile bodyPtrEnvBuiltinsHashInput
  exprSimHash bodyPtrDefs exprSimProps loweringPosts valueEncoding valueEncodingDefs
  vyperAST vyperValue compileEnv venomState words finite_map list builtinHashing

Theorem memory_hash_bytes_input:
  expr_post ctx fn cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  ptr_val_ok cx (expr_type e) (BytesV bs) op G tn s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) ==>
  ?root a b sz.
    op = Var root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s 32 /\ FLOOKUP G root = SOME (b,sz) /\
    b <= w2n a + 32 /\ w2n a + 32 + w2n (n2w (LENGTH bs):bytes32) <= b + sz /\
    w2n a + 32 < dimword(:256) /\ mload (w2n a) s = n2w (LENGTH bs) /\
    (!i. w2n a <= i /\ i < w2n a + 32 + w2n (n2w (LENGTH bs):bytes32) ==>
         i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all hash_dynamic_post_view >> strip_tac >>
  `b < dimword(:256)` by decide_tac >>
  `ptr_mem_ok cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) op G tn s` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  gvs[] >> drule_all ptr_val_ok_bytes_read_clean >> strip_tac >>
  drule ptr_mem_ok_read_range >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`0`, `32 + LENGTH bs`] mp_tac) >>
  simp[val_footprint_def] >> strip_tac >>
  qexistsl_tac [`x`, `n2w b`, `b'`, `sz`] >>
  gvs[eval_operand_def, ptr_val_ok_def, ptr_covers_def, mload_def, mem_word_at_def] >>
  rpt gen_tac >> disch_tac >> Cases_on `i < b + 32` >> gvs[] >>
  metis_tac[arithmeticTheory.NOT_LESS]
QED

Theorem memory_hash_string_input:
  expr_post ctx fn cenv cx e es sa sm s0 es' (StringV str) op s /\
  ptr_val_ok cx (expr_type e) (StringV str) op G tn s /\
  expr_type e = BaseT (StringT cap) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT cap)) ==>
  ?root a b sz.
    op = Var root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s 32 /\ FLOOKUP G root = SOME (b,sz) /\
    b <= w2n a + 32 /\ w2n a + 32 + w2n (n2w (LENGTH str):bytes32) <= b + sz /\
    w2n a + 32 < dimword(:256) /\ mload (w2n a) s = n2w (LENGTH str) /\
    (!i. w2n a <= i /\ i < w2n a + 32 + w2n (n2w (LENGTH str):bytes32) ==>
         i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all hash_string_post_view >> strip_tac >>
  `b < dimword(:256)` by decide_tac >>
  `ptr_mem_ok cx (BaseT (StringT cap)) (StringV str) op G tn s` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  gvs[] >> drule_all ptr_val_ok_string_read_clean >> strip_tac >>
  drule ptr_mem_ok_read_range >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`0`, `32 + LENGTH str`] mp_tac) >>
  simp[val_footprint_def] >> strip_tac >>
  qexistsl_tac [`x`, `n2w b`, `b'`, `sz`] >>
  gvs[eval_operand_def, ptr_val_ok_def, ptr_covers_def, mload_def, mem_word_at_def] >>
  rpt gen_tac >> disch_tac >> Cases_on `i < b + 32` >> gvs[] >>
  metis_tac[arithmeticTheory.NOT_LESS]
QED

Theorem memory_hash_typed_counted:
  expr_post ctx fn cenv cx e es sa sm s0 es' v arg s /\
  ptr_val_ok cx (expr_type e) v arg G tn s /\
  ((?cap bs. expr_type e = BaseT (BytesT (Dynamic cap)) /\ v = BytesV bs /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap)))) \/
   (?cap str. expr_type e = BaseT (StringT cap) /\ v = StringV str /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT cap)))) /\
  compile_method_id_hash (expr_type e) arg sm = (op,sh) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
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
  strip_tac
  >- (gvs[] >> drule_at (Pat `expr_type _ = _`) memory_hash_bytes_input >>
      simp[] >> disch_then drule_all >> strip_tac >>
      gvs[compile_method_id_hash_def] >>
      drule_at (Pat `compile_keccak256_bytes _ _ = _`) memory_hash_compile_counted >>
      disch_then irule >> gvs[] >> metis_tac[]) >>
  gvs[] >> drule_at (Pat `expr_type _ = _`) memory_hash_string_input >>
  simp[] >> disch_then drule_all >> strip_tac >>
  gvs[compile_method_id_hash_def] >>
  drule_at (Pat `compile_keccak256_bytes _ _ = _`) memory_hash_compile_counted >>
      disch_then irule >> gvs[] >> metis_tac[]
QED
