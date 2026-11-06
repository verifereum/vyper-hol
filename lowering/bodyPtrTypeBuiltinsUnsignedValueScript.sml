(* Robust source-value boundary; annotation and lowered capacity stay distinct. *)
Theory bodyPtrTypeBuiltinsUnsignedValue
Ancestors
  bodyPtrTypeBuiltinsUnsignedCompose bodyPtrTypeBuiltinsBytesRead
  bodyPtrTypeBuiltinsHeaderLoad valueEncodingProps bodyPtrDefs
  venomState valueEncoding exprLoweringProps exprLowering compileEnv
  arithmetic finite_map representationCleanPtr

Theorem unsigned_bytes_value_source_facts:
  ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn s /\
  ptr_buf_ok cenv e (Var src) G s /\ op_taint tn (Var src) = {} /\
  lookup_var src s = SOME a /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k))) /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) ==>
  ptr_covers G tn src s (type_memory_bytes cenv (lowered_value_type cenv e)) /\
  mload (w2n a) s = n2w (LENGTH bs) /\
  (!x. w2n a <= x /\ x < w2n a+32+LENGTH bs ==> x NOTIN tn.t_mem)
Proof
  strip_tac >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  conj_tac
  >- (irule ptr_buf_ok_covers >> simp[] >> qexistsl_tac [`cenv`,`e`] >> simp[]) >>
  conj_tac
  >- (drule_all ptr_mem_ok_bytes_length >> simp[mem_word_at_eq_mload]) >>
  `!x. w2n a <= x /\ x < w2n a+32 ==> x NOTIN tn.t_mem` by
    metis_tac[ptr_mem_ok_bytes_header_clean] >>
  `!x. w2n a+32 <= x /\ x < w2n a+32+LENGTH bs ==> x NOTIN tn.t_mem` by
    (mp_tac (GEN_ALL (Q.INST [`off` |-> `0:num`, `n` |-> `LENGTH bs`]
       (SPEC_ALL ptr_mem_ok_bytes_window_clean))) >> simp[] >> metis_tac[]) >>
  gen_tac >> disch_then strip_assume_tac >>
  Cases_on `x < w2n a+32` >> metis_tac[arithmeticTheory.NOT_LESS]
QED

Theorem unsigned_loader_from_bytes_value:
  load_bytestring_as_word (Var src) SHR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_var src s = SOME a /\
  ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn s /\
  ptr_buf_ok cenv e (Var src) G s /\ op_taint tn (Var src) = {} /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k))) /\
  LENGTH bs <= 32 /\ 64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  w2n a+32 < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx+6)) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    op_prov H bits = NONE /\ op_taint th bits = {} /\
    eval_operand bits t = SOME (n2w (8*(32-LENGTH bs))) /\
    ghost_inv d cenv cx es H th (t with vs_inst_idx := s.vs_inst_idx+6) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (t with vs_inst_idx := s.vs_inst_idx+6) =
      s with <|vs_vars := t.vs_vars; vs_inst_idx := s.vs_inst_idx+6|> /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all unsigned_bytes_value_source_facts >> strip_tac >>
  drule_all unsigned_loader_counted_ghost_frame >> simp[]
QED

Theorem unsigned_string_value_source_facts:
  ptr_mem_ok cx (expr_type e) (StringV str) (Var src) G tn s /\
  ptr_buf_ok cenv e (Var src) G s /\ op_taint tn (Var src) = {} /\
  lookup_var src s = SOME a /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) ==>
  ptr_covers G tn src s (type_memory_bytes cenv (lowered_value_type cenv e)) /\
  mload (w2n a) s = n2w (LENGTH str) /\
  (!x. w2n a <= x /\ x < w2n a+32+LENGTH str ==> x NOTIN tn.t_mem)
Proof
  strip_tac >> conj_tac
  >- (irule ptr_buf_ok_covers >> simp[] >> qexistsl_tac [`cenv`,`e`] >> simp[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv (StringV str) (w2n a) mem` by
    gvs[ptr_mem_ok_def, eval_operand_def] >>
  `val_in_memory tv (StringV str) (w2n a) s.vs_memory` by
    metis_tac[mem_agree_outside_def] >>
  conj_tac >- fs[val_in_memory_def, mem_word_at_eq_mload] >>
  drule_all robust_val_in_memory_string_clean >> strip_tac >>
  gen_tac >> disch_then strip_assume_tac >>
  Cases_on `x < w2n a+32` >> metis_tac[arithmeticTheory.NOT_LESS]
QED

Theorem unsigned_loader_from_string_value:
  load_bytestring_as_word (Var src) SHR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_var src s = SOME a /\
  ptr_mem_ok cx (expr_type e) (StringV str) (Var src) G tn s /\
  ptr_buf_ok cenv e (Var src) G s /\ op_taint tn (Var src) = {} /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  LENGTH str <= 32 /\ 64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  w2n a+32 < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx+6)) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    op_prov H bits = NONE /\ op_taint th bits = {} /\
    eval_operand bits t = SOME (n2w (8*(32-LENGTH str))) /\
    ghost_inv d cenv cx es H th (t with vs_inst_idx := s.vs_inst_idx+6) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (t with vs_inst_idx := s.vs_inst_idx+6) =
      s with <|vs_vars := t.vs_vars; vs_inst_idx := s.vs_inst_idx+6|> /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all unsigned_string_value_source_facts >> strip_tac >>
  drule_all unsigned_loader_counted_ghost_frame >> simp[]
QED
