Theory bodyPtrTypeBuiltinsCastSemantic
Ancestors
  bodyPtrTypeBuiltinsCast bodyPtrTypeBuiltinsWidenSemantic
  exprLoweringProps bodyPtrDefs venomState

Theorem convert_cast_converted_counted_certificate:
  compile_type_convert (Var src) (ConvBytestringCast n i) sa = (out,sb) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ptr_covers G tn src s sz /\ 32 <= sz /\ lookup_var src s = SOME w /\
  not_fresh_at sa src /\
  (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p z. cenv.ce_return_buf = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  (!p z. cenv.ce_return_pc = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  is_bytestring_type tsrc /\ is_bytestring_type tdst /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\
  evaluate_type (get_tenv cx) tdst = SOME tv2 /\ value_has_type tv v /\
  convert_result cx tsrc tdst v = INL v' /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
  out = Var src /\ ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    ghost_inv d cenv cx es H th t /\ ghost_kept cenv es sa G tn s H th /\
    ptr_covers H th src t sz /\ t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    (!m. mem_agree_outside th.t_mem t.vs_memory m ==> val_in_memory tv2 v' (w2n w) m)
Proof
  strip_tac >> drule_all convert_cast_success_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >> simp[] >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  qpat_assum `convert_result _ _ _ _ = _`
    (mp_then Any mp_tac convert_bytestring_robust_memory) >>
  disch_then (fn h => qpat_assum `evaluate_type _ tdst = _`
    (mp_then Any mp_tac h)) >> simp[] >> metis_tac[]
QED
