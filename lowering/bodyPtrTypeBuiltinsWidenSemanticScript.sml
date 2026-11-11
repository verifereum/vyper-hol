Theory bodyPtrTypeBuiltinsWidenSemantic
Ancestors
  bodyPtrTypeBuiltinsWidenCounted exprSimConvert bodyPtrDefs
  exprLoweringProps venomState compileEnv vyperTyping vyperValueOperation
  vyperTypeSystem abiDecoderString valueEncoding valueEncodingDefs words vyperValue

Theorem convert_bytestring_robust_memory:
  is_bytestring_type tsrc /\ is_bytestring_type tdst /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\
  evaluate_type (get_tenv cx) tdst = SOME tv2 /\
  value_has_type tv v /\ convert_result cx tsrc tdst v = INL v' /\
  (!m. mem_agree_outside bad mem m ==> val_in_memory tv v off m) ==>
  !m. mem_agree_outside bad mem m ==> val_in_memory tv2 v' off m
Proof
  strip_tac >> rpt strip_tac >>
  `val_in_memory tv v off m` by metis_tac[] >>
  Cases_on `tsrc` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bs)` >>
  Cases_on `bs` >> gvs[is_bytestring_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >>
       Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  Cases_on `tdst` >> gvs[is_bytestring_type_def] >>
  rename1 `evaluate_type _ (BaseT bt) = SOME tv2` >>
  Cases_on `bt` >> gvs[is_bytestring_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >>
       Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  Cases_on `v` >>
  gvs[evaluate_type_def, value_has_type_def, convert_result_def,
      evaluate_convert_from_def, evaluate_convert_def, val_in_memory_def,
      abi_decoder_string_bytes_roundtrip, AllCaseEqs()]
QED

Theorem widen_copy_converted_counted_certificate:
  compile_bytestring_widen_copy capacity (Var src) n sa = (op,sb) /\
  fn_has_code sa sb fn /\ run_inst_seq (emitted_insts sa sb) s0 = OK t /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ capacity < dimword(:256) /\ n <= capacity /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  expr_val_at cenv cx tsrc slo sa es v (Var src) s0 /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ ~is_word_type tsrc /\
  val_wf tv v /\ val_footprint tv v <= n /\ lookup_var src s0 = SOME a /\
  ptr_covers G0 tn0 src s0 n /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==> val_in_memory tv v (w2n a) m) /\
  ~s0.vs_halted /\ lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s0.vs_inst_idx bb.bb_instructions) /\
  is_bytestring_type tsrc /\ is_bytestring_type tdst /\
  evaluate_type (get_tenv cx) tdst = SOME tv2 /\ value_has_type tv v /\
  convert_result cx tsrc tdst v = INL v' ==>
  ?dst b G th. op = Var dst /\
    gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 G th
      (OK (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    lookup_var dst (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb)) = SOME b /\
    ptr_covers G th dst (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb)) capacity /\
    ghost_inv d cenv cx es G th (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    ghost_kept cenv es sa G0 tn0 s0 G th /\
    (!m. mem_agree_outside th.t_mem t.vs_memory m ==> val_in_memory tv2 v' (w2n b) m)
Proof
  strip_tac >> drule_all widen_copy_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`dst`,`b`,`G`,`th`] >> simp[] >>
  qpat_assum `convert_result _ _ _ _ = _`
    (mp_then Any mp_tac convert_bytestring_robust_memory) >>
  disch_then (fn h => qpat_assum `evaluate_type _ tdst = _`
    (mp_then Any mp_tac h)) >>
  simp[] >> metis_tac[]
QED
