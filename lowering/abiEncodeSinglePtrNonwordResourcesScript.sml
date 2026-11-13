(* Phase-ready resources for an unstaged memory argument.  The uniform
   translation is supplied by the caller, independently of source geometry. *)
Theory abiEncodeSinglePtrNonwordResources
Ancestors
  abiEncodeSinglePtrSource exprSimAbiEncodeTranslatedResources
  exprSimAbiEncodeTranslatedNoBlock exprSimAbiEncodeObserverEntry
  exprSimAbiEncodeCapacity exprSimAbiEncodeArgsPhysicalCapacity
  exprSimAbiEncodeNonwordResult abiEncoderCounters abiBuiltinEncodeCode
  bodyPtrDefs exprLoweringProps compileEnv words venomMemDefs

Theorem abi_encode_single_nonword_phase_resources:
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es origin st s0 ee v src s /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  ptr_val_ok cx (post_value_type ce e) v src G tn s /\
  eval_operand src s = SOME a /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e) /\
  maxlen = abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  m = (case mid of NONE => 0 | SOME _ => 4) /\
  mw = (case mid of NONE => 0 | SOME _ => 32) /\
  outsz = 32+32*word_size (maxlen+m) /\
  enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei ct rv (w2n a) (val_footprint tv v) mem) /\
  abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce st /\
  (!x. src = Var x ==> not_fresh_at st x) ==>
  ?p.
    abi_encoder_admissible ei /\ op_taint tn src = {} /\
    (0 < val_footprint tv v ==>
      (?x. src = Var x /\ ptr_covers G tn x s (val_footprint tv v)) /\
      w2n a+val_footprint tv v <= s.vs_alloca_next) /\
    (val_footprint tv v = 0 ==> (ei = AbiCopy 0 \/ ei = AbiComplex []) /\ enc ct rv = []) /\
    alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz s) /\
    alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz s) /\
    ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas st.cs_next_id = SOME(p,outsz)) /\
    outsz < dimword (:256) /\ p < dimword (:256) /\
    (mid <> NONE ==> p+32 < dimword (:256)) /\
    p+32+m+LENGTH(enc ct rv) <=
      (abi_builtin_allocate_state st.cs_next_id outsz s).vs_alloca_next /\
    (0 < val_footprint tv v ==>
      w2n a+val_footprint tv v <=
        (abi_builtin_allocate_state st.cs_next_id outsz s).vs_alloca_next /\
      venomMemDefs$regions_disjoint (w2n a,val_footprint tv v)
        (p+32+m,LENGTH(enc ct rv)) /\
      (w2n a+val_footprint tv v <= p+32 \/ p+32+mw <= w2n a)) /\
    venomMemDefs$regions_disjoint (p+32,m) (p+32+m,LENGTH(enc ct rv)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids ready body_end /\
      FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz s).vs_allocas inst.inst_id = SOME(b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (w2n a,val_footprint tv v) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32+m,LENGTH(enc ct rv)) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32,m) (b,sz)) /\
    LENGTH(enc ct rv) <= maxlen /\ 32+mw <= outsz /\
    p+32+m+LENGTH(enc ct rv) <= p+outsz /\
    abi_decoder_operand_live st.cs_next_var src /\
    (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
    (!x. FST ops = Var x ==> not_fresh_at ready x) /\
    abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
    st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var
Proof
  strip_tac >>
  drule_all abi_encode_nonword_source_resources >> strip_tac >>
  `!j. MEM j (fn_insts func) /\ j.inst_opcode <> STOP /\
    j.inst_opcode <> NOP ==> MEM j (fn_insts func)` by simp[] >>
  qpat_x_assum `maxlen = _` SUBST_ALL_TAC >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    metis_tac[exprSimHypsTheory.expr_body_pre_type_evaluates,
      optionTheory.IS_SOME_EXISTS] >>
  `vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[abi_args_fits_conversion] >>
  `vyper_to_abi_type (get_tenv cx) (expr_type e) =
    vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)` by
    metis_tac[abi_args_fits_abi_type] >>
  drule_all abi_encode_nonword_numerical_capacity >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_translated_nonword_phase_resources >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_translated_operand_liveness >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `w = a /\ w' = a` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `!j. MEM j (fn_insts func) /\ _ ==> MEM j (fn_insts func)` kall_tac >>
  qpat_x_assum `w = a` SUBST_ALL_TAC >>
  qpat_x_assum `w' = a` SUBST_ALL_TAC >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  qpat_x_assum `m = _` SUBST_ALL_TAC >>
  qpat_x_assum `mw = _` SUBST_ALL_TAC >>
  qpat_assum `enc ct rv = _` (fn th => pure_rewrite_tac [th]) >>
  qexists `p` >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, asm_rewrite_tac []] >>
  qpat_assum `enc ct' rv' = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_assum `vyper_to_abi_type _ (expr_type e) = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `mid = _` SUBST_ALL_TAC >>
  Cases_on `mid0` >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [optionTheory.OPTION_MAP_DEF,
    optionTheory.option_CLAUSES]) >>
  pure_rewrite_tac [optionTheory.OPTION_MAP_DEF, optionTheory.option_CLAUSES] >>
  RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
  FIRST [first_assum ACCEPT_TAC,
    (sym_tac >> first_assum ACCEPT_TAC), all_tac] >>
  rpt (qpat_x_assum `_ <= _` mp_tac) >>
  rpt (qpat_x_assum `ready.cs_next_var = _` mp_tac) >>
  simp_tac arith_ss [] >> rpt strip_tac >>
  qpat_x_assum `0 < val_footprint tv v` mp_tac >>
  qpat_x_assum `val_footprint tv v = 0` SUBST_ALL_TAC >>
  simp_tac arith_ss []
QED
