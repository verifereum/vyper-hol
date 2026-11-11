Theory exprSimAbiEncodeProducerExecution
Ancestors
  loweringStateRelDefs
  exprSimAbiEncodePrefixWindow exprSimAbiEncodeExecution
  exprSimAbiEncodeEmptySource exprSimAbiEncodeNonwordResources
  exprSimAbiEncodeCapacity exprSimAbiEncodeEmptyExecution exprSimAbiEncodeSourceRoom
  exprSimAbiEncodeBoundaryProbe exprSimAbiEncodeWindowRoom abiEncoderSourceInvoke
  abiBuiltinEncodeContext abiBuiltinEncodeCode abiDecoderContract abiDecoderReentry
  abiBuiltinAllocation abiEncodeWindowBuiltin abiEncoderCounters
  abiTupleValueEncoding abiEncoderAdmissible exprSimAlloc loweringPosts
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomMemDefs venomState venomInst words finite_map list arithmetic

(* Check operand liveness at the actual staging boundary, rather than
   assuming the encoder operands are live independently. *)
Theorem abi_encode_word_prefix_live:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  abi_builtin_encode_setup mid maxlen sh = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) buf.buf_operand ei ready = (len,body_end) ==>
  abi_decoder_operand_live sh.cs_next_var buf.buf_operand /\
  (!x. buf.buf_operand = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops)
Proof
  strip_tac >>
  drule abi_builtin_encode_setup_outputs >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
   sh.cs_next_var = sa.cs_next_var + 1` by
    gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  `abi_decoder_operand_live body_end.cs_next_var (FST ops)` by
    (irule abi_decoder_operand_live_mono >>
     qexists_tac `ready.cs_next_var` >> simp[]) >>
  Cases_on `mid` >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

(* Resource supplement for the actual word producer. *)
Theorem abi_encode_word_prefix_phase_resources:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es') /\
  evaluate_type_builtin cx (AbiEncode F mid0) (TupleT [expr_type e])
    [expr_type e] [v] = INL result /\
  is_word_type (expr_type e) /\
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (expr_type e))
    sh = (ops,ready) /\
  fn_has_code sa sm func /\ fn_has_code sh ready func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  ?allocated addr ct rv p.
    let staged = mstore (w2n addr) (typed_val_to_w256
      (THE (evaluate_type (get_tenv cx) (expr_type e))) v) allocated in
    let k = case mid of NONE => 0 | SOME _ => 4 in
    let w = case mid of NONE => 0 | SOME _ => 32 in
    let outsz = 32 + 32 * word_size (32+k) in
    let a = abi_builtin_allocate_state sh.cs_next_id outsz staged in
    run_inst_seq (emitted_insts sa sm) s = OK allocated /\
    run_inst_seq (emitted_insts sm sh) allocated = OK staged /\
    stmt_state_rel ctx func ce cx es' staged /\
    eval_operand buf.buf_operand allocated = SOME addr /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e))
      (THE (vyper_to_abi (get_tenv cx) (expr_type e) v)) /\
    LENGTH (enc ct rv) = 32 /\
    abi_encoder_window_input (type_to_abi_enc_info sf ce (expr_type e))
      ct rv (w2n addr) 32 staged.vs_memory /\
    alloca_inv a /\ alloca_room ctx func a /\
    w2n addr+32 <= a.vs_alloca_next /\
    FLOOKUP a.vs_allocas sh.cs_next_id = SOME (p,outsz) /\
    p+(32+k)+32 <= a.vs_alloca_next /\
    venomMemDefs$regions_disjoint (w2n addr,32) (p+(32+k),32) /\
    eval_operand buf.buf_operand staged = SOME addr /\
    FLOOKUP staged.vs_allocas sa.cs_next_id = SOME (w2n addr,32) /\
    ((FLOOKUP staged.vs_allocas sh.cs_next_id = NONE /\ p = staged.vs_alloca_next) \/
      FLOOKUP staged.vs_allocas sh.cs_next_id = SOME (p,outsz)) /\
    outsz < dimword (:256) /\ p < dimword (:256) /\
    (mid <> NONE ==> p+32 < dimword (:256)) /\
    (w2n addr+32 <= p+32 \/ p+32+w <= w2n addr) /\
    venomMemDefs$regions_disjoint (p+32,k) (p+32+k,LENGTH (enc ct rv))
Proof
  strip_tac >> drule_all abi_encode_word_prefix_resources >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qspec_then `sf` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func ce cx es' staged` >>
  `stmt_state_rel ctx func ce cx es' s` by fs[expr_post_def] >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >> gvs[] >>
  `sh.cs_next_id = sa.cs_next_id+2` by
    gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  `eval_operand buf.buf_operand staged = SOME addr /\
   FLOOKUP staged.vs_allocas sa.cs_next_id = SOME (w2n addr,32)` by
    simp[Abbr `staged`, mstore_def, eval_operand_def, lookup_var_def] >>
  qmatch_asmsub_abbrev_tac `alloca_inv a` >>
  `FLOOKUP a.vs_allocas sa.cs_next_id = SOME (w2n addr,32)` by
    simp[Abbr `a`, abi_window_allocate_other_row] >>
  `w2n addr+32 <= p \/
   p+(32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))) <= w2n addr` by
    (fs[alloca_inv_def, allocas_non_overlapping_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`sa.cs_next_id`, `sh.cs_next_id`] mp_tac) >>
     simp[] >> metis_tac[ADD_COMM]) >>
  `a.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  qexistsl [`ct`, `rv`] >>
  simp_tac bool_ss [LET_THM] >>
  `p+32 < dimword (:256)` by decide_tac >>
  `32+32*word_size (32+(case (mid:bytes32 option) of NONE => 0 | SOME _ => 4))
    < dimword (:256)` by
    (Cases_on `mid` >> simp[vfmConstantsTheory.word_size_def, dimword_def]) >>
  unabbrev_all_tac >> asm_rewrite_tac [] >>
  conj_tac
  >- (qpat_x_assum `FLOOKUP (abi_builtin_allocate_state _ _ _).vs_allocas _ = SOME (p,_)` mp_tac >>
      simp[abi_builtin_allocate_state_def, mstore_def] >>
      Cases_on `FLOOKUP allocated.vs_allocas (sa.cs_next_id+2)` >>
      gvs[FLOOKUP_UPDATE]) >>
  Cases_on `mid` >>
  gvs[vfmConstantsTheory.word_size_def, venomMemDefsTheory.regions_disjoint_def] >>
  qpat_x_assum `FLOOKUP (abi_builtin_allocate_state _ _ _).vs_allocas _ = SOME (p,_)` mp_tac >>
  simp[abi_builtin_allocate_state_def, mstore_def] >>
  Cases_on `FLOOKUP allocated.vs_allocas (sa.cs_next_id+2)` >>
  gvs[FLOOKUP_UPDATE]
QED

Theorem abi_encode_word_producer_phases:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es') /\
  evaluate_type_builtin cx (AbiEncode F mid0) (TupleT [expr_type e])
    [expr_type e] [v] = INL result /\
  is_word_type (expr_type e) /\
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (expr_type e))
    sh = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) buf.buf_operand
    (type_to_abi_enc_info sf ce (expr_type e)) ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len
    (case mid of NONE => 0 | SOME _ => 4) body_end = ((),final) /\
  fn_has_code sa sm func /\ fn_has_code sh ready func /\
  fn_has_code sh ready obs /\ fn_has_code ready body_end obs /\
  fn_has_code body_end final obs /\ fn_inst_ids_distinct obs /\
  obs.fn_name = func.fn_name /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
       i.inst_opcode <> NOP ==> MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  ?allocated addr ct rv p.
    let staged = mstore (w2n (addr:bytes32)) (typed_val_to_w256
      (THE (evaluate_type (get_tenv cx) (expr_type e))) v) allocated in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    let w = case mid of NONE => 0 | SOME _ => 32 in
    let outsz = 32+32*word_size (32+m) in
    run_inst_seq (emitted_insts sa sm) s = OK allocated /\
    run_inst_seq (emitted_insts sm sh) allocated = OK staged /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e))
      (THE (vyper_to_abi (get_tenv cx) (expr_type e) v)) /\
    LENGTH (enc ct rv) = 32 /\
    !limit_st.
      ready.cs_next_var <= limit_st.cs_next_var /\
      body_end.cs_next_var <= limit_st.cs_next_var /\
      final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st staged /\
      ~staged.vs_halted /\ staged.vs_current_bb = sh.cs_current_bb /\
      staged.vs_inst_idx = LENGTH sh.cs_current_insts ==>
      ?prepared body actual.
        eval_operand (FST ops) actual = SOME (n2w p) /\
        mload p actual = n2w (32+m) /\
        mem_bytes_at (p+32+m) 32 actual.vs_memory = enc ct rv /\
        (case mid of NONE => T | SOME selector =>
          mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
        ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
        actual.vs_inst_idx = LENGTH final.cs_current_insts /\
        abi_decode_sim ctx obs staged actual /\
        abi_builtin_encode_setup_frame sh.cs_next_var sh.cs_next_id outsz p w staged prepared /\
        window_strong_result (ctx with ctx_functions := [obs]) obs ready body_end len
          ct rv (p+32+m) prepared body /\
        abi_decode_frame p 32 body actual
Proof
  strip_tac >> drule_all abi_encode_word_prefix_phase_resources >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qspec_then `sf`
    (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS))) >>
  qexistsl [`allocated`, `addr`, `ct`, `rv`, `p`] >>
  simp_tac bool_ss [LET_THM] >> asm_rewrite_tac [] >>
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func ce cx es' staged` >>
  `abi_size_bound ce.ce_struct_fields (expr_type e) = 32` by
    metis_tac[abi_encode_word_size_bound] >>
  `abi_encoder_admissible (type_to_abi_enc_info sf ce (expr_type e))` by
    (drule abi_word_metadata >> simp[abi_encoder_admissible_def]) >>
  drule_all abi_encode_word_prefix_live >> strip_tac >>
  drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)
    abi_encode_word_body_no_alloca >> disch_then assume_tac >>
  `!inst. MEM inst (fn_insts obs) /\ inst.inst_id IN frag_ids ready body_end ==>
    inst.inst_opcode <> ALLOCA` by metis_tac[] >>
  drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)
    abi_encode_bridge_phases_open >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_finish _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code ready body_end _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (qspecl_then
    [`case mid of NONE => 0 | SOME _ => 32`, `p`,
     `p+32+(case mid of NONE => 0 | SOME _ => 4)`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      REFL_TAC,
      qpat_assum `abi_size_bound _ _ = 32`
        (fn th => pure_rewrite_tac [th] >> REFL_TAC),
      (pure_rewrite_tac [wordsTheory.n2w_w2n] >> first_assum ACCEPT_TAC),
      qpat_assum `LENGTH (enc ct rv) = 32` (fn length_eq =>
        pure_rewrite_tac [length_eq, GSYM ADD_ASSOC] >>
        first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [length_eq, GSYM ADD_ASSOC])),
      (rpt gen_tac >> strip_tac >>
       qpat_assum `!inst. MEM inst (fn_insts obs) /\ _ ==> _`
         (fn th => drule_all th) >>
       qpat_assum `inst.inst_opcode = ALLOCA`
         (fn th => pure_rewrite_tac [th] >> simp_tac bool_ss []))]) >>
  disch_then (qx_choose_then `prepared` (qx_choose_then `body_state`
    (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  qexistsl [`prepared`, `body_state`, `actual`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    qpat_assum `LENGTH (enc ct rv) = 32` (fn length_eq =>
      first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [length_eq])),
    qpat_assum `LENGTH (enc ct rv) = 32` (fn length_eq =>
      qpat_assum `enc ct rv = _` (fn enc_eq =>
        first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [length_eq, enc_eq])))]
QED

(* The counted unwrap ends in expr_post at sa, retaining origin.  In the
   empty case its actual pointer remains unconstrained by the frontier. *)
Theorem abi_encode_nonword_producer_source_split:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  ~is_word_type (post_value_type ce e) /\
  abi_enc_plan (get_tenv cx) (post_value_type ce e) ei /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (post_value_type ce e) v = SOME av ==>
  ?w ct rv. eval_operand op s = SOME w /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (post_value_type ce e)) av /\
    abi_encoder_window_input ei ct rv (w2n w) (val_footprint tv v) s.vs_memory /\
    ((val_footprint tv v = 0 /\ ei = AbiCopy 0) \/
     (0 < val_footprint tv v /\
      w2n w + val_footprint tv v <= s.vs_alloca_next))
Proof
  strip_tac >> drule_all abi_encode_nonword_expr_window >> strip_tac >>
  drule_all abi_encode_nonword_expr_bound >> strip_tac
  >- (drule_all abi_encode_nonword_zero_plan >> strip_tac >>
      qexistsl [`w`, `ct`, `rv`] >> simp[]) >>
  qexistsl [`w`, `ct`, `rv`] >> simp[] >>
  Cases_on `val_footprint tv v = 0`
  >- metis_tac[abi_encode_nonword_zero_plan] >> simp[]
QED

(* Resources at the actual nonword expression boundary. Empty footprints
   retain the real pointer and impose no endpoint constraint. *)
Theorem abi_encode_nonword_phase_resources:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (lowered_value_type ce e) ei /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
    sa = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) op ei ready = (len,body_end) /\
  fn_has_code sa ready func /\ fn_has_code ready body_end obs /\
  fn_inst_ids_distinct obs /\ fn_inst_ids_distinct func /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\
       j.inst_opcode <> NOP ==> MEM j (fn_insts func)) /\
  local_ptrs_reserved ce sa ==>
  ?w ct rv p.
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    let mw = case mid of NONE => 0 | SOME _ => 32 in
    let outsz = 32+32*word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+m) in
    let a = abi_builtin_allocate_state sa.cs_next_id outsz s in
    eval_operand op s = SOME w /\ enc ct rv = bytes /\
    abi_encoder_window_input ei ct rv (w2n w) (val_footprint tv v) s.vs_memory /\
    ((val_footprint tv v = 0 /\ ei = AbiCopy 0) \/
     (0 < val_footprint tv v /\ w2n w+val_footprint tv v <= s.vs_alloca_next)) /\
    alloca_inv a /\ alloca_room ctx func a /\
    FLOOKUP a.vs_allocas sa.cs_next_id = SOME (p,outsz) /\
    ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,outsz)) /\
    outsz < dimword (:256) /\ p < dimword (:256) /\
    (mid <> NONE ==> p+32 < dimword (:256)) /\
    p+32+m+LENGTH bytes <= a.vs_alloca_next /\
    (0 < val_footprint tv v ==>
      w2n w+val_footprint tv v <= a.vs_alloca_next /\
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (p+32+m,LENGTH bytes) /\
      (w2n w+val_footprint tv v <= p+32 \/ p+32+mw <= w2n w)) /\
    venomMemDefs$regions_disjoint (p+32,m) (p+32+m,LENGTH bytes) /\
    (!inst b sz. MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids ready body_end /\
      FLOOKUP a.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32+m,LENGTH bytes) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32,m) (b,sz))
Proof
  strip_tac >>
  drule_all abiEncodeMaterializeTheory.materialize_expr_post_lowered_source >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  drule_all abiEncoderSourceFootprintTheory.abi_encoder_source_footprint >> strip_tac >>
  drule abiEncoderWindowTheory.abi_encoder_open_input_window >> strip_tac >>
  drule_all abi_encode_post_lowered_footprint >>
  disch_then (qx_choose_then `ptv` strip_assume_tac) >>
  `val_footprint tv v = 0 /\ ei = AbiCopy 0 \/
   0 < val_footprint tv v /\ w2n w + val_footprint tv v <= s.vs_alloca_next` by
    (drule_all abi_encode_nonword_expr_bound >>
     qpat_assum `val_footprint ptv v = _` (fn th => rewrite_tac[th]) >>
     strip_tac >- metis_tac[abi_encode_zero_footprint_plan] >>
     Cases_on `val_footprint tv v = 0` >>
     metis_tac[abi_encode_zero_footprint_plan, arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    metis_tac[optionTheory.IS_SOME_EXISTS,
      exprSimHypsTheory.expr_body_pre_type_evaluates] >>
  `vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_conversion] >>
  `vyper_to_abi_type (get_tenv cx) (expr_type e) =
    vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_abi_type] >>
  drule_all abi_encode_nonword_numerical_capacity >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `(case mid0 of NONE => 0 | SOME _ => 4) =
   (case mid of NONE => 0 | SOME _ => 4)` by
    (Cases_on `mid0` >> fs[]) >>
  `(case mid0 of NONE => 0 | SOME _ => 32) =
   (case mid of NONE => 0 | SOME _ => 32)` by
    (Cases_on `mid0` >> fs[]) >>
  qpat_assum `(case mid0 of NONE => 0 | SOME _ => 4) = _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_assum `(case mid0 of NONE => 0 | SOME _ => 32) = _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `mid = OPTION_MAP _ _` kall_tac >>
  qpat_x_assum `(case mid of NONE => 0 | SOME _ => 4) = _` kall_tac >>
  qpat_x_assum `(case mid of NONE => 0 | SOME _ => 32) = _` kall_tac >>
  `0 < val_footprint tv v ==> w2n w+val_footprint tv v <= s.vs_alloca_next` by
    (simp[]) >>
  `0 < val_footprint ptv v ==> w2n w+val_footprint ptv v <= s.vs_alloca_next` by
    metis_tac[] >>
  drule_all abi_encode_nonword_setup_output >>
  qpat_assum `val_footprint ptv v = _` (fn th => rewrite_tac[th]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `alloca_inv (abi_builtin_allocate_state _ outsz _)` >>
  qmatch_asmsub_abbrev_tac `alloca_inv a` >>
  `((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
     FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,outsz))` by
    (qpat_x_assum `FLOOKUP a.vs_allocas _ = _` mp_tac >>
     simp[Abbr `a`, abi_builtin_allocate_state_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> gvs[FLOOKUP_UPDATE]) >>
  (`s.vs_alloca_next <= a.vs_alloca_next` by
    (simp[Abbr `a`, abi_builtin_allocate_state_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[]) >>
  `p < dimword (:256) /\ (mid <> NONE ==> p+32 < dimword (:256)) /\
   p+32+(case mid of NONE => 0 | SOME _ => 4)+
     LENGTH (enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av) <= a.vs_alloca_next` by
    (fs[Abbr `outsz`] >> gvs[]) >>
  `0 < val_footprint tv v ==>
    w2n w+val_footprint tv v <= a.vs_alloca_next /\
    venomMemDefs$regions_disjoint (w2n w,val_footprint tv v)
      (p+32+(case mid of NONE => 0 | SOME _ => 4),
       LENGTH (enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av)) /\
    (w2n w+val_footprint tv v <= p+32 \/
     p+32+(case mid of NONE => 0 | SOME _ => 32) <= w2n w)` by
    (strip_tac >> Cases_on `mid` >>
     fs[Abbr `outsz`, venomMemDefsTheory.regions_disjoint_def] >> gvs[]) >>
  qexistsl [`w`, `ct`, `rv`, `p`] >> simp_tac bool_ss [LET_THM] >>
  unabbrev_all_tac >> asm_rewrite_tac [] >>
  conj_tac >- simp[venomMemDefsTheory.regions_disjoint_def] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`) abi_encode_nonword_scratch_row >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (b,sz)`)) >>
  disch_then (qspecl_then [`w`, `ptv`, `obs`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac []) >>
  qpat_assum `val_footprint ptv v = _` (fn th => rewrite_tac[th]) >> strip_tac >>
  drule_all abi_encode_setup_scratch_slices >>
  strip_tac >> asm_rewrite_tac [] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (p+32,_) (b,sz)` mp_tac >>
  qpat_x_assum `venomMemDefs$regions_disjoint (p+32+_,_) (b,sz)` mp_tac >>
  Cases_on `mid` >> simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac)
QED


local
  (* Eliminate only reflexive aliases; the general simplifier is expensive here. *)
  val bytes_phases = abi_encode_bridge_bytes_phases_open |> SPEC_ALL
    |> Q.INST [`d` |-> `p+32+m`, `outsz` |-> `32+32*word_size(maxlen+m)`]
    |> Q.INST [`m` |-> `(case method_id of NONE => 0 | SOME mid => 4)`,
               `w` |-> `(case method_id of NONE => 0 | SOME mid => 32)`]
    |> PURE_REWRITE_RULE [REFL_CLAUSE, IMP_CLAUSES, AND_CLAUSES];
  val empty_phases = abi_encode_empty_phases_open |> SPEC_ALL
    |> Q.INST [`d` |-> `p+32+m`, `outsz` |-> `32+32*word_size(maxlen+m)`]
    |> Q.INST [`m` |-> `(case method_id of NONE => 0 | SOME mid => 4)`,
               `w` |-> `(case method_id of NONE => 0 | SOME mid => 32)`]
    |> PURE_REWRITE_RULE [REFL_CLAUSE, IMP_CLAUSES, AND_CLAUSES];
in
Theorem abi_encode_nonword_producer_phases:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (lowered_value_type ce e) ei /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
    sa = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) op ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len
    (case mid of NONE => 0 | SOME _ => 4) body_end = ((),final) /\
  fn_has_code sa ready func /\ fn_has_code sa ready obs /\
  fn_has_code ready body_end obs /\ fn_has_code body_end final obs /\
  fn_inst_ids_distinct obs /\ fn_inst_ids_distinct func /\
  obs.fn_name = func.fn_name /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\
       j.inst_opcode <> NOP ==> MEM j (fn_insts func)) /\
  (!j. MEM j (fn_insts obs) ==> j.inst_opcode <> INVOKE) /\
  local_ptrs_reserved ce sa /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  ?p. !limit_st.
    ready.cs_next_var <= limit_st.cs_next_var /\
    body_end.cs_next_var <= limit_st.cs_next_var /\
    final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?actual.
      let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
      let m = case mid of NONE => 0 | SOME _ => 4 in
      eval_operand (FST ops) actual = SOME (n2w p) /\
      mload p actual = n2w (LENGTH bytes+m) /\
      mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
      (case mid of NONE => T | SOME selector =>
        mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
      ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
      actual.vs_inst_idx = LENGTH final.cs_current_insts /\
      abi_decode_sim ctx obs s actual
Proof
  strip_tac >> drule_all abi_encode_nonword_phase_resources >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `source_word` (qx_choose_then `ct` (qx_choose_then `rv`
    (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  qexists `p` >> rpt strip_tac >> simp_tac bool_ss [LET_THM] >>
  `abi_encoder_admissible ei` by metis_tac[abi_enc_plan_admissible] >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `abi_decoder_operand_live sa.cs_next_var op` by
    (qpat_assum `!x. op = Var x ==> _` mp_tac >> Cases_on `op` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `abi_decoder_operand_live ready.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists `sa.cs_next_var` >>
     conj_tac
     >- (qpat_assum `ready.cs_next_var = _` (fn th => rewrite_tac[th]) >>
         Cases_on `mid` >> simp_tac (srw_ss()) []) >>
     first_assum ACCEPT_TAC) >>
  `(!x. op = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
   (!x. FST ops = Var x ==> not_fresh_at ready x) /\
   abi_decoder_operand_live body_end.cs_next_var (FST ops)` by
    (conj_tac
     >- (rpt strip_tac
         >- (qpat_assum `abi_decoder_operand_live ready.cs_next_var op` mp_tac >>
             qpat_assum `op = Var x` (fn th => rewrite_tac[th]) >>
             simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
               not_fresh_at_def])
         >> qpat_assum `abi_decoder_operand_live ready.cs_next_var (SND ops)` mp_tac >>
         qpat_assum `SND ops = Var x` (fn th => rewrite_tac[th]) >>
         simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `abi_decoder_operand_live ready.cs_next_var (FST ops)` mp_tac >>
         qpat_assum `FST ops = Var x` (fn th => rewrite_tac[th]) >>
         simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
     irule abi_decoder_operand_live_mono >> qexists `ready.cs_next_var` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `val_footprint tv v = 0`
  >- suspend "empty"
  >> suspend "positive"
QED

Resume abi_encode_nonword_producer_phases[positive]:
  `0 < val_footprint tv v` by decide_tac >>
  qpat_assum `0 < val_footprint tv v ==> _` mp_tac >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`) bytes_phases >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code body_end final _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `enc _ _ = _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  impl_tac
  >- (rewrite_tac[wordsTheory.n2w_w2n] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexists `actual` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_nonword_producer_phases[empty]:
  `ei = AbiCopy 0` by
    (qpat_assum `val_footprint tv v = 0 /\ _ \/ _` mp_tac >>
     qpat_assum `val_footprint tv v = 0` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) []) >>
  qpat_x_assum `ei = AbiCopy 0` SUBST_ALL_TAC >>
  qpat_assum `val_footprint tv v = 0` (fn zero =>
    qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _`
      (assume_tac o PURE_REWRITE_RULE [zero])) >>
  `alloca_room (ctx with ctx_functions := [obs]) obs
    (abi_builtin_allocate_state sa.cs_next_id
      (32+32*word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) +
        (case mid of NONE => 0 | SOME _ => 4))) s)` by
    (irule abi_encode_bridge_local_room >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists `func` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`) empty_phases >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  disch_then (qspec_then `final` mp_tac) >>
  qpat_assum `enc ct rv = _` (fn eq => rewrite_tac[eq]) >>
  impl_tac
  >- (reverse (rpt conj_tac)
      >- (rpt strip_tac >>
          qpat_assum `!inst b sz. MEM inst _ /\ _ ==> _`
            (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
          simp_tac bool_ss [] >> metis_tac[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  `abi_decode_sim ctx obs s actual` by
    (irule abi_decode_sim_ctx_no_invoke >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists `ctx with ctx_functions := [obs]` >> first_assum ACCEPT_TAC) >>
  qexists `actual` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise abi_encode_nonword_producer_phases
end
