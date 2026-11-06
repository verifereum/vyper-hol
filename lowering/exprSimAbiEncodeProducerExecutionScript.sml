Theory exprSimAbiEncodeProducerExecution
Ancestors
  exprSimAbiEncodePrefixWindow exprSimAbiEncodeExecution
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
