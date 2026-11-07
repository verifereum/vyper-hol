(* Shared SHR/SHL interface for dynamic bytes and String fixed-byte results. *)
Theory bodyPtrTypeBuiltinsFixedContinue
Ancestors bodyPtrTypeBuiltinsUintContinue bodyPtrTypeBuiltinsUnsignedValue
  bodyPtrTypeBuiltinsUnsignedSemantics bodyPtrTypeBuiltinsScalarArithmetic
  exprLowering exprLoweringProps builtinConvertPrefix emitHelperProps
  compileEnv vyperTypeSystem vyperValue venomExecSemantics venomState venomInst
  fragExec finite_map list bodyPtrTypeBuiltinsSourceFrame
  fragGasPathPtr ptrDiscipline opcodeClass instIdxIndep arithmetic
  bodyPtrTypeBuiltinsUintCounted bodyPtrTypeBuiltinsUnsignedLoad rich_list
  freshWrites varsExt convertScalarEncoding exprSimConvert
  vyperTyping vyperValueOperation valueEncoding valueEncodingProofs byte words
  exprSimDefs loweringPosts

Theorem dynamic_scalar_conversion_partition:
  is_bytestring_type src /\ valid_conversion src dst /\
  ~is_bytestring_type dst /\ (!b. dst <> BaseT (IntT b)) /\ dst <> BaseT DecimalT ==>
  (?n. src = BaseT (BytesT (Dynamic n)) /\
       ((?b. dst = BaseT (UintT b)) \/ dst = BaseT BoolT \/
        dst = BaseT AddressT \/ (?m. dst = BaseT (BytesT (Fixed m))))) \/
  (?n m. src = BaseT (StringT n) /\ dst = BaseT (BytesT (Fixed m)))
Proof
  Cases_on `src` >> gvs[is_bytestring_type_def] >>
  Cases_on `b` >> gvs[is_bytestring_type_def] >>
  Cases_on `dst` >> gvs[valid_conversion_def, is_bytestring_type_def] >>
  Cases_on `b` >> gvs[valid_conversion_def, is_bytestring_type_def] >>
  Cases_on `b'` >> gvs[valid_conversion_def, is_bytestring_type_def] >>
  Cases_on `b''` >> gvs[valid_conversion_def, is_bytestring_type_def]
QED

Theorem bytestring_fixed_convert_parts:
  compile_type_convert x (ConvBytestringToBytesM m) sa = (out,sb) ==>
  ?word bits sm.
    load_bytestring_as_word x SHR sa = ((word,bits),sm) /\
    emitHelper$emit_op SHL [bits;word] sm = (out,sb) /\
    inst_extends sa sm /\ inst_extends sm sb
Proof
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def, comp_return_def,
                   LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[inst_extends_load_bytestring_as_word, inst_extends_emit_op]
QED

Theorem fixed_shl_run_actual:
  emitHelper$emit_op SHL [bits;word] sa = (out,sb) /\
  eval_operand bits s = SOME k /\ eval_operand word s = SOME w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME (word_lsl w (w2n k)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id SHL [bits;word]
     [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (word_lsl w (w2n k)) s)` by (irule step_SHL >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (word_lsl w (w2n k)) s)` by simp[run_inst_seq_def] >>
  `MEM SHL [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_emit_runtime_frame >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* The suffix is shared by Bytes and String; it consumes only the loader's
   clean word/count packet, not any source representation internals. *)
Theorem fixed_shl_counted_frame:
  emitHelper$emit_op SHL [bits;word] sa = (out,sb) /\
  op_prov G bits = NONE /\ op_prov G word = NONE /\
  op_taint tn bits = {} /\ op_taint tn word = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    ghost_inv d cenv cx es H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `MEM SHL [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_emit_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all scalar_emit_runtime_frame >> strip_tac >>
  `ghost_kept cenv es0 s0a G0 tn0 s0 H th` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`tn`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient` by
    (qpat_x_assum `(_ with vs_vars := _) = _` (fn eq =>
      map_every (fn q => mp_tac (Q.AP_TERM q eq))
        [`\v. v.vs_memory`,`\v. v.vs_call_ctx`,
         `\v. v.vs_accounts`,`\v. v.vs_transient`]) >> simp[]) >>
  `ghost_inv d cenv cx es H th
     (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`s`,`tn`] >>
     gs[lookup_var_def] >> metis_tac[]) >>
  qexistsl_tac [`H`,`th`] >> simp[]
QED

Theorem bytestring_fixed_counted_success:
  compile_type_convert (Var src) (ConvBytestringToBytesM m) sa = (out,sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_has_code sa sb fn /\ lookup_var src s = SOME a /\
  ptr_covers G tn src s capacity /\ 64 <= capacity /\
  w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    ghost_inv d cenv cx es H th (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule bytestring_fixed_convert_parts >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    metis_tac[unsigned_loader_shape_fresh] >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (qpat_x_assum `emitHelper$emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, comp_bind_def, comp_return_def,
          comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  drule_all fn_code_emitted_parts >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sm) s = OK u /\
       run_inst_seq (emitted_insts sm sb) u = OK t` by
    metis_tac[bodyPtrTypeBuiltinsScalarComposeTheory.scalar_seq_append_ok_iff] >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  drule_all bodyPtrTypeBuiltinsUnsignedComposeTheory.unsigned_loader_counted_ghost_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `LENGTH (emitted_insts sa sm) = 6` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >> simp[]) >>
  suspend "suffix"
QED

Resume bytestring_fixed_counted_success[suffix]:
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `u with vs_inst_idx := _ = _` mp_tac >>
     disch_then (fn th => map_every mp_tac
       [Q.AP_TERM `\v. v.vs_current_bb` th, Q.AP_TERM `\v. v.vs_halted` th]) >>
     simp[]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >>
     simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >> simp[]) >>
  `run_inst_seq (emitted_insts sm sb) (u with vs_inst_idx := s.vs_inst_idx+6) =
     OK (t with vs_inst_idx := s.vs_inst_idx+6)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
       (drule emitted_insts_emit_op >> strip_tac >> simp[mk_inst_def, is_terminator_def]) >>
     qpat_x_assum `u with vs_inst_idx := _ = _` kall_tac >>
     simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  `lookup_block (u with vs_inst_idx := s.vs_inst_idx+6).vs_current_bb
    fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb)
    (DROP (u with vs_inst_idx := s.vs_inst_idx+6).vs_inst_idx bb.bb_instructions) /\
   ~(u with vs_inst_idx := s.vs_inst_idx+6).vs_halted` by gs[] >>
  qpat_x_assum `run_inst_seq (emitted_insts sm sb) u = _` kall_tac >>
  qpat_x_assum `u with vs_inst_idx := _ = _` kall_tac >>
  `s0a.cs_next_var <= sm.cs_next_var` by decide_tac >>
  `(!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by metis_tac[] >>
  drule_all fixed_shl_counted_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >> gs[] >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx+6+LENGTH (emitted_insts sm sb)` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H' th'
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all gas_path_ptr_then >> gs[]) >>
  qexistsl_tac [`H'`,`th'`] >> simp[] >>
  conj_tac
  >- (drule emitted_insts_emit_op >> strip_tac >>
      `MEM SHL [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
      drule_all scalar_emit_runtime_frame >> strip_tac >>
      qpat_x_assum `(_ with vs_vars := _) = _` mp_tac >>
      disch_then (mp_tac o Q.AP_TERM `\v. v.vs_current_bb`) >> simp[]) >>
  fs[lookup_var_def] >> metis_tac[]
QED

Finalise bytestring_fixed_counted_success

Theorem bytestring_fixed_raw_exact:
  compile_type_convert op (ConvBytestringToBytesM m) sa = (out,sb) /\
  eval_operand op ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= 32 /\ w2n (a+32w) = w2n a+32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a+32) (LENGTH bs) ss.vs_memory = bs ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand out sf = SOME (word_of_bytes_be bs:bytes32)
Proof
  strip_tac >> drule bytestring_fixed_convert_parts >> strip_tac >>
  drule_all unsigned_load_word_decoded_exact >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  drule_all fixed_shl_run_actual >> strip_tac >>
  `w2n (n2w (8*(32-LENGTH bs)):bytes32) = 8*(32-LENGTH bs)` by
    (simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >> decide_tac) >>
  `eval_operand out t = SOME (word_of_bytes_be bs:bytes32)` by
    metis_tac[unsigned_payload_left_align] >>
  qexists_tac `t` >> simp[] >>
  irule run_inst_seq_compose_ok >> qexistsl_tac [`u`,`sm`] >> simp[]
QED

Theorem bytestring_fixed_code_frame:
  compile_type_convert op (ConvBytestringToBytesM m) sa = (r,sb) ==>
  EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
             EVERY (\x. ~not_fresh_at sa x) i.inst_outputs)
        (emitted_insts sa sb)
Proof
  simp[compile_type_convert_def, load_bytestring_as_word_def,
       emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, fresh_write_op_def, not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >> decide_tac
QED

Theorem bytestring_fixed_run_frame:
  compile_type_convert op (ConvBytestringToBytesM m) sa = (r,sb) /\
  run_inst_seq (emitted_insts sa sb) ss = OK sf ==>
  sf = ss with vs_vars := sf.vs_vars /\
  (!z. not_fresh_at sa z ==> FLOOKUP sf.vs_vars z = FLOOKUP ss.vs_vars z)
Proof
  strip_tac >> drule bytestring_fixed_code_frame >> strip_tac >>
  drule_all bodyPtrTypeBuiltinsUintActualTheory.readonly_run_frame >> simp[]
QED

Theorem bytestring_fixed_replay:
  compile_type_convert op (ConvBytestringToBytesM m) sa = (r,sb) ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa ss))
    (run_inst_seq (emitted_insts sa sb) ss)
Proof
  strip_tac >> drule bytestring_fixed_code_frame >> disch_tac >>
  irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
  gvs[fresh_write_op_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem bytestring_fixed_raw_actual:
  compile_type_convert op (ConvBytestringToBytesM m) sa = (out,sb) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ eval_operand op ss = SOME a /\
  LENGTH bs <= 32 /\ w2n (a+32w) = w2n a+32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a+32) (LENGTH bs) ss.vs_memory = bs ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand out sf = SOME (word_of_bytes_be bs:bytes32) /\
    sf = ss with vs_vars := sf.vs_vars /\
    (!z. not_fresh_at sa z ==> FLOOKUP sf.vs_vars z = FLOOKUP ss.vs_vars z)
Proof
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa ss) /\
   eval_operand op (drop_fresh sa ss) = SOME a` by
    simp[fresh_vars_wrt_drop_fresh, eval_operand_drop_fresh] >>
  `mem_word_at (w2n a) (drop_fresh sa ss).vs_memory = n2w (LENGTH bs) /\
   mem_bytes_at (w2n a+32) (LENGTH bs) (drop_fresh sa ss).vs_memory = bs` by
    simp[drop_fresh_def] >>
  drule_all bytestring_fixed_raw_exact >> strip_tac >>
  drule bytestring_fixed_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >>
  `actual = ss with vs_vars := actual.vs_vars /\
   (!z. not_fresh_at sa z ==> FLOOKUP actual.vs_vars z = FLOOKUP ss.vs_vars z)` by
    (irule bytestring_fixed_run_frame >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qexists_tac `actual` >> simp[] >>
  fs[vars_ext_def] >>
  qpat_x_assum `actual = sf with vs_vars := _` SUBST1_TAC >>
  simp[eval_operand_vars_ext]
QED

Theorem bytestring_fixed_semantic_packet:
  (src = BaseT (BytesT (Dynamic n)) \/ src = BaseT (StringT n)) /\
  valid_conversion src (BaseT (BytesT (Fixed m))) /\
  well_formed_type tenv (BaseT (BytesT (Fixed m))) /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  val_in_memory stv v off mem ==>
  ?bs. LENGTH bs <= 32 /\
    mem_word_at off mem = n2w (LENGTH bs) /\
    mem_bytes_at (off+32) (LENGTH bs) mem = bs /\
    convert_result cx src (BaseT (BytesT (Fixed m))) v =
      INL (BytesV (PAD_RIGHT 0w m bs)) /\
    typed_val_to_w256 (BaseTV (BytesT (Fixed m)))
      (BytesV (PAD_RIGHT 0w m bs)) = (word_of_bytes_be bs:bytes32)
Proof
  strip_tac >> gvs[valid_conversion_def, well_formed_type_def,
    vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  qmatch_asmsub_abbrev_tac `mem_bytes_at _ _ _ = payload` >>
  qexists_tac `payload` >> simp[Abbr `payload`] >>
  simp[scalar_fixed_widen, typed_val_to_w256_def,
       word_of_bytes_be_pad_right] >> decide_tac
QED

Theorem bytestring_fixed_semantic_run_actual:
  (src = BaseT (BytesT (Dynamic n)) \/ src = BaseT (StringT n)) /\
  valid_conversion src (BaseT (BytesT (Fixed m))) /\
  well_formed_type tenv (BaseT (BytesT (Fixed m))) /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  compile_type_convert op (ConvBytestringToBytesM m) sa = (r,sb) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ eval_operand op ss = SOME a /\
  w2n a+32 < dimword(:256) /\ val_in_memory stv v (w2n a) ss.vs_memory ==>
  ?vout sf.
    convert_result cx src (BaseT (BytesT (Fixed m))) v = INL vout /\
    run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) vout) /\
    sf = ss with vs_vars := sf.vs_vars /\
    (!z. not_fresh_at sa z ==> FLOOKUP sf.vs_vars z = FLOOKUP ss.vs_vars z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bytestring_fixed_semantic_packet >> strip_tac >>
  `w2n (a+32w) = w2n a+32` by
    simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, LESS_MOD] >>
  drule_all bytestring_fixed_raw_actual >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem bytestring_fixed_stmt_frame:
  compile_type_convert op (ConvBytestringToBytesM m) sa = (r,sb) /\
  run_inst_seq (emitted_insts sa sb) ss = OK sf /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es ss ==>
  stmt_state_rel ctx func cenv cx es sf
Proof
  strip_tac >> drule_all bytestring_fixed_run_frame >> strip_tac >>
  qpat_x_assum `sf = _` SUBST1_TAC >>
  irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
  fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED

Theorem bytestring_fixed_source_packet:
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  (expr_type e = BaseT (BytesT (Dynamic n)) \/ expr_type e = BaseT (StringT n)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\ value_has_type stv v ==>
  ?a. eval_operand x t0 = SOME a /\
      val_in_memory stv v (w2n a) t0.vs_memory /\
      w2n a+32 < dimword(:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx func cenv cx ee t0 /\
   expr_val_rel cx (expr_type e) v x t0 /\
   expr_val_at cenv cx (expr_type e) sa s1 ee v x t0` by fs[expr_post_def] >>
  `~is_word_type (expr_type e) /\ 32 <= val_footprint stv v` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     gvs[is_word_type_def, vyperValueTheory.evaluate_type_def] >>
     Cases_on `v` >> gvs[value_has_type_def, val_footprint_def]) >>
  `?a. eval_operand x t0 = SOME a /\ val_in_memory stv v (w2n a) t0.vs_memory` by
    gvs[expr_val_rel_def] >>
  drule_all bodyPtrTypeBuiltinsFrameProbeTheory.expr_val_at_payload_nonwrap >> strip_tac >>
  qexists_tac `a` >> simp[]
QED
