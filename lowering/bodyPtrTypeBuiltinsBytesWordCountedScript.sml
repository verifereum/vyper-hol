Theory bodyPtrTypeBuiltinsBytesWordCounted
Ancestors
  bodyPtrTypeBuiltinsBytesWordSuffix bodyPtrSignedConvertUnsignedCompose
  bodyPtrTypeBuiltinsBytesWordParts
  bodyPtrHashBuiltinsGhostFrame
  bodyPtrTypeBuiltinsUintCounted bodyPtrSignedConvertUnsignedLoad
  bodyPtrTypeBuiltinsScalarCompose
  fragGasPathPtr instIdxIndep fragExec exprLoweringProps emitHelperProps
  exprLowering compileEnv venomState venomExecSemantics builtinConvertPrefix
  arithmetic finite_map list rich_list

(* Common source footprint, obtained for BytesV or StringV by the existing
   unsigned_*_value_source_facts boundaries. *)
Theorem bytes_word_loaded_counted_success:
  load_bytestring_as_word (Var src) SHR sa = ((word,bits),sm) /\
  (compile_type_convert word ConvToBool sm = (out,sb) \/
   emit_op SHL [bits;word] sm = (out,sb) \/
   (?b. compile_int_clamp F b word sm = (out,sb))) /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all loaded_word_suffix_shape >> strip_tac >>
  `inst_extends sa sm` by metis_tac[inst_extends_load_bytestring_as_word] >>
  `sm.cs_current_bb = sa.cs_current_bb /\ sm.cs_next_var = sa.cs_next_var+6 /\
   LENGTH (emitted_insts sa sm) = 6` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >> simp[]) >>
  drule_all fn_code_emitted_parts >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sm) s = OK u /\
       run_inst_seq (emitted_insts sm sb) u = OK t` by
    metis_tac[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok] >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  drule_all unsigned_loader_counted_ghost_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "suffix"
QED

Resume bytes_word_loaded_counted_success[suffix]:
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `u with vs_inst_idx := _ = _` mp_tac >>
     disch_then (fn th => map_every mp_tac
       [Q.AP_TERM `\v. v.vs_current_bb` th, Q.AP_TERM `\v. v.vs_halted` th]) >> simp[]) >>
  (Q.SUBGOAL_THEN
   `compile_type_convert word ConvToBool sm = (out,sb) \/
    emit_op SHL [bits;word] sm = (out,sb) \/
    (?signed b. compile_int_clamp signed b word sm = (out,sb))` assume_tac
   >- metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule loaded_word_suffix_filter >> strip_tac >> fs[EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sm sb) (u with vs_inst_idx := s.vs_inst_idx+6) =
     OK (t with vs_inst_idx := s.vs_inst_idx+6)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `lookup_block (u with vs_inst_idx := s.vs_inst_idx+6).vs_current_bb
      fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb)
      (DROP (u with vs_inst_idx := s.vs_inst_idx+6).vs_inst_idx bb.bb_instructions) /\
   ~(u with vs_inst_idx := s.vs_inst_idx+6).vs_halted` by gs[] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `s0a.cs_next_var <= sm.cs_next_var` by decide_tac >>
  `(!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by metis_tac[] >>
  (Q.SUBGOAL_THEN
   `compile_type_convert word ConvToBool sm = (out,sb) \/
    emit_op SHL [bits;word] sm = (out,sb) \/
    (?signed b. compile_int_clamp signed b word sm = (out,sb))` assume_tac
   >- metis_tac[]) >>
  qpat_x_assum `run_inst_seq (emitted_insts sm sb) u = _` kall_tac >>
  qpat_x_assum `u with vs_inst_idx := _ = _` kall_tac >>
  drule_all loaded_word_suffix_ghost >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx+6+LENGTH (emitted_insts sm sb)` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H' th'
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all gas_path_ptr_then >> gs[]) >>
  `t.vs_current_bb = sb.cs_current_bb` by
    (qpat_x_assum `(_ with vs_vars := _) = _` mp_tac >>
     disch_then (mp_tac o Q.AP_TERM `\v. v.vs_current_bb`) >> simp[]) >>
  suspend "post"
QED

Resume bytes_word_loaded_counted_success[post]:
  qexistsl_tac [`H'`,`th'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `ghost_inv d cenv cx es H' th' _` mp_tac >>
      simp_tac (srw_ss()) [hash_ghost_inv_inst_idx]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!p. not_fresh_at sm p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sa p ==> lookup_var p u = _ /\ _`
    (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sa p ==> not_fresh_at sm p`
    (qspec_then `p` mp_tac) >>
  qpat_x_assum `not_fresh_at sa p` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [lookup_var_def] >> metis_tac[]
QED

Finalise bytes_word_loaded_counted_success

Theorem bytes_word_counted_success:
  (conv = ConvBytestringToBool \/ (?m. conv = ConvBytestringToBytesM m) \/
   (?b cap. conv = ConvBytestringToInt F b cap)) /\
  compile_type_convert (Var src) conv sa = (out,sb) /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bytes_word_convert_parts >> strip_tac >>
  Cases_on `out = word /\ sb = sm`
  >- suspend "loader" >>
  irule bytes_word_loaded_counted_success >>
  metis_tac[]
QED

Resume bytes_word_counted_success[loader]:
  qpat_x_assum `out = word /\ sb = sm`
    (fn th => map_every (SUBST_ALL_TAC o SYM) (CONJUNCTS th)) >>
  `inst_extends sa sb` by metis_tac[inst_extends_load_bytestring_as_word] >>
  `sb.cs_current_bb = sa.cs_current_bb /\ LENGTH (emitted_insts sa sb) = 6` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >> simp[]) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx+6` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND]) >>
  drule_all fn_code_emitted_prefix >> strip_tac >>
  drule_all unsigned_loader_counted_ghost_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `t.vs_current_bb = sb.cs_current_bb` by
    (qpat_x_assum `t with vs_inst_idx := _ = _` mp_tac >>
     disch_then (mp_tac o Q.AP_TERM `\v. v.vs_current_bb`) >> simp[]) >>
  qexistsl_tac [`H`,`th`] >> gvs[]
QED

Finalise bytes_word_counted_success

Theorem bytes_word_pure_no_abort:
  (conv = ConvBytestringToBool \/ (?m. conv = ConvBytestringToBytesM m)) /\
  compile_type_convert (Var src) conv sa = (out,sb) /\ not_fresh_at sa src ==>
  run_inst_seq (emitted_insts sa sb) s <> Abort err t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  (Q.SUBGOAL_THEN
   `conv = ConvBytestringToBool \/ (?m. conv = ConvBytestringToBytesM m) \/
    (?b cap. conv = ConvBytestringToInt F b cap)` assume_tac >- metis_tac[]) >>
  drule_all bytes_word_convert_parts >> strip_tac >>
  `compile_type_convert word ConvToBool sm = (out,sb) \/
   emit_op SHL [bits;word] sm = (out,sb)` by metis_tac[] >>
  `inst_extends sm sb` by metis_tac[loaded_word_suffix_shape] >>
  `inst_extends sa sm` by metis_tac[inst_extends_load_bytestring_as_word] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  drule_all unsigned_loader_no_abort >> strip_tac >>
  fs[scalar_seq_append_abort_iff] >> metis_tac[loaded_word_pure_suffix_no_abort]
QED
