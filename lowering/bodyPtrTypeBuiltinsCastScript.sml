Theory bodyPtrTypeBuiltinsCast
Ancestors
  bodyPtrTypeBuiltinsHeaderLoad bodyPtrTypeBuiltinsCheckedArithmetic
  bodyPtrTypeBuiltinsScalarChecks bodyPtrDefs typedCopyPtr
  exprSimPtrProps exprLowering exprLoweringProps
  compileEnv emitHelper emitHelperProps ASCIInumbers rich_list
  exprSimPtrLiteralBuffer ghostPcTransportPtr
  fragGasSeqPtr fragGasSeqAbort fragGasPathPtr instIdxIndep fragExec wordArgsPtr
  venomExecSemantics venomState venomInst ptrDiscipline arithmetic stmtAppendStoragePathPtr

Theorem convert_cast_emitted_shape:
  compile_type_convert x (ConvBytestringCast n i) sa = (out,sb) ==>
  out = x /\
  (if n < i then
    ?a b c.
      emitted_insts sa sb =
        [mk_inst sa.cs_next_id MLOAD [x] [a];
         mk_inst (sa.cs_next_id+1) GT [Var a;Lit (n2w n)] [b];
         mk_inst (sa.cs_next_id+2) ISZERO [Var b] [c];
         mk_inst (sa.cs_next_id+3) ASSERT [Var c] []] /\
      (!p. not_fresh_at sa p ==> p <> a /\ p <> b /\ p <> c)
   else sb = sa)
Proof
  strip_tac >> Cases_on `n < i`
  >- (gvs[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> rpt (pairarg_tac >> gvs[]) >>
      gvs[emit_void_def, emit_op_def, emit_inst_def, comp_bind_def,
          comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
          comp_return_def] >>
      simp[emitted_insts_def] >>
      CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
      simp[DROP_LENGTH_APPEND] >>
      qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
        `STRING #"%" (toString (sa.cs_next_var+1))`,
        `STRING #"%" (toString (sa.cs_next_var+2))`] >>
      simp[not_fresh_at_def] >> rpt strip_tac >> gvs[]) >>
  gvs[compile_type_convert_def, comp_return_def]
QED

Theorem cast_check_success_certificate:
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id GT [Var len;Lit (n2w n)] [a];
    mk_inst (id+1) ISZERO [Var a] [b]; mk_inst (id+2) ASSERT [Var b] []] s = OK t /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p. not_fresh_at sa p ==> p <> a /\ p <> b) ==>
  !k. ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id GT [Var len;Lit (n2w n)] [a];
       mk_inst (id+1) ISZERO [Var a] [b]; mk_inst (id+2) ASSERT [Var b] []]
      (s with vs_inst_idx := k) H th /\
    ghost_inv d cenv cx es H th t /\ ghost_kept cenv es sa G tn s H th /\
    (!p sz. p <> a /\ p <> b /\ ptr_covers G tn p s sz ==>
       ptr_covers H th p t sz) /\
    (!p. p <> a /\ p <> b ==> lookup_var p t = lookup_var p s /\
       FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\ t.vs_memory = s.vs_memory
Proof
  strip_tac >> gen_tac >>
  `MEM GT [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
   op_prov G (Lit (n2w n)) = NONE /\ op_taint tn (Lit (n2w n)) = {}` by
    simp[op_prov_def, op_taint_def] >>
  drule_all scalar_checked_pair_runtime_frame >> strip_tac >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t with vs_vars := _ = s`
       (mp_tac o Q.AP_TERM `\v. v.vs_memory`) >> simp[]) >>
  drule_all (cj 1 (PURE_REWRITE_RULE
    [LEFT_AND_OVER_OR, DISJ_IMP_THM] scalar_checked_pair_uniform_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`,`k`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> conj_tac
  >- (irule ghost_inv_fresh_frame >> goal_assum (drule_at Any) >>
      simp[] >> gvs[venom_state_component_equality] >> metis_tac[]) >>
  conj_tac >- (simp[ghost_kept_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]
QED

Theorem cast_header_run_suffix:
  EVERY (\i. ~is_terminator i.inst_opcode) code /\
  lookup_var src s = SOME w /\
  run_inst_seq (mk_inst id MLOAD [Var src] [len] :: code) s = r ==>
  run_inst_seq code ((update_var len (mload (w2n w) s) s) with
    vs_inst_idx := SUC s.vs_inst_idx) =
    exec_result_map (\t. t with vs_inst_idx := SUC s.vs_inst_idx) r
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [len]) s =
     OK (update_var len (mload (w2n w) s) s)` by
    (irule step_MLOAD >> simp[eval_operand_def]) >>
  gvs[run_inst_seq_def] >> simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem cast_narrow_success_path:
  code = [mk_inst id MLOAD [Var src] [len];
    mk_inst (id+1) GT [Var len;Lit (n2w n)] [a];
    mk_inst (id+2) ISZERO [Var a] [b]; mk_inst (id+3) ASSERT [Var b] []] /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq code s = OK t /\
  ptr_covers G tn src s sz /\ 32 <= sz /\ lookup_var src s = SOME w /\
  src <> len /\ src <> a /\ src <> b /\
  (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p z. cenv.ce_return_buf = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  (!p z. cenv.ce_return_pc = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  (!p. not_fresh_at sa p ==> p <> len /\ p <> a /\ p <> b) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx+4)) /\
    ghost_inv d cenv cx es H th t /\
    ghost_kept cenv es sa G tn s H th /\ ptr_covers H th src t sz /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem
Proof
  strip_tac >> qpat_x_assum `code = _` SUBST_ALL_TAC >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac) >>
  drule instruction_prefix_cursor >> strip_tac >>
  `(!p. not_fresh_at sa p ==> p <> len) /\
   (!p. not_fresh_at sa p ==> p <> a /\ p <> b)` by metis_tac[] >>
  drule_all mload_counted_ghost_frame >>
  disch_then (qspecl_then [`PG`,`D`] (qx_choose_then `J`
    (qx_choose_then `tk` (qx_choose_then `u` strip_assume_tac)))) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     [mk_inst (id+1) GT [Var len;Lit (n2w n)] [a];
      mk_inst (id+2) ISZERO [Var a] [b]; mk_inst (id+3) ASSERT [Var b] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all cast_header_run_suffix >> pure_rewrite_tac[exec_result_map_def] >> BETA_TAC >>
  qpat_x_assum `u = update_var _ _ _ with vs_inst_idx := _` (fn th =>
    pure_rewrite_tac[GSYM th]) >> disch_tac >>
  `id+2 = (id+1)+1 /\ id+3 = (id+1)+2` by decide_tac >>
  drule_all (SRULE [GSYM ADD_ASSOC]
    (Q.INST [`id` |-> `id+1`] (SPEC_ALL cast_check_success_certificate))) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`,`u.vs_inst_idx`] strip_assume_tac) >>
  `~u.vs_halted /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by
    (conj_tac >- metis_tac[gas_path_ptr_ok_not_halted] >>
     qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (mp_tac o Q.AP_TERM `\v. v.vs_current_bb`) >> simp[]) >>
  `isPREFIX [mk_inst (id+1) GT [Var len;Lit (n2w n)] [a];
     mk_inst (id+2) ISZERO [Var a] [b]; mk_inst (id+3) ASSERT [Var b] []]
     (DROP u.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  `u.vs_memory = s.vs_memory` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (mp_tac o Q.AP_TERM `\v. v.vs_memory`) >> simp[]) >>
  qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
  qpat_x_assum `id+2 = _` kall_tac >> qpat_x_assum `id+3 = _` kall_tac >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[] >> disch_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     [mk_inst (id+1) GT [Var len;Lit (n2w n)] [a];
      mk_inst (id+2) ISZERO [Var a] [b]; mk_inst (id+3) ASSERT [Var b] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[mk_inst_def, is_terminator_def] >> disch_tac >>
  qexistsl_tac [`H`,`th`] >> conj_tac
  >- (rev_drule gas_path_ptr_then >> disch_then drule >>
      simp[mk_inst_def, ADD1]) >>
  conj_tac
  >- (qpat_x_assum `ghost_inv _ _ _ _ H _ _` mp_tac >>
      simp[SRULE [] (Q.INST [`gs` |-> `es.gas_obs`]
        (SPEC_ALL literal_ptr_ghost_inv_normalize))]) >>
  conj_tac >- (simp[ghost_kept_def] >> metis_tac[]) >>
  fs[] >> metis_tac[]
QED

Theorem cast_narrow_abort_path:
  code = [mk_inst id MLOAD [Var src] [len];
    mk_inst (id+1) GT [Var len;Lit (n2w n)] [a];
    mk_inst (id+2) ISZERO [Var a] [b]; mk_inst (id+3) ASSERT [Var b] []] /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq code s = Abort err t /\
  ptr_covers G tn src s sz /\ 32 <= sz /\ lookup_var src s = SOME w /\
  src <> len /\
  (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p z. cenv.ce_return_buf = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  (!p z. cenv.ce_return_pc = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  (!p. not_fresh_at sa p ==> p <> len /\ p <> a /\ p <> b) ==>
  ?H th j.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (Abort err (t with vs_inst_idx := j)) /\ ghost_kept cenv es sa G tn s H th
Proof
  strip_tac >> qpat_x_assum `code = _` SUBST_ALL_TAC >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac) >>
  drule instruction_prefix_cursor >> strip_tac >>
  `(!p. not_fresh_at sa p ==> p <> len)` by metis_tac[] >>
  drule_all mload_counted_ghost_frame >>
  disch_then (qspecl_then [`PG`,`D`] (qx_choose_then `J`
    (qx_choose_then `tk` (qx_choose_then `u` strip_assume_tac)))) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     [mk_inst (id+1) GT [Var len;Lit (n2w n)] [a];
      mk_inst (id+2) ISZERO [Var a] [b]; mk_inst (id+3) ASSERT [Var b] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all cast_header_run_suffix >> pure_rewrite_tac[exec_result_map_def] >> BETA_TAC >>
  qpat_x_assum `u = update_var _ _ _ with vs_inst_idx := _` (fn th =>
    pure_rewrite_tac[GSYM th]) >> disch_tac >>
  `MEM GT [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
   op_prov J (Lit (n2w n)) = NONE /\ op_taint tk (Lit (n2w n)) = {}` by
    simp[op_prov_def, op_taint_def] >>
  drule_all (SRULE [GSYM ADD_ASSOC]
    (Q.INST [`id` |-> `id+1`, `opc` |-> `GT`]
    (SPEC_ALL (cj 2 (PURE_REWRITE_RULE [LEFT_AND_OVER_OR, DISJ_IMP_THM]
      scalar_checked_pair_uniform_certificate))))) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`,`u.vs_inst_idx`] strip_assume_tac) >>
  `~u.vs_halted /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by
    (conj_tac >- metis_tac[gas_path_ptr_ok_not_halted] >>
     qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (mp_tac o Q.AP_TERM `\v. v.vs_current_bb`) >> simp[]) >>
  qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
  `isPREFIX [mk_inst (id+1) GT [Var len;Lit (n2w n)] [a];
     mk_inst (id+2) ISZERO [Var a] [b]; mk_inst (id+3) ASSERT [Var b] []]
     (DROP u.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[] >> disch_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     [mk_inst (id+1) GT [Var len;Lit (n2w n)] [a];
      mk_inst (id+2) ISZERO [Var a] [b]; mk_inst (id+3) ASSERT [Var b] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     [mk_inst (id+1) GT [Var len;Lit (n2w n)] [a];
      mk_inst (id+2) ISZERO [Var a] [b]; mk_inst (id+3) ASSERT [Var b] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`j`] >> conj_tac
  >- (rev_drule gas_path_ptr_then >> disch_then drule >> simp[]) >>
  simp[ghost_kept_def] >> metis_tac[]
QED

Theorem convert_cast_success_path:
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
  (!p z. cenv.ce_return_pc = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) ==>
  out = Var src /\ ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    ghost_inv d cenv cx es H th t /\
    ghost_kept cenv es sa G tn s H th /\ ptr_covers H th src t sz /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem
Proof
  strip_tac >> drule convert_cast_emitted_shape >> strip_tac >> simp[] >>
  Cases_on `n < i` >> fs[]
  >- (`src <> a /\ src <> b /\ src <> c` by metis_tac[] >>
      drule_all cast_narrow_success_path >> simp[]) >>
  gvs[emitted_insts_def, run_inst_seq_def] >>
  qexistsl_tac [`G`,`tn`] >> simp[gas_path_ptr_rules, ghost_kept_refl]
QED

Theorem convert_cast_abort_path:
  compile_type_convert (Var src) (ConvBytestringCast n i) sa = (out,sb) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ptr_covers G tn src s sz /\ 32 <= sz /\ lookup_var src s = SOME w /\
  not_fresh_at sa src /\
  (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p z. cenv.ce_return_buf = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  (!p z. cenv.ce_return_pc = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) ==>
  out = Var src /\ ?H th j.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (Abort err (t with vs_inst_idx := j)) /\ ghost_kept cenv es sa G tn s H th
Proof
  strip_tac >> drule convert_cast_emitted_shape >> strip_tac >> simp[] >>
  Cases_on `n < i` >> fs[]
  >- (`src <> a` by metis_tac[] >>
      drule_all cast_narrow_abort_path >> simp[]) >>
  gvs[emitted_insts_def, run_inst_seq_def]
QED
