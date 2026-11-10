(* Same actual runs, certified at compiler boundaries, without expression posts. *)
Theory bodyPtrTypeBuiltinsUintCounted
Ancestors bodyPtrSignedConvertUnsignedValue bodyPtrSignedConvertUnsignedLoad
  bodyPtrSignedConvertClamp bodyPtrTypeBuiltinsUintActual
  bodyPtrTypeBuiltinsScalarCompose bodyPtrSignedConvertSourceFrame
  fragGasPathPtr fragGasSeqPtr fragGasSeqAbort fragExec emitHelperProps exprLoweringProps exprLowering
  builtinConvertPrefix venomState venomInst venomExecSemantics opcodeClass
  rich_list list arithmetic finite_map ptrDiscipline instIdxIndep
  compileEnv loweringStateRelDefs loweringShapeDefs venomInstProps

Theorem appended_prefix_drop:
  isPREFIX (xs ++ ys) zs ==>
  isPREFIX ys (DROP (LENGTH xs) zs)
Proof
  simp[IS_PREFIX_APPEND] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]
QED

Theorem fn_code_emitted_prefix:
  fn_has_code sa sb fn /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  simp[fn_has_code_def, inst_extends_def] >> strip_tac >> gs[] >>
  drule appended_prefix_drop >> strip_tac >> metis_tac[]
QED

Theorem inst_seq_no_abort[local]:
  !code s err t.
    EVERY (\i. !ss a tt. step_inst_base i ss <> Abort a tt) code ==>
    run_inst_seq code s <> Abort err t
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >> metis_tac[]
QED

Theorem unsigned_loader_no_abort:
  load_bytestring_as_word (Var src) SHR sa = ((out,bits),sb) /\
  not_fresh_at sa src ==>
  run_inst_seq (emitted_insts sa sb) s <> Abort err t
Proof
  strip_tac >> drule_all unsigned_loader_shape_fresh >> strip_tac >>
  irule inst_seq_no_abort >> simp[] >> rpt conj_tac >>
  rpt strip_tac >> drule step_inst_base_abort_opcodes >> simp[mk_inst_def]
QED

Theorem appended_prefix_advance:
  isPREFIX (xs ++ ys) (DROP k zs) ==>
  isPREFIX ys (DROP (k + LENGTH xs) zs)
Proof
  strip_tac >> drule appended_prefix_drop >>
  simp[DROP_DROP_T, ADD_COMM]
QED

Theorem fn_code_emitted_parts:
  fn_has_code sa sb fn /\ inst_extends sa sm /\ inst_extends sm sb /\
  sm.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sm.cs_current_bb /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    isPREFIX (emitted_insts sm sb)
      (DROP (s.vs_inst_idx + LENGTH (emitted_insts sa sm)) bb.bb_instructions) /\
    LENGTH sm.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sm) /\
    emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb
Proof
  strip_tac >>
  `inst_extends sa sb` by metis_tac[inst_extends_trans] >>
  `sb.cs_current_bb = sa.cs_current_bb` by simp[] >>
  drule_all fn_code_emitted_prefix >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qexists_tac `bb` >> gs[] >> conj_tac
  >- (drule appended_prefix_advance >> simp[]) >>
  fs[inst_extends_def] >> metis_tac[LENGTH_APPEND]
QED

Theorem uint_convert_parts:
  not_fresh_at sa src /\
  compile_type_convert (Var src) (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (UintT b))) sa = (out,sb) ==>
  ?word bits sm.
    load_bytestring_as_word (Var src) SHR sa = ((word,bits),sm) /\ 
    inst_extends sa sm /\ sm.cs_current_bb = sa.cs_current_bb /\
    (if 8*n > b then compile_int_clamp F b word sm = (out,sb)
     else out = word /\ sb = sm)
Proof
  simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def] >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def, comp_return_def,
                   LET_THM, COND_CLAUSES] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  `inst_extends sa cs'` by metis_tac[inst_extends_load_bytestring_as_word] >>
  `cs'.cs_current_bb = sa.cs_current_bb` by
    metis_tac[unsigned_loader_shape_fresh] >>
  Cases_on `8*n > b` >> gvs[comp_return_def]
QED

Theorem bytes_uint_counted_success:
  compile_type_convert (Var src) (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (UintT b))) sa = (out,sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_has_code sa sb fn /\ lookup_var src s = SOME a /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn s /\
  ptr_buf_ok cenv e (Var src) G s /\ op_taint tn (Var src) = {} /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k))) /\
  LENGTH bs <= 32 /\ 64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  w2n a+32 < dimword(:256) /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
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
  strip_tac >> drule_all uint_convert_parts >> strip_tac >>
  Cases_on `8*n > b` >> gvs[]
  >- suspend "clamp" >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (drule_all fn_code_emitted_prefix >> simp[]) >>
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn s /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by simp[] >>
  drule_all unsigned_loader_from_bytes_value >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `LENGTH (emitted_insts sa sb) = 6` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >> simp[]) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx+6` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND]) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  qpat_x_assum `t with vs_inst_idx := _ = _` mp_tac >>
  disch_then (mp_tac o Q.AP_TERM `\u. u.vs_current_bb`) >> gs[]
QED

Resume bytes_uint_counted_success[clamp]:
  `inst_extends sm sb` by metis_tac[inst_extends_compile_int_clamp] >>
  `sb.cs_current_bb = sm.cs_current_bb` by metis_tac[int_clamp_unsigned_code] >>
  drule_all fn_code_emitted_parts >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sm) s = OK u /\
       run_inst_seq (emitted_insts sm sb) u = OK t` by
    metis_tac[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok] >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn s /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by simp[] >>
  drule_all unsigned_loader_from_bytes_value >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `LENGTH (emitted_insts sa sm) = 6` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >> simp[]) >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `u with vs_inst_idx := _ = _` mp_tac >>
     disch_then (fn th => map_every mp_tac
       [Q.AP_TERM `\v. v.vs_current_bb` th, Q.AP_TERM `\v. v.vs_halted` th]) >>
     simp[]) >>
  `run_inst_seq (emitted_insts sm sb) (u with vs_inst_idx := s.vs_inst_idx+6) =
     OK (t with vs_inst_idx := s.vs_inst_idx+6)` by
    (drule int_clamp_instruction_filter >> strip_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     qpat_x_assum `u with vs_inst_idx := _ = _` kall_tac >>
     simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  `lookup_block (u with vs_inst_idx := s.vs_inst_idx+6).vs_current_bb
    fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb)
    (DROP (u with vs_inst_idx := s.vs_inst_idx+6).vs_inst_idx bb.bb_instructions) /\
   ~(u with vs_inst_idx := s.vs_inst_idx+6).vs_halted` by gs[] >>
  qpat_x_assum `run_inst_seq (emitted_insts sm sb) u = _` kall_tac >>
  qpat_x_assum `u with vs_inst_idx := _ = _` kall_tac >>
  drule_all int_clamp_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx+6+LENGTH (emitted_insts sm sb)` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H' th'
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all gas_path_ptr_then >> gs[]) >>
  suspend "frame"
QED

Resume bytes_uint_counted_success[frame]:
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >>
     simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `t = s with vs_vars := t.vs_vars /\
   (!z. not_fresh_at sa z ==> FLOOKUP t.vs_vars z = FLOOKUP s.vs_vars z)` by
    (drule_all uint_convert_run_frame >> simp[]) >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP H' p = FLOOKUP G p /\ op_taint th' (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[]) >>
  `ghost_kept cenv es0 s0a G0 tn0 s0 H' th'` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`H`,`not_fresh_at sa`,`th`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `ghost_inv d cenv cx es H' th' (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`H`,`not_fresh_at sm`,
       `u with vs_inst_idx := s.vs_inst_idx+6`,`th`] >>
     `(!p. not_fresh_at sm p ==>
       lookup_var p (t with vs_inst_idx := s.vs_inst_idx+6) =
       lookup_var p (u with vs_inst_idx := s.vs_inst_idx+6)) /\
       ((t with vs_inst_idx := s.vs_inst_idx+6) with
         vs_vars := (u with vs_inst_idx := s.vs_inst_idx+6).vs_vars) =
       (u with vs_inst_idx := s.vs_inst_idx+6)` by
       metis_tac[int_clamp_runtime_frame] >>
     `t.vs_memory = u.vs_memory /\ t.vs_call_ctx = u.vs_call_ctx /\
      t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient` by
       (qpat_x_assum `(_ with vs_vars := _) = _` (fn eq =>
         map_every (fn q => mp_tac (Q.AP_TERM q eq))
           [`\v. v.vs_memory`,`\v. v.vs_call_ctx`,
            `\v. v.vs_accounts`,`\v. v.vs_transient`]) >> simp[]) >>
     gs[lookup_var_def] >> metis_tac[]) >>
  qexistsl_tac [`H'`,`th'`] >> simp[] >>
  qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]
QED

Finalise bytes_uint_counted_success

(* No GAS instructions means the executed abort prefix has zero observations. *)
Theorem no_gas_seq_abort_counted:
  !code s t a G tn H th ctx fn bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                i.inst_opcode <> GAS) code /\
    inst_seq_ptr D lo ctx fn PG G tn code s H th /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_path_ptr D lo ctx fn PG G tn s 0 H th
          (Abort a (t with vs_inst_idx := j))
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def]
  >~ [`step_inst_base h s = OK u`]
  >- (`step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`, `a`, `step_prov PG G h u`,
        `step_taint h s u tn`, `H`, `th`, `ctx`, `fn`, `bb`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
      drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) gas_path_ptr_step >>
      simp[] >> metis_tac[]) >>
  qexists_tac `t.vs_inst_idx` >>
  simp[] >> drule_all gas_path_ptr_abort >> simp[]
QED

Theorem int_clamp_abort_zero_counted:
  compile_int_clamp signed bits x sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th j. gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] int_clamp_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule int_clamp_instruction_filter >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all no_gas_seq_abort_counted >> metis_tac[]
QED

Theorem bytes_uint_counted_abort:
  compile_type_convert (Var src) (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (UintT b))) sa = (out,sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_has_code sa sb fn /\ lookup_var src s = SOME a /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn s /\
  ptr_buf_ok cenv e (Var src) G s /\ op_taint tn (Var src) = {} /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k))) /\
  LENGTH bs <= 32 /\ 64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  w2n a+32 < dimword(:256) /\ run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?H th j. gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all uint_convert_parts >> strip_tac >>
  Cases_on `8*n > b` >> gvs[]
  >- suspend "clamp" >>
  drule_all unsigned_loader_no_abort >> metis_tac[]
QED

Resume bytes_uint_counted_abort[clamp]:
  `inst_extends sm sb` by metis_tac[inst_extends_compile_int_clamp] >>
  `sb.cs_current_bb = sm.cs_current_bb` by metis_tac[int_clamp_unsigned_code] >>
  drule_all fn_code_emitted_parts >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sm) s = OK u /\
       run_inst_seq (emitted_insts sm sb) u = Abort err t` by
    (drule_all unsigned_loader_no_abort >> strip_tac >>
     fs[scalar_seq_append_abort_iff] >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn s /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by simp[] >>
  drule_all unsigned_loader_from_bytes_value >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `LENGTH (emitted_insts sa sm) = 6` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >> simp[]) >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `u with vs_inst_idx := _ = _` mp_tac >>
     disch_then (fn th => map_every mp_tac
       [Q.AP_TERM `\v. v.vs_current_bb` th, Q.AP_TERM `\v. v.vs_halted` th]) >>
     simp[]) >>
  `run_inst_seq (emitted_insts sm sb) (u with vs_inst_idx := s.vs_inst_idx+6) =
     Abort err (t with vs_inst_idx := s.vs_inst_idx+6)` by
    (drule int_clamp_instruction_filter >> strip_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     qpat_x_assum `u with vs_inst_idx := _ = _` kall_tac >>
     simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  `lookup_block (u with vs_inst_idx := s.vs_inst_idx+6).vs_current_bb
    fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb)
    (DROP (u with vs_inst_idx := s.vs_inst_idx+6).vs_inst_idx bb.bb_instructions) /\
   ~(u with vs_inst_idx := s.vs_inst_idx+6).vs_halted` by gs[] >>
  qpat_x_assum `run_inst_seq (emitted_insts sm sb) u = _` kall_tac >>
  qpat_x_assum `u with vs_inst_idx := _ = _` kall_tac >>
  drule_all int_clamp_abort_zero_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> gs[] >> metis_tac[]
QED

Finalise bytes_uint_counted_abort
