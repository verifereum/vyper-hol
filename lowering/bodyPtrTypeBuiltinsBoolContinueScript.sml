(* Bytes-to-Bool continuation boundaries: the shared loader and pure Bool suffix. *)
Theory bodyPtrTypeBuiltinsBoolContinue
Ancestors bodyPtrTypeBuiltinsUintContinue bodyPtrTypeBuiltinsUintCounted
  bodyPtrTypeBuiltinsBool bodyPtrTypeBuiltinsIszero bodyPtrTypeBuiltinsUnsignedSemantics
  exprLowering exprLoweringProps emitHelperProps builtinConvertPrefix
  fragExec venomExecSemantics venomInst venomState ptrDiscipline finite_map opcodeClass
  vyperTypeSystem vyperValueOperation exprSimConvert compileEnv loweringShapeDefs
  fragGasPathPtr bodyPtrTypeBuiltinsUnsignedValue bodyPtrTypeBuiltinsUnsignedLoad
  bodyPtrTypeBuiltinsSourceFrame rich_list list arithmetic instIdxIndep
  bodyPtrTypeBuiltinsSourceTyping exprSimDefs exprSimWordArgs exprSimProps loweringPosts bodyPtrDefs vyperAST
Libs monadsyntax

Theorem bytes_bool_convert_parts:
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (out,sb) ==>
  ?word bits sm.
    load_bytestring_as_word x SHR sa = ((word,bits),sm) /\
    compile_type_convert word ConvToBool sm = (out,sb) /\
    inst_extends sa sm /\ inst_extends sm sb
Proof
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def, comp_return_def,
                   LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_bind_def, comp_return_def] >>
  metis_tac[inst_extends_load_bytestring_as_word, inst_extends_emit_op,
            inst_extends_trans]
QED

Theorem convert_bool_run_actual:
  compile_type_convert x ConvToBool sa = (out,sb) /\
  eval_operand x s = SOME w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (bool_to_word (w <> 0w)) /\
      (t with vs_vars := s.vs_vars) = s /\
      (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> drule convert_bool_code >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ISZERO [x] [a]) s =
     OK (update_var a (bool_to_word (w = 0w)) s)` by
    (irule step_ISZERO >> simp[]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b])
      (update_var a (bool_to_word (w = 0w)) s) =
     OK (update_var b (bool_to_word (bool_to_word (w = 0w) = 0w))
       (update_var a (bool_to_word (w = 0w)) s))` by
    (irule step_ISZERO >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `run_inst_seq (emitted_insts sa sb) s =
     OK (update_var b (bool_to_word (bool_to_word (w = 0w) = 0w))
       (update_var a (bool_to_word (w = 0w)) s))` by
    simp[run_inst_seq_def] >>
  drule_all convert_bool_runtime_frame >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `w = 0w` >> simp[bool_to_word_def]
QED

Theorem convert_bool_no_abort:
  compile_type_convert x ConvToBool sa = (out,sb) ==>
  run_inst_seq (emitted_insts sa sb) s <> Abort err t
Proof
  strip_tac >> drule convert_bool_code >> strip_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> rpt strip_tac >>
  drule step_inst_base_abort_opcodes >> simp[mk_inst_def]
QED

Theorem bytes_bool_no_abort:
  compile_type_convert (Var src) (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (out,sb) /\ not_fresh_at sa src ==>
  run_inst_seq (emitted_insts sa sb) s <> Abort err t
Proof
  strip_tac >> drule bytes_bool_convert_parts >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  drule_all unsigned_loader_no_abort >> strip_tac >>
  drule convert_bool_no_abort >> strip_tac >>
  simp[bodyPtrTypeBuiltinsScalarComposeTheory.scalar_seq_append_abort_iff] >>
  metis_tac[]
QED

Theorem zero_bool_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ v1 = BytesV [] /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) (BaseT BoolT) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx
        (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT) [e])
        es sa s1 s0 fin v (Lit 0w) ss /\
      ss.vs_current_bb = s1.cs_current_bb /\
      ss.vs_inst_idx = LENGTH s1.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT BoolT) v (Lit 0w) H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >> gvs[] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (BoolV F)`,`ee`,`G`,`tn`,`OK t0`] >>
  simp[gas_path_ptr_rules, bodyPtrTypeBuiltinsLiteralPostTheory.ptr_val_ok_word_literal,
       is_word_type_def] >>
  irule zero_convert_child_post >>
  simp[is_word_type_def, vyperValueTheory.evaluate_type_def,
       valueEncodingTheory.typed_val_to_w256_def,
       valueEncodingTheory.val_to_w256_def, bool_to_word_def] >>
  goal_assum (drule_at Any)
QED

Theorem bytes_bool_counted_success:
  compile_type_convert (Var src) (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (out,sb) /\
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
  strip_tac >> drule bytes_bool_convert_parts >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    metis_tac[unsigned_loader_shape_fresh] >>
  `sb.cs_current_bb = sm.cs_current_bb` by metis_tac[convert_bool_code] >>
  drule_all fn_code_emitted_parts >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sm) s = OK u /\
       run_inst_seq (emitted_insts sm sb) u = OK t` by
    metis_tac[bodyPtrTypeBuiltinsScalarComposeTheory.scalar_seq_append_ok_iff] >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn s /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by simp[] >>
  drule_all unsigned_loader_from_bytes_value >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `LENGTH (emitted_insts sa sm) = 6` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >> simp[]) >>
  suspend "suffix"
QED

Resume bytes_bool_counted_success[suffix]:
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `u with vs_inst_idx := _ = _` mp_tac >>
     disch_then (fn th => map_every mp_tac
       [Q.AP_TERM `\v. v.vs_current_bb` th, Q.AP_TERM `\v. v.vs_halted` th]) >>
     simp[]) >>
  `run_inst_seq (emitted_insts sm sb) (u with vs_inst_idx := s.vs_inst_idx+6) =
     OK (t with vs_inst_idx := s.vs_inst_idx+6)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
       (drule convert_bool_code >> strip_tac >> simp[mk_inst_def, is_terminator_def]) >>
     qpat_x_assum `u with vs_inst_idx := _ = _` kall_tac >>
     simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  `lookup_block (u with vs_inst_idx := s.vs_inst_idx+6).vs_current_bb
    fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb)
    (DROP (u with vs_inst_idx := s.vs_inst_idx+6).vs_inst_idx bb.bb_instructions) /\
   ~(u with vs_inst_idx := s.vs_inst_idx+6).vs_halted` by gs[] >>
  qpat_x_assum `run_inst_seq (emitted_insts sm sb) u = _` kall_tac >>
  qpat_x_assum `u with vs_inst_idx := _ = _` kall_tac >>
  drule_all convert_bool_counted_certificate >>
  disch_then (qspecl_then [`PG`,`H`,`D`] strip_assume_tac) >> gs[] >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx+6+LENGTH (emitted_insts sm sb)` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H' th'
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all gas_path_ptr_then >> gs[]) >>
  suspend "frame"
QED

Resume bytes_bool_counted_success[frame]:
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >>
     simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `(!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p u) /\
    ((t with vs_inst_idx := s.vs_inst_idx+6) with
       vs_vars := (u with vs_inst_idx := s.vs_inst_idx+6).vs_vars) =
       (u with vs_inst_idx := s.vs_inst_idx+6)` by
    (drule_all convert_bool_runtime_frame >> simp[lookup_var_def] >> metis_tac[]) >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP H' p = FLOOKUP G p /\ op_taint th' (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> metis_tac[]) >>
  `ghost_kept cenv es0 s0a G0 tn0 s0 H' th'` by
    (irule bodyPtrTypeBuiltinsSourceFrameTheory.ghost_kept_readonly_frame >>
     qexistsl_tac [`H`,`not_fresh_at sa`,`th`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `ghost_inv d cenv cx es H' th' (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule bodyPtrTypeBuiltinsSourceFrameTheory.ghost_inv_readonly_frame >>
     qexistsl_tac [`H`,`not_fresh_at sm`,
       `u with vs_inst_idx := s.vs_inst_idx+6`,`th`] >>
     `t.vs_memory = u.vs_memory /\ t.vs_call_ctx = u.vs_call_ctx /\
      t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient` by
       (qpat_x_assum `(_ with vs_vars := _) = _` (fn eq =>
         map_every (fn q => mp_tac (Q.AP_TERM q eq))
           [`\v. v.vs_memory`,`\v. v.vs_call_ctx`,
            `\v. v.vs_accounts`,`\v. v.vs_transient`]) >> simp[]) >>
     gs[lookup_var_def] >> metis_tac[]) >>
  qexistsl_tac [`H'`,`th'`] >> simp[] >>
  qpat_x_assum `(_ with vs_vars := _) = _` mp_tac >>
  disch_then (mp_tac o Q.AP_TERM `\v. v.vs_current_bb`) >> simp[]
QED

Finalise bytes_bool_counted_success

Theorem bytes_bool_code_frame:
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (r,sb) ==>
  EVERY (\i. (freshWrites$fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
             EVERY (\x. ~not_fresh_at sa x) i.inst_outputs)
        (emitted_insts sa sb)
Proof
  simp[mk_convert_op_def, is_bytestring_type_def, compile_type_convert_def,
       load_bytestring_as_word_def, emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, freshWritesTheory.fresh_write_op_def, not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >> decide_tac
QED

Theorem bytes_bool_run_frame:
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (r,sb) /\
  run_inst_seq (emitted_insts sa sb) ss = OK sf ==>
  sf = ss with vs_vars := sf.vs_vars /\
  (!z. not_fresh_at sa z ==> FLOOKUP sf.vs_vars z = FLOOKUP ss.vs_vars z)
Proof
  strip_tac >> drule bytes_bool_code_frame >> strip_tac >>
  drule_all bodyPtrTypeBuiltinsUintActualTheory.readonly_run_frame >> simp[]
QED

Theorem bytes_bool_replay:
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (r,sb) ==>
  varsExt$vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa ss))
    (run_inst_seq (emitted_insts sa sb) ss)
Proof
  strip_tac >> drule bytes_bool_code_frame >> disch_tac >>
  irule varsExtTheory.run_inst_seq_vars_ext >> simp[varsExtTheory.vars_ext_drop_fresh] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
  gvs[freshWritesTheory.fresh_write_op_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem bytes_bool_encoding:
  LENGTH bs <= 32 ==>
  typed_val_to_w256 (BaseTV BoolT) (BoolV (EXISTS (\b. b <> 0w) bs)) =
    bool_to_word (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs)) <> 0w)
Proof
  strip_tac >>
  `EXISTS (\b. b <> 0w) bs = ~EVERY (\b. b = 0w) bs` by
    (Induct_on `bs` >> simp[]) >>
  drule unsigned_decoded_zero >> strip_tac >>
  Cases_on `EVERY (\b. b = 0w) bs` >>
  asm_rewrite_tac[ valueEncodingTheory.typed_val_to_w256_def,
       valueEncodingTheory.val_to_w256_def, bool_to_word_def]
QED

Theorem bytes_bool_fresh_run:
  compile_type_convert v (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (r,sb) /\ eval_operand v ss = SOME a /\
  fresh_vars_wrt sa ss /\ LENGTH bs <= 32 /\ w2n (a+32w) = w2n a+32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a+32) (LENGTH bs) ss.vs_memory = bs ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME
      (typed_val_to_w256 (BaseTV BoolT) (BoolV (EXISTS (\b. b <> 0w) bs)))
Proof
  strip_tac >> drule bytes_bool_convert_parts >> strip_tac >>
  drule_all unsigned_load_word_decoded_exact >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  drule_all convert_bool_run_actual >> strip_tac >>
  qexists_tac `t` >> simp[bytes_bool_encoding] >>
  irule run_inst_seq_compose_ok >> qexistsl_tac [`u`,`sm`] >> simp[]
QED

Theorem bytes_bool_semantic_run_actual:
  valid_conversion (BaseT (BytesT (Dynamic n))) (BaseT BoolT) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = SOME stv /\
  value_has_type stv v /\
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (r,sb) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ eval_operand op ss = SOME a /\
  w2n a+32 < dimword(:256) /\ val_in_memory stv v (w2n a) ss.vs_memory ==>
  ?vout sf.
    convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT BoolT) v = INL vout /\
    evaluate_type (get_tenv cx) (BaseT BoolT) = SOME (BaseTV BoolT) /\
    run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME (typed_val_to_w256 (BaseTV BoolT) vout) /\
    sf = ss with vs_vars := sf.vs_vars /\
    (!z w. not_fresh_at sa z /\ lookup_var z ss = SOME w ==> lookup_var z sf = SOME w)
Proof
  strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, valid_conversion_def] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, valueEncodingTheory.val_in_memory_def] >>
  rename1 `mem_bytes_at _ _ _ = bs` >>
  `LENGTH bs <= 32` by decide_tac >>
  `w2n (a+32w) = w2n a+32` by
    simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, LESS_MOD] >>
  `fresh_vars_wrt sa (drop_fresh sa ss) /\
   eval_operand op (drop_fresh sa ss) = SOME a` by
    simp[varsExtTheory.fresh_vars_wrt_drop_fresh,
         freshWritesTheory.eval_operand_drop_fresh] >>
  `mem_word_at (w2n a) (drop_fresh sa ss).vs_memory = n2w (LENGTH bs) /\
   mem_bytes_at (w2n a+32) (LENGTH bs) (drop_fresh sa ss).vs_memory = bs` by
    simp[varsExtTheory.drop_fresh_def] >>
  drule_all bytes_bool_fresh_run >> strip_tac >>
  drule bytes_bool_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[varsExtTheory.vars_ext_result_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >>
  `actual = ss with vs_vars := actual.vs_vars /\
   (!z. not_fresh_at sa z ==> FLOOKUP actual.vs_vars z = FLOOKUP ss.vs_vars z)` by
    (irule bytes_bool_run_frame >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qexistsl_tac [`BoolV (EXISTS (\b. b <> 0w) bs)`,`actual`] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  conj_tac
  >- (fs[varsExtTheory.vars_ext_def] >>
      qpat_x_assum `actual = sf with vs_vars := _` SUBST1_TAC >>
      simp[varsExtTheory.eval_operand_vars_ext]) >>
  rpt strip_tac >> fs[lookup_var_def]
QED

Theorem bytes_bool_stmt_frame:
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (r,sb) /\
  run_inst_seq (emitted_insts sa sb) ss = OK sf /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es ss ==>
  stmt_state_rel ctx func cenv cx es sf
Proof
  strip_tac >> drule_all bytes_bool_run_frame >> strip_tac >>
  qpat_x_assum `sf = _` SUBST1_TAC >>
  irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
  fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED

Theorem bytes_bool_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  valid_conversion (expr_type e) (BaseT BoolT) /\
  well_formed_type tenv (BaseT BoolT) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  value_has_type stv v1 /\ expr_body_pre cenv cx env e es /\
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v1,ee) /\
  (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e = BaseT (StringT 0)
   then op = Lit 0w /\ sb = s1
   else compile_type_convert x (mk_convert_op (expr_type e) (BaseT BoolT)) s1 =
        (op,sb)) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var /\ ~ctx_has_dalloca ctx /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  ptr_val_ok cx (expr_type e) v1 x G tn t0 /\ ptr_buf_ok cenv e x G t0 /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) (BaseT BoolT) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx
        (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT BoolT) v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
            lowered_value_type cenv e = BaseT (StringT 0)`
  >- (gvs[] >> `v1 = BytesV []` by
        (Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0))`
         >- (drule_all source_read_zero_bytes >> simp[]) >>
         gvs[] >> drule_all source_read_zero_string >> strip_tac >>
         gvs[vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def]) >>
      qpat_assum `expr_type e = _` (fn th => once_rewrite_tac[GSYM th]) >>
      irule zero_bool_continuation >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `is_bytestring_type (expr_type e)` by simp[is_bytestring_type_def] >>
  `64 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    (drule_all source_lowered_nonzero_capacity >> simp[]) >>
  `?bs. v1 = BytesV bs /\ LENGTH bs <= 32` by
    (gvs[vyperValueTheory.evaluate_type_def, valid_conversion_def] >>
     Cases_on `v1` >> gvs[vyperTypingTheory.value_has_type_def] >> decide_tac) >>
  gvs[] >>
  `?a. eval_operand x t0 = SOME a /\
       val_in_memory stv (BytesV bs) (w2n a) t0.vs_memory /\
       w2n a+32 < dimword(:256)` by metis_tac[bytes_uint_source_packet] >>
  `?src. x = Var src` by
    (Cases_on `x` >> gvs[ptr_val_ok_def, is_word_type_def, ptr_mem_ok_def,
                         ptr_buf_ok_def, op_prov_def]) >>
  gvs[] >> suspend "nonzero"
QED

Resume bytes_bool_continuation[nonzero]:
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn t0 /\
   op_taint tn (Var src) = {} /\ lookup_var src t0 = SOME a /\
   stv <> BaseTV AddressT /\ (!k. stv <> BaseTV (BytesT (Fixed k)))` by
    gvs[ptr_val_ok_def, is_word_type_def, eval_operand_def,
        vyperValueTheory.evaluate_type_def] >>
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
               not_fresh_at s1 p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!z. Var src = Var z ==> not_fresh_at s1 z` by simp[] >>
  drule_all bytes_bool_semantic_run_actual >> strip_tac >>
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn t0 /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by simp[] >>
  drule_all bytes_bool_counted_success >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) sf` by
    (irule bytes_bool_stmt_frame >> goal_assum (drule_at Any) >>
     fs[expr_post_def] >> metis_tac[]) >>
  `expr_post ctx func cenv cx
      (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT) [e])
      es sa sb s0 (ee with gas_obs := []) vout op
      (sf with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule scalar_suffix_expr_post >>
     simp[expr_type_def, is_word_type_def, stmt_state_rel_inst_idx,
          instIdxIndepTheory.eval_op_inst_idx] >>
     conj_tac >- (fs[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
     qexistsl_tac [`e`,`s1`,`t0`,`BytesV bs`,`Var src`] >>
     simp[lookup_var_def] >> conj_tac
     >- metis_tac[lookup_var_def] >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >> simp[]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL vout`,`ee`,`H`,`th`,
    `OK (sf with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[ptr_val_ok_def, is_word_type_def]
QED

Finalise bytes_bool_continuation
