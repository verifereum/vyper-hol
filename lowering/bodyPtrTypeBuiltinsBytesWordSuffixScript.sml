Theory bodyPtrTypeBuiltinsBytesWordSuffix
Ancestors
  bodyPtrTypeBuiltinsBytesWordParts bodyPtrTypeBuiltinsScalarArithmetic
  bodyPtrSignedConvertClamp bodyPtrSignedConvertBool
  bodyPtrSignedConvertSourceFrame fragGasPathPtr venomState venomInst
  venomExecSemantics emitHelperProps builtinConvertPrefix
  exprLoweringProps exprLowering compileEnv finite_map arithmetic

(* One boundary for the three suffix implementations; no source memory facts
   are needed once both loaded operands are clean. *)
Theorem loaded_word_suffix_counted:
  (compile_type_convert word ConvToBool sa = (out,sb) \/
   emit_op SHL [bits;word] sa = (out,sb) \/
   (?signed b. compile_int_clamp signed b word sa = (out,sb))) /\
  op_prov G word = NONE /\ op_prov G bits = NONE /\
  op_taint tn word = {} /\ op_taint tn bits = {} /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac
  >- (drule_all convert_bool_counted_certificate >> metis_tac[])
  >- (drule_all (SRULE []
        (Q.INST [`opc` |-> `SHL`] scalar_emit_counted_certificate)) >> metis_tac[]) >>
  drule_all int_clamp_counted_certificate >> metis_tac[]
QED

Theorem loaded_word_suffix_runtime_frame:
  (compile_type_convert word ConvToBool sa = (out,sb) \/
   emit_op SHL [bits;word] sa = (out,sb) \/
   (?signed b. compile_int_clamp signed b word sa = (out,sb))) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac
  >- (drule_all convert_bool_runtime_frame >> simp[])
  >- (irule scalar_emit_runtime_frame >> simp[] >>
      qexistsl_tac [`SHL`,`out`,`sb`,`bits`,`word`] >> simp[]) >>
  drule_all int_clamp_runtime_frame >> simp[]
QED

Theorem loaded_word_suffix_ghost:
  (compile_type_convert word ConvToBool sa = (out,sb) \/
   emit_op SHL [bits;word] sa = (out,sb) \/
   (?signed b. compile_int_clamp signed b word sa = (out,sb))) /\
  op_prov G word = NONE /\ op_prov G bits = NONE /\
  op_taint tn word = {} /\ op_taint tn bits = {} /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
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
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) /\
    (t with vs_vars := s.vs_vars) = s
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all loaded_word_suffix_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all loaded_word_suffix_runtime_frame >> strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient` by
    (qpat_x_assum `(_ with vs_vars := _) = _` (fn eq =>
       map_every (fn q => mp_tac (Q.AP_TERM q eq))
         [`\v. v.vs_memory`,`\v. v.vs_call_ctx`,
          `\v. v.vs_accounts`,`\v. v.vs_transient`]) >> simp[]) >>
  `ghost_inv d cenv cx es H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`s`,`tn`] >> simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `ghost_kept cenv es0 s0a G0 tn0 s0 H th` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`tn`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]
QED

Theorem loaded_word_suffix_filter:
  (compile_type_convert word ConvToBool sa = (out,sb) \/
   emit_op SHL [bits;word] sa = (out,sb) \/
   (?signed b. compile_int_clamp signed b word sa = (out,sb))) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac
  >- (drule convert_bool_code >> strip_tac >>
      simp[mk_inst_def, is_terminator_def])
  >- (drule_all (SRULE [] (Q.INST [`opc` |-> `SHL`]
        scalar_emit_instruction_filter)) >> simp[]) >>
  drule int_clamp_instruction_filter >> simp[]
QED

Theorem loaded_word_suffix_shape:
  (compile_type_convert word ConvToBool sa = (out,sb) \/
   emit_op SHL [bits;word] sa = (out,sb) \/
   (?b. compile_int_clamp F b word sa = (out,sb))) ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac
  >- (conj_tac
      >- (fs[compile_type_convert_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
          imp_res_tac inst_extends_emit_op >> metis_tac[inst_extends_trans]) >>
      drule convert_bool_code >> strip_tac >> simp[])
  >- (imp_res_tac inst_extends_emit_op >> imp_res_tac emit_op_extends >>
      drule emitted_insts_emit_op >> strip_tac >> gvs[same_blocks_def]) >>
  imp_res_tac builtinConvertPrefixTheory.inst_extends_compile_int_clamp >>
  drule int_clamp_unsigned_code >> strip_tac >> simp[]
QED

Theorem loaded_word_pure_suffix_no_abort:
  (compile_type_convert word ConvToBool sa = (out,sb) \/
   emit_op SHL [bits;word] sa = (out,sb)) ==>
  run_inst_seq (emitted_insts sa sb) s <> Abort err t
Proof
  strip_tac
  >- (drule convert_bool_code >> strip_tac >>
      gvs[run_inst_seq_def, AllCaseEqs()] >>
      metis_tac[bodyPtrSignedConvertScalarOpsTheory.scalar_iszero_no_abort]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `SHL`] scalar_emit_no_abort)) >> simp[]
QED
