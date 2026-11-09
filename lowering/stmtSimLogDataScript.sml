Theory stmtSimLogData
Ancestors
  loweringPosts
  stmtSimLogTopics exprSimBufferStore stmtLowering context compileEnv loweringStateRelDefs
  supportedTypes vyperValue valueEncoding words list abiEncoderInput
  emitHelper exprLoweringProps venomExecSemantics venomInst venomState emitHelperProps

Theorem compile_log_store_data_cons:
  supported_scalar_type ty ==>
  compile_log_store_data cenv ((src,ty)::rest) buf off =
    do dst <- emit_op ADD [buf; Lit (n2w off)];
       compile_store_memory cenv src dst ty ty;
       compile_log_store_data cenv rest buf (off + type_memory_bytes cenv ty)
    od
Proof
  strip_tac >> simp[Once compile_log_store_data_def] >>
  drule log_scalar_topic_shape >> strip_tac >>
  Cases_on `is_bytestring_type ty`
  >- simp[compile_store_memory_def] >>
  `is_word_type ty` by metis_tac[] >>
  simp[compile_store_memory_def]
QED

Theorem log_scalar_memory_size:
  supported_scalar_type ty /\ evaluate_type tenv ty = SOME tv ==>
  type_memory_bytes cenv ty = type_memory_size tv
Proof
  Cases_on `ty` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def,
       evaluate_type_def, type_memory_bytes_def, type_memory_size_def] >>
  rpt strip_tac >> gvs[type_memory_size_def, vfmConstantsTheory.word_size_def] >>
  rename1 `BaseT (BytesT bd)` >> Cases_on `bd` >>
  gvs[supported_word_type_def, supported_string_type_def,
       evaluate_type_def, type_memory_bytes_def, type_memory_size_def,
       vfmConstantsTheory.word_size_def, AllCaseEqs()]
QED

Theorem log_data_prefix_bounds:
  !cenv tys i off cap.
    i < LENGTH tys /\ off + SUM (MAP (type_memory_bytes cenv) tys) <= cap ==>
    off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) +
      type_memory_bytes cenv (EL i tys) <= cap
Proof
  rpt strip_tac >>
  drule abiEncoderInputTheory.abi_encoder_prefix_sum_bound >>
  disch_then (qspec_then `type_memory_bytes cenv` assume_tac) >> decide_tac
QED

Theorem log_data_address_run:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sb) /\
  eval_operand buf s = SOME (n2w b) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand dst t = SOME (n2w (b + off)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operand_def, bind_outputs_def] >>
  simp[run_inst_seq_def, word_add_n2w, lookup_var_update_var] >>
  conj_tac >- simp[update_var_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem log_data_address_shape:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. dst = Var x ==> not_fresh_at sb x)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> simp[]
QED

Theorem log_data_address_value:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sb) /\
  eval_operand buf s = SOME (n2w b) /\
  expr_val_rel cx ty v src s /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand dst t = SOME (n2w (b + off)) /\
    expr_val_rel cx ty v src t /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all log_data_address_run >> strip_tac >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t with vs_vars := _ = s`
      (mp_tac o AP_TERM ``\z. z.vs_memory``) >> simp[]) >>
  `eval_operand src t = eval_operand src s` by
    (Cases_on `src` >> simp[eval_operand_def]
     >- (qpat_assum `t with vs_vars := _ = s`
           (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
     first_x_assum irule >> first_x_assum irule >> simp[]) >>
  qexists_tac `t` >> gvs[loweringPostsTheory.expr_val_rel_def]
QED

Theorem log_data_field_run:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm) /\
  compile_store_memory cenv src dst ty ty sm = ((),sb) /\
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ expr_val_rel cx ty v src s /\
  eval_operand buf s = SOME (n2w b) /\ b + off < dimword (:256) /\
  type_memory_bytes cenv ty < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
    val_in_memory tv v (b + off) q.vs_memory /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (!a k. a + k <= b + off \/ b + off + type_memory_size tv <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >> drule_all log_data_address_value >> strip_tac >>
  drule log_data_address_shape >> strip_tac >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >- (irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `sa` >> simp[]) >> simp[]) >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (drule_all log_scalar_memory_size >> simp[]) >>
  `type_memory_size tv < dimword (:256)` by metis_tac[] >>
  drule_all buffer_store_memory_encoding >> simp[] >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t with vs_vars := _ = s`
      (mp_tac o AP_TERM ``\z. z.vs_memory``) >> simp[]) >>
  qexists_tac `q` >> simp[] >>
  conj_tac >-
    (qpat_assum `q with <|vs_memory := _; vs_vars := _|> = t`
       (mp_tac o AP_TERM ``\z. z with vs_vars := s.vs_vars``) >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sm x` by
      (irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `sa` >> simp[]) >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at _ _ q.vs_memory = _`
    (qspecl_then [`a`, `k`] mp_tac) >> simp[]
QED
