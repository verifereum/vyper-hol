(* Source and compiler boundaries shared by RawLog memory fragments. *)
Theory bodyMemRawLogPrepare
Ancestors
  bodyMemRawLogTopics bodySimCallRawLog bodySimRawLogBodySource
  bodyMemoryPreds exprSimHypsDefs exprSimWordArgs exprSimPrecompiles
  exprSimRawLog exprLowering exprLoweringProps exprOperandVar
  compileEnv emitHelper context emitHelperProps list rich_list fragExec
Libs
  pairLib

Theorem raw_log_mem_source_prepare:
  body_exprs_mem_ok cx [Builtin a (MakeArray elem bd) topics; data] /\
  expr_body_pre cenv cx env
    (Call ann RawLog [Builtin a (MakeArray elem bd) topics; data] dflt) es ==>
  ?n.
    ann = NoneT /\ dflt = NONE /\
    a = ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n) /\
    elem = SOME (BaseT (BytesT (Fixed 32))) /\ bd = Dynamic n /\
    LENGTH topics <= n /\ n <= 4 /\ LENGTH topics <= 4 /\
    body_exprs_mem_ok cx topics /\ expr_sim_inv cenv cx env es /\
    (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
      expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) /\
    (!s. expr_sim_inv cenv cx env s ==> expr_body_pre cenv cx env data s)
Proof
  strip_tac >> drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  (drule_all raw_log_literal_typed >> strip_tac >> gvs[] >>
  `body_exprs_mem_ok cx topics` by
    (qpat_assum `body_exprs_mem_ok cx [_;_]`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_mem_ok_def]) >>
     drule_all body_make_array_children_mem_ok >> simp[]) >>
  simp[] >>
  conj_tac >- fs[expr_body_pre_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
          qpat_x_assum `MEM e topics` mp_tac >>
          qpat_x_assum `expr_sim_inv _ _ _ s` mp_tac >>
          rpt (pop_assum kall_tac) >> rpt strip_tac >>
          metis_tac[expr_body_pre_raw_log_arg, expr_body_pre_make_array_arg, MEM]) >>
      fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  rpt strip_tac >> irule expr_body_pre_raw_log_arg >>
  qpat_assum `expr_body_pre _ _ _ (Call _ RawLog _ _) _` (irule_at Any) >> simp[])
QED

Theorem raw_log_dynamic_compile_stages:
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  compile_expr cenv ty
    (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt) sa =
      (StackValue ann (Lit 0w),sb) ==>
  ?ops sm data_op sn len_op sl ptr_op sp.
    lower_word_args cenv expr_type topics sa = (ops,sm) /\
    lower_value compile_expr cenv (expr_type data) data sm = (data_op,sn) /\
    emit_op MLOAD [data_op] sn = (len_op,sl) /\
    emit_op ADD [data_op; Lit 32w] sl = (ptr_op,sp) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] sp = ((),sb)
Proof
  strip_tac >> qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem raw_log_fixed_compile_stages:
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  compile_expr cenv ty
    (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt) sa =
      (StackValue ann (Lit 0w),sb) ==>
  ?ops sm buf sk data_op sn sp.
    lower_word_args cenv expr_type topics sa = (ops,sm) /\
    compile_alloc_buffer 32 sm = (buf,sk) /\
    lower_value compile_expr cenv (expr_type data) data sk = (data_op,sn) /\
    emit_void MSTORE [buf.buf_operand;data_op] sn = ((),sp) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] sp = ((),sb)
Proof
  strip_tac >> qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem raw_log_dynamic_stage_structure:
  wb_args_shape cenv expr_type topics /\
  lower_word_args cenv expr_type topics sa = (ops,sm) /\
  lower_value compile_expr cenv (expr_type data) data sm = (data_op,sn) /\
  emit_op MLOAD [data_op] sn = (len_op,sl) /\
  emit_op ADD [data_op; Lit 32w] sl = (ptr_op,sp) /\
  emit_inst LOG log_ops [] sp = ((),sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\ cs_extends sm sb /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sn.cs_next_id /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn /\
  LENGTH ops = LENGTH topics /\
  EVERY (\op. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l)) ops /\
  (!z. data_op = Var z ==> not_fresh_at sn z)
Proof
  strip_tac >> drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sn /\ sm.cs_next_var <= sn.cs_next_var /\
   sm.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends sn sl /\ cs_extends sl sp /\ cs_extends sp sb` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, comp_return_def,
          comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
          cs_extends_def] >> rpt strip_tac >> gvs[] >>
     simp[cs_extends_def, IS_PREFIX_APPEND]) >>
  `cs_extends sn sb /\ cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  simp[] >> metis_tac[compile_lower_value_var]
QED

Theorem raw_log_fixed_stage_structure:
  wb_args_shape cenv expr_type topics /\
  lower_word_args cenv expr_type topics sa = (ops,sm) /\
  compile_alloc_buffer 32 sm = (buf,sk) /\
  lower_value compile_expr cenv (expr_type data) data sk = (data_op,sn) /\
  emit_void MSTORE [buf.buf_operand;data_op] sn = ((),sp) /\
  emit_inst LOG log_ops [] sp = ((),sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  cs_extends sa sm /\ cs_extends sm sk /\ cs_extends sk sn /\
  cs_extends sn sb /\ cs_extends sk sb /\ cs_extends sm sb /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sk.cs_next_var /\
  sk.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sk.cs_next_id /\
  sk.cs_next_id <= sn.cs_next_id /\
  fn_has_code sa sm func /\ fn_has_code sm sk func /\
  fn_has_code sk sn func /\ fn_has_code sn sb func /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sk /\ local_ptrs_reserved cenv sn /\
  LENGTH ops = LENGTH topics /\
  EVERY (\op. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l)) ops /\
  (!z. data_op = Var z ==> not_fresh_at sn z)
Proof
  strip_tac >> drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sk /\ sm.cs_next_var <= sk.cs_next_var /\
   sm.cs_next_id <= sk.cs_next_id` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
          comp_bind_def, comp_return_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, IS_PREFIX_APPEND]) >>
  `cs_extends sk sn /\ sk.cs_next_var <= sn.cs_next_var /\
   sk.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends sn sp /\ cs_extends sp sb` by
    (qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
          fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, IS_PREFIX_APPEND]) >>
  `cs_extends sn sb /\ cs_extends sk sb /\ cs_extends sm sb` by
    metis_tac[cs_extends_trans] >>
  `cs_extends sa sk /\ cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sk func /\
   fn_has_code sk sn func /\ fn_has_code sn sb func` by
    (rpt conj_tac >> irule fn_has_code_mid >> simp[] >>
     qexistsl_tac [`sb`, `sa`] >> simp[cs_extends_refl]) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sk /\
   local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  simp[] >> metis_tac[compile_lower_value_var]
QED
