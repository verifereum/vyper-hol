(* Physical RHS layout is recovered from the actual post, not buffer capacity. *)
Theory widenedAssignPtrRhsInput
Ancestors exprSimHyps exprSimHypsDefs exprOperandVar bodyPtrDefs loweringPosts exprSimProps
  compileEnv valueEncoding valueEncodingDefs venomExecSemantics venomState
  ptrDiscipline finite_map words exprPtrUnwrapIdentity externalReturnIntcallProducer
  gasSummaryComposePtr valueCopyBytes exprLowering context
  staticTypeFitsPtr abiTupleValueEncoding exprSimLayoutTransport
  bodyPtrStructLitLayoutTransfer

Theorem retained_rhs_physical_input_ptr:
  !ce cx env e es ctx fn sa sb s0 ee v op s G tn ty.
    expr_body_pre ce cx env e es /\
    expr_post ctx fn ce cx e es sa sb s0 ee v op s /\
    ~is_word_type (post_value_type ce e) /\
    lower_value compile_expr ce ty e sa = (op,sb) /\
    local_ptrs_reserved ce sa /\
    ptr_val_ok cx (post_value_type ce e) v op G tn s /\
    ptr_buf_ok ce e op G s ==>
    ?tv w.
      evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
      type_memory_bytes ce (post_value_type ce e) = type_memory_size tv /\
      val_wf tv v /\ eval_operand op s = SOME w /\
      op_taint tn op = {} /\
      expr_val_at ce cx (post_value_type ce e) sa sb ee v op s /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory tv v (w2n w) m) /\
      (type_memory_bytes ce (lowered_value_type ce e) = 0 \/
       ?src. op = Var src /\ lookup_var src s = SOME w /\
         not_fresh_at sb src /\
         (!dst. ~not_fresh_at sb dst ==> src <> dst) /\
         ptr_covers G tn src s (type_memory_bytes ce (lowered_value_type ce e)))
Proof
  rpt gen_tac >> strip_tac >>
  drule post_type_evaluates >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `expr_val_at ce cx (post_value_type ce e) sa sb ee v op s` by
    fs[expr_post_def] >>
  `val_wf tv v /\ ?w. eval_operand op s = SOME w` by
    (fs[expr_val_at_def] >> metis_tac[]) >>
  qexistsl_tac [`tv`,`w`] >> simp[] >>
  `op_taint tn op = {} /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory tv v (w2n w) m)` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  simp[] >>
  Cases_on `type_memory_bytes ce (lowered_value_type ce e) = 0` >> simp[] >>
  drule compile_lower_value_var >> disch_then drule >> disch_tac >>
  fs[ptr_buf_ok_def] >> first_x_assum drule >> simp[] >> strip_tac >>
  gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]
QED

Theorem retained_intcall_unwrap_read_ptr:
  compile_expr ce ct (Call ann (IntCall fid) args drv) sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sb) /\
  ~is_word_type (post_value_type ce (Call ann (IntCall fid) args drv)) /\
  vv_post ctx fn ce cx (Call ann (IntCall fid) args drv) es sa sm s0 ee raw vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d ce cx ee G tn s /\
  ptr_vv_ok cx (post_value_type ce (Call ann (IntCall fid) args drv))
    raw vv ee G tn s /\
  ptr_buf_ok ce (Call ann (IntCall fid) args drv) (vv_operand vv) G s /\
  ghost_kept ce es sa G0 tn0 s0 G tn ==>
  ?v Gf tnf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG (read_result cx raw)
      (ee,s,G,tn) [] (INL v) ee Gf tnf (OK u) /\
    expr_post ctx fn ce cx (Call ann (IntCall fid) args drv)
      es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d ce cx ee Gf tnf u /\
    ptr_val_ok cx (post_value_type ce (Call ann (IntCall fid) args drv))
      v op Gf tnf u /\
    ptr_buf_ok ce (Call ann (IntCall fid) args drv) op Gf u /\
    ghost_kept ce es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >> drule return_compile_intcall_output >> strip_tac
  >- (`~is_word_type (ce.ce_func_return_type (nsid_to_string fid))` by
        (fs[vv_post_def, vv_holds_def] >> metis_tac[is_bytestring_word_type]) >>
      gvs[vv_operand_def, Excl "post_value_type_def"] >>
      drule_all unwrap_memory_marked_read_ptr >> metis_tac[]) >>
  gvs[vv_operand_def, Excl "post_value_type_def"] >>
  `~is_word_type (post_value_type ce (Call ann (IntCall fid) args drv)) ==>
   ptr_buf_ok ce (Call ann (IntCall fid) args drv) (Lit 0w) G s` by simp[] >>
  drule_all unwrap_stack_marked_read_ptr >> simp[]
QED

Theorem retained_intcall_physical_layout:
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  ~(lowered_value_type ce (Call ann (IntCall fid) args drv) = ann \/
    is_bytestring_type ann /\
    is_bytestring_type (lowered_value_type ce (Call ann (IntCall fid) args drv)) /\
    arg_type_fits (lowered_value_type ce (Call ann (IntCall fid) args drv)) ann) ==>
  ~is_word_type ann /\ ~is_bytestring_type ann /\
  post_value_type ce (Call ann (IntCall fid) args drv) =
    lowered_value_type ce (Call ann (IntCall fid) args drv) /\
  ~is_word_type (post_value_type ce (Call ann (IntCall fid) args drv)) /\
  ?tv. evaluate_type (get_tenv cx)
         (post_value_type ce (Call ann (IntCall fid) args drv)) = SOME tv /\
       type_memory_bytes ce (lowered_value_type ce (Call ann (IntCall fid) args drv)) =
         type_memory_size tv /\
       type_memory_size tv < 2 ** 64
Proof
  strip_tac >> drule ifexp_body_pre_intcall_physical >> strip_tac >>
  `~is_word_type ann` by
    (strip_tac >>
     `~is_abi_dynamic ce.ce_struct_fields ann` by metis_tac[abi_word_metadata] >>
     drule (INST_TYPE [alpha |-> ``:string``, beta |-> ``:num``]
       (cj 1 static_arg_type_fits)) >>
     disch_then (qspec_then `ce.ce_struct_fields` mp_tac) >> fs[]) >>
  `~is_bytestring_type ann` by metis_tac[arg_type_fits_bytestring_source] >>
  `~is_word_type (lowered_value_type ce (Call ann (IntCall fid) args drv))` by
    metis_tac[compatible_word_type] >>
  simp[Excl "post_value_type_def"] >>
  `post_value_type ce (Call ann (IntCall fid) args drv) =
   lowered_value_type ce (Call ann (IntCall fid) args drv)` by simp[] >>
  simp[Excl "post_value_type_def"] >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `type_memory_bytes ce (lowered_value_type ce (Call ann (IntCall fid) args drv)) =
   type_memory_size tvp` by metis_tac[expr_sim_inv_memory_size] >>
  drule expr_body_pre_type_evaluates >> simp[vyperASTTheory.expr_type_def] >>
  strip_tac >> Cases_on `evaluate_type (get_tenv cx) ann` >> fs[] >>
  rename1 `evaluate_type (get_tenv cx) ann = SOME atv` >>
  `type_memory_size atv < 2 ** 64` by
    (drule expr_body_pre_copy_ok >> simp[vyperASTTheory.expr_type_def] >>
     disch_then drule >> simp[]) >>
  `type_memory_size tvp <= type_memory_size atv` by
    metis_tac[arg_type_fits_memory_size] >>
  fs[]
QED
