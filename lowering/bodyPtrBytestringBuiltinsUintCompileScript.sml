Theory bodyPtrBytestringBuiltinsUintCompile
Ancestors
  bodyPtrBytestringBuiltinsUintResult bodyPtrBytestringBuiltinsUintReady
  bodyPtrBytestringBuiltinsUint2Str wordArgsPtr exprSimUint2Str
  bodyPtrDefs fragGasPathPtr loweringPosts venomState venomExecSemantics
  venomInst ptrDiscipline compileEnv contextCodegenRel codegenRel words list arithmetic
  exprLowering vyperAST vyperValue valueEncoding vfmConstants

Theorem compile_uint2str_counted_ptr:
  compile_uint2str op n sz sa = (out,sb) /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME (n2w X) /\ op_prov G op = NONE /\ op_taint tn op = {} /\
  X < dimword(:256) /\ 78 <= n /\ 32 <= sz /\ sz+n < dimword(:256) /\
  post_value_type cenv e = expr_type e /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT cap)) /\
  type_memory_bytes cenv (lowered_value_type cenv e) =
    type_memory_size (BaseTV (StringT cap)) /\
  type_memory_size (BaseTV (StringT cap)) = sz /\
  val_wf (BaseTV (StringT cap)) (StringV (num_to_dec_string X)) /\
  LENGTH (num_to_dec_string X)+32 <= type_memory_size (BaseTV (StringT cap)) /\
  val_footprint (BaseTV (StringT cap)) (StringV (num_to_dec_string X)) <= sz ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es sa G tn s G' tn' /\
    vv_post ctx fn cenv cx e es sa sb s es (Value (StringV (num_to_dec_string X)))
      (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>) t /\
    ptr_vv_ok cx (expr_type e) (Value (StringV (num_to_dec_string X)))
      (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>)
      es G' tn' t /\ ptr_buf_ok cenv e out G' t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> drule compile_uint2str_layout >> strip_tac >>
  drule_all u2s_alloc_ready_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_kept cenv es a G1 tn1 ready G1 tn1` by simp[ghost_kept_refl] >>
  `lookup_block ready.vs_current_bb fn.fn_blocks = SOME
     <|bb_label := a.cs_current_bb;
       bb_instructions := a.cs_current_insts ++ u2s_setup a op (Var p)|>` by simp[] >>
  drule_all (SRULE [] (Q.INST
    [`bb` |-> `<|bb_label := a.cs_current_bb;
       bb_instructions := a.cs_current_insts ++ u2s_setup a op (Var p)|>`]
    u2s_setup_exit_invariant_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >>
  conj_tac >- metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
  conj_tac >- suspend "kept" >>
  conj_tac >- suspend "post" >>
  suspend "ptr"
QED

Resume compile_uint2str_counted_ptr[kept]:
  `wb_frame cenv es es sa s ready` by
    (qpat_x_assum `!out. u2s_safe _ _ _ _ _ _ _ _ _ _ _ out ==> _`
       (qspec_then `ready` mp_tac) >> simp[]) >>
  irule u2s_alloc_loop_ghost_kept >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G1`, `a`, `ba`, `ready`, `sz+n`, `tn1`] >> simp[]
QED

Resume compile_uint2str_counted_ptr[post]:
  `LENGTH (num_to_dec_string X) <= n` by
    (mp_tac (Q.INST [`x` |-> `X`] uint256_decimal_length) >>
     fs[dimword_def] >> decide_tac) >>
  `b <= b+n-LENGTH (num_to_dec_string X) /\
   b+n-LENGTH (num_to_dec_string X) < dimword(:256) /\
   b+n-LENGTH (num_to_dec_string X) +
     val_footprint (BaseTV (StringT cap)) (StringV (num_to_dec_string X)) <= b+(sz+n)`
    by decide_tac >>
  `wb_frame cenv es es sa s t /\ pure_frame cenv fn es sa s t` by
    (qpat_x_assum `!out. u2s_safe _ _ _ _ _ _ _ _ _ _ _ out ==> _`
       (qspec_then `t` mp_tac) >> simp[]) >>
  `inst.inst_id = sa.cs_next_id` by simp[mk_inst_def] >>
  `u2s_safe ctx fn cenv cx es a ba.buf_operand b (sz+n) inst sr t` by metis_tac[] >>
  drule_all u2s_result_vv_post >> simp[]
QED

Resume compile_uint2str_counted_ptr[ptr]:
  `b+n-LENGTH (num_to_dec_string X) < dimword(:256)` by decide_tac >>
  `type_memory_size (BaseTV (StringT cap)) <= sz` by simp[] >>
  drule_all u2s_result_ptr_post >>
  disch_then (qspec_then `es` strip_assume_tac) >>
  simp[] >> gvs[u2s_layout_def, u2s_end_def]
QED

Finalise compile_uint2str_counted_ptr

(* The family caller uses this concrete builtin/type, not an arbitrary
   expression satisfying additional representation assumptions. *)
Theorem u2s_builtin_result_requirements:
  expr_body_pre cenv cx env (Builtin (BaseT (StringT n)) (Uint2Str n) args) es /\
  X < dimword(:256) /\ 78 <= n /\
  sz = type_memory_bytes cenv (BaseT (StringT n)) ==>
  ~is_word_type (expr_type (Builtin (BaseT (StringT n)) (Uint2Str n) args)) /\
  evaluate_type (get_tenv cx)
    (expr_type (Builtin (BaseT (StringT n)) (Uint2Str n) args)) =
      SOME (BaseTV (StringT n)) /\
  type_memory_bytes cenv
    (lowered_value_type cenv (Builtin (BaseT (StringT n)) (Uint2Str n) args)) =
      type_memory_size (BaseTV (StringT n)) /\
  type_memory_size (BaseTV (StringT n)) = sz /\ 32 <= sz /\
  sz+n < dimword(:256) /\
  val_wf (BaseTV (StringT n)) (StringV (num_to_dec_string X)) /\
  LENGTH (num_to_dec_string X)+32 <= type_memory_size (BaseTV (StringT n)) /\
  val_footprint (BaseTV (StringT n)) (StringV (num_to_dec_string X)) <= sz
Proof
  strip_tac >> drule_all uint2str_result_memory_bounds >> strip_tac >>
  drule uint2str_body_capacity >> strip_tac >>
  `LENGTH (num_to_dec_string X) <= n` by
    (mp_tac (Q.INST [`x` |-> `X`] uint256_decimal_length) >>
     fs[dimword_def] >> decide_tac) >>
  simp[expr_type_def, is_word_type_def, evaluate_type_def,
       type_slot_size_def, lowered_value_type_def, type_memory_size_def, type_memory_bytes_def,
       word_size_def] >>
  gvs[type_memory_bytes_def, word_size_def, dimword_def] >> decide_tac
QED
