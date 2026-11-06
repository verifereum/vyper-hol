(* Full semantic continuation pieces for bytes-to-uint, retaining ghost posts. *)
Theory bodyPtrTypeBuiltinsUintContinue
Ancestors bodyPtrTypeBuiltinsSourceTyping bodyPtrTypeBuiltinsFrameProbe
  bodyPtrTypeBuiltinsUnsignedValue bodyPtrTypeBuiltinsLiteralPost
  exprSimConvert exprSimWordArgs exprSimDefs fragGasPathPtr gasSummaryComposePtr
  loweringPosts exprLoweringProps compileEnv vyperAST venomState bodyPtrDefs
  exprSimProps loweringShapeDefs bodyPtrTypeBuiltinsUintActual
  bodyPtrTypeBuiltinsUintCounted bodyPtrTypeBuiltinsScalarCompose opcodeClass bodyPtrTypeBuiltinsUnsignedLoad venomInst exprLowering ptrDiscipline builtinConvertPrefix emitHelperProps fragExec bodyPtrTypeBuiltinsClamp
Libs monadsyntax

Theorem zero_convert_child_post:
  expr_post ctx func cenv cx e es sa s1 s0 ee v1 x s /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv /\
  typed_val_to_w256 tv v = 0w ==>
  expr_post ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa s1 s0
    ee v (Lit 0w) s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def] >> metis_tac[]
QED

Theorem zero_uint_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  valid_conversion (expr_type e) (BaseT (UintT b)) /\
  well_formed_type tenv (BaseT (UintT b)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  value_has_type stv v1 /\ v1 = BytesV [] /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) (BaseT (UintT b)) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx
        (TypeBuiltin (BaseT (UintT b)) Convert (BaseT (UintT b)) [e])
        es sa s1 s0 fin v (Lit 0w) ss /\
      ss.vs_current_bb = s1.cs_current_bb /\
      ss.vs_inst_idx = LENGTH s1.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT (UintT b)) v (Lit 0w) H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >> gvs[] >>
  simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_def,
       vyperValueOperationTheory.evaluate_convert_def,
       listTheory.PAD_LEFT, byteTheory.word_of_bytes_be_def,
       GSYM rich_listTheory.REPLICATE_GENLIST,
       valueEncodingProofsTheory.word_of_bytes_replicate_zero,
       vyperValueTheory.within_int_bound_def] >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (IntV 0)`,`ee`,`G`,`tn`,`OK t0`] >>
  simp[gas_path_ptr_rules, ptr_val_ok_word_literal, is_word_type_def] >>
  irule zero_convert_child_post >>
  gvs[is_word_type_def, vyperValueTheory.evaluate_type_def,
       vyperTypeSystemTheory.well_formed_type_def,
       valueEncodingTheory.typed_val_to_w256_def,
       valueEncodingTheory.val_to_w256_def, integer_wordTheory.i2w_def] >>
  goal_assum (drule_at Any)
QED

(* Semantic post transport for a memory-preserving scalar suffix. *)
Theorem scalar_suffix_expr_post:
  expr_post ctx func cenv cx e es sa s1 s0 ee v1 x t0 /\
  stmt_state_rel ctx func cenv cx ee s /\
  evaluate_type (get_tenv cx) (expr_type eout) = SOME tv /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  (!z w. not_fresh_at s1 z /\ lookup_var z t0 = SOME w ==>
         lookup_var z s = SOME w) /\
  s.vs_allocas = t0.vs_allocas /\ s.vs_memory = t0.vs_memory /\
  is_word_type (expr_type eout) /\ sa.cs_next_var <= s1.cs_next_var ==>
  expr_post ctx func cenv cx eout es sa sb s0 ee v op s
Proof
  simp[expr_post_def] >> strip_tac >>
  `locals_kept cenv es s0 s` by
    (irule locals_kept_mem_tail >> qexists_tac `t0` >> asm_rewrite_tac[]) >>
  simp[expr_val_rel_def, expr_val_at_def] >> conj_tac
  >- (rpt strip_tac >> rename1 `lookup_var z s0 = SOME w` >>
      `not_fresh_at s1 z` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
      qpat_x_assum `!z w. not_fresh_at s1 z /\ lookup_var z t0 = _ ==> _`
        irule >> asm_rewrite_tac[] >>
      qpat_x_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = _ ==> _`
        irule >> asm_rewrite_tac[]) >>
  rpt strip_tac >> fs[] >> metis_tac[]
QED

Theorem bytes_uint_read_length:
  expr_body_pre cenv cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  valid_conversion (expr_type e) (BaseT (UintT b)) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  ?bs. v = BytesV bs /\ LENGTH bs <= 32
Proof
  strip_tac >>
  `is_bytestring_type (expr_type e)` by simp[is_bytestring_type_def] >>
  drule_all source_read_bytestring_view >>
  gvs[is_bytestring_type_def, vyperTypeSystemTheory.valid_conversion_def] >>
  strip_tac >> gvs[] >> decide_tac
QED

(* Placement yields the actual memory view and excludes the wrapping ADD. *)
Theorem bytes_uint_source_packet:
  expr_post ctx func cenv cx e es sa s1 s0 ee (BytesV bs) x t0 /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv ==>
  ?a. eval_operand x t0 = SOME a /\
      val_in_memory stv (BytesV bs) (w2n a) t0.vs_memory /\
      w2n a + 32 < dimword(:256)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee t0 /\
   expr_val_rel cx (expr_type e) (BytesV bs) x t0 /\
   expr_val_at cenv cx (expr_type e) sa s1 ee (BytesV bs) x t0` by
    fs[expr_post_def] >>
  `?a. eval_operand x t0 = SOME a /\
       val_in_memory stv (BytesV bs) (w2n a) t0.vs_memory` by
    gvs[expr_val_rel_def, is_word_type_def] >>
  `~is_word_type (expr_type e) /\
   32 <= val_footprint stv (BytesV bs)` by
    gvs[is_word_type_def, val_footprint_def,
        vyperValueTheory.evaluate_type_def] >>
  drule_all expr_val_at_payload_nonwrap >> strip_tac >>
  qexists_tac `a` >> simp[]
QED


Theorem bytes_uint_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  valid_conversion (expr_type e) (BaseT (UintT b)) /\
  well_formed_type tenv (BaseT (UintT b)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  value_has_type stv v1 /\ expr_body_pre cenv cx env e es /\
  supported_expr tops e /\ supported_program tops /\
  get_module_code cx NONE = SOME tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v1,ee) /\
  (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e = BaseT (StringT 0)
   then op = Lit 0w /\ sb = s1
   else compile_type_convert x (mk_convert_op (expr_type e) (BaseT (UintT b))) s1 =
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
    (\vs. (convert_result cx (expr_type e) (BaseT (UintT b)) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx
        (TypeBuiltin (BaseT (UintT b)) Convert (BaseT (UintT b)) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT (UintT b)) v op H th ss /\
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
      irule zero_uint_continuation >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `is_bytestring_type (expr_type e)` by simp[is_bytestring_type_def] >>
  `64 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    (drule_all source_lowered_nonzero_capacity >> simp[]) >>
  `?bs. v1 = BytesV bs /\ LENGTH bs <= 32` by metis_tac[bytes_uint_read_length] >>
  gvs[] >>
  `?a. eval_operand x t0 = SOME a /\
       val_in_memory stv (BytesV bs) (w2n a) t0.vs_memory /\
       w2n a+32 < dimword(:256)` by metis_tac[bytes_uint_source_packet] >>
  `?src. x = Var src` by
    (Cases_on `x` >> gvs[ptr_val_ok_def, is_word_type_def, ptr_mem_ok_def,
                         ptr_buf_ok_def, op_prov_def]) >>
  gvs[] >>
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn t0 /\
   op_taint tn (Var src) = {} /\ lookup_var src t0 = SOME a /\
   stv <> BaseTV AddressT /\ (!k. stv <> BaseTV (BytesT (Fixed k)))` by
    gvs[ptr_val_ok_def, is_word_type_def, eval_operand_def,
        vyperValueTheory.evaluate_type_def] >>
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
               not_fresh_at s1 p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!z. Var src = Var z ==> not_fresh_at s1 z` by simp[] >>
  drule_all (SRULE [] (Q.INST
    [`res` |-> `convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT (UintT b)) (BytesV bs)`,
     `v` |-> `BytesV bs`] bytes_uint_semantic_run_actual)) >>
  Cases_on `convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT (UintT b)) (BytesV bs)` >>
  simp[] >> strip_tac
  >- suspend "success" >>
  suspend "abort"
QED

Resume bytes_uint_continuation[success]:
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn t0 /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by simp[] >>
  drule_all bytes_uint_counted_success >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) sf` by
    (irule uint_convert_stmt_frame >> goal_assum (drule_at Any) >>
     fs[expr_post_def] >> metis_tac[]) >>
  `expr_post ctx func cenv cx
      (TypeBuiltin (BaseT (UintT b)) Convert (BaseT (UintT b)) [e])
      es sa sb s0 (ee with gas_obs := []) x op
      (sf with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule scalar_suffix_expr_post >>
     simp[expr_type_def, is_word_type_def, stmt_state_rel_inst_idx,
          instIdxIndepTheory.eval_op_inst_idx] >>
     conj_tac >- (fs[stmt_state_rel_gas_obs]) >>
     qexistsl_tac [`e`,`s1`,`t0`,`BytesV bs`,`Var src`] >>
     simp[lookup_var_def] >> conj_tac
     >- metis_tac[lookup_var_def] >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >> simp[]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL x`,`ee`,`H`,`th`,
    `OK (sf with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[ptr_val_ok_def, is_word_type_def]
QED

Resume bytes_uint_continuation[abort]:
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn t0 /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by simp[] >>
  drule_all bytes_uint_counted_abort >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`ee`,`H`,`th`,
    `Abort Revert_abort (sf with vs_inst_idx := j)`] >>
  simp[exit_result_def, expr_exit_def]
QED

Finalise bytes_uint_continuation
