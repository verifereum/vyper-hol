(* Address shares Uint160 code, not its semantic value constructor. *)
Theory bodyPtrTypeBuiltinsAddressContinue
Ancestors bodyPtrTypeBuiltinsUintContinue bodyPtrTypeBuiltinsUintCounted
  bodyPtrTypeBuiltinsUintActual bodyPtrTypeBuiltinsBytesUintSemantics
  bodyPtrTypeBuiltinsUnsignedSemantics exprSimConvert exprLowering
  builtinConvertPrefix compileEnv exprLoweringProps emitHelperProps
  fragExec venomState words valueEncoding valueEncodingProofs vyperValue
  vyperTypeSystem vyperTyping vyperValueOperation byte rich_list list
  exprSimProps varsExt freshWrites finite_map vfmTypes
  bodyPtrTypeBuiltinsSourceTyping bodyPtrDefs fragGasPathPtr exprSimDefs
  exprSimWordArgs vyperAST loweringPosts instIdxIndep
Libs monadsyntax

Theorem bytes_address_compile_op:
  mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT AddressT) =
  mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT (UintT 160))
Proof
  simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def]
QED

Theorem bytes_address_encoding:
  w2n (x:bytes32) < 2 ** 160 ==>
  typed_val_to_w256 (BaseTV AddressT) (AddressV (n2w (w2n x))) = x
Proof
  strip_tac >>
  gvs[typed_val_to_w256_def, GSYM word_to_bytes_w2w_address,
       word_of_bytes_be_def, vfmTypesTheory.word_to_bytes_word_of_bytes_256,
       w2w_n2w, w2n_n2w, dimword_def, arithmeticTheory.LESS_MOD,
       bitTheory.BITS_ZERO3, fcpLib.INDEX_CONV ``dimindex(:160)``]
QED

Theorem bytes_address_conversion_result:
  LENGTH bs <= 32 ==>
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV bs) =
  if within_int_bound (Unsigned 160)
       (&(w2n (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs)))))
  then INL (AddressV (n2w (w2n
       (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs))))))
  else INR (Error (RuntimeError "convert bytes address"))
Proof
  strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       unsigned_payload_padding, within_int_bound_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem bytes_address_fresh_run:
  compile_type_convert v (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT AddressT)) sa = (r,sb) /\
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV bs) = res /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= n /\ n <= 32 /\ w2n (a+32w) = w2n a+32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a+32) (LENGTH bs) ss.vs_memory = bs ==>
  case res of
  | INL vout => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 (BaseTV AddressT) vout)
  | INR ex => (?m. ex = Error (RuntimeError m)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `compile_type_convert v (ConvBytestringToInt F 160 n) sa = (r,sb)` by
    gvs[mk_convert_op_def, is_bytestring_type_def, type_bounds_def] >>
  `LENGTH bs <= 32` by decide_tac >>
  drule_all (SRULE [] (Q.INST [`b` |-> `160:num`] bytes_uint_raw_exact)) >> simp[] >>
  qpat_x_assum `convert_result _ _ _ _ = _` mp_tac >>
  simp[bytes_address_conversion_result] >>
  qmatch_goalsub_abbrev_tac `within_int_bound (Unsigned 160) i` >>
  Cases_on `within_int_bound (Unsigned 160) i` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  `w2n (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs))) < 2 ** 160` by
    gvs[within_int_bound_def, Abbr `i`] >>
  simp[bytes_address_encoding] >> goal_assum (drule_at Any)
QED

Theorem bytes_address_semantic_run_actual:
  valid_conversion (BaseT (BytesT (Dynamic n))) (BaseT AddressT) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = SOME stv /\
  value_has_type stv v /\
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) v = res /\
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT AddressT)) sa = (r,sb) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ eval_operand op ss = SOME a /\
  w2n a+32 < dimword(:256) /\ val_in_memory stv v (w2n a) ss.vs_memory ==>
  case res of
  | INL vout => ?dtv sf. evaluate_type (get_tenv cx) (BaseT AddressT) = SOME dtv /\
      run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 dtv vout) /\
      sf = ss with vs_vars := sf.vs_vars /\
      (!z w. not_fresh_at sa z /\ lookup_var z ss = SOME w ==>
             lookup_var z sf = SOME w)
  | INR ex => (?m. ex = Error (RuntimeError m)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `?bs. v = BytesV bs /\ LENGTH bs <= n /\ n <= 32 /\
    mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (w2n a+32) (LENGTH bs) ss.vs_memory = bs` by
    (gvs[vyperValueTheory.evaluate_type_def, valid_conversion_def] >>
     Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def]) >>
  gvs[] >>
  `fresh_vars_wrt sa (drop_fresh sa ss) /\
   eval_operand op (drop_fresh sa ss) = SOME a` by
    simp[fresh_vars_wrt_drop_fresh, eval_operand_drop_fresh] >>
  `w2n (a+32w) = w2n a+32` by simp[w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `mem_word_at (w2n a) (drop_fresh sa ss).vs_memory = n2w (LENGTH bs) /\
   mem_bytes_at (w2n a+32) (LENGTH bs) (drop_fresh sa ss).vs_memory = bs` by
    simp[drop_fresh_def] >>
  drule_all (SRULE [] (Q.INST
    [`res` |-> `convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV bs)`]
    bytes_address_fresh_run)) >>
  disch_then (qspec_then `cx` mp_tac) >>
  Cases_on `convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV bs)` >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac
  >- suspend "success" >>
  drule (REWRITE_RULE [GSYM bytes_address_compile_op] (Q.INST [`b` |-> `160:num`] uint_convert_replay)) >>
  disch_then (qspec_then `ss` mp_tac) >> simp[vars_ext_result_def] >> metis_tac[]
QED

Resume bytes_address_semantic_run_actual[success]:
  drule (REWRITE_RULE [GSYM bytes_address_compile_op] (Q.INST [`b` |-> `160:num`] uint_convert_replay)) >>
  disch_then (qspec_then `ss` mp_tac) >> simp[vars_ext_result_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >>
  `actual = ss with vs_vars := actual.vs_vars /\
   (!z. not_fresh_at sa z ==> FLOOKUP actual.vs_vars z = FLOOKUP ss.vs_vars z)` by
    (irule (REWRITE_RULE [GSYM bytes_address_compile_op] (Q.INST [`b` |-> `160:num`] uint_convert_run_frame)) >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  qexists_tac `actual` >> simp[] >> conj_tac
  >- (fs[vars_ext_def] >>
      qpat_x_assum `actual = sf with vs_vars := _` SUBST1_TAC >>
      simp[eval_operand_vars_ext]) >>
  rpt strip_tac >> fs[lookup_var_def]
QED

Finalise bytes_address_semantic_run_actual

Theorem zero_address_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ v1 = BytesV [] /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) (BaseT AddressT) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx
        (TypeBuiltin (BaseT AddressT) Convert (BaseT AddressT) [e])
        es sa s1 s0 fin v (Lit 0w) ss /\
      ss.vs_current_bb = s1.cs_current_bb /\
      ss.vs_inst_idx = LENGTH s1.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT AddressT) v (Lit 0w) H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >> gvs[] >>
  `convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV []) =
    INL (AddressV 0w)` by
    (simp[bytes_address_conversion_result, word_of_bytes_be_def,
          word_of_bytes_def, within_int_bound_def, ZERO_SHIFT]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (AddressV 0w)`,`ee`,`G`,`tn`,`OK t0`] >>
  simp[gas_path_ptr_rules, bodyPtrTypeBuiltinsLiteralPostTheory.ptr_val_ok_word_literal,
       is_word_type_def] >>
  irule zero_convert_child_post >>
  simp[is_word_type_def, vyperValueTheory.evaluate_type_def] >>
  conj_tac
  >- (mp_tac (Q.INST [`x` |-> `0w:bytes32`] bytes_address_encoding) >> simp[]) >>
  goal_assum (drule_at Any)
QED

Theorem bytes_address_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  valid_conversion (expr_type e) (BaseT AddressT) /\
  well_formed_type tenv (BaseT AddressT) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  value_has_type stv v1 /\ expr_body_pre cenv cx env e es /\
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v1,ee) /\
  (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e = BaseT (StringT 0)
   then op = Lit 0w /\ sb = s1
   else compile_type_convert x (mk_convert_op (expr_type e) (BaseT AddressT)) s1 =
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
    (\vs. (convert_result cx (expr_type e) (BaseT AddressT) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx
        (TypeBuiltin (BaseT AddressT) Convert (BaseT AddressT) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT AddressT) v op H th ss /\
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
         gvs[vyperValueTheory.evaluate_type_def, value_has_type_def]) >>
      qpat_assum `expr_type e = _` (fn th => once_rewrite_tac[GSYM th]) >>
      irule zero_address_continuation >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `is_bytestring_type (expr_type e)` by simp[is_bytestring_type_def] >>
  `64 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    (drule_all source_lowered_nonzero_capacity >> simp[]) >>
  `?bs. v1 = BytesV bs /\ LENGTH bs <= 32` by
    (gvs[vyperValueTheory.evaluate_type_def, valid_conversion_def] >>
     Cases_on `v1` >> gvs[value_has_type_def] >> decide_tac) >>
  gvs[] >>
  `?a. eval_operand x t0 = SOME a /\
       val_in_memory stv (BytesV bs) (w2n a) t0.vs_memory /\
       w2n a+32 < dimword(:256)` by metis_tac[bytes_uint_source_packet] >>
  `?src. x = Var src` by
    (Cases_on `x` >> gvs[ptr_val_ok_def, is_word_type_def, ptr_mem_ok_def,
                         ptr_buf_ok_def, ptrDisciplineTheory.op_prov_def]) >>
  gvs[] >> suspend "nonzero"
QED

Resume bytes_address_continuation[nonzero]:
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn t0 /\
   ptrDiscipline$op_taint tn (Var src) = {} /\ lookup_var src t0 = SOME a /\
   stv <> BaseTV AddressT /\ (!k. stv <> BaseTV (BytesT (Fixed k)))` by
    gvs[ptr_val_ok_def, is_word_type_def, eval_operand_def,
        vyperValueTheory.evaluate_type_def] >>
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
               not_fresh_at s1 p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!z. Var src = Var z ==> not_fresh_at s1 z` by simp[] >>
  drule_all (SRULE [] (Q.INST
    [`res` |-> `convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV bs)`,
     `v` |-> `BytesV bs`] bytes_address_semantic_run_actual)) >>
  Cases_on `convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV bs)` >>
  simp[] >> strip_tac
  >- suspend "success" >>
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn t0 /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by simp[] >>
  drule_all (REWRITE_RULE [GSYM bytes_address_compile_op]
    (Q.INST [`b` |-> `160:num`] bytes_uint_counted_abort)) >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`ee`,`H`,`th`,
    `Abort Revert_abort (sf with vs_inst_idx := j)`] >>
  simp[exit_result_def, expr_exit_def]
QED

Resume bytes_address_continuation[success]:
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn t0 /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by simp[] >>
  drule_all (REWRITE_RULE [GSYM bytes_address_compile_op]
    (Q.INST [`b` |-> `160:num`] bytes_uint_counted_success)) >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) sf` by
    (irule (REWRITE_RULE [GSYM bytes_address_compile_op]
      (Q.INST [`b` |-> `160:num`] uint_convert_stmt_frame)) >>
     goal_assum (drule_at Any) >> fs[expr_post_def] >> metis_tac[]) >>
  `expr_post ctx func cenv cx
      (TypeBuiltin (BaseT AddressT) Convert (BaseT AddressT) [e])
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

Finalise bytes_address_continuation
