(* The bytestring cast suffix tests the reached length, not the buffer size. *)
Theory bodyConvertBytesCastRunMods
Ancestors
  bodyFullConvertCastOrigin bodyPtrTypeBuiltinsMemoryInterface
  bodyPtrTypeBuiltinsMemoryBounds bodyPtrIfExpCopyHeader
  bodyPtrSignedConvertSourceTyping exprSimConvertBytes valueCopyBytes
  bodyFullShadowBodyInv bodyPtrDefs loweringPosts venomState vyperAST

Theorem bytes_convert_cast_run_mods:
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  type_alloc_ok ce (expr_type e) /\ type_alloc_ok ce dst /\
  type_memory_bytes ce dst <= type_memory_bytes ce (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  value_has_type pt v /\ ptr_val_ok cx (post_value_type ce e) v op G tn t /\
  eval_operand op t = SOME a /\
  (type_memory_bytes ce (lowered_value_type ce e) = 0 \/
   w2n a + type_memory_bytes ce (lowered_value_type ce e) <= t.vs_alloca_next) /\
  (0 < type_memory_bytes ce (lowered_value_type ce e) ==>
   ?src. op = Var src /\ not_fresh_at sm src /\
         ptr_covers G tn src t (type_memory_bytes ce (lowered_value_type ce e))) /\
  ghost_inv_at_mods Di lo d ce cx mid G tn t /\
  compile_type_convert op (mk_convert_op (expr_type e) dst) sm = (out,sb) /\
  fn_has_code sm sb func /\ ~t.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  out = op /\
  ((?vout src q Gf tnf.
    convert_result cx (expr_type e) dst v = INL vout /\
    op = Var src /\ not_fresh_at sm src /\
    lookup_var src t = SOME a /\ lookup_var src q = SOME a /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK q,Gf,tnf)) /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame q = state_frame (t with vs_inst_idx := q.vs_inst_idx) /\
    (!p. not_fresh_at sm p ==> lookup_var p q = lookup_var p t /\
         FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm) \/
   (?msg q Gf tnf.
    convert_result cx (expr_type e) dst v = INR (Error (RuntimeError msg)) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
      (Abort Revert_abort q,Gf,tnf)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 <= type_memory_bytes ce dst` by (irule bytestring_memory_header_bound >> simp[]) >>
  `32 <= type_memory_bytes ce (lowered_value_type ce e)` by decide_tac >>
  `0 < type_memory_bytes ce (lowered_value_type ce e)` by decide_tac >>
  qpat_x_assum `0 < _ ==> _`
    (drule_then (qx_choose_then `src` (CONJUNCTS_THEN2 SUBST_ALL_TAC strip_assume_tac))) >>
  qpat_x_assum `eval_operand (Var src) t = _`
    (assume_tac o REWRITE_RULE [eval_operand_def]) >>
  `w2n a + 32 <= t.vs_alloca_next` by decide_tac >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `post_value_type ce e = expr_type e` by simp[] >>
  pop_assum (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  qspecl_then [`expr_type e`,`dst`] mp_tac memory_convert_shapes >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`i`,`n`] strip_assume_tac) >>
  `i < dimword(:256) /\ n < dimword(:256)` by
    metis_tac[bytestring_alloc_capacity_bound] >>
  `?L. L <= i /\ ((?bs. v = BytesV bs /\ L = LENGTH bs) \/
                   (?str. v = StringV str /\ L = LENGTH str))` by
    (drule_all bytestring_typed_value_view >> strip_tac >> fs[] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory pt v (w2n a) mem` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_val_ok_def, ptr_mem_ok_def, is_bytestring_word_type, eval_operand_def] >>
     metis_tac[]) >>
  `mload (w2n a) t = n2w L /\
   (!j. w2n a <= j /\ j < w2n a + 32 ==> j NOTIN tn.t_mem)` by
    (irule robust_bytestring_header >>
     qexistsl_tac [`pt`,`expr_type e`,`get_tenv cx`,`v`] >> simp[]) >>
  `compile_type_convert (Var src) (ConvBytestringCast n i) sm = (out,sb)` by
    metis_tac[] >>
  drule_all convert_cast_origin_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  (conj_tac >- asm_rewrite_tac[]) >>
  (Cases_on `L <= n`
   >- (qpat_x_assum `L <= n ==> _`
         (drule_then (qx_choosel_then [`q`,`Gf`,`tnf`] strip_assume_tac)) >>
       `?vout. convert_result cx (expr_type e) dst v = INL vout` by
         fs[convert_result_bytes_to_bytestring, convert_result_string_to_bytestring] >>
       `lookup_var src q = SOME a` by
         (qpat_assum `!p. not_fresh_at sm p ==> _` (qspec_then `src` mp_tac) >> simp[]) >>
       disj1_tac >> qexistsl_tac [`vout`,`src`,`q`,`Gf`,`tnf`] >> asm_rewrite_tac[]) >>
   `n < L` by decide_tac >>
   qpat_x_assum `n < L ==> _`
     (drule_then (qx_choosel_then [`q`,`Gf`,`tnf`] strip_assume_tac)) >>
   `?msg. convert_result cx (expr_type e) dst v = INR (Error (RuntimeError msg))` by
     fs[convert_result_bytes_to_bytestring, convert_result_string_to_bytestring] >>
   disj2_tac >> qexistsl_tac [`msg`,`q`,`Gf`,`tnf`] >> asm_rewrite_tac[])
QED
