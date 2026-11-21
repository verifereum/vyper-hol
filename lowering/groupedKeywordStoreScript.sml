(* Store an evaluated omitted default in its reserved argument buffer. *)
Theory groupedKeywordStore
Ancestors
  bodyFullExtCallSlotWrite bodyFullExtCallDefaultBytesStore bodyDeclMemoryCore
  annassignRelayoutSource exprSimMemDefs exprSimProps loweringPosts exprLowering context typedMemoryCopy
  bodyPtrDefs fragGasOriginPtr compileEnv valueCopyBytes vyperTyping venomState arithmetic

Theorem grouped_keyword_store_value:
  (if is_word_type ty then emit_void MSTORE [Var dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src (Var dst)
   else emit_void MCOPY [Var dst;src;Lit (n2w (type_memory_bytes ce ty))])
    sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  expr_val_rel cx ty v src s /\ ptr_val_ok cx ty v src G tn s /\
  expr_store_bound cx ty v src s /\ (~is_word_type ty ==> val_wf tv v) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s (type_memory_size tv) /\
  w2n b + type_memory_size tv <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory tv v (w2n b) m) /\
    typed_copy_state_frame sa (w2n b) (type_memory_size tv) s t /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!i. i < w2n b \/ w2n b+type_memory_size tv <= i ==>
         (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >>
  qpat_assum `expr_val_rel cx ty v src s`
    (strip_assume_tac o REWRITE_RULE[expr_val_rel_def]) >>
  qpat_assum `ptr_val_ok cx ty v src G tn s`
    (strip_assume_tac o REWRITE_RULE[ptr_val_ok_def]) >>
  Cases_on `is_word_type ty`
  >- (irule extcall_tuple_slot_write >>
      asm_rewrite_tac[] >> qexistsl_tac [`ce`,`cx`,`dst`,`src`,`ty`] >>
      `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
      fs[]) >>
  rename1 `eval_operand src s = SOME a` >>
  `(!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m) /\
   (val_footprint tv v <> 0 ==>
      ?x. src = Var x /\ ptr_covers G tn x s (val_store_size tv v))` by
    (qpat_assum `~is_word_type ty ==> ptr_mem_ok cx ty v src G tn s`
      (strip_assume_tac o UNDISCH) >>
     qpat_assum `ptr_mem_ok cx ty v src G tn s`
       (mp_tac o REWRITE_RULE[ptr_mem_ok_def]) >>
     disch_then (qspecl_then [`tv`,`a`] mp_tac) >> asm_rewrite_tac[] >>
     strip_tac >> asm_rewrite_tac[] >> strip_tac >>
     qpat_assum `val_footprint tv v <> 0 ==> _` (drule_then strip_assume_tac) >>
     qexists_tac `x` >> asm_rewrite_tac[ptr_covers_def, eval_operand_def] >>
     metis_tac[eval_operand_def]) >>
  `val_store_size tv v <> 0 ==> w2n a + val_store_size tv v <= s.vs_alloca_next` by
    (qpat_assum `expr_store_bound cx ty v src s` (mp_tac o REWRITE_RULE[expr_store_bound_def]) >>
     disch_then (qspecl_then [`tv`,`a`] mp_tac) >> asm_rewrite_tac[] >> metis_tac[]) >>
  Cases_on `is_bytestring_type ty`
  >- suspend "bytes"
  >> suspend "flat"
QED

Resume grouped_keyword_store_value[flat]:
  `val_store_size tv v = type_memory_size tv /\ val_footprint tv v = type_memory_size tv` by
    metis_tac[val_store_size_non_bytestring, nonbytes_evaluated_val_footprint] >>
  irule extcall_tuple_slot_write >>
  asm_rewrite_tac[] >> qexistsl_tac [`ce`,`cx`,`dst`,`src`,`ty`] >>
  asm_rewrite_tac[] >> simp[] >>
  Cases_on `type_memory_size tv = 0`
  >- fs[ptr_covers_def] >>
  gvs[]
QED

Resume grouped_keyword_store_value[bytes]:
  `val_footprint tv v <> 0 /\ val_store_size tv v <> 0` by
    (drule_all bytestring_type_value >> strip_tac >> Cases_on `v` >>
     gvs[value_has_type_def, val_footprint_def, val_store_size_def]) >>
  `w2n a + val_store_size tv v <= s.vs_alloca_next` by simp[] >>
  qpat_assum `val_footprint tv v <> 0 ==> _` (drule_then strip_assume_tac) >>
  gvs[eval_operand_def] >>
  `compile_store_memory ce (Var x) (Var dst) ty ty sa = ((),sb)` by
    simp[compile_store_memory_def] >>
  `w2n b + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
  mp_tac (Q.INST [`rt` |-> `ty`,`sty` |-> `ty`,`stv` |-> `tv`,
    `src` |-> `x`,`sw` |-> `a`,`dw` |-> `b`,`func` |-> `fn`,
    `v` |-> `v`,`lo` |-> `lo`,`ctx` |-> `ctx`,`G` |-> `G`,`tn` |-> `tn`]
    bytestring_store_extent_joint) >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  qexistsl_tac [`u`,`Gf`,`tm`] >> asm_rewrite_tac[] >>
  qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[venom_state_component_equality, typed_copy_state_frame_def, typed_copy_frame_def] >>
  strip_tac >> simp[] >> conj_tac
  >- (qx_genl_tac [`off`,`k`] >> disch_tac >>
      qpat_assum `!off k. _ ==> mem_bytes_at off k u.vs_memory = _`
        (qspecl_then [`off`,`k`] mp_tac) >>
      impl_tac >- decide_tac >> disch_then ACCEPT_TAC) >>
  gen_tac >> disch_tac >> qpat_assum `!i. _ ==> (i IN tm.t_mem <=> _)`
    (qspec_then `i` mp_tac) >> impl_tac >- decide_tac >> disch_then ACCEPT_TAC
QED

Finalise grouped_keyword_store_value
