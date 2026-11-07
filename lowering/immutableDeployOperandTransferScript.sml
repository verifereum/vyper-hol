(* Immutable stores whose input operands are syntactically old.
   Generated temporaries may already be populated in the initial state. *)
Theory immutableDeployOperandTransfer
Ancestors
  immutableDeployAssignExecution immutableDeployAssignTransfer
  immutableWordExecution immutableCopyExecution moduleLoweringProps
  exprSimWordBuiltins context compileEnv venomState venomInst
  emitHelperProps exprLoweringProps fragExec venomExecSemantics
  placeMemoryFieldsForward exprSimMapKey typedMemoryCopy ctorAbiActualObservations

Theorem immutable_store_word_old_execution:
  compile_imm_store_word imm dst value sa = ((),sb) /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  eval_operand dst s = SOME a /\
  eval_operand value s = SOME v ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    t.vs_memory = (mstore (w2n a) v s).vs_memory /\
    t.vs_immutables = s.vs_immutables |+ (w2n a,v)
Proof
  Cases_on `imm`
  >- (simp[compile_imm_store_word_def, emitHelperTheory.emit_void_def,
           fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def] >> strip_tac >> gvs[] >>
      qexists_tac `istore (w2n a) v s` >>
      simp[emitted_insts_def, listTheory.DROP_APPEND, run_inst_seq_def,
           mk_inst_def, step_inst_base_def, eval_operands_def,
           istore_def, mstore_def, lookup_var_def]) >>
  simp[] >> strip_tac >>
  `eval_operand value (update_var (STRING #"%" (toString sa.cs_next_var)) a s) = SOME v` by
    (drule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     disch_then (qspecl_then [`s`,`sa.cs_next_var`,`a`] mp_tac) >> simp[]) >>
  drule_all (SRULE [] compile_imm_store_word_execution) >> strip_tac >>
  qexists_tac `istore (w2n a) v
    (update_var (STRING #"%" (toString sa.cs_next_var)) a s)` >>
  simp[istore_def, mstore_def, update_var_def] >>
  rpt strip_tac >>
  gvs[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem immutable_byte_offset_old_execution:
  compile_lit_byte_offset op off sa = (out,sb) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME a ==>
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  (!x. out = Var x ==> not_fresh_at sb x) /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME (a + n2w off) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def, same_blocks_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[emitted_insts_def, same_blocks_def, run_inst_seq_def, wordsTheory.WORD_ADD_0]) >>
  Cases_on `?w. op = Lit w`
  >- (strip_tac >> gvs[compile_lit_byte_offset_def, comp_return_def,
                       emitted_insts_def, same_blocks_def, eval_operand_def] >> qexists_tac `s` >>
      simp[emitted_insts_def, same_blocks_def, run_inst_seq_def, eval_operand_def]) >>
  strip_tac >>
  `compile_with_byte_offset op off sa = (out,sb)` by
    (Cases_on `op` >> gvs[compile_lit_byte_offset_def, compile_with_byte_offset_def]) >>
  drule_all compile_with_byte_offset_fresh >> strip_tac >> simp[] >>
  drule_all compile_with_byte_offset_sequence >> strip_tac >>
  simp[] >> qexists_tac `u` >> simp[]
QED

Theorem immutable_store_one_old_execution:
  immutable_store_one imm src dst off sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    t.vs_memory = (immutable_word_transfer T T a b off s).vs_memory /\
    t.vs_immutables = (immutable_word_transfer T T a b off s).vs_immutables
Proof
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (sp,c1)` >>
  rename1 `emit_op MLOAD [sp] c1 = (loaded,c2)` >>
  rename1 `compile_lit_byte_offset dst off c2 = (dp,c3)` >>
  qpat_assum `compile_lit_byte_offset src off sa = _`
    (mp_then Any mp_tac immutable_byte_offset_old_execution) >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  drule emit_MLOAD_frame >>
  disch_then (qspec_then `s1` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule typed_copy_emit_op_fresh >> strip_tac >>
  `!x. dst = Var x ==> not_fresh_at c2 x` by
    fs[not_fresh_at_def] >>
  `eval_operand dst s2 = SOME b /\
   (!region. imm = SOME region ==> eval_operand region s2 = SOME 0w)` by
    suspend "old_inputs" >>
  qpat_assum `compile_lit_byte_offset dst off c2 = _`
    (mp_then Any mp_tac immutable_byte_offset_old_execution) >>
  disch_then (qspec_then `s2` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `(!x. loaded = Var x ==> not_fresh_at c3 x) /\
   eval_operand loaded s3 = SOME (mload (w2n (a+n2w off)) s) /\
   (!region. imm = SOME region ==> eval_operand region s3 = SOME 0w)` by suspend "store_inputs" >>
  drule_all immutable_store_word_old_execution >> strip_tac >>
  qexists_tac `t` >> suspend "compose"
QED

Resume immutable_store_one_old_execution[old_inputs]:
  `s1.vs_labels = s.vs_labels` by
    (qpat_x_assum `s1 with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `s2.vs_labels = s1.vs_labels` by
    (qpat_x_assum `s2 with vs_vars := _ = s1` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s` by
    (rpt strip_tac >> `not_fresh_at c1 x` by fs[not_fresh_at_def] >> simp[]) >>
  conj_tac
  >- (irule ctor_actual_old_operand >> qexistsl_tac [`s`,`sa`] >>
      simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule ctor_actual_old_operand >>
  qexistsl_tac [`s`,`sa`] >> simp[] >> metis_tac[]
QED
Resume immutable_store_one_old_execution[store_inputs]:
  `s3.vs_labels = s2.vs_labels` by
    (qpat_x_assum `s3 with vs_vars := _ = s2` mp_tac >>
     simp[venom_state_component_equality]) >>
  `s1.vs_memory = s.vs_memory` by
    (qpat_x_assum `s1 with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  conj_tac >- fs[not_fresh_at_def] >>
  conj_tac >-
    (irule ctor_actual_old_operand >> qexistsl_tac [`s2`,`c2`] >>
     fs[mload_def]) >>
  rpt strip_tac >> irule ctor_actual_old_operand >> qexistsl_tac [`s2`,`c2`] >>
  simp[] >> fs[not_fresh_at_def] >> metis_tac[]
QED
Resume immutable_store_one_old_execution[compose]:
  `c3.cs_next_var <= sb.cs_next_var /\
   sb.cs_current_insts = c3.cs_current_insts ++ emitted_insts c3 sb /\
   same_blocks c3 sb` by
    (qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `imm` >>
     simp_tac (srw_ss()) [compile_imm_store_word_def, emitHelperTheory.emit_op_def,
          emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def,
          same_blocks_def, emitted_insts_def, listTheory.DROP_APPEND] >>
     strip_tac >> gvs[emitted_insts_def, listTheory.DROP_APPEND, same_blocks_def]) >>
  `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2` by
    (irule emitted_insts_append >> simp[]) >>
  `c2.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c2` by
    simp[listTheory.APPEND_ASSOC] >>
  `emitted_insts sa c3 = emitted_insts sa c2 ++ emitted_insts c2 c3` by
    (irule emitted_insts_append >> simp[]) >>
  `c3.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c3` by
    simp[listTheory.APPEND_ASSOC] >>
  `emitted_insts sa sb = emitted_insts sa c3 ++ emitted_insts c3 sb` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac >-
    (qpat_assum `run_inst_seq (emitted_insts sa c1) s = _`
       (mp_then Any assume_tac run_inst_seq_append) >>
     `run_inst_seq (emitted_insts sa c2) s = OK s2` by metis_tac[] >>
     pop_assum (mp_then Any assume_tac run_inst_seq_append) >>
     `run_inst_seq (emitted_insts sa c3) s = OK s3` by metis_tac[] >>
     pop_assum (mp_then Any assume_tac run_inst_seq_append) >> metis_tac[]) >>
  conj_tac >- simp[listTheory.APPEND_ASSOC] >>
  conj_tac >-
    (`same_blocks c3 sb` by
       (qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
        simp[compile_imm_store_word_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def, comp_bind_def,
             comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
             emit_def, same_blocks_def] >> strip_tac >> gvs[]) >>
     gvs[same_blocks_def]) >>
  conj_tac >- decide_tac >>
  conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at c1 x /\ not_fresh_at c2 x /\ not_fresh_at c3 x` by
       fs[not_fresh_at_def] >> simp[]) >>
  qpat_x_assum `s1 with vs_vars := _ = s` mp_tac >>
  qpat_x_assum `s2 with vs_vars := _ = s1` mp_tac >>
  qpat_x_assum `s3 with vs_vars := _ = s2` mp_tac >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s3` mp_tac >>
  simp[venom_state_component_equality, immutable_word_transfer_def,
       immutable_copy_read_def, istore_def, mstore_def]
QED
Finalise immutable_store_one_old_execution

Theorem immutable_store_words_old_execution:
  !n off sa sb s.
  compile_imm_store_words imm src dst n off sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    t.vs_memory = (immutable_transfers T T a b n off s).vs_memory /\
    t.vs_immutables = (immutable_transfers T T a b n off s).vs_immutables
Proof
  Induct
  >- (simp[compile_imm_store_words_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[emitted_insts_def, same_blocks_def, run_inst_seq_def,
           immutable_transfers_def]) >>
  rpt gen_tac >> simp[immutable_store_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  strip_tac >> rename1 `immutable_store_one _ _ _ _ sa = (u,c1)` >>
  Cases_on `u` >>
  drule_all (SRULE [] immutable_store_one_old_execution) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  `(!x. src = Var x ==> not_fresh_at c1 x) /\
   (!x. dst = Var x ==> not_fresh_at c1 x) /\
   (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at c1 x)` by fs[not_fresh_at_def] >>
  `eval_operand src s1 = SOME a /\ eval_operand dst s1 = SOME b /\
   (!region. imm = SOME region ==> eval_operand region s1 = SOME 0w)` by suspend "operands" >>
  qpat_x_assum `!off sa sb s. _` drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 sb) s1 = OK s2` >>
  qexists_tac `s2` >> suspend "compose"
QED
Resume immutable_store_words_old_execution[operands]:
  `s1.vs_labels = s.vs_labels` by
    (qpat_x_assum `s1 with <|vs_memory := _; vs_vars := _; vs_immutables := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  conj_tac >- (irule ctor_actual_old_operand >>
    qexistsl_tac [`s`,`sa`] >> simp[]) >>
  conj_tac >- (irule ctor_actual_old_operand >>
    qexistsl_tac [`s`,`sa`] >> simp[]) >>
  rpt strip_tac >> irule ctor_actual_old_operand >>
  qexistsl_tac [`s`,`sa`] >> simp[] >> metis_tac[]
QED
Resume immutable_store_words_old_execution[compose]:
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac >-
    (qpat_assum `run_inst_seq (emitted_insts sa c1) s = _`
       (mp_then Any mp_tac run_inst_seq_append) >> simp[]) >>
  conj_tac >- simp[listTheory.APPEND_ASSOC] >>
  conj_tac >- gvs[same_blocks_def] >>
  conj_tac >- decide_tac >>
  conj_tac >-
    (rpt strip_tac >> `not_fresh_at c1 x` by fs[not_fresh_at_def] >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `s1 with <|vs_memory := _; vs_vars := _; vs_immutables := _|> = s`
       mp_tac >>
     qpat_x_assum `s2 with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s1`
       mp_tac >> simp[venom_state_component_equality]) >>
  `s1.vs_data_section = (immutable_word_transfer T T a b off s).vs_data_section` by
    (qpat_x_assum `s1 with <|vs_memory := _; vs_vars := _; vs_immutables := _|> = s`
       mp_tac >> simp[venom_state_component_equality, immutable_transfer_data]) >>
  simp[immutable_transfers_def] >>
  irule immutable_transfers_cong >> simp[]
QED
Finalise immutable_store_words_old_execution

Theorem immutable_words_old_prefix_path:
  compile_imm_store_words imm src dst n 0 sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  k <= 32*n /\ a+k < dimword (:256) /\ b+32*n < dimword (:256) /\
  (a+k <= b \/ b+32*n <= a) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    gas_marked_path F ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    mem_bytes_at b k u.vs_memory = mem_bytes_at a k s.vs_memory /\
    (!p len. p+len <= b \/ b+32*n <= p ==>
      mem_bytes_at p len u.vs_memory = mem_bytes_at p len s.vs_memory) /\
    u.vs_immutables = (immutable_transfers T T (n2w a) (n2w b) n 0 s).vs_immutables
Proof
  strip_tac >> (drule_all immutable_store_words_old_execution >> strip_tac >>
  `gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule placeTypedCopyPathTheory.place_copy_seq_path >> simp[] >>
      qexists_tac `sa` >> simp[] >>
      drule immutable_store_words_insts >> strip_tac >>
      fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
      qpat_x_assum `!i. MEM i (emitted_insts sa sb) ==> _`
        (qspec_then `i` mp_tac) >> simp[] >>
      strip_tac >> gvs[is_terminator_def] >> metis_tac[is_terminator_def]) >>
  qexists_tac `t` >> simp[] >>
  conj_tac >- (irule immutable_transfers_memory_prefix >> simp[]) >>
  rpt strip_tac >> irule immutable_transfers_memory_frame >> simp[])
QED

Theorem immutable_direct_composite_old_path:
  compile_assign_value cenv dst LocCode src F src_loc dty sty da mem_size sa = ((),sb) /\
  cenv.ce_imm_alloca = imm /\
  (dty = sty \/ (is_bytestring_type dty /\ is_bytestring_type sty)) /\
  copy_size = (if is_bytestring_type dty then type_memory_bytes cenv sty else mem_size) /\
  n = (if copy_size <= 32 then 1 else (copy_size+31) DIV 32) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  k <= 32*n /\ a+k < dimword (:256) /\ b+32*n < dimword (:256) /\
  (a+k <= b \/ b+32*n <= a) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    gas_marked_path F ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    mem_bytes_at b k u.vs_memory = mem_bytes_at a k s.vs_memory /\
    (!p len. p+len <= b \/ b+32*n <= p ==>
      mem_bytes_at p len u.vs_memory = mem_bytes_at p len s.vs_memory) /\
    u.vs_immutables = (immutable_transfers T T (n2w a) (n2w b) n 0 s).vs_immutables
Proof
  rpt gen_tac >> disch_tac >>
  gvs[stmtLoweringTheory.compile_assign_value_def, immutable_comp_bind_cases,
      comp_return_def] >>
  (qmatch_asmsub_abbrev_tac `copybytes <= 32` >>
   Cases_on `copybytes <= 32` >> gvs[]
   >- (`compile_imm_store_words cenv.ce_imm_alloca src dst 1 0 sa = ((),sb)` by
         (pure_rewrite_tac[arithmeticTheory.ONE] >>
          qpat_x_assum `(do loaded <- _; _ od) sa = _` mp_tac >>
          simp[compile_imm_store_words_def, compile_lit_byte_offset_def,
               comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
          Cases_on `emit_op MLOAD [src] sa` >> simp[] >>
          pairarg_tac >> simp[]) >>
       irule (SRULE [arithmeticTheory.ADD_COMM]
         (Q.INST [`n` |-> `1`] immutable_words_old_prefix_path)) >>
       simp[] >> metis_tac[]) >>
   irule (SRULE [arithmeticTheory.ADD_COMM] immutable_words_old_prefix_path) >>
   simp[] >> metis_tac[])
QED
