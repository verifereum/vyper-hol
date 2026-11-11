(* Clean arithmetic for the finite dynamic-array staging path. *)
Theory appendDynamicPurePtr
Ancestors typedCopyAmbientFramePtr typedCopyPtr
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  bodyPtrDefs compileEnv loweringStateRelDefs context emitHelper finite_map codegenRel contextCodegenRel

Theorem dynamic_binop_ok[local]:
  !D ctx fn G tn s id opc left right tmp fuel.
    (opc = GT \/ opc = MUL) /\ (?k. right = Lit k) /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id opc [left;right] [tmp]) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dynamic_binop_step_ptr:
  !opc f G tn s id left k out a PG.
    (opc = GT /\ f = (\a b. bool_to_word (w2n a > w2n b)) \/
     opc = MUL /\ f = word_mul) /\
    eval_operand left s = SOME a /\ op_taint tn left = {} ==>
    ?u Gf tf.
      u = update_var out (f a k) s /\
      step_inst_base (mk_inst id opc [left;Lit k] [out]) s = OK u /\
      Gf = step_prov PG G (mk_inst id opc [left;Lit k] [out]) u /\
      tf = step_taint (mk_inst id opc [left;Lit k] [out]) s u tn /\
      (!D fuel ctx fn. ~ctx_has_dalloca ctx ==>
        ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [left;Lit k] [out]) s) /\
      (u with vs_vars := s.vs_vars) = s /\
      lookup_var out u = SOME (f a k) /\ op_taint tf (Var out) = {} /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!p. p <> out ==> lookup_var p u = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `update_var out (f a k) s` >>
  qexists_tac `step_prov PG G (mk_inst id opc [left;Lit k] [out])
    (update_var out (f a k) s)` >>
  qexists_tac `step_taint (mk_inst id opc [left;Lit k] [out]) s
    (update_var out (f a k) s) tn` >> simp[] >>
  conj_tac >-
    (gvs[] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM,
       opcode_case_def] >> simp[exec_pure2_def, eval_operand_def]) >>
  conj_tac >- (rpt strip_tac >> irule dynamic_binop_ok >>
    simp[op_taint_def] >> metis_tac[]) >>
  `new_site_bytes s (update_var out (f a k) s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[lookup_var_def, update_var_def, step_prov_def, set_prov_def,
    out_prov_def, step_taint_def, mk_inst_def, set_var_taint_def, out_taint_def,
    op_taint_def, store_taint_def, adopt_reset_def, mem_taint_def, imm_taint_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    range_bytes_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem dynamic_binop_fragment[local]:
  !cx ctx PG sa sb id opc left right tmp f P Q R.
    (opc = GT /\ f = (\a b. bool_to_word (w2n a > w2n b)) \/
     opc = MUL /\ f = word_mul) /\ (?k. right = Lit k) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id opc [left;right] [tmp]] /\
    (!G tn s. P G tn s ==>
      op_taint tn left = {} /\ op_taint tn right = {} /\
      ?a b. eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
        Q (step_prov PG G (mk_inst id opc [left;right] [tmp])
             (update_var tmp (f a b) s))
          (step_taint (mk_inst id opc [left;right] [tmp]) s
             (update_var tmp (f a b) s) tn)
          ((update_var tmp (f a b) s) with vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule ptr_fragment_step >> simp[] >>
  reverse conj_tac >- gvs[is_terminator_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `update_var tmp (f a b) s` >> conj_tac >-
    (gvs[] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM,
       opcode_case_def] >> simp[exec_pure2_def]) >>
  asm_rewrite_tac[] >> simp[update_var_def] >> rpt strip_tac >>
  irule dynamic_binop_ok >> simp[] >> metis_tac[]
QED

Theorem emit_dynamic_binop_clean_ptr:
  !opc f G cx ctx PG R sa sb left k out tn s a.
    (opc = GT /\ f = (\a b. bool_to_word (w2n a > w2n b)) \/
     opc = MUL /\ f = word_mul) /\
    emit_op opc [left; Lit k] sa = (Var out,sb) /\
    eval_operand left s = SOME a /\ op_taint tn left = {} ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      lookup_var out sf = SOME (f a k) /\ op_taint tnf (Var out) = {} /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc [left;Lit k] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all dynamic_binop_step_ptr >>
  disch_then (qspec_then `G` mp_tac) >>
  disch_then (qspecl_then [`sa.cs_next_id`, `k`, `out`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tf`, `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (irule dynamic_binop_fragment >> simp[mk_inst_def] >>
     gvs[mk_inst_def, eval_operand_def, op_taint_def]) >>
  simp[lookup_var_def] >> gvs[update_var_def] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  `p <> out` by metis_tac[] >> simp[]
QED

Theorem dynamic_unary_ok[local]:
  !D ctx fn G tn s id opc arg outs fuel.
    (opc = ISZERO \/ opc = ASSERT) /\ op_taint tn arg = {} /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [arg] outs) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dynamic_iszero_step_ptr:
  !G tn s id arg out a PG.
    eval_operand arg s = SOME a /\ op_taint tn arg = {} ==>
    ?u Gf tf.
      u = update_var out (bool_to_word (a = 0w)) s /\
      step_inst_base (mk_inst id ISZERO [arg] [out]) s = OK u /\
      Gf = step_prov PG G (mk_inst id ISZERO [arg] [out]) u /\
      tf = step_taint (mk_inst id ISZERO [arg] [out]) s u tn /\
      (!D fuel ctx fn. ~ctx_has_dalloca ctx ==>
        ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ISZERO [arg] [out]) s) /\
      (u with vs_vars := s.vs_vars) = s /\
      lookup_var out u = SOME (bool_to_word (a = 0w)) /\
      op_taint tf (Var out) = {} /\ tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!p. p <> out ==> lookup_var p u = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `update_var out (bool_to_word (a = 0w)) s` >>
  qexists_tac `step_prov PG G (mk_inst id ISZERO [arg] [out])
    (update_var out (bool_to_word (a = 0w)) s)` >>
  qexists_tac `step_taint (mk_inst id ISZERO [arg] [out]) s
    (update_var out (bool_to_word (a = 0w)) s) tn` >> simp[] >>
  conj_tac >- simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def] >>
  conj_tac >- (rpt strip_tac >> irule dynamic_unary_ok >> simp[]) >>
  `new_site_bytes s (update_var out (bool_to_word (a = 0w)) s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[lookup_var_def, update_var_def, step_prov_def, set_prov_def,
    out_prov_def, step_taint_def, mk_inst_def, set_var_taint_def, out_taint_def,
    op_taint_def, store_taint_def, adopt_reset_def, mem_taint_def, imm_taint_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    range_bytes_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem dynamic_iszero_fragment[local]:
  !cx ctx PG sa sb id arg out P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id ISZERO [arg] [out]] /\
    (!G tn s. P G tn s ==>
      op_taint tn arg = {} /\
      ?a. eval_operand arg s = SOME a /\
        Q (step_prov PG G (mk_inst id ISZERO [arg] [out])
             (update_var out (bool_to_word (a = 0w)) s))
          (step_taint (mk_inst id ISZERO [arg] [out]) s
             (update_var out (bool_to_word (a = 0w)) s) tn)
          ((update_var out (bool_to_word (a = 0w)) s) with
             vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule ptr_fragment_step >> simp[is_terminator_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `update_var out (bool_to_word (a = 0w)) s` >> conj_tac >-
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def] >>
  asm_rewrite_tac[] >> simp[update_var_def] >> rpt strip_tac >>
  irule dynamic_unary_ok >> simp[]
QED

Theorem emit_dynamic_iszero_clean_ptr:
  !G cx ctx PG R sa sb arg out tn s a.
    emit_op ISZERO [arg] sa = (Var out,sb) /\
    eval_operand arg s = SOME a /\ op_taint tn arg = {} ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      lookup_var out sf = SOME (bool_to_word (a = 0w)) /\
      op_taint tnf (Var out) = {} /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ISZERO [arg] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all dynamic_iszero_step_ptr >>
  disch_then (qspecl_then [`G`, `sa.cs_next_id`, `out`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tf`, `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (irule dynamic_iszero_fragment >> gvs[mk_inst_def]) >>
  simp[lookup_var_def] >> gvs[update_var_def] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  `p <> out` by metis_tac[] >> simp[]
QED

Theorem dynamic_assert_true_step_ptr:
  !G tn s id arg a PG.
    eval_operand arg s = SOME a /\ a <> 0w /\ op_taint tn arg = {} ==>
    step_inst_base (mk_inst id ASSERT [arg] []) s = OK s /\
    step_prov PG G (mk_inst id ASSERT [arg] []) s = G /\
    step_taint (mk_inst id ASSERT [arg] []) s s tn = tn /\
    (!D fuel ctx fn. ~ctx_has_dalloca ctx ==>
      ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ASSERT [arg] []) s)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  `!D fuel ctx fn. ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ASSERT [arg] []) s` by
    (rpt strip_tac >> irule dynamic_unary_ok >> simp[]) >>
  simp[] >>
  `new_site_bytes s s = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
    mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
    store_taint_def, adopt_reset_def, mem_taint_def, imm_taint_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    range_bytes_def, DRESTRICT_UNIV, taint_component_equality]
QED

Theorem emit_dynamic_assert_true_ptr:
  !G cx ctx PG R sa sb arg tn s a.
    emit_void ASSERT [arg] sa = ((),sb) /\
    eval_operand arg s = SOME a /\ a <> 0w /\ op_taint tn arg = {} ==>
    frag_exec_ptr cx ctx PG sa sb
      (\g t v. g = G /\ t = tn /\ v = s)
      (\g t v. g = G /\ t = tn /\
          v = s with vs_inst_idx := SUC s.vs_inst_idx) R
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ASSERT [arg] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  irule ptr_fragment_step >> simp[is_terminator_def] >>
  rpt strip_tac >> qexists_tac `s` >>
  conj_tac >- simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  simp[] >> conj_tac >-
    simp[dynamic_unary_ok] >>
  `new_site_bytes s s = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION,
         SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, adopt_reset_def, mem_taint_def, imm_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, DRESTRICT_UNIV] >>
  simp[taint_component_equality]
QED
