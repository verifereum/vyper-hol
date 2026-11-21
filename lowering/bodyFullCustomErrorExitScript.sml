Theory bodyFullCustomErrorExit
Ancestors
  fragGasEmitCtrl fragGasOriginPtr fragExec revertReasonPtr ptrSafetyTransport
  emitHelperProps emitHelper bodyPtrDefs gasEvents gasCount memSafeRun
  instMemFrontier unitTransformDefs codegenRel contextCodegenRel memLocDefs
  venomExecProps venomExecSemantics venomInst venomState memoryReadProps words
  typedCopyPtr bodyPtrAttributeAdd fragGasSeqPtrContext compileEnv
  ptrDiscipline fragGasSeqPtr loweringShapeRules loweringStateRelDefs finite_map list arithmetic
  logAbiPrefixPtr decoderGhostFramePtr fragGasOriginPtrLoop

(* The encoder supplies the exact slice, without exposing the bytes before it. *)
Theorem custom_error_revert_slice[local]:
  emit_inst REVERT [Var p;len] [] sa = ((),sb) /\ fn_has_code sa sb func /\
  eval_operand (Var p) s = SOME off /\ eval_operand len s = SOME n /\
  ptr_covers G tn p s (w2n n) /\ op_taint tn len = {} /\
  w2n off + w2n n <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  ?t. t.vs_returndata = read_memory (w2n off) (w2n n) s /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort t,G,tn)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id REVERT [Var p;len] []` >>
  `get_instruction bb s.vs_inst_idx = SOME i` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `i`]) >>
  qabbrev_tac `bytes = read_memory (w2n off) (w2n n) s` >>
  qabbrev_tac `t = revert_state (set_returndata bytes s)` >>
  `!fuel. step_inst fuel ctx i s = Abort Revert_abort t` by
    (gen_tac >>
     drule_all (Q.SPECL [`s`,`Var p`,`len`,`sa.cs_next_id`,`off`,`n`]
       step_revert_behavior) >>
     simp[Abbr `i`, Abbr `t`, Abbr `bytes`, mk_inst_def,
          step_inst_non_invoke, read_memory_def]) >>
  qexists_tac `t` >>
  conj_tac >- simp[Abbr `t`, Abbr `bytes`, revert_state_def, set_returndata_def] >>
  gen_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    (irule ptr_inst_ok_lower_bound_transport >>
     simp[] >> qexists_tac `0` >>
     simp[Abbr `i`] >> irule ptr_inst_ok_revert >> simp[]) >>
  `mem_safe_step 0 ctx i s` by
    simp[Abbr `i`, mk_inst_def, mem_safe_step_non_invoke,
         inst_mem_below_frontier_def, inst_dload_in_section_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def,
         memory_range_of_operands_def] >>
  irule exit_inst_origin_ptr >> simp[exit_result_def] >>
  qexists_tac `i` >>
  `get_instruction bb (LENGTH sa.cs_current_insts) = SOME i` by fs[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[Abbr `i`, mk_inst_def, gas_events_step_def, gas_count_step_def]
QED

(* Both operand orders occur in the custom-error tail. The addition has no
   memory effect and leaves the pointer inputs of the following REVERT live. *)
Theorem custom_error_add[local]:
  emit_op ADD [left;right] a = (out,b) /\ fn_has_code a b func /\
  eval_operand left s = SOME l /\ eval_operand right s = SOME r /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?q t G' tn'.
    out = Var q /\ not_fresh_at b q /\
    eval_operand out t = SOME (l+r) /\ op_taint tn' out = {} /\
    (!k. right = Lit k ==> FLOOKUP G' q = op_prov G left) /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_allocas = s.vs_allocas /\ t.vs_initial_fmp = s.vs_initial_fmp /\
    t.vs_fmp = s.vs_fmp /\
    t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn'))
Proof
  strip_tac >> drule emit_op_facts >> strip_tac >>
  `out' = STRING #"%" (toString a.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `i = mk_inst a.cs_next_id ADD [left;right] [out']` >>
  qabbrev_tac `u = update_var out' (l+r) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G' = step_prov PG G i u` >>
  qabbrev_tac `tn' = step_taint i s u tn` >>
  `get_instruction bb s.vs_inst_idx = SOME i` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `i`]) >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def] >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn i s` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     simp[] >> qexists_tac `0` >> simp[Abbr `i`, ptr_inst_ok_copy_len_binop]) >>
  `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >>
     mp_tac (Q.INST [`u` |-> `u`, `i` |-> `i`] straight_line_origin_ptr_edge) >>
     simp[Abbr `t`, Abbr `G'`, Abbr `tn'`] >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def,
          inst_dload_in_section_def]) >>
  `!x. not_fresh_at a x ==> x <> out'` by
    (rw[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >> irule (SIMP_RULE bool_ss [APPEND_NIL]
       (Q.SPECL [`D`, `lo`, `explicit`, `ctx`, `func`, `PG`, `s`, `G`, `tn`,
         `[]`, `t`, `G'`, `tn'`, `[]`] (cj 2 gas_origin_ptr_path_rules))) >> simp[] >>
     qexistsl_tac [`G'`,`t`,`tn'`] >> simp[] >>
     irule (cj 1 gas_origin_ptr_path_rules) >> simp[Abbr `t`, Abbr `u`, update_var_def]) >>
  `op_taint tn' (Var out') = {} /\
    (!x. x <> out' ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))` by
    (simp[Abbr `tn'`, Abbr `G'`, Abbr `i`, Abbr `u`] >>
     metis_tac[copy_len_binop_ghost_frame]) >>
  `!k. right = Lit k ==> FLOOKUP G' out' = op_prov G left` by
    rw[Abbr `G'`, Abbr `i`, Abbr `u`, attribute_add_provenance] >>
  `!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >> `x <> out'` by metis_tac[] >>
     simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `!x. not_fresh_at a x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  qexistsl_tac [`out'`,`t`,`G'`,`tn'`] >>
  qpat_x_assum `out' = STRING _ _` SUBST_ALL_TAC >>
  fs[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
     eval_operand_def] >>
  qpat_assum `s.vs_inst_idx = LENGTH a.cs_current_insts` (fn idx =>
    qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK _,G',tn')`
      (ACCEPT_TAC o PURE_REWRITE_RULE [idx]))
QED

Theorem custom_error_terminal_path:
  emit_op ADD [Var root;Lit 28w] a = (offset,b) /\ fn_has_code a b func /\
  (case encoded of
     NONE => k = 0 /\ len = Lit 4w /\ c = b
   | SOME op => emit_op ADD [Lit 4w;op] b = (len,c) /\ fn_has_code b c func /\
                eval_operand op s = SOME (n2w k) /\ op_taint tn op = {} /\
                (!x. op = Var x ==> not_fresh_at a x)) /\
  emit_inst REVERT [offset;len] [] c = ((),en) /\ fn_has_code c en func /\
  lookup_var root s = SOME w /\ ptr_covers G tn root s (32+k) /\
  w2n w + 32+k <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t Gf tf.
    t.vs_returndata = read_memory (w2n w+28) (4+k) s /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (Abort Revert_abort t,Gf,tf)
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME w /\ op_taint tn (Var root) = {}` by
    (fs[eval_operand_def, ptr_covers_def] >> gvs[]) >>
  `eval_operand (Lit 28w) s = SOME 28w /\ op_taint tn (Lit 28w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  mp_tac (Q.INST [`left` |-> `Var root`, `right` |-> `Lit 28w`,
    `out` |-> `offset`, `l` |-> `w`, `r` |-> `28w`] custom_error_add) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`q`,`u`,`Gu`,`tu`] strip_assume_tac) >>
  qpat_x_assum `offset = Var q` SUBST_ALL_TAC >>
  `lookup_var q u = SOME (w + 28w) /\ FLOOKUP Gu q = FLOOKUP G root` by
    fs[eval_operand_def, op_prov_def] >>
  `w2n w + 28 < dimword (:256) /\
   w2n (w + 28w) = w2n w + 28 /\
   w2n (n2w (4+k) : 256 word) = 4+k` by
    (conj_tac >- decide_tac >>
     conj_tac >- (simp[w2n_add_2] >> irule LESS_MOD >> decide_tac) >>
     simp[w2n_n2w] >> irule LESS_MOD >> decide_tac) >>
  `ptr_covers Gu tu q u (4+k)` by
    (irule ptr_covers_offset_transport >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G`,`28`,`root`,`s`,`tn`,`w`] >>
     `28+(4+k) = 32+k` by decide_tac >> asm_rewrite_tac[] >> fs[]) >>
  `allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `?v Gv tv. eval_operand len v = SOME (n2w (4+k)) /\ op_taint tv len = {} /\
     lookup_var q v = SOME (w + 28w) /\ ptr_covers Gv tv q v (4+k) /\
     v.vs_alloca_next = u.vs_alloca_next /\ v.vs_memory = u.vs_memory /\
     allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
     ~v.vs_halted /\ v.vs_current_bb = c.cs_current_bb /\
     v.vs_inst_idx = LENGTH c.cs_current_insts /\
     !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (u,Gu,tu) [] (OK v,Gv,tv)` by
    (Cases_on `encoded`
     >- (gvs[] >> qexistsl_tac [`u`,`Gu`,`tu`] >>
         simp[eval_operand_def, op_taint_def, gas_origin_ptr_path_rules]) >>
     gvs[] >>
     rename1 `emit_op ADD [Lit 4w; alen] b = (len,c)` >>
     `eval_operand alen u = SOME (n2w k) /\ op_taint tu alen = {}` by
       (Cases_on `alen` >> fs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
     `eval_operand (Lit 4w) u = SOME 4w /\ op_taint tu (Lit 4w) = {}` by
       simp[eval_operand_def, op_taint_def] >>
     mp_tac (Q.INST [`left` |-> `Lit 4w`, `right` |-> `alen`,
       `out` |-> `len`, `a` |-> `b`, `b` |-> `c`, `l` |-> `4w`,
       `r` |-> `n2w k`, `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`] custom_error_add) >>
     impl_tac >- simp[] >> strip_tac >>
     `ptr_covers G' tn' q t (4+k)` by
       (irule ptr_covers_frame >> qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]) >>
     qexistsl_tac [`t`,`G'`,`tn'`] >>
     fs[word_add_n2w, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `eval_operand (Var q) v = SOME (w + 28w)` by simp[eval_operand_def] >>
  `w2n (w + 28w) + w2n (n2w (4+k) : 256 word) <= v.vs_alloca_next` by
    (asm_rewrite_tac[] >> decide_tac) >>
  mp_tac (Q.INST [`p` |-> `q`, `sa` |-> `c`, `sb` |-> `en`,
    `s` |-> `v`, `G` |-> `Gv`, `tn` |-> `tv`,
    `off` |-> `w+28w`, `n` |-> `n2w (4+k)`] custom_error_revert_slice) >>
  impl_tac >- fs[] >>
  strip_tac >>
  qexistsl_tac [`t`,`Gv`,`tv`] >>
  conj_tac >- fs[read_memory_def] >>
  gen_tac >>
  irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gu`,`u`,`tu`] >> simp[] >>
  irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gv`,`v`,`tv`] >> simp[]
QED
