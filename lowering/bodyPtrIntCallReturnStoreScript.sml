Theory bodyPtrIntCallReturnStore
Ancestors
  intCallResult exprLowering exprLoweringProps emitHelper emitHelperProps
  valueEncodingDefs valueEncodingProps
  compileEnv loweringStateRelDefs freshWrites fragExec fragGasPathPtr fragGasSeqPtr
  bodyPtrStructLitFieldStore bodyPtrIfExpStorageLoop typedCopyLoopHeaderPtr
  typedCopyPtr wordLoadStorePtr bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics
  venomInst venomState words finite_map pred_set list arithmetic ASCIInumbers

(* A single ADD/MSTORE pair: the result word need not carry provenance. *)
Theorem store_result_head_counted_ptr[local]:
  !D ctx fn PG buf value off sa sm sb dst s G tn b w site cap.
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm) /\
  emit_void MSTORE [dst;value] sm = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p. buf = Var p ==> not_fresh_at sa p) /\
  (!p. value = Var p ==> not_fresh_at sa p) /\
  eval_operand buf s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  op_taint tn buf = {} /\ op_taint tn value = {} /\
  op_prov G buf = SOME (site,cap) /\ site <= b+off /\
  b+off+32 <= site+cap /\ b+off+32 < dimword(:256) ==>
  ?Gf tf t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    t.vs_memory = (mstore (b+off) w s).vs_memory /\
    tf.t_mem = tn.t_mem DIFF {i | b+off <= i /\ i < b+off+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (rpt strip_tac >> gvs[not_fresh_at_def, Abbr `out`] >>
     metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [buf;Lit (n2w off)] [out]` >>
  qabbrev_tac `u = update_var out (n2w b+n2w off) s` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  `w2n (n2w b+n2w off:bytes32) = b+off` by
    (simp[word_add_n2w, w2n_n2w] >> decide_tac) >>
  `eval_operand value s1 = SOME w /\ op_taint tn1 value = {}` by
    (Cases_on `value` >>
     simp[Abbr `s1`, Abbr `u`, Abbr `tn1`, Abbr `i`,
          copy_len_binop_ghost_frame] >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
         op_taint_def] >> metis_tac[]) >>
  `ptr_covers G1 tn1 out s1 32` by
    (simp[Abbr `s1`, Abbr `u`, Abbr `G1`, Abbr `tn1`, Abbr `i`] >>
     irule ifexp_dynamic_add_covers >> simp[] >>
     qexistsl_tac [`site`, `cap`] >> simp[]) >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME i /\
   get_instruction bb s1.vs_inst_idx =
     SOME (mk_inst (sa.cs_next_id+1) MSTORE [Var out;value] [])` by
    (simp[Abbr `s1`, Abbr `u`] >> conj_tac >-
       (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     first_x_assum (qspec_then `1` mp_tac) >> simp[ADD1]) >>
  qabbrev_tac `j = mk_inst (sa.cs_next_id+1) MSTORE [Var out;value] []` >>
  qabbrev_tac `v = mstore (b+off) w s1` >>
  qabbrev_tac `tf = step_taint j s1 v tn1` >>
  qabbrev_tac `t = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tf (OK t)` by
    (simp[Abbr `tf`, Abbr `t`, Abbr `v`, Abbr `j`] >>
     qpat_assum `w2n _ = b+off` (fn th => pure_rewrite_tac[GSYM th]) >>
     irule field_add_store_counted >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `i`, Abbr `s1`, Abbr `u`] >>
     qexists_tac `buf` >> gvs[]) >>
  `lookup_var out s1 = SOME (n2w b+n2w off)` by
    simp[Abbr `s1`, Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_prov PG G1 j v = G1 /\ tf.t_var = tn1.t_var /\
   tf.t_stor = tn1.t_stor /\ tf.t_trans = tn1.t_trans /\
   tf.t_mem = tn1.t_mem DIFF {i | b+off <= i /\ i < b+off+32}` by
    (drule_all mstore_ghost_frame >>
     disch_then (qspecl_then [`PG`, `G1`, `sa.cs_next_id+1`] mp_tac) >>
     simp[Abbr `tf`, Abbr `j`, Abbr `v`]) >>
  qexistsl_tac [`G1`, `tf`, `t`] >> simp[] >>
  simp[Abbr `t`, Abbr `v`, Abbr `s1`, Abbr `u`,
       mstore_def, write_memory_with_expansion_def, update_var_def] >>
  simp[Abbr `tf`, Abbr `j`, step_taint_def, imm_taint_def, mk_inst_def] >>
  simp[Abbr `tn1`, Abbr `i`, copy_len_binop_ghost_frame] >>
  rpt strip_tac >>
  simp[Abbr `G1`, copy_len_binop_ghost_frame, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, op_taint_def,
       step_taint_def, set_var_taint_def, mk_inst_def] >>
  qpat_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[imm_taint_def, op_prov_def, DRESTRICT_UNIV]
QED

Theorem store_multi_results_counted_ptr:
  !ops D ctx fn PG buf off sa sb s G tn b ws site cap.
    store_multi_results buf ops off sa = ((),sb) /\
    fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!p. buf = Var p ==> not_fresh_at sa p) /\
    (!p. MEM (Var p) ops ==> not_fresh_at sa p) /\
    eval_operand buf s = SOME (n2w b) /\
    MAP (\op. eval_operand op s) ops = MAP SOME ws /\
    op_taint tn buf = {} /\ EVERY (\op. op_taint tn op = {}) ops /\
    op_prov G buf = SOME (site,cap) /\ site <= b+off /\
    b+off+32*LENGTH ops <= site+cap /\
    b+off+32*LENGTH ops < dimword(:256) ==>
    ?Gf tf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!i. i < LENGTH ws ==>
        mem_word_at (b+off+32*i) t.vs_memory = EL i ws) /\
      (!a len. a+len <= b+off \/ b+off+32*LENGTH ops <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      tf.t_mem = tn.t_mem DIFF {i | b+off <= i /\ i < b+off+32*LENGTH ops} /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!p. not_fresh_at sa p ==>
        lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[store_multi_results_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[gas_path_ptr_rules] >>
      qpat_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
      simp[] >> AP_TERM_TAC >> SET_TAC[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `store_multi_results _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once store_multi_results_def, LET_THM, comp_bind_def,
                    comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE [dst;h] mid = (u,post)` >> Cases_on `u` >>
  Cases_on `ws` >> gvs[] >>
  rename1 `MAP (\op. eval_operand op s) ops = MAP SOME rest` >>
  rename1 `eval_operand h s = SOME w` >>
  `ci_mono sa mid /\ ci_mono mid post /\ ci_mono post sb` by
    (metis_tac[ci_mono_emit_op, ci_mono_emit_void,
               ci_mono_store_multi_results, pairTheory.SND]) >>
  `cs_extends sa post /\ cs_extends post sb /\ sa.cs_next_var <= post.cs_next_var` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa post fn /\ fn_has_code post sb fn` by
    metis_tac[fn_has_code_split] >>
  `!p. h = Var p ==> not_fresh_at sa p` by metis_tac[] >>
  `b+off+32 <= site+cap /\ b+off+32 < dimword(:256)` by decide_tac >>
  drule_all store_result_head_counted_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t)` >>
  `!p. not_fresh_at sa p ==> not_fresh_at post p` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
      (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
  `!op. (!p. op = Var p ==> not_fresh_at sa p) ==>
    eval_operand op t = eval_operand op s /\
    op_taint tn1 op = op_taint tn op /\ op_prov G1 op = op_prov G op` by
    (Cases >> simp[eval_operand_def, op_taint_def, op_prov_def]) >>
  `eval_operand buf t = SOME (n2w b) /\ op_taint tn1 buf = {} /\
   op_prov G1 buf = SOME (site,cap)` by metis_tac[] >>
  `MAP (\op. eval_operand op t) ops = MAP SOME rest` by
    (qpat_x_assum `MAP _ ops = MAP SOME _` (SUBST1_TAC o SYM) >>
     irule MAP_CONG >> simp[] >> metis_tac[]) >>
  `EVERY (\op. op_taint tn1 op = {}) ops` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`D`, `ctx`, `fn`, `PG`, `buf`, `off+32`,
    `post`, `sb`, `t`, `G1`, `tn1`, `b`, `rest`, `site`, `cap`] mp_tac) >>
  (impl_tac >- (simp[MULT_SUC] >> metis_tac[])) >> strip_tac >>
  qexistsl_tac [`Gf`, `tf`, `t'`] >>
  conj_tac >- (metis_tac[gas_path_ptr_then, ADD_CLAUSES]) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s` mp_tac >>
      qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = t` mp_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac
  >- (qx_gen_tac `i` >> strip_tac >> Cases_on `i`
      >- (simp[] >>
          qpat_assum `!a len. _ ==> mem_bytes_at a len t'.vs_memory = _`
            (qspecl_then [`b+off`, `32`] mp_tac) >>
          simp_tac arith_ss [] >>
          pure_rewrite_tac[mem_bytes_at_def] >> strip_tac >>
          `mem_word_at (b+off) t'.vs_memory = mem_word_at (b+off) t.vs_memory` by
            (pure_rewrite_tac[mem_word_at_def] >> asm_rewrite_tac[]) >>
          metis_tac[mstore_mem_word_at_same]) >>
      simp[EL, MULT_SUC] >> first_x_assum (qspec_then `n` mp_tac) >>
      simp[] ) >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at a len t'.vs_memory = mem_bytes_at a len t.vs_memory` by
        (first_x_assum irule >> decide_tac) >>
      simp[] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  simp[EXTENSION, IN_DIFF, MULT_SUC] >> gen_tac >>
  Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac
QED
