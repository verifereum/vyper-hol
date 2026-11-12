(* Same-element Dynamic capacity widening: finite prefix and live MCOPY. *)
Theory appendDynamicStageCopyPtr
Ancestors appendDynamicMemoryStepPtr appendDynamicPrefixPtr appendDynamicTransportPtr typedCopyLayoutPtr
  annAssignPtrCopy typedCopyPtr valueTypingMemoryProps contextCodegenRel
  compileEnv context emitHelper venomState venomInst words finite_map
  fragGasSeqPtr exprSimPtrLiteralChunks exprLoweringProps fragExec emitHelperProps list rich_list
  valueEncodingProps representationCleanPtr bodyPtrDefs vyperTyping loweringShapeRules

Theorem append_dynamic_stage_copy_core:
  !cx ctx PG R cenv et tv vs sn dn src dst sa sb G tn s a b.
    compile_copy_dynarray_typed cenv (Var dst) et dn (Var src) et sa = ((),sb) /\
    supported_full_word_type et /\
    type_memory_bytes cenv et = type_memory_size tv /\
    value_has_type (ArrayTV tv (Dynamic sn)) (ArrayV (DynArrayV vs)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic sn)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (32+sn*type_memory_size tv) /\
    ptr_covers G tn dst s (32+dn*type_memory_size tv) /\
    sn <= dn /\ dn < dimword(:256) /\
    LENGTH vs * type_memory_size tv < dimword(:256) /\
    w2n a+32 < dimword(:256) /\ w2n b+32 < dimword(:256) /\
    (w2n a+32+sn*type_memory_size tv <= w2n b \/
     w2n b+32+dn*type_memory_size tv <= w2n a) ==>
    ?Gf tnf sf.
      sf.vs_inst_idx = s.vs_inst_idx + 9 /\
      (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_inst_idx := s.vs_inst_idx|>) = s /\
      run_inst_seq (emitted_insts sa sb) s = OK (sf with vs_inst_idx := s.vs_inst_idx) /\
      (!D ctx fn. ~ctx_has_dalloca ctx ==>
        inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf) /\
      LENGTH (emitted_insts sa sb) = 9 /\
      EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
        i.inst_opcode <> GAS) (emitted_insts sa sb) /\
      sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory (ArrayTV tv (Dynamic dn)) (ArrayV (DynArrayV vs)) (w2n b) m) /\
      (!i. i < w2n b \/ w2n b+32+dn*type_memory_size tv <= i ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      cs_extends sa sb /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     mem_word_at (w2n a) m = n2w (LENGTH vs)` by
    metis_tac[dynarray_in_memory_robust_length] >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    metis_tac[mem_agree_outside_def, mem_word_at_eq_mload] >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_mem_word_at_clean] >>
  `LENGTH vs <= sn` by gvs[value_has_type_def] >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  `?q. length = Var q` by metis_tac[emit_op_facts] >>
  `?q. too_long = Var q` by metis_tac[emit_op_facts] >>
  `?q. ok = Var q` by metis_tac[emit_op_facts] >>
  `?q. src_data = Var q` by metis_tac[emit_op_facts] >>
  `?q. dst_data = Var q` by metis_tac[emit_op_facts] >>
  `?q. data_sz = Var q` by metis_tac[emit_op_facts] >> gvs[] >>
  rename1 `emit_op MLOAD [Var src] sa = (Var len,s1)` >>
  rename1 `emit_op GT [Var len; Lit (n2w dn)] s1 = (Var gt,s2)` >>
  rename1 `emit_op ISZERO [Var gt] s2 = (Var ok,s3)` >>
  rename1 `emit_void ASSERT [Var ok] s3 = ((),s4)` >>
  rename1 `emit_void MSTORE [Var dst; Var len] s4 = ((),s5)` >>
  rename1 `emit_op ADD [Var src; Lit 32w] s5 = (Var sd,s6)` >>
  rename1 `emit_op ADD [Var dst; Lit 32w] s6 = (Var dd,s7)` >>
  rename1 `emit_op MUL _ s7 = (Var cnt,last)` >>
  drule (SIMP_RULE bool_ss [GSYM AND_IMP_INTRO]
    append_dynamic_prefix_core) >>
  ntac 7 (disch_then drule) >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] mp_tac) >>
  disch_then (qspecl_then [`G`, `tn`, `s`, `a`, `b`, `LENGTH vs`, `sn`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  disch_then (qx_choose_then `Gp` (qx_choose_then `tp` (qx_choose_then `sp` strip_assume_tac))) >>
  qpat_x_assum `compile_copy_memory_dynamic _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [compile_copy_memory_dynamic_def]) >>
  `sb.cs_current_bb = last.cs_current_bb /\
   sb.cs_current_insts = last.cs_current_insts ++
     [mk_inst last.cs_next_id MCOPY [Var dd;Var sd;Var cnt] []] /\
   cs_extends last sb` by
    (gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
         comp_return_def, cs_extends_def]) >>
  drule_all append_dynamic_prefix_shape >> strip_tac >>
  `inst_extends sa last` by
    (imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     metis_tac[inst_extends_trans]) >>
  `emitted_insts sa sb = emitted_insts sa last ++
    [mk_inst last.cs_next_id MCOPY [Var dd;Var sd;Var cnt] []]` by
    (gvs[inst_extends_def, emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  qabbrev_tac `n = LENGTH vs * type_memory_size tv` >>
  qabbrev_tac `u = mcopy (w2n b+32) (w2n a+32) n sp` >>
  qabbrev_tac `tf = step_taint
    (mk_inst last.cs_next_id MCOPY [Var dd;Var sd;Var cnt] []) sp u tp` >>
  `step_inst_base (mk_inst last.cs_next_id MCOPY [Var dd;Var sd;Var cnt] []) sp = OK u /\
   (!D fuel ctx fn. ~ctx_has_dalloca ctx ==>
     ptr_inst_ok D 0 fuel ctx fn Gp tp
       (mk_inst last.cs_next_id MCOPY [Var dd;Var sd;Var cnt] []) sp) /\
   (u with vs_memory := sp.vs_memory) = sp /\
   step_prov PG Gp (mk_inst last.cs_next_id MCOPY [Var dd;Var sd;Var cnt] []) u = Gp /\
   tf.t_var = tp.t_var /\ tf.t_stor = tp.t_stor /\ tf.t_trans = tp.t_trans /\
   tf.t_imm = tp.t_imm /\
   tf.t_mem = (tp.t_mem DIFF {i | w2n b+32 <= i /\ i < w2n b+32+n}) UNION
     {w2n b+32+i | i < n /\ w2n a+32+i IN tp.t_mem}` by
    (mp_tac dynamic_mcopy_covered_step_ptr >>
     disch_then (qspecl_then [`PG`, `Gp`, `tp`, `sp`] mp_tac) >>
     disch_then (qspecl_then [`last.cs_next_id`, `dd`, `sd`, `Var cnt`] mp_tac) >>
     simp[eval_operand_def, Abbr `n`] >> strip_tac >>
     gvs[Abbr `tf`, Abbr `u`, Abbr `n`]) >>
  `frag_exec_ptr cx ctx PG last sb
    (\g t v. g = Gp /\ t = tp /\ v = sp)
    (\g t v. g = Gp /\ t = tf /\ v = (u with vs_inst_idx := SUC sp.vs_inst_idx)) R` by
    (irule mcopy_operand_frag_ptr >> (conj_tac >- simp[]) >>
     qexistsl_tac [`Var cnt`, `dd`, `last.cs_next_id`, `sd`] >> simp[] >>
     rpt strip_tac >> gvs[] >>
     qexists_tac `n2w n` >>
     simp[eval_operand_def, Abbr `n`] >>
     gvs[Abbr `n`, Abbr `u`, Abbr `tf`]) >>
  `!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tp.t_mem` by
    metis_tac[robust_mem_word_at_clean] >>
  `!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
    mem_word_at (w2n b) m = n2w (LENGTH vs)` by
    (rpt strip_tac >>
     `mem_bytes_at (w2n b) 32 m = mem_bytes_at (w2n b) 32 sp.vs_memory` by
       (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >> rpt strip_tac >>
        `i NOTIN tf.t_mem` by (simp[] >> decide_tac) >>
        `mem_bytes_at i 1 m = mem_bytes_at i 1 u.vs_memory` by
          metis_tac[mem_agree_outside_def] >>
        simp[Abbr `u`] >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
     `mem_word_at (w2n b) sp.vs_memory = n2w (LENGTH vs)` by
       metis_tac[mem_agree_outside_def] >>
     metis_tac[valueEncodingDefsTheory.mem_word_at_def,
       valueEncodingDefsTheory.mem_bytes_at_def]) >>
  `n <= sn * type_memory_size tv /\ n <= dn * type_memory_size tv` by
    simp[Abbr `n`] >>
  `mem_bytes_at (w2n b+32) n u.vs_memory =
    mem_bytes_at (w2n a+32) n s.vs_memory` by
    (simp[Abbr `u`, mcopy_mem_bytes_at_same] >>
     irule mem_bytes_at_translated_window >>
     qexists_tac `32+sn*type_memory_size tv` >> simp[]) >>
  `!i. i < n ==> (w2n b+32+i IN tf.t_mem <=> w2n a+32+i IN tn.t_mem)` by
    (rpt strip_tac >> simp[] >>
     `!j. w2n b+32+i = w2n b+32+j <=> i = j` by decide_tac >>
     simp[] >> qpat_x_assum `!j. j < w2n b \/ _ <= j ==> _`
       (qspec_then `w2n a+32+i` mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  (qexistsl_tac [`Gp`, `tf`, `u with vs_inst_idx := SUC sp.vs_inst_idx`] >>
  conj_tac >-
    (simp[Abbr `u`, venomExecSemanticsTheory.mcopy_def,
      venomStateTheory.write_memory_with_expansion_def] >> decide_tac) >>
  conj_tac >-
    (qpat_x_assum `(sp with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[Abbr `u`, venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.write_memory_with_expansion_def]) >>
  conj_tac >-
    (`run_inst_seq [mk_inst last.cs_next_id MCOPY [Var dd;Var sd;Var cnt] []] sp = OK u` by
       (simp[run_inst_seq_def] >> asm_rewrite_tac[]) >>
     qpat_assum `emitted_insts sa sb = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `run_inst_seq (emitted_insts sa last) s = _`
       (mp_then Any mp_tac run_inst_seq_append) >> disch_then (qspec_then
       `[mk_inst last.cs_next_id MCOPY [Var dd;Var sd;Var cnt] []]`
       (fn th => pure_rewrite_tac[th])) >>
     simp[run_inst_seq_inst_idx, mk_inst_def, is_terminator_def,
       instIdxIndepTheory.exec_result_map_def]) >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_assum `emitted_insts sa sb = _` (fn th => pure_rewrite_tac[th]) >>
     `LENGTH (emitted_insts sa last) = 8` by simp[] >>
     `((sp with vs_inst_idx := s.vs_inst_idx) with
       vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa last)) = sp` by
       (asm_rewrite_tac[] >>
        qpat_assum `sp.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
        simp[NoAsms]) >>
     irule literal_inst_seq_ptr_append >>
     (conj_tac >- simp[mk_inst_def, is_terminator_def]) >>
     qexistsl_tac [`Gp`, `tp`, `sp with vs_inst_idx := s.vs_inst_idx`] >>
     conj_tac >- asm_rewrite_tac[] >>
     conj_tac >- metis_tac[] >>
     asm_rewrite_tac[] >> simp[inst_seq_ptr_def, Abbr `tf`] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[mk_inst_def, is_terminator_def] >>
  conj_tac >- simp[] >>
  conj_tac >- gvs[inst_extends_def, APPEND_ASSOC] >>
  conj_tac >- (irule fragExecPtrTheory.frag_exec_ptr_seq >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >> irule append_dynamic_live_transport >>
     qexistsl_tac [`s.vs_memory`, `u.vs_memory`, `sn`, `w2n a`, `tn.t_mem`, `tf.t_mem`] >>
     gvs[Abbr `n`] ) >>
  conj_tac >-
    (rpt strip_tac >> simp[] >>
     `i < w2n b \/ w2n b+32 <= i` by decide_tac >>
     `mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 sp.vs_memory` by
       (simp[Abbr `u`, mcopy_mem_bytes_at_disjoint]) >>
     `!j. j < n ==> i <> j+(w2n b+32)` by decide_tac >>
     simp[] >> metis_tac[]) >>
  simp[] >>
  conj_tac >- metis_tac[compileEnvTheory.cs_extends_trans] >>
  simp[Abbr `u`, venomExecSemanticsTheory.mcopy_def,
    venomStateTheory.write_memory_with_expansion_def] >>
  gvs[lookup_var_def, ptrDisciplineTheory.op_taint_def])
QED

Theorem append_dynamic_stage_copy_ptr:
  !cx ctx PG R cenv et tv vs sn dn src dst sa sb G tn s a b.
    compile_copy_dynarray_typed cenv (Var dst) et dn (Var src) et sa = ((),sb) /\
    supported_full_word_type et /\
    type_memory_bytes cenv et = type_memory_size tv /\
    value_has_type (ArrayTV tv (Dynamic sn)) (ArrayV (DynArrayV vs)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic sn)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (32+sn*type_memory_size tv) /\
    ptr_covers G tn dst s (32+dn*type_memory_size tv) /\
    sn <= dn /\ dn < dimword(:256) /\
    LENGTH vs * type_memory_size tv < dimword(:256) /\
    w2n a+32 < dimword(:256) /\ w2n b+32 < dimword(:256) /\
    (w2n a+32+sn*type_memory_size tv <= w2n b \/
     w2n b+32+dn*type_memory_size tv <= w2n a) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory (ArrayTV tv (Dynamic dn)) (ArrayV (DynArrayV vs)) (w2n b) m) /\
      (!i. i < w2n b \/ w2n b+32+dn*type_memory_size tv <= i ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      cs_extends sa sb /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all append_dynamic_stage_copy_core >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[]
QED
