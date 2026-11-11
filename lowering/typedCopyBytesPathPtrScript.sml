(* Counted bytestring copying, with only the live representation clean. *)
Theory typedCopyBytesPathPtr
Ancestors
 annAssignPtrLength annAssignPtrCopy typedCopyRobustTransportPtr
 typedCopyBytesRobustPtr typedCopyAmbientFramePtr exprSimBufferStore
 fragGasPathPtr fragGasSeqPtr context emitHelper emitHelperProps
 exprLoweringProps fragExec compileEnv loweringStateRelDefs
 bodyPtrDefs ptrDiscipline typedCopyPtr codegenRel venomExecSemantics venomState venomMemDefs venomMemProofs finite_map pred_set arithmetic

Theorem compile_store_bytestring_path_ptr:
 !D ctx func PG sa sb src dst G tn s a b len n.
 compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
 fn_has_code sa sb func /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 n = 32 + 32 * ((len+31) DIV 32) /\ n < dimword(:256) /\
 ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
 mload (w2n a) s = n2w len /\
 (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
 (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
   mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
 (!i. ~(w2n b <= i /\ i < w2n b+n) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!p. not_fresh_at sa p ==>
   lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
   op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
 simp[compile_store_bytestring_def, comp_bind_def] >>
 pairarg_tac >> simp[LET_THM, pairTheory.pair_case_def] >> strip_tac >>
 rename1 `compile_bytestring_copy_len (Var src) sa = (count_op,sc)` >>
 `cs_extends sa sc /\ cs_extends sc sb` by
  (qpat_x_assum `compile_bytestring_copy_len _ _ = _` mp_tac >>
   qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
   POP_ASSUM_LIST (K all_tac) >>
   simp[compile_bytestring_copy_len_def, emit_op_def,
        emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def, LET_THM,
        pairTheory.pair_case_def] >> rpt strip_tac >> gvs[] >>
   rewrite_tac[cs_extends_def] >> qexists `[]` >> simp[] >>
   pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
   simp[rich_listTheory.IS_PREFIX_APPEND]) >>
 `fn_has_code sa sc func /\ fn_has_code sc sb func` by
   metis_tac[fn_has_code_split] >>
 `ptr_covers G tn src s 32` by
   (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
 drule_all annassign_bytestring_copy_len_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK s1)` >>
 `eval_operand count_op s1 = SOME (n2w n)` by
   (gvs[] >> qspec_then `len` mp_tac buffer_round_size >>
    simp[vfmConstantsTheory.word_size_def]) >>
 `lookup_var src s1 = SOME a /\ lookup_var dst s1 = SOME b /\
  ptr_covers G1 tn1 src s1 n /\ ptr_covers G1 tn1 dst s1 n` by
   (qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `src` strip_assume_tac) >>
    qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `dst` strip_assume_tac) >>
    gvs[ptr_covers_def] >> metis_tac[]) >>
 `sb.cs_current_bb = sc.cs_current_bb /\
  sb.cs_current_insts = sc.cs_current_insts ++
    [mk_inst sc.cs_next_id MCOPY [Var dst;Var src;count_op] []]` by
   gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       emit_def, comp_return_def] >>
 `?bb. lookup_block s1.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
    SOME (mk_inst sc.cs_next_id MCOPY [Var dst;Var src;count_op] [])` by
   (drule_all fn_has_code_same_block >> strip_tac >> qexists `bb` >>
    simp[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
 qabbrev_tac `t = mcopy (w2n b) (w2n a) n s1` >>
 qabbrev_tac `tnf = step_taint
   (mk_inst sc.cs_next_id MCOPY [Var dst;Var src;count_op] []) s1 t tn1` >>
 qexistsl [`G1`,`tnf`,`t with vs_inst_idx := SUC s1.vs_inst_idx`] >>
 conj_tac >- suspend "path" >>
 suspend "frame"
QED

Resume compile_store_bytestring_path_ptr[path]:
 `gas_path_ptr D 0 ctx func PG G1 tn1 s1 0 G1 tnf
   (OK (t with vs_inst_idx := SUC s1.vs_inst_idx))` by
  (qunabbrev_tac `tnf` >> qunabbrev_tac `t` >>
   irule annassign_mcopy_path_ptr >> simp[] >> gvs[]) >>
 drule_all gas_path_ptr_then >> simp[]
QED

Resume compile_store_bytestring_path_ptr[frame]:
 `tnf.t_var = tn1.t_var /\
  tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\
  tnf.t_mem = (tn1.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n}) UNION
    {w2n b+i | i < n /\ w2n a+i IN tn1.t_mem}` by
  (simp[Abbr `tnf`, Abbr `t`, step_taint_def,
        venomInstTheory.mk_inst_def, set_var_taint_def, store_taint_def,
        adopt_reset_def, mem_taint_def, step_writes_def,
        source_memory_write_ranges_def, fixed_source_write_range_def,
        sized_source_write_range_def, written_taint_def, range_bytes_def,
        new_site_bytes_def, mcopy_def, write_memory_with_expansion_def,
        eval_operand_def, FLOOKUP_DEF, DRESTRICT_UNIV, EXTENSION] >>
   rpt strip_tac >> metis_tac[]) >>
 `tnf.t_imm = tn1.t_imm` by
   simp[Abbr `tnf`, step_taint_def, imm_taint_def, venomInstTheory.mk_inst_def] >>
 conj_tac >- simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, write_memory_def] >>
 conj_tac >- simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, write_memory_def] >>
 conj_tac >- simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, write_memory_def] >>
 conj_tac >-
  (qpat_x_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >>
   simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, write_memory_def] >>
   fs[venom_state_component_equality]) >>
 conj_tac >- simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, write_memory_def] >>
 conj_tac >-
  (rpt strip_tac >> simp[Abbr `t`] >>
   `mem_bytes_at i 1 (mcopy (w2n b) (w2n a) n s1).vs_memory =
    mem_bytes_at i 1 s1.vs_memory` by
     (irule buffer_mcopy_exterior >> decide_tac) >> gvs[]) >>
 simp[] >> conj_tac >-
  (rpt strip_tac >> eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
 rpt strip_tac >>
 qpat_x_assum `!p. not_fresh_at sa p ==> _` (qspec_then `p` mp_tac) >>
 simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, write_memory_def,
      lookup_var_def, op_taint_def]
QED

Finalise compile_store_bytestring_path_ptr

Theorem compile_store_bytestring_robust_path_ptr:
 !D ctx func PG sa sb src dst G tn s a b len n tenv sty dty stv dtv v.
 compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
 fn_has_code sa sb func /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 n = 32 + 32 * ((len+31) DIV 32) /\
 len+31 < dimword(:256) /\ n < dimword(:256) /\
 ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
 is_bytestring_type sty /\ is_bytestring_type dty /\
 evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
 value_has_type stv v /\ value_has_type dtv v /\
 ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
  (?str. v = StringV str /\ len = LENGTH str)) /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory stv v (w2n a) m) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
 (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
   mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
 (!i. ~(w2n b <= i /\ i < w2n b+n) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!p. not_fresh_at sa p ==>
   lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
   op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
   val_in_memory dtv v (w2n b) m) /\
 (!ft fv p. val_wf ft fv /\
   (p + type_memory_size ft <= w2n b \/ w2n b+n <= p) /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory ft fv p m) ==>
   !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
     val_in_memory ft fv p m)
Proof
 typedCopyRobustLib.intro >>
 qpat_x_assum `_ /\ _` strip_assume_tac >>
 drule_all compile_store_bytestring_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 drule robust_representation_exterior_frame >> disch_then drule >>
 disch_then (assume_tac o SIMP_RULE bool_ss [AND_IMP_INTRO]) >>
 typedCopyRobustLib.witness >>
 typedCopyRobustLib.conclude clean_copied_window
QED
