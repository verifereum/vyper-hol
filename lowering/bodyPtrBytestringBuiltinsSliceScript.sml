(* Memory slice fragment boundaries, factored at actual compiler steps. *)
Theory bodyPtrBytestringBuiltinsSlice
Ancestors
  bodyPtrBytestringBuiltinsBounds bodyPtrBytestringBuiltinsSource
  bodyPtrBytestringBuiltinsBuffer builtinBytes emitHelper compileEnv fragExec
  exprLoweringProps list rich_list exprSimPtrProps typedCopyPtr fragExecPtr
  ptrDiscipline venomInst venomState emitHelperProps fragGasPathPtr finite_map
  venomExecSemantics bodyPtrDefs

Theorem compile_slice_data_parts:
  compile_slice_data src_len src_data start len N sa = (out,sb) ==>
  ?s1 s2 s3 s4 s5 buf data copy.
    compile_assert_slice_bounds start len src_len sa = ((),s1) /\
    compile_alloc_buffer N s1 = (buf,s2) /\ out = buf.buf_operand /\
    emit_op ADD [out; Lit 32w] s2 = (data,s3) /\
    emit_op ADD [src_data; start] s3 = (copy,s4) /\
    emit_void MCOPY [data; copy; len] s4 = ((),s5) /\
    emit_void MSTORE [out; len] s5 = ((),sb)
Proof
  simp[compile_slice_data_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem slice_bounds_extends:
  compile_assert_slice_bounds a n limit sa = ((),sb) ==> cs_extends sa sb
Proof
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def,
    emit_op_def, emit_void_def, comp_return_def, fresh_id_def, fresh_var_def,
    emit_def] >> strip_tac >> gvs[cs_extends_def] >>
  metis_tac[IS_PREFIX_APPEND, IS_PREFIX_TRANS]
QED

Theorem compile_slice_data_stages:
  compile_slice_data src_len src_data start len N sa = (out,sb) ==>
  ?s1 s2 s3 s4 data copy.
    compile_assert_slice_bounds start len src_len sa = ((),s1) /\
    compile_slice_out_buf N s1 = ((out,data),s2) /\
    emit_op ADD [src_data; start] s2 = (copy,s3) /\
    emit_void MCOPY [data; copy; len] s3 = ((),s4) /\
    emit_void MSTORE [out; len] s4 = ((),sb) /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
    cs_extends s3 s4 /\ cs_extends s4 sb
Proof
  strip_tac >> drule compile_slice_data_parts >> strip_tac >>
  `compile_slice_out_buf N s1 = ((out,data),s3)` by
    (gvs[] >> simp[compile_slice_out_buf_def, comp_bind_def, comp_return_def]) >>
  `cs_extends sa s1` by metis_tac[slice_bounds_extends] >>
  `cs_extends s1 s3` by
    (drule compile_slice_out_buf_compiler_parts >> strip_tac >>
     metis_tac[cs_extends_trans]) >>
  `cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  qexistsl_tac [`s1`,`s3`,`s4`,`s5`,`data`,`copy`] >> simp[]
QED

(* Abort contracts are cursor-independent: a failed ASSERT has no normal
   continuation, so no output allocation or copy endpoint is required. *)
Theorem compile_slice_data_bounds_abort:
  compile_slice_data src_len src_data start len N sa = (out,sb) /\
  compile_assert_slice_bounds start len src_len sa = ((),sc) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fresh_vars_wrt sa s /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  eval_operand src_len s = SOME wl /\
  (!op. MEM op [start;len;src_len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sa sc) s = Abort ab u ==>
  ab = Revert_abort /\
  ?G' tn' j.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (Abort Revert_abort (u with vs_inst_idx := j)) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >> drule compile_slice_data_stages >> strip_tac >>
  `s1 = sc` by metis_tac[pairTheory.PAIR_EQ] >> gvs[] >>
  `cs_extends s1 s3` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 s4` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 fn` by metis_tac[fn_has_code_split] >>
  drule_all (SRULE [] compile_assert_slice_bounds_counted_abort) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  simp[] >> qexistsl_tac [`G'`,`tn'`,`j`] >> gvs[]
QED

Theorem emit_slice_copy_counted:
  emit_void MCOPY [Var dst; Var src; cnt_op] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand cnt_op s = SOME n /\ op_taint tn cnt_op = {} /\
  ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  !D PG. ?tn' t.
    t = (mcopy (w2n b) (w2n a) (w2n n) s) with vs_inst_idx := SUC s.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn' (OK t) /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem} /\
    (!x. lookup_var x t = lookup_var x s) /\
    (!root cap. ptr_covers G tn root s cap ==> ptr_covers G tn' root t cap) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> rpt gen_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MCOPY [Var dst; Var src; cnt_op] []]` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id MCOPY [Var dst; Var src; cnt_op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id MCOPY [Var dst; Var src; cnt_op] []) s =
    OK (mcopy (w2n b) (w2n a) (w2n n) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst sa.cs_next_id MCOPY [Var dst; Var src; cnt_op] []) s` by
    (irule ptr_inst_ok_mcopy_operand >> simp[]) >>
  suspend "copy_path"
QED

Resume emit_slice_copy_counted[copy_path]:
  `eval_operand (Var src) s = SOME a /\ eval_operand (Var dst) s = SOME b` by
    simp[eval_operand_def] >>
  `step_prov PG G (mk_inst sa.cs_next_id MCOPY [Var dst; Var src; cnt_op] [])
     (mcopy (w2n b) (w2n a) (w2n n) s) = G` by
    (irule (cj 1 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
  qabbrev_tac `tn' = step_taint (mk_inst sa.cs_next_id MCOPY [Var dst; Var src; cnt_op] [])
    s (mcopy (w2n b) (w2n a) (w2n n) s) tn` >>
  qabbrev_tac `t = (mcopy (w2n b) (w2n a) (w2n n) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G tn' (OK t)` by
    (simp_tac pure_ss [Abbr `t`, Abbr `tn'`] >>
     `~(mcopy (w2n b) (w2n a) (w2n n) s).vs_halted` by
       simp[mcopy_def, write_memory_with_expansion_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
     `(mk_inst sa.cs_next_id MCOPY [Var dst; Var src; cnt_op] []).inst_opcode <> INVOKE /\
      ~is_terminator (mk_inst sa.cs_next_id MCOPY [Var dst; Var src; cnt_op] []).inst_opcode /\
      (mk_inst sa.cs_next_id MCOPY [Var dst; Var src; cnt_op] []).inst_opcode <> GAS` by
       simp[mk_inst_def, is_terminator_def] >>
     drule_all gas_path_ptr_one_step >>
     disch_then (qspec_then `PG` mp_tac) >> simp[]) >>
  qexistsl_tac [`tn'`,`t`] >> simp[Abbr `t`] >>
  suspend "copy_frame"
QED

Resume emit_slice_copy_counted[copy_frame]:
  `tn'.t_var = tn.t_var` by
    (simp_tac pure_ss [Abbr `tn'`] >> irule (cj 2 mcopy_operand_ghost_frame) >> simp[]) >>
  `tn'.t_stor = tn.t_stor` by
    (simp_tac pure_ss [Abbr `tn'`] >> irule (cj 3 mcopy_operand_ghost_frame) >> simp[]) >>
  `tn'.t_trans = tn.t_trans` by
    (simp_tac pure_ss [Abbr `tn'`] >> irule (cj 4 mcopy_operand_ghost_frame) >> simp[]) >>
  `tn'.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
    {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem}` by
    (simp_tac pure_ss [Abbr `tn'`] >> irule (cj 5 mcopy_operand_ghost_frame) >> simp[]) >>
  `tn'.t_imm = tn.t_imm` by
    simp[Abbr `tn'`, step_taint_def, imm_taint_def, mk_inst_def] >>
  simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def,
    ptr_covers_def, op_taint_def]
QED

Finalise emit_slice_copy_counted
