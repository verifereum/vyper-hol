(* Memory slice fragment boundaries, factored at actual compiler steps. *)
Theory bodyPtrBytestringBuiltinsSlice
Ancestors
  bodyPtrBytestringBuiltinsBounds bodyPtrBytestringBuiltinsSource
  bodyPtrBytestringBuiltinsBuffer builtinBytes emitHelper compileEnv fragExec
  exprLoweringProps list rich_list exprSimPtrProps typedCopyPtr fragExecPtr
  ptrDiscipline venomInst venomState emitHelperProps fragGasPathPtr finite_map
  venomExecSemantics bodyPtrDefs freshWrites exprSimProps emittedSeqComposePtr

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

(* The successful bounds prefix changes only fresh scalar registers.  This
   keeps allocation resources available at the next compiler cursor. *)
Theorem slice_bounds_allocation_frame:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  stmt_state_rel ctx fn cenv cx es
    (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  local_ptrs_reserved cenv sb /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule compile_assert_slice_bounds_layout >> strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by
    (simp[writes_fresh_def, mk_inst_def, fresh_write_op_def,
      not_fresh_at_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    simp[lookup_var_def] >>
  `stmt_state_rel ctx fn cenv cx es (s with vs_vars := u.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     gvs[lookup_var_def]) >>
  conj_tac
  >- (qpat_x_assum `u = _` SUBST1_TAC >> simp[stmt_state_rel_inst_idx]) >>
  simp[] >> irule local_ptrs_reserved_next_var >>
  qexists_tac `sa` >> simp[]
QED


Theorem compile_slice_data_counted_normal:
  compile_slice_data src_len (Var src) start len N sa = (out,sb) /\
  compile_assert_slice_bounds start len src_len sa = ((),sc) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct fn /\ fresh_vars_wrt sa s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  32 <= N /\ N < dimword(:256) /\
  run_inst_seq (emitted_insts sa sc) s = OK u /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s cap /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  eval_operand src_len s = SOME wl /\ not_fresh_at sa src /\
  (!op. MEM op [start;len;src_len] ==>
    (!x. op = Var x ==> not_fresh_at sa x) /\
    op_prov G op = NONE /\ op_taint tn op = {}) /\
  w2n wa + w2n wn <= cap /\ w2n wn <= N - 32 /\
  w2n a + w2n wa < dimword(:256) ==>
  ?r b t G' tn'.
    out = Var r /\ lookup_var r t = SOME b /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ptr_covers G' tn' r t N /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ mem_word_at (w2n b) t.vs_memory = wn /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule compile_slice_data_stages >> strip_tac >>
  `s1 = sc` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `s1 = sc` SUBST_ALL_TAC >>
  `cs_extends sc sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by metis_tac[fn_has_code_split] >>
  `!op. MEM op [start;len;src_len] ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    simp[] >>
  drule_all compile_assert_slice_bounds_counted_ok >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all slice_bounds_allocation_frame >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ G tn s _ Gb tnb (OK ub)` >>
  `fn_has_code sc s2 fn /\ fn_has_code s2 sb fn` by
    (`cs_extends s2 sb` by metis_tac[cs_extends_trans] >> metis_tac[fn_has_code_split]) >>
  `u.vs_halted = s.vs_halted` by
    (qpat_assum `u = _` (mp_tac o Q.AP_TERM `\t. t.vs_halted`) >> simp[]) >>
  `~ub.vs_halted /\ ub.vs_current_bb = sc.cs_current_bb /\
   ub.vs_inst_idx = LENGTH sc.cs_current_insts` by simp[Abbr `ub`] >>
  drule_all compile_slice_out_buf_counted >>
  disch_then (qspecl_then [`tnb`,`PG`,`Gb`,`D`] strip_assume_tac) >>
  suspend "source_offset"
QED

Resume compile_slice_data_counted_normal[source_offset]:
  qpat_x_assum `G2 = _` kall_tac >> qpat_x_assum `tn2 = _` kall_tac >>
  qpat_x_assum `t = _` kall_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (drule compile_assert_slice_bounds_layout >> strip_tac >> rpt strip_tac >>
     irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
    op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `ub`] >> fs[lookup_var_def]) >>
  `lookup_var src t = SOME a /\ ptr_covers G2 tn2 src t cap` by
    (qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
       (qspec_then `src` mp_tac) >> simp[] >>
     simp[ptr_covers_def] >> gvs[ptr_covers_def]) >>
  `!op w. MEM op [start;len;src_len] /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w /\ op_taint tn2 op = {}` by
    (rpt strip_tac >>
     `!x. op = Var x ==> not_fresh_at sc x` by metis_tac[] >>
     `eval_operand op t = eval_operand op ub /\ op_taint tn2 op = op_taint tnb op` by simp[] >>
     `eval_operand op ub = SOME w` by simp[Abbr `ub`] >>
     `op_taint tnb op = op_taint tn op` by
       (irule old_operand_taint_frame >> qexists_tac `sa` >> simp[] >> metis_tac[]) >>
     `op_taint tn op = {}` by metis_tac[] >>
     simp[]) >>
  `?q. copy = Var q` by
    (qpat_x_assum `emit_op ADD [Var src; start] _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]) >>
  `fn_has_code s2 s3 fn /\ fn_has_code s3 sb fn` by
    (`cs_extends s3 sb` by metis_tac[cs_extends_trans] >> metis_tac[fn_has_code_split]) >>
  `eval_operand start t = SOME (n2w (w2n wa)) /\ op_taint tn2 start = {}` by simp[] >>
  qpat_x_assum `copy = Var q` SUBST_ALL_TAC >>
  qpat_x_assum `emit_op ADD [Var r; Lit 32w] _ = _` kall_tac >>
  drule_all (PURE_REWRITE_RULE [wordsTheory.n2w_w2n]
    (Q.SPECL [`src`,`w2n wa`] emit_pointer_offset_counted_covers)) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  suspend "copy_store"
QED

Resume compile_slice_data_counted_normal[copy_store]:
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ G3 tn3 (OK v)` >>
  `q = STRCAT "%" (toString s2.cs_next_var) /\
   s3.cs_next_var = s2.cs_next_var + 1 /\
   s3.cs_current_bb = s2.cs_current_bb /\
   LENGTH s3.cs_current_insts = LENGTH s2.cs_current_insts + 1` by
    (qpat_x_assum `emit_op ADD [Var src; start] _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]) >>
  `not_fresh_at s2 r /\ not_fresh_at s2 p /\ sc.cs_next_var <= s2.cs_next_var` by
    (`compile_slice_out_buf N sc = ((Var r,Var p),s2)` by simp[] >>
     pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compile_slice_out_buf_def, contextTheory.compile_alloc_buffer_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[fresh_var_distinct]) >>
  `!x. not_fresh_at s2 x ==> x <> q` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     metis_tac[fresh_var_distinct, prim_recTheory.LESS_REFL]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sc` >> simp[]) >>
  suspend "offset_frame"
QED

Resume compile_slice_data_counted_normal[offset_frame]:
  `!x. x <> q ==> FLOOKUP G3 x = FLOOKUP G2 x /\
    op_taint tn3 (Var x) = op_taint tn2 (Var x)` by
    (rpt strip_tac >> simp[Abbr `G3`, Abbr `tn3`, copy_len_binop_ghost_frame]) >>
  `!x. x <> q ==> lookup_var x v = lookup_var x t` by
    simp[Abbr `v`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `!x k. x <> q /\ ptr_covers G2 tn2 x t k ==> ptr_covers G3 tn3 x v k` by
    (rpt strip_tac >> fs[ptr_covers_def]) >>
  `ptr_covers G3 tn3 r v N /\ ptr_covers G3 tn3 p v (N - 32)` by simp[] >>
  `!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s /\
    FLOOKUP G3 x = FLOOKUP G x /\ op_taint tn3 (Var x) = op_taint tn (Var x)` by simp[] >>
  `eval_operand len v = SOME wn /\ op_taint tn3 len = {}` by
    (`eval_operand len t = SOME wn /\ op_taint tn2 len = {}` by simp[] >>
     `!x. len = Var x ==> x <> q` by metis_tac[listTheory.MEM] >>
     conj_tac
     >- (`eval_operand len v = eval_operand len t` by
           (Cases_on `len` >> simp[NoAsms, Abbr `v`, eval_operand_def, lookup_var_def,
             update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >> simp[]) >>
     Cases_on `len` >> simp[op_taint_def] >>
     first_x_assum (qspec_then `s'` mp_tac) >> simp[op_taint_def]) >>
  `v.vs_current_bb = s3.cs_current_bb /\
   v.vs_inst_idx = LENGTH s3.cs_current_insts /\ ~v.vs_halted` by
    simp[Abbr `v`, update_var_def] >>
  suspend "copy_apply"
QED

Resume compile_slice_data_counted_normal[copy_apply]:
  `fn_has_code s3 s4 fn /\ fn_has_code s4 sb fn` by
    metis_tac[fn_has_code_split] >>
  `emit_void MCOPY [Var p; Var q; len] s3 = ((),s4)` by metis_tac[] >>
  `?av. lookup_var q v = SOME av` by metis_tac[ptr_covers_def] >>
  `?bv. lookup_var p v = SOME bv` by metis_tac[ptr_covers_def] >>
  `ptr_covers G3 tn3 p v (w2n wn)` by
    (qpat_assum `ptr_covers G3 tn3 p v (N - 32)` mp_tac >>
     qpat_assum `w2n wn <= N - 32` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ptr_covers_def] >> rpt strip_tac >>
     qexistsl_tac [`w`,`b`,`sz'`] >> simp[] >> decide_tac) >>
  drule_all emit_slice_copy_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  suspend "store_apply"
QED

Resume compile_slice_data_counted_normal[store_apply]:
  `emit_void MSTORE [Var r; len] s4 = ((),sb)` by metis_tac[] >>
  `ptr_covers G3 tn'' r t' N` by simp[] >>
  `ptr_covers G3 tn'' r t' 32` by
    (qpat_assum `ptr_covers G3 tn'' r t' N` mp_tac >>
     qpat_assum `32 <= N` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ptr_covers_def] >> rpt strip_tac >>
     qexistsl_tac [`w`,`b`,`sz'`] >> simp[] >> decide_tac) >>
  `?br. lookup_var r t' = SOME br` by metis_tac[ptr_covers_def] >>
  `eval_operand len t' = SOME wn` by
    (`eval_operand len t' = eval_operand len v` by
       (qpat_x_assum `t' = _` SUBST1_TAC >>
        Cases_on `len` >>
        simp[NoAsms, mcopy_def, write_memory_with_expansion_def,
          eval_operand_def, lookup_var_def]) >> simp[]) >>
  `op_taint tn'' len = {}` by
    (Cases_on `len` >> fs[op_taint_def]) >>
  drule_all emit_scratch_word_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  suspend "compose_final"
QED

Resume compile_slice_data_counted_normal[compose_final]:
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ G3 tn'' t' _ G3 tnf (OK t'')` >>
  `gas_path_ptr D 0 ctx fn PG G3 tn3 v 0 G3 tnf (OK t'')` by
    (irule (REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]
       (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     qexistsl_tac [`G3`,`t'`,`tn''`] >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G2 tn2 t 0 G3 tnf (OK t'')` by
    (qpat_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `gas_path_ptr _ _ _ _ _ G3 tn3 v _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]) >>
  `gas_path_ptr D 0 ctx fn PG Gb tnb ub 0 G3 tnf (OK t'')` by
    (irule (REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]
       (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     qexistsl_tac [`G2`,`t`,`tn2`] >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G3 tnf (OK t'')` by
    (irule (REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]
       (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     qexistsl_tac [`Gb`,`ub`,`tnb`] >> simp[]) >>
  qexistsl_tac [`r`,`br`,`t''`,`G3`,`tnf`] >> simp[] >>
  rpt strip_tac >> fs[op_taint_def]
QED

Finalise compile_slice_data_counted_normal
