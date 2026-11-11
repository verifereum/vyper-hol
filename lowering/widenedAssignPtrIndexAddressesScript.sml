Theory widenedAssignPtrIndexAddresses
Ancestors
  bodyPtrPopLocalRootFrame placeTypedCopyRecursivePath bodyPtrAttributeAdd
  exprLoweringProps typedMemoryCopy fragExec
  typedCopyLoopHeaderPtr emitHelperProps emitHelper compileEnv loweringStateRelDefs
  venomState ptrDiscipline finite_map words list fragGasPathPtr

(* Empty subregions need clean arithmetic, but no invented pointer coverage. *)
Theorem widened_assign_index_add_exact:
  emit_op ADD [bop;offset] sa = (dst,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand bop s = SOME a /\ eval_operand offset s = SOME (n2w off) /\
  op_taint tn bop = {} /\ op_taint tn offset = {} /\
  (!root. bop = Var root ==> not_fresh_at sa root) /\
  (0 < n ==> ?root total. bop = Var root /\
    ptr_covers G tn root s total /\ off < total /\ off+n <= total /\
    w2n a + off < dimword(:256)) ==>
  ?out t G' tn'. dst = Var out /\ not_fresh_at sb out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    eval_operand dst t = SOME (a + n2w off) /\
    op_taint tn' dst = {} /\ (0 < n ==> ptr_covers G' tn' out t n) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `?out G' tn' t.
    dst = Var out /\ gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (update_var out (a + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst sa.cs_next_id ADD [bop;offset] [out])
      (update_var out (a + n2w off) s) /\
    tn' = step_taint (mk_inst sa.cs_next_id ADD [bop;offset] [out]) s
      (update_var out (a + n2w off) s) tn /\
    tn'.t_imm = tn.t_imm /\ op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!v. v <> out ==> FLOOKUP G' v = FLOOKUP G v /\
      op_taint tn' (Var v) = op_taint tn (Var v))` by
    (irule attribute_emit_binop_path_ptr >>
     simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   not_fresh_at sb out /\ (!v. not_fresh_at sa v ==> v <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `0 < n ==> ptr_covers G' tn' out t n` by
    (strip_tac >>
     qpat_x_assum `0 < n ==> _` drule >> strip_tac >>
     `lookup_var root s = SOME a /\ root <> out` by
       metis_tac[eval_operand_def] >>
     `ptr_covers G' tn' out (update_var out (a + n2w off) s) n` by
       (simp[] >> irule typed_copy_loop_dynamic_offset_covers >> metis_tac[]) >>
     gvs[bodyPtrDefsTheory.ptr_covers_def, update_var_def, lookup_var_def]) >>
  qpat_x_assum `G' = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `tn' = step_taint _ _ _ _` kall_tac >>
  qexistsl_tac [`out`, `t`, `G'`, `tn'`] >>
  simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem widened_assign_index_offsets_counted:
  emit_op MUL [Var counter; Lit (n2w ss)] sa = (so,sb) /\
  emit_op MUL [Var counter; Lit (n2w ds)] sb = (doff,sc) /\
  not_fresh_at sa counter /\ lookup_var counter s = SOME (n2w k) /\
  op_taint tn (Var counter) = {} /\
  fn_has_code sa sc fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    eval_operand so t = SOME (n2w (k*ss)) /\
    eval_operand doff t = SOME (n2w (k*ds)) /\
    op_taint tn' so = {} /\ op_taint tn' doff = {} /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `!tm w. op_taint tm (Lit w) = {}` by simp[op_taint_def] >>
  `ci_mono sa sb /\ ci_mono sb sc` by metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn` by
    metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def] >>
  qpat_assum `emit_op MUL _ sa = _` (mp_then Any mp_tac pop_local_mul_exact) >>
  disch_then (qspecl_then [`tn`, `s`] mp_tac) >>
  disch_then drule >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var counter t = SOME (n2w k) /\ op_taint tn' (Var counter) = {}` by metis_tac[] >>
  `!v. not_fresh_at sa v ==> not_fresh_at sb v` by
    (gvs[ci_mono_def, not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  qpat_assum `emit_op MUL _ sb = _` (mp_then Any mp_tac pop_local_mul_exact) >>
  disch_then (qspecl_then [`tn'`, `t`] mp_tac) >>
  disch_then drule >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`PG`, `G'`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G' tn' t 0 H tm (OK u)` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK u)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  qexistsl_tac [`u`, `H`, `tm`] >>
  gvs[eval_operand_def, GSYM word_mul_n2w, WORD_MULT_COMM] >>
  qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED
