(* Robust dynamic-array header preparation. *)
Theory widenedAssignPtrDynPrefix
Ancestors
  bodyPtrBopInHeaderControl bodyPtrSubscriptLengthRead
  assignTuplePtrLoadStep representationCleanPtr valueEncoding
  bodyPtrDefs contextProps valueEncodingProps freshWrites
  widenedAssignPtrIndexAdmin typedMemoryCopy emitHelperProps emitHelper
  compileEnv exprLoweringProps loweringStateRelDefs fragExec fragGasPathPtr
  venomState venomExecSemantics ptrDiscipline finite_map words list arithmetic

Theorem widened_assign_capacity_counted[local]:
  emit_op GT [length; Lit (n2w C)] a = (Var flag,b) /\
  emit_op ISZERO [Var flag] b = (Var valid,c) /\
  emit_void ASSERT [Var valid] c = ((),d) /\
  eval_operand length s = SOME (n2w N) /\ N <= C /\ C < dimword (:256) /\
  op_taint tn length = {} /\ op_prov G length = NONE /\
  fn_has_code a d fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = d.cs_current_bb /\
    t.vs_inst_idx = LENGTH d.cs_current_insts /\ ~t.vs_halted /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `d.cs_current_bb = a.cs_current_bb /\
   d.cs_current_insts = a.cs_current_insts ++
     [mk_inst a.cs_next_id GT [length; Lit (n2w C)] [flag];
      mk_inst b.cs_next_id ISZERO [Var flag] [valid];
      mk_inst c.cs_next_id ASSERT [Var valid] []] /\
   (!x. not_fresh_at a x ==> x <> flag /\ x <> valid)` by
    (gvs[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
         comp_return_def, not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst a.cs_next_id GT [length; Lit (n2w C)] [flag]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst b.cs_next_id ISZERO [Var flag] [valid]) /\
   get_instruction bb (s.vs_inst_idx+2) =
     SOME (mk_inst c.cs_next_id ASSERT [Var valid] [])` by
    (rpt conj_tac
     >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
     >- (first_x_assum (qspec_then `1` mp_tac) >> simp[ADD1]) >>
     first_x_assum (qspec_then `2` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all membership_capacity_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`G'`,`tn'`,`t`] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  metis_tac[]
QED

Theorem widened_assign_dyn_read_check_counted:
  emit_op MLOAD [Var src] a = (length,b) /\
  emit_op GT [length; Lit (n2w C)] b = (Var flag,c) /\
  emit_op ISZERO [Var flag] c = (Var valid,d) /\
  emit_void ASSERT [Var valid] d = ((),e) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME sw /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n sw) m = n2w N) /\
  N <= C /\ C < dimword (:256) /\ fn_has_code a e fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = e.cs_current_bb /\
    t.vs_inst_idx = LENGTH e.cs_current_insts /\ ~t.vs_halted /\
    eval_operand length t = SOME (n2w N) /\
    op_taint tm length = {} /\ op_prov H length = NONE /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d /\ cs_extends d e` by
    gvs[ci_mono_def] >>
  `fn_has_code a b fn /\ fn_has_code b e fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!i. w2n sw <= i /\ i < w2n sw + 32 ==> i NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  `mload (w2n sw) s = n2w N` by
    (rewrite_tac[GSYM mem_word_at_eq_mload] >>
     first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all emit_mload_member_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >> gvs[] >>
  `eval_operand (Var out) t = SOME (n2w N)` by simp[eval_operand_def] >>
  `t.vs_current_bb = b.cs_current_bb` by simp[] >>
  qpat_assum `emit_op GT _ b = _`
    (mp_then Any mp_tac widened_assign_capacity_counted) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `!x. not_fresh_at a x ==> not_fresh_at b x` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `not_fresh_at b out` by simp[] >>
  `eval_operand (Var out) t' = SOME (n2w N) /\
   op_taint tm (Var out) = {} /\ op_prov H (Var out) = NONE` by
    (simp[eval_operand_def, op_prov_def] >> gvs[op_prov_def]) >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    simp[venom_state_component_equality] >>
  qpat_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t)`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexistsl_tac [`H`,`tm`,`t'`] >> simp[] >>
  qpat_assum `t' = _` (fn th => once_rewrite_tac[th]) >>
  qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
  simp[NoAsms] >> simp[]
QED
