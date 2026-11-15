(* Robust dynamic-array header preparation. *)
Theory widenedAssignPtrDynPrefix
Ancestors
  bodyPtrBopInHeaderControl bodyPtrSubscriptLengthRead
  bodyPtrBytestringBuiltinsSource bodyPtrPrecompileBuiltinsArithmeticValue
  augAssignPtrFieldLoad pred_set typedCopyRobustTransportPtr
  assignTuplePtrLoadStep representationCleanPtr valueEncoding
  bodyPtrDefs contextProps valueEncodingProps valueEncodingDefs freshWrites
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

Theorem widened_assign_checked_header_store_counted:
  emit_op MLOAD [Var src] a = (length,b) /\
  emit_op GT [length; Lit (n2w C)] b = (Var flag,c) /\
  emit_op ISZERO [Var flag] c = (Var valid,d) /\
  emit_void ASSERT [Var valid] d = ((),e) /\
  emit_void MSTORE [Var dst; length] e = ((),f) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME sw /\
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME dw /\
  not_fresh_at a dst /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n sw) m = n2w N) /\
  N <= C /\ C < dimword (:256) /\ fn_has_code a f fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = f.cs_current_bb /\
    t.vs_inst_idx = LENGTH f.cs_current_insts /\ ~t.vs_halted /\
    eval_operand length t = SOME (n2w N) /\
    op_taint tm length = {} /\ op_prov H length = NONE /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      mem_word_at (w2n dw) m = n2w N) /\
    typed_copy_state_frame a (w2n dw) 32 s t /\
    tm.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32} /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ ci_mono e f` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends a e /\ cs_extends e f` by
    metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code a e fn /\ fn_has_code e f fn` by
    metis_tac[fn_has_code_split] >>
  drule_all widened_assign_dyn_read_check_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var dst t = SOME dw /\ ptr_covers H tm dst t 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  drule_all emit_scratch_word_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qpat_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t)`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexistsl_tac [`H`,`tn'`,`t'`] >> simp[] >>
  conj_tac >- (Cases_on `length` >> gvs[op_taint_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_word_at (w2n dw) m = mem_word_at (w2n dw) t'.vs_memory` by
        (sym_tac >> irule clean_word_mem_agree >>
         qexists_tac `tn'.t_mem` >> simp[] >> gvs[]) >>
      metis_tac[]) >>
  conj_tac
  >- (`typed_copy_state_frame a (w2n dw) 32 s t` by
        (rewrite_tac[typed_copy_state_frame_def] >> conj_tac
         >- (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
             simp[venom_state_component_equality]) >>
         conj_tac >- metis_tac[] >>
         qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
         simp[typed_copy_frame_def]) >>
      irule typed_copy_state_frame_trans >> qexists_tac `t` >>
      simp[typed_copy_mstore_state_frame]) >>
  gvs[op_taint_def]
QED

Theorem widened_assign_checked_header_prefix_counted:
  emit_op MLOAD [Var src] a = (length,b) /\
  emit_op GT [length; Lit (n2w C)] b = (Var flag,c) /\
  emit_op ISZERO [Var flag] c = (Var valid,d) /\
  emit_void ASSERT [Var valid] d = ((),e) /\
  emit_void MSTORE [Var dst; length] e = ((),f) /\
  emit_op ADD [Var src; Lit 32w] f = (Var sd,g) /\
  emit_op ADD [Var dst; Lit 32w] g = (Var dd,h) /\
  ptr_covers G tn src s (32+sn) /\ lookup_var src s = SOME sw /\
  ptr_covers G tn dst s (32+dn) /\ lookup_var dst s = SOME dw /\
  not_fresh_at a src /\ not_fresh_at a dst /\
  w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n sw) m = n2w N) /\
  N <= C /\ C < dimword (:256) /\ fn_has_code a h fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = h.cs_current_bb /\
    t.vs_inst_idx = LENGTH h.cs_current_insts /\ ~t.vs_halted /\
    eval_operand length t = SOME (n2w N) /\
    op_taint tm length = {} /\ op_prov H length = NONE /\
    lookup_var sd t = SOME (sw+32w) /\ ptr_covers H tm sd t sn /\
    lookup_var dd t = SOME (dw+32w) /\ ptr_covers H tm dd t dn /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      mem_word_at (w2n dw) m = n2w N) /\
    typed_copy_state_frame a (w2n dw) 32 s t /\
    tm.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32} /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\
   ci_mono e f /\ ci_mono f g /\ ci_mono g h` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono a f /\ ci_mono a g` by (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `fn_has_code a f fn /\ fn_has_code f g fn /\ fn_has_code g h fn` by
    metis_tac[fn_has_code_split, ci_mono_def, cs_extends_trans] >>
  `ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32` by
    (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all widened_assign_checked_header_store_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var src t = SOME sw /\ lookup_var dst t = SOME dw /\
   ptr_covers H tm src t (32+sn) /\ ptr_covers H tm dst t (32+dn)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `?site. FLOOKUP H src = SOME site` by gvs[ptr_covers_def] >>
  `op_taint tm (Var src) = {}` by gvs[ptr_covers_def] >>
  drule_all emit_add_member_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >> gvs[] >>
  `!x. not_fresh_at a x ==> not_fresh_at f x /\ not_fresh_at g x` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `lookup_var dst t' = SOME dw /\ op_taint tn' (Var dst) = {} /\
   ?site'. FLOOKUP G' dst = SOME site'` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `t'.vs_current_bb = g.cs_current_bb` by simp[] >>
  qpat_assum `emit_op ADD _ g = _` (mp_then Any mp_tac emit_add_member_path_ptr) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >> gvs[] >>
  `!x. length = Var x ==> not_fresh_at b x` by
    metis_tac[typed_copy_emit_op_fresh] >>
  `!x. length = Var x ==> not_fresh_at f x /\ not_fresh_at g x` by
    (gvs[ci_mono_def] >> metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]) >>
  `eval_operand length t'' = SOME (n2w N) /\
   op_taint tn'' length = {} /\ op_prov G'' length = NONE` by
    (Cases_on `length` >> gvs[eval_operand_def, op_prov_def, op_taint_def] >> metis_tac[]) >>
  `lookup_var out t'' = SOME (sw+32w) /\ op_taint tn'' (Var out) = {} /\
   FLOOKUP G'' out = SOME site` by metis_tac[] >>
  `w2n (sw+32w) = w2n sw + 32 /\ w2n (dw+32w) = w2n dw + 32` by
    (gvs[wordsTheory.dimword_def] >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
          wordsTheory.dimword_def]) >>
  `ptr_covers G'' tn'' out t'' sn /\ ptr_covers G'' tn'' dd t'' dn` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  `typed_copy_state_frame a (w2n dw) 32 t t''` by
    (simp[typed_copy_state_frame_def, venom_state_component_equality,
          typed_copy_frame_def] >> metis_tac[]) >>
  qpat_assum `gas_path_ptr D 0 ctx fn PG H tm t 0 G' tn' (OK t')`
    (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >> strip_tac >>
  qpat_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t)`
    (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >> strip_tac >>
  qexistsl_tac [`G''`,`tn''`,`t''`] >> simp[] >>
  metis_tac[typed_copy_state_frame_trans]
QED

Theorem widened_assign_dynarray_header_prefix_counted:
  emit_op MLOAD [Var src] a = (length,b) /\
  emit_op GT [length; Lit (n2w C)] b = (Var flag,c) /\
  emit_op ISZERO [Var flag] c = (Var valid,d) /\
  emit_void ASSERT [Var valid] d = ((),e) /\
  emit_void MSTORE [Var dst; length] e = ((),f) /\
  emit_op ADD [Var src; Lit 32w] f = (Var sd,g) /\
  emit_op ADD [Var dst; Lit 32w] g = (Var dd,h) /\
  ptr_covers G tn src s (32+scap*type_memory_size stv) /\
  lookup_var src s = SOME sw /\
  ptr_covers G tn dst s (32+dn) /\ lookup_var dst s = SOME dw /\
  not_fresh_at a src /\ not_fresh_at a dst /\
  w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
      (w2n sw) m) /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
    w2n dw + 32 <= w2n sw) /\
  LENGTH vs <= C /\ C < dimword (:256) /\ fn_has_code a h fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = h.cs_current_bb /\
    t.vs_inst_idx = LENGTH h.cs_current_insts /\ ~t.vs_halted /\
    eval_operand length t = SOME (n2w (LENGTH vs)) /\
    op_taint tm length = {} /\ op_prov H length = NONE /\
    lookup_var sd t = SOME (sw+32w) /\
    ptr_covers H tm sd t (LENGTH vs * type_memory_size stv) /\
    lookup_var dd t = SOME (dw+32w) /\ ptr_covers H tm dd t dn /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      mem_word_at (w2n dw) m = n2w (LENGTH vs)) /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      elems_in_memory vs (w2n sw + 32) stv m) /\
    typed_copy_state_frame a (w2n dw) 32 s t /\
    tm.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32} /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n sw) m = n2w (LENGTH vs)` by
    gvs[val_in_memory_def] >>
  drule_all widened_assign_checked_header_prefix_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
    val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
      (w2n sw) m` by
    (rpt strip_tac >> irule robust_representation_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`w2n dw`, `s.vs_memory`, `t.vs_memory`, `32`,
                  `tn.t_mem`, `tm.t_mem`] >>
     gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `LENGTH vs <= scap` by gvs[val_wf_def] >>
  `LENGTH vs * type_memory_size stv <= scap * type_memory_size stv` by
    simp[LESS_MONO_MULT] >>
  qexistsl_tac [`H`,`tm`,`t`] >> simp[] >>
  conj_tac >-
    (gvs[ptr_covers_def] >> irule LESS_EQ_TRANS >>
     qexists_tac `w2n (sw+32w) + scap * type_memory_size stv` >>
     simp[LESS_MONO_MULT]) >>
  gvs[val_in_memory_def]
QED
