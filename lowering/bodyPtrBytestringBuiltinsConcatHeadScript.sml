(* Typed operand boundary for the Concat head. *)
Theory bodyPtrBytestringBuiltinsConcatHead
Ancestors
  bodyPtrBytestringBuiltinsConcatScratch bodyPtrBytestringBuiltinsConcatArms
  bodyPtrBytestringBuiltinsConcatOperand exprSimConcatArgs exprSimProps
  loweringPosts valueEncoding valueEncodingProps valueEncodingProofs
  bodyPtrDefs vyperValue vyperTypeSystem vyperTyping compileEnv venomState words arithmetic list
  exprLowering exprLoweringProps exprSimConcatPath fragExec freshWrites exprOperandVar finite_map
Libs
  monadsyntax

Theorem concat_operand_fixed_value:
  expr_post ctx func cenv cx e es sa sb s0 es1 v op t /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ ptr_val_ok cx (post_value_type cenv e) v op G tn t ==>
  ?bs. v = BytesV bs /\ LENGTH bs = m /\ m <= 32 /\
    eval_operand op t = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) /\
    op_taint tn op = {}
Proof
  strip_tac >>
  `m <= 32 /\ tv = BaseTV (BytesT (Fixed m))` by
    gvs[evaluate_type_def, AllCaseEqs()] >>
  `post_value_type cenv e = expr_type e` by simp[is_word_type_def] >>
  `expr_val_rel cx (BaseT (BytesT (Fixed m))) v op t` by fs[expr_post_def] >>
  gvs[] >> Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[expr_val_rel_def, is_word_type_def, typed_val_to_w256_def,
      evaluate_type_def, ptr_val_ok_def]
QED

Theorem concat_head_arm_ptr:
  compile_concat compile_expr cenv (e::args) (Var dv)
    (MAP (\e. if is_bytestring_type (expr_type e) then (T,0:num)
      else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m) | _ => (F,32:num)) (e::args))
    (Var ov) sa = ((),sb) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,s1) /\
  (is_bytestring_type (expr_type e) \/ ?m. expr_type e = BaseT (BytesT (Fixed m))) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  expr_post ctx func cenv cx e es sa s1 s0 es1 v op t /\
  ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts /\ fn_has_code sa sb func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  not_fresh_at sa dv /\ not_fresh_at sa ov /\
  lookup_var dv s0 = SOME (n2w (B+32)) /\ lookup_var ov s0 = SOME ow /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  binst.inst_id < sa.cs_next_id /\ FLOOKUP s0.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  oinst.inst_id < sa.cs_next_id /\ FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
  (B+bsz <= w2n ow \/ w2n ow+64 <= B) /\ B+bsz < dimword (:256) /\
  mload (w2n ow) s0 = n2w k /\ k <= P /\
  32+P+SUM (MAP concat_payload_capacity (MAP expr_type (e::args))) <= bsz /\
  32+concat_data_bound P (MAP expr_type (e::args)) <= bsz /\
  ghost_inv d cenv cx es1 G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  ptr_covers G0 tn0 dv s0 (bsz-32) /\ ptr_covers G0 tn0 ov s0 32 /\
  (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn0.t_mem) /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn0.t_mem) /\
  ~ctx_has_dalloca ctx /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) ==>
  ?s2 t2 Gf tnf.
    compile_concat compile_expr cenv args (Var dv)
      (MAP (\e. if is_bytestring_type (expr_type e) then (T,0:num)
        else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m) | _ => (F,32:num)) args)
      (Var ov) s2 = ((),sb) /\
    ci_mono sa s1 /\ ci_mono s1 s2 /\ fn_has_code s2 sb func /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 Gf tnf (OK t2) /\
    stmt_state_rel ctx func cenv cx es1 t2 /\ ~t2.vs_halted /\
    t2.vs_current_bb = s2.cs_current_bb /\ t2.vs_inst_idx = LENGTH s2.cs_current_insts /\
    lookup_var dv t2 = SOME (n2w (B+32)) /\ lookup_var ov t2 = SOME ow /\
    FLOOKUP t2.vs_allocas binst.inst_id = SOME (B,bsz) /\
    FLOOKUP t2.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
    (!name lb lsz. local_region cenv es1.scopes t2 name lb lsz ==>
      (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
    mload (w2n ow) t2 = n2w (k+LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) /\
    k+LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= P+concat_payload_capacity (expr_type e) /\
    t2.vs_allocas = t.vs_allocas /\
    (!z. not_fresh_at s1 z ==> lookup_var z t2 = lookup_var z t) /\
    mem_bytes_at (B+32) (k+LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) t2.vs_memory =
      mem_bytes_at (B+32) k t.vs_memory ++ (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) /\
    (!p n. (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) ==>
      mem_bytes_at p n t2.vs_memory = mem_bytes_at p n t.vs_memory) /\
    mem_bytes_at (B+32) k t.vs_memory = mem_bytes_at (B+32) k s0.vs_memory /\
    ghost_inv d cenv cx es1 Gf tnf t2 /\ ghost_kept cenv es1 s1 G tn t Gf tnf /\
    ptr_covers Gf tnf dv t2 (bsz-32) /\ ptr_covers Gf tnf ov t2 32 /\
    (!i. B+32 <= i /\ i < B+32+k+LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) ==> i NOTIN tnf.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tnf.t_mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `ci_mono sa s1` by (drule (cj 2 compile_expr_grows) >> simp[ci_mono_def]) >>
  `sa.cs_next_var <= s1.cs_next_var /\ cs_extends sa s1` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. op = Var x ==> not_fresh_at s1 x` by metis_tac[compile_lower_value_var] >>
  `not_fresh_at s1 dv /\ not_fresh_at s1 ov` by metis_tac[not_fresh_at_mono] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    metis_tac[not_fresh_at_mono] >>
  `32+P+(concat_payload_capacity (expr_type e) +
    SUM (MAP concat_payload_capacity (MAP expr_type args))) <= bsz` by
    (qpat_x_assum `32+P+SUM _ <= _` mp_tac >> simp[]) >>
  `32+k <= bsz` by decide_tac >>
  drule_all concat_args_pre_ptr >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es1 t` by fs[expr_post_def] >>
  `mload (w2n ow) t = n2w k` by metis_tac[] >>
  Cases_on `is_bytestring_type (expr_type e)`
  >- suspend "bytes"
  >> suspend "fixed"
QED

Resume concat_head_arm_ptr[bytes]:
  qpat_x_assum `compile_concat _ _ (_::_) _ _ _ _ = _` mp_tac >>
  simp[] >> strip_tac >> drule compile_concat_bytes_cons >> strip_tac >>
  `mem_ptr = op /\ s1' = s1` by
    (qpat_x_assum `lower_value _ _ _ _ _ = (mem_ptr,_)` mp_tac >> simp[]) >>
  qpat_x_assum `mem_ptr = op` SUBST_ALL_TAC >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  drule_all concat_operand_bytes_read >> strip_tac >>
  qpat_x_assum `op = Var p` SUBST_ALL_TAC >>
  `ci_mono s1 s2` by
    (qpat_x_assum `(do arg_len <- _; _ od) s1 = ((),s2)` mp_tac >>
     qmatch_goalsub_abbrev_tac `stp s1 = ((),s2) ==> _` >>
     `ci_mono s1 (SND (stp s1))` suffices_by (rpt strip_tac >> gvs[]) >>
     qunabbrev_tac `stp` >>
     rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void]) ORELSE gen_tac) >>
     simp[ci_mono_emit_op, ci_mono_emit_void]) >>
  `ci_mono s2 sb` by
    metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (fs[ci_mono_def] >>
     `cs_extends sa s2` by metis_tac[cs_extends_trans] >>
     `cs_extends sb sb` by simp[cs_extends_refl] >> metis_tac[fn_has_code_mid]) >>
  `mload (w2n w) t = n2w (LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []))` by
    fs[mem_word_at_eq_mload] >>
  `32+k+LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= bsz` by decide_tac >>
  `not_fresh_at s1 p` by simp[] >>
  drule_all concat_bytes_arm_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "common_b"
QED

Resume concat_head_arm_ptr[fixed]:
  `?m. expr_type e = BaseT (BytesT (Fixed m))` by metis_tac[] >>
  qpat_x_assum `compile_concat _ _ (_::_) _ _ _ _ = _` mp_tac >>
  simp[] >> strip_tac >> drule compile_concat_fixed_cons >> strip_tac >>
  `v' = op /\ s1' = s1` by
    (qpat_x_assum `lower_value _ _ _ _ _ = (v',_)` mp_tac >> simp[]) >>
  qpat_x_assum `v' = op` SUBST_ALL_TAC >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  drule_all concat_operand_fixed_value >> strip_tac >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `ci_mono s1 s2` by
    (qpat_x_assum `(do offset_op <- _; _ od) s1 = ((),s2)` mp_tac >>
     qmatch_goalsub_abbrev_tac `stp s1 = ((),s2) ==> _` >>
     `ci_mono s1 (SND (stp s1))` suffices_by (rpt strip_tac >> gvs[]) >>
     qunabbrev_tac `stp` >>
     rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void]) ORELSE gen_tac) >>
     simp[ci_mono_emit_op, ci_mono_emit_void]) >>
  `ci_mono s2 sb` by
    metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (fs[ci_mono_def] >>
     `cs_extends sa s2` by metis_tac[cs_extends_trans] >>
     `cs_extends sb sb` by simp[cs_extends_refl] >> metis_tac[fn_has_code_mid]) >>
  `32+k+32 <= bsz` by
    (qpat_x_assum `32+concat_data_bound _ _ <= _` mp_tac >>
     simp[concat_data_bound_def, is_bytestring_type_def] >>
     rewrite_tac[arithmeticTheory.MAX_DEF] >> IF_CASES_TAC >> decide_tac) >>
  drule_all concat_fixed_arm_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "common_f"
QED

Resume concat_head_arm_ptr[common_b]:
  qexistsl_tac [`s2`,`u`,`Gf`,`tnf`] >>
  `lookup_var dv u = SOME (n2w (B+32)) /\ lookup_var ov u = SOME ow` by metis_tac[] >>
  `FLOOKUP u.vs_allocas binst.inst_id = SOME (B,bsz) /\
   FLOOKUP u.vs_allocas oinst.inst_id = SOME (w2n ow,64)` by simp[] >>
  `!name lb lsz. local_region cenv es1.scopes u name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)` by
    (rpt gen_tac >> strip_tac >>
     `local_region cenv es1.scopes t name lb lsz` by
       (irule local_region_frame >>
        conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`s1`,`es1.scopes`,`u`] >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  simp[] >> rpt conj_tac >> metis_tac[ADD_COMM]
QED

Resume concat_head_arm_ptr[common_f]:
  qexistsl_tac [`s2`,`u`,`Gf`,`tnf`] >>
  `lookup_var dv u = SOME (n2w (B+32)) /\ lookup_var ov u = SOME ow` by metis_tac[] >>
  `FLOOKUP u.vs_allocas binst.inst_id = SOME (B,bsz) /\
   FLOOKUP u.vs_allocas oinst.inst_id = SOME (w2n ow,64)` by simp[] >>
  `!name lb lsz. local_region cenv es1.scopes u name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)` by
    (rpt gen_tac >> strip_tac >>
     `local_region cenv es1.scopes t name lb lsz` by
       (irule local_region_frame >>
        conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`s1`,`es1.scopes`,`u`] >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  simp[concat_payload_capacity_def] >> rpt conj_tac >> metis_tac[ADD_COMM]
QED

Finalise concat_head_arm_ptr
