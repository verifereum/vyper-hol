(* The counted LocMemory suffix, starting after operand preparation. *)
Theory bodyAppendMemorySuffixMods
Ancestors
  bodyAppendMemoryGuardMods bodyAppendMemoryAddressMods
  bodyAppendMemoryPayloadMods bodyAppendMemoryEncodingMods
  representationCleanPtr valueEncodingProps reasonCopySourcePtr
  assignTuplePtrCopyLen typedCopyOriginPtrBase typedMemoryCopy
  exprLoweringProps exprLowering emitHelperProps emitHelper
  fragExec fragGasOriginPtrLoop contextCodegenRel compileEnv context freshWrites
  bodyPtrDefs valueEncodingDefs venomState venomInst ptrDiscipline
  finite_map pred_set list arithmetic words

Theorem memory_append_suffix_parts[local]:
  compile_dynarray_append cenv bop src 32 stride elem elem cap F LocMemory a0 = ((),a9) <=>
  ?len valid data off dst next a1 a2 a3 a4 a5 a6 a7 a8.
    emit_op MLOAD [bop] a0 = (len,a1) /\
    emit_op LT [len; Lit (n2w cap)] a1 = (valid,a2) /\
    emit_void ASSERT [valid] a2 = ((),a3) /\
    emit_op ADD [bop; Lit 32w] a3 = (data,a4) /\
    emit_op MUL [len; Lit (n2w stride)] a4 = (off,a5) /\
    emit_op ADD [data;off] a5 = (dst,a6) /\
    compile_store_memory cenv src dst elem elem a6 = ((),a7) /\
    emit_op ADD [len; Lit 1w] a7 = (next,a8) /\
    emit_void MSTORE [bop;next] a8 = ((),a9)
Proof
  simp[compile_dynarray_append_def, compile_ptr_load_def, compile_ptr_store_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def, emit_op_def,
       emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def] >>
  pairarg_tac >> simp[] >> eq_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `(\(_0,cs'). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem memory_append_suffix_cuts[local]:
  emit_op MLOAD [bop] a = (len,a1) /\
  emit_op LT [len; Lit (n2w cap)] a1 = (valid,a2) /\
  emit_void ASSERT [valid] a2 = ((),a3) /\
  emit_op ADD [bop; Lit 32w] a3 = (data,a4) /\
  emit_op MUL [len; Lit (n2w stride)] a4 = (off,a5) /\
  emit_op ADD [data;off] a5 = (dst,a6) /\
  compile_store_memory cenv src dst elem elem a6 = ((),a7) /\
  emit_op ADD [len; Lit 1w] a7 = (next,a8) /\
  emit_void MSTORE [bop;next] a8 = ((),b) /\ fn_has_code a b func ==>
  ci_mono a a3 /\ ci_mono a3 a6 /\
  fn_has_code a a3 func /\ fn_has_code a3 a6 func /\ fn_has_code a6 b func
Proof
  strip_tac >>
  `ci_mono a a1 /\ ci_mono a1 a2 /\ ci_mono a2 a3` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono a3 a4 /\ ci_mono a4 a5 /\ ci_mono a5 a6` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono a6 a7 /\ ci_mono a7 a8 /\ ci_mono a8 b` by
    metis_tac[ci_mono_compile_store_memory, typed_copy_emit_op_mono,
      ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono a a3 /\ ci_mono a3 a6 /\ ci_mono a6 b` by
    metis_tac[ci_mono_trans] >>
  `cs_extends a a3 /\ cs_extends a3 a6 /\ cs_extends a6 b` by fs[ci_mono_def] >>
  simp[] >>
  `fn_has_code a a3 func /\ fn_has_code a3 b func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  metis_tac[fn_has_code_split]
QED

Theorem memory_append_prepared_operand_frame[local]:
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_labels = s.vs_labels /\ tf.t_mem = tn.t_mem /\
  (if is_word_type elem then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs s = SOME sw /\
     ptr_covers G tn xs s (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= s.vs_alloca_next /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) ==>
  (if is_word_type elem then
     eval_operand src t = SOME (typed_val_to_w256 tv v) /\ op_taint tf src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs t = SOME sw /\
     ptr_covers Gf tf xs t (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= t.vs_alloca_next /\
     !mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tv v (w2n sw) mem)
Proof
  strip_tac >> Cases_on `is_word_type elem` >> fs[]
  >- (Cases_on `src` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  irule ptr_covers_lookup_frame >> metis_tac[]
QED

Theorem append_memory_counted_suffix_mods:
  compile_dynarray_append cenv (Var p) src 32 (type_memory_size tv)
    elem elem cap F LocMemory a = ((),b) /\
  fn_has_code a b func /\
  not_fresh_at a p /\ (!x. src = Var x ==> not_fresh_at a x) /\
  lookup_var p s = SOME bp /\
  ptr_covers G tn p s (32+cap*type_memory_size tv) /\
  w2n bp+32+cap*type_memory_size tv <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\
  evaluate_type tenv elem = SOME tv /\ type_memory_bytes cenv elem = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
  value_has_type tv v /\ val_wf tv v /\ (!j. j < LENGTH vs ==> val_wf tv (EL j vs)) /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  (if is_word_type elem then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs s = SOME sw /\
     ptr_covers G tn xs s (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= s.vs_alloca_next /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  if LENGTH vs < cap then
    ?t Gf tf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
      (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
        val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV (vs ++ [v]))) (w2n bp) mem) /\
      typed_copy_state_frame a (w2n bp) (32+cap*type_memory_size tv) s t /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n bp <= i /\ i < w2n bp+32+cap*type_memory_size tv) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts
  else
    ?r Gf tf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort r,Gf,tf))
Proof
  strip_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> mem_word_at (w2n bp) m = n2w (LENGTH vs)` by
    (rpt strip_tac >>
     qpat_assum `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> _`
       (qspec_then `m` (mp_tac o PURE_ONCE_REWRITE_RULE [val_in_memory_def])) >> simp[]) >>
  drule robust_mem_word_at_clean >> strip_tac >>
  `mem_word_at (w2n bp) s.vs_memory = n2w (LENGTH vs)` by
    (first_assum irule >> simp[mem_agree_outside_def]) >>
  `mload (w2n bp) s = n2w (LENGTH vs)` by
    fs[mem_word_at_eq_mload] >>
  `ptr_covers G tn p s 32` by (irule ptr_covers_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `w2n bp+32 <= s.vs_alloca_next` by decide_tac >>
  qpat_x_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [memory_append_suffix_parts]) >>
  rename1 `emit_op MLOAD [Var p] a = (lop,a1)` >>
  rename1 `emit_void ASSERT [_] _ = ((),a3)` >>
  rename1 `compile_store_memory _ _ dst _ _ a6 = _` >>
  drule_all memory_append_suffix_cuts >> strip_tac >>
  drule_all append_memory_guard_path_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  Cases_on `LENGTH vs < cap` >> simp[] >> strip_tac
  >- suspend "guarded" >> metis_tac[]
QED

Resume append_memory_counted_suffix_mods[guarded]:
  rename1 `lop = Var lenvar` >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sg,Gg,tg)` >>
  qpat_x_assum `lop = Var lenvar` SUBST_ALL_TAC >>
  `sg.vs_alloca_next = s.vs_alloca_next /\ sg.vs_labels = s.vs_labels` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `lookup_var p sg = SOME bp /\ not_fresh_at a3 p` by simp[] >>
  `ptr_covers Gg tg p sg (32+cap*type_memory_size tv)` by
    (irule ptr_covers_lookup_frame >> metis_tac[]) >>
  `w2n bp + (32+cap*type_memory_size tv) <= sg.vs_alloca_next /\
    sg.vs_alloca_next < dimword (:256)` by simp[] >>
  drule_all append_memory_address_path_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`xd`,`sd`,`Gd`,`td`] strip_assume_tac)) >>
  `ci_mono a a6` by metis_tac[ci_mono_trans] >>
  `!x. not_fresh_at a x ==> not_fresh_at a6 x /\ lookup_var x sd = lookup_var x s /\
    FLOOKUP Gd x = FLOOKUP G x /\ op_taint td (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> metis_tac[]) >>
  `td.t_mem = tn.t_mem /\ sd.vs_memory = s.vs_memory /\
    sd.vs_alloca_next = s.vs_alloca_next` by simp[] >>
  suspend "addressed"
QED

Resume append_memory_counted_suffix_mods[addressed]:
  qpat_x_assum `dst = Var xd` SUBST_ALL_TAC >>
  `!x. src = Var x ==> not_fresh_at a6 x` by metis_tac[] >>
  `not_fresh_at a6 p /\ not_fresh_at a6 lenvar /\
    lookup_var p sd = SOME bp /\ lookup_var lenvar sd = SOME (n2w (LENGTH vs)) /\
    op_taint td (Var lenvar) = {}` by simp[] >>
  `ptr_covers Gd td p sd (32+cap*type_memory_size tv)` by
    (irule ptr_covers_lookup_frame >> metis_tac[]) >>
  `w2n bp+32+cap*type_memory_size tv <= sd.vs_alloca_next /\
    lo <= sd.vs_alloca_next` by simp[] >>
  `w2n ((n2w (w2n bp+32+LENGTH vs*type_memory_size tv)):bytes32) =
    w2n bp+32+LENGTH vs*type_memory_size tv` by
    (`w2n bp+32+LENGTH vs*type_memory_size tv < dimword (:256)` by decide_tac >> simp[]) >>
  `(if is_word_type elem then
     eval_operand src sd = SOME (typed_val_to_w256 tv v) /\ op_taint td src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs sd = SOME sw /\
     ptr_covers Gd td xs sd (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= sd.vs_alloca_next /\
     !mem. mem_agree_outside td.t_mem sd.vs_memory mem ==> val_in_memory tv v (w2n sw) mem)` by
    (irule memory_append_prepared_operand_frame >> metis_tac[]) >>
  drule_all append_memory_payload_writes_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac)) >>
  qpat_x_assum `w2n (n2w _ : bytes32) = _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  suspend "written"
QED

Resume append_memory_counted_suffix_mods[written]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by
    metis_tac[gas_origin_ptr_path_trans] >>
  `typed_copy_state_frame a (w2n bp) (32+cap*type_memory_size tv) s t` by
    suspend "frame" >>
  `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
     val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV (vs ++ [v]))) (w2n bp) mem`
    by suspend "representation" >>
  `!i. ~(w2n bp <= i /\ i < w2n bp+32+cap*type_memory_size tv) ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)` by suspend "exterior" >>
  `!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> metis_tac[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> fs[] >> gen_tac >> strip_tac >>
  qpat_assum `!i. _ ==> (i IN tf.t_mem <=> _)` (qspec_then `i` mp_tac) >>
  simp[]
QED

Resume append_memory_counted_suffix_mods[frame]:
  `typed_copy_state_frame a 0 0 sg sd` by metis_tac[typed_copy_state_frame_mono] >>
  `typed_copy_state_frame a 0 0 s sd` by metis_tac[typed_copy_state_frame_trans] >>
  `typed_copy_state_frame a (w2n bp) (32+cap*type_memory_size tv) s sd` by
    (qpat_assum `sd.vs_memory = s.vs_memory` mp_tac >>
     qpat_assum `typed_copy_state_frame a 0 0 s sd` mp_tac >>
     simp_tac (srw_ss() ++ boolSimps.CONJ_ss) [typed_copy_state_frame_def] >>
     strip_tac >> disch_tac >> asm_rewrite_tac[]) >>
  `typed_copy_state_frame a (w2n bp) (32+cap*type_memory_size tv) sd t` by
    metis_tac[typed_copy_state_frame_mono] >>
  metis_tac[typed_copy_state_frame_trans]
QED

Resume append_memory_counted_suffix_mods[representation]:
  `!i. ~(w2n bp <= i /\ i < w2n bp+32) /\
       ~(w2n bp+32+LENGTH vs*type_memory_size tv <= i /\
         i < w2n bp+32+(LENGTH vs+1)*type_memory_size tv) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (qpat_assum `!i. _ ==> mem_bytes_at i 1 t.vs_memory = _ /\ _` mp_tac >>
     qpat_assum `sd.vs_memory = s.vs_memory` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `td.t_mem = tn.t_mem` (fn th => pure_rewrite_tac[th]) >>
     simp_tac (srw_ss()) [RIGHT_ADD_DISTRIB, ADD_ASSOC]) >>
  rpt strip_tac >> irule append_memory_robust_array_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`t.vs_memory`,`tf.t_mem`,`s.vs_memory`,`tn.t_mem`] >>
  asm_rewrite_tac[]
QED

Resume append_memory_counted_suffix_mods[exterior]:
  rpt strip_tac >>
  qpat_assum `!i. _ ==> mem_bytes_at i 1 t.vs_memory = _ /\ _` (qspec_then `i` mp_tac) >>
  qpat_assum `td.t_mem = tn.t_mem` (fn th => pure_rewrite_tac[th]) >>
  (impl_tac >- decide_tac) >> simp[]
QED

Finalise append_memory_counted_suffix_mods
