(* The final store runs at the selected input, after any scratch copy. *)
Theory bodyAssignNameCopyStoreEffectMods
Ancestors
  bodyLocalBytesCopyPathMods bodyFullAssignLocalCopyFrame bodyDeclMemoryCore
  bodyFullPathHistory placeMemoryCopyEffect reasonCopySourcePtr valueEncodingTyping
  exprSimProps valueCopyBytes typedMemoryCopy words vyperTyping context

Theorem bytes_store_extent[local]:
  is_bytestring_type sty /\ evaluate_type tenv sty = SOME rt /\
  value_has_type rt v ==>
  ?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
         (?str. v = StringV str /\ len = LENGTH str)) /\
    val_store_size rt v = 32 + 32 * word_size len
Proof
  strip_tac >> drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def,val_store_size_def]
QED

Theorem flat_copy_store_frame[local]:
  typed_copy_effect ctx func sc sb z t dst n ==>
  typed_copy_state_frame sc dst n z t /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[typed_copy_effect_def,typed_copy_state_frame_def,typed_copy_frame_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem assign_name_copy_store_effect_mods:
  compile_store_memory cenv (Var ys) (Var p) ty sty sc = ((),sb) /\
  ~is_word_type ty /\ (sty = ty \/ is_bytestring_type ty) /\
  type_widens_to tenv sty ty /\
  evaluate_type tenv sty = SOME rt /\ evaluate_type tenv ty = SOME tv /\
  type_memory_bytes cenv ty = type_memory_size tv /\ 0 < type_memory_size tv /\
  value_has_type rt v /\ value_has_type tv v /\
  (!m. mem_agree_outside tz.t_mem z.vs_memory m ==> val_in_memory rt v (w2n sw) m) /\
  not_fresh_at sc ys /\ not_fresh_at sc p /\
  lookup_var ys z = SOME sw /\ lookup_var p z = SOME dw /\
  ptr_covers Gz tz ys z (type_memory_size rt) /\ ptr_covers Gz tz p z cap /\
  type_memory_size tv <= cap /\
  w2n sw + val_store_size rt v <= z.vs_alloca_next /\
  w2n dw + cap <= z.vs_alloca_next /\ z.vs_alloca_next < dimword (:256) /\
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  alloca_history func z /\ alloca_inv z /\ fn_inst_ids_distinct func /\
  fn_has_code sc sb func /\ ~z.vs_halted /\
  z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?bytes t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK t,Gf,tf)) /\
    bytes = val_store_size tv v /\ bytes <= type_memory_size tv /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory tv v (w2n dw) m) /\
    typed_copy_state_frame sc (w2n dw) bytes z t /\
    (!x. not_fresh_at sc x ==>
         lookup_var x t = lookup_var x z /\ FLOOKUP Gf x = FLOOKUP Gz x /\
         op_taint tf (Var x) = op_taint tz (Var x)) /\
    tf.t_stor = tz.t_stor /\ tf.t_trans = tz.t_trans /\ tf.t_imm = tz.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + bytes) ==> (i IN tf.t_mem <=> i IN tz.t_mem)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_bytestring_type ty`
  >- suspend "bytes" >>
  suspend "flat"
QED

Resume assign_name_copy_store_effect_mods[bytes]:
  `is_bytestring_type sty` by (drule_all typed_copy_bytestring_source >> simp[]) >>
  `val_wf rt v /\ val_wf tv v` by simp[value_has_type_val_wf] >>
  `val_store_size rt v = val_store_size tv v` by
    (irule bytestring_val_store_size_eq >> simp[] >>
     qexistsl_tac [`sty`,`ty`,`tenv`] >> simp[]) >>
  `val_store_size rt v <= type_memory_size rt /\ val_store_size rt v <= type_memory_size tv` by
    (qpat_assum `val_wf rt v` (mp_then Any assume_tac val_store_size_le) >>
     qpat_assum `val_wf tv v` (mp_then Any assume_tac val_store_size_le) >> fs[]) >>
  qpat_assum `evaluate_type tenv sty = SOME rt` (mp_then Any mp_tac bytes_store_extent) >>
  disch_then (qspec_then `v` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `len` (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `bytes = val_store_size rt v` >>
  `ptr_covers Gz tz ys z bytes /\ ptr_covers Gz tz p z bytes` by
    (conj_tac >- (irule ptr_covers_mono >> qexists_tac `type_memory_size rt` >> simp[]) >>
     irule ptr_covers_mono >> qexists_tac `cap` >> simp[] >> decide_tac) >>
  `w2n sw + bytes <= z.vs_alloca_next /\ w2n dw + bytes <= z.vs_alloca_next /\
   bytes < dimword (:256)` by decide_tac >>
  drule_all local_bytes_copy_path_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `ARB` assume_tac) >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  qexistsl_tac [`bytes`,`t`,`Gf`,`tf`] >> simp[]
QED

Resume assign_name_copy_store_effect_mods[flat]:
  `sty = ty` by fs[] >> qpat_x_assum `sty = ty` SUBST_ALL_TAC >>
  `rt = tv` by fs[] >> qpat_x_assum `rt = tv` SUBST_ALL_TAC >>
  `val_store_size tv v = type_memory_size tv` by
    (drule_all val_store_size_non_bytestring >> simp[]) >>
  `compile_copy_memory (Var p) (Var ys) (type_memory_size tv) sc = ((),sb)` by
    fs[compile_store_memory_def] >>
  `ptr_covers Gz tz p z (type_memory_size tv)` by
    (irule ptr_covers_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `val_wf tv v /\ val_footprint tv v <= type_memory_size tv` by
    simp[value_has_type_val_wf,val_footprint_le] >>
  `w2n sw + type_memory_size tv <= z.vs_alloca_next /\
   w2n dw + type_memory_size tv <= z.vs_alloca_next /\
   w2n sw + type_memory_size tv < dimword (:256) /\
   w2n dw + type_memory_size tv < dimword (:256)` by decide_tac >>
  `type_memory_size tv = type_memory_size tv` by REFL_TAC >>
  drule_all bodyFullAssignLocalCopyFrameTheory.body_assign_local_memory_flat_copy_effect >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_then strip_assume_tac flat_copy_store_frame >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `ARB` assume_tac) >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  qexistsl_tac [`type_memory_size tv`,`t`,`Gf`,`tf`] >> simp[]
QED

Finalise assign_name_copy_store_effect_mods
