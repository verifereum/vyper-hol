(* Execute the store at the reached default-keyword cursor.  The copy is
   independent of the module that supplied the readable source operand. *)
Theory bodyExtKeywordDefaultStoreMods
Ancestors
  bodyFullExtCallDefaultBytesStore bodyFullExtCallDefaultCopy
  exprSimProps valueCopyBytes bodyPtrDefs typedMemoryCopy
  fragGasOriginPtr venomState words finite_map

Theorem ext_kw_default_store_path_mods:
  compile_store_memory cenv src (Var q) dt dt sc = ((),sb) /\
  ~is_word_type dt /\ evaluate_type (get_tenv cx) dt = SOME ltv /\
  value_has_type ltv v /\ val_wf ltv v /\
  type_memory_bytes cenv dt = type_memory_size ltv /\
  type_memory_size ltv + 64 < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sc x) /\ not_fresh_at sc q /\
  eval_operand src z = SOME sw /\ lookup_var q z = SOME dw /\
  (!m. mem_agree_outside tn'.t_mem z.vs_memory m ==>
       val_in_memory ltv v (w2n sw) m) /\
  ptr_covers G' tn' q z (type_memory_size ltv) /\
  w2n dw + type_memory_size ltv <= z.vs_alloca_next /\
  z.vs_alloca_next < dimword (:256) /\
  (type_memory_size ltv <> 0 ==>
     (?x. src = Var x /\ ptr_covers G' tn' x z (type_memory_size ltv)) /\
     w2n sw + type_memory_size ltv <= z.vs_alloca_next) /\
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  fn_has_code sc sb func /\ ~z.vs_halted /\
  z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (z,G',tn') [] (OK t,Gf,tf)) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
         val_in_memory ltv v (w2n dw) m) /\
    lookup_var q t = SOME dw /\
    typed_copy_state_frame sc (w2n dw) (type_memory_size ltv) z t /\
    (!x. not_fresh_at sc x ==>
      lookup_var x t = lookup_var x z /\ FLOOKUP Gf x = FLOOKUP G' x /\
      op_taint tf (Var x) = op_taint tn' (Var x)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size ltv) ==>
       (i IN tf.t_mem <=> i IN tn'.t_mem)) /\
    tf.t_stor = tn'.t_stor /\ tf.t_trans = tn'.t_trans /\ tf.t_imm = tn'.t_imm /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_current_bb = z.vs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_bytestring_type dt`
  >- (`type_memory_size ltv <> 0` by
        (drule_all bytestring_type_value >> strip_tac >>
         gvs[valueEncodingTheory.type_memory_size_def, vfmConstantsTheory.word_size_def]) >>
      qpat_x_assum `type_memory_size ltv <> 0 ==> _` (strip_assume_tac o UNDISCH) >>
      gvs[eval_operand_def] >>
      `w2n sw + type_memory_size ltv <= z.vs_alloca_next /\
       w2n dw + type_memory_size ltv <= z.vs_alloca_next` by decide_tac >>
      drule_all extcall_default_bytes_store_capacity_joint >>
      disch_then (qspecl_then [`explicit`,`PG`]
        (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tf`
          (map_every assume_tac o CONJUNCTS))))) >>
      qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
      conj_tac
      >- (simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
          conj_tac >- gvs[venom_state_component_equality] >>
          rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      gvs[venom_state_component_equality]) >>
  `ptr_mem_ok cx dt v src G' tn' z` by
    (simp[ptr_mem_ok_def] >> strip_tac >>
     `type_memory_size ltv <> 0` by
       (drule exprSimPropsTheory.val_footprint_le >> decide_tac) >>
     qpat_x_assum `type_memory_size ltv <> 0 ==> _` (strip_assume_tac o UNDISCH) >>
     gvs[ptr_covers_def, eval_operand_def] >>
     drule exprSimPropsTheory.val_store_size_le >> decide_tac) >>
  `type_memory_size ltv <> 0 ==>
     (?x. src = Var x /\ ptr_covers G' tn' x z (type_memory_size ltv)) /\
     ptr_covers G' tn' q z (type_memory_size ltv) /\
     w2n sw + type_memory_size ltv <= z.vs_alloca_next /\
     w2n dw + type_memory_size ltv <= z.vs_alloca_next /\
     z.vs_alloca_next < dimword (:256)` by simp[] >>
  drule_all extcall_default_copy_capacity_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)
QED
