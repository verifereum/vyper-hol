Theory placeMemoryStoreEffect
Ancestors
  placeMemoryPrimitiveForward placeMemoryTypedPrimitive placeMemoryChildForward
  placeMemoryCopyEffect context memoryLocalRhsProps vyperTypeSystem
  venomState compileEnv memoryLayoutDefs memoryLayoutSource memoryLayoutRel
  memoryValueEncoding

Theorem compile_store_memory_nonword_effect:
  ~is_word_type dty /\ ~is_word_type sty /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw) u.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
  eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
  (!x. dp = Var x ==> not_fresh_at a x) /\
  (!x. sp = Var x ==> not_fresh_at a x) /\
  fn_has_code a b func /\ ~u.vs_halted /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  cenv.ce_target CapMcopy /\
  typed_memory_child_forward cenv tenv ctx func dty /\
  (dty <> sty /\ ~is_bytestring_type dty ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  compile_store_memory cenv sp dp dty sty a = ((),b) ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)
Proof
  strip_tac >> Cases_on `dty = sty`
  >- suspend "same" >>
  Cases_on `is_bytestring_type dty`
  >- suspend "bytes" >>
  Cases_on `tuple_memory_layout_eq dty sty`
  >- suspend "layout" >>
  `compile_store_memory_typed cenv dp dty sp sty a = ((),b)` by
    gvs[compile_store_memory_def] >>
  `w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw` by metis_tac[] >>
  irule typed_memory_child_forward_apply >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[SF SFY_ss]
QED

Resume compile_store_memory_nonword_effect[same]:
  gvs[] >>
  drule compile_store_memory_same_type_forward >>
  disch_then (qspec_then `v` mp_tac) >>
  disch_then (drule_at (Pat `eval_operand sp _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  simp[] >> disch_then (qspecl_then [`func`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[typed_copy_effect_def] >>
  conj_tac
  >- (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = u`
        (mp_tac o Q.AP_TERM `\z. z with <|vs_prev_bb := u.vs_prev_bb;
          vs_current_bb := u.vs_current_bb|>`) >> simp[]) >>
  qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = u`
    (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

(* Tuples with equal layouts are copied in bulk, as the same type is. *)
Resume compile_store_memory_nonword_effect[layout]:
  `compile_store_memory cenv sp dp dty dty a = ((),b)` by
    gvs[compile_store_memory_def] >>
  `memory_layout_key dty = memory_layout_key sty` by
    (Cases_on `dty` >> Cases_on `sty` >>
     gvs[tuple_memory_layout_eq_def, memory_layout_key_tuple]) >>
  `memory_layout_rel dtv stv` by metis_tac[memory_layout_key_evaluated] >>
  `val_in_memory dtv v (w2n sw) u.vs_memory` by
    (irule memory_value_rel_val_in_memory >> simp[] >>
     irule memory_layout_rel_value >> qexists_tac `stv` >> simp[] >>
     irule val_in_memory_memory_value_rel >> simp[]) >>
  drule compile_store_memory_same_type_forward >>
  disch_then (qspec_then `v` mp_tac) >>
  disch_then (drule_at (Pat `eval_operand sp _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  simp[] >> disch_then (qspecl_then [`func`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[typed_copy_effect_def] >>
  conj_tac
  >- (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = u`
        (mp_tac o Q.AP_TERM `\z. z with <|vs_prev_bb := u.vs_prev_bb;
          vs_current_bb := u.vs_current_bb|>`) >> simp[]) >>
  qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = u`
    (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Resume compile_store_memory_nonword_effect[bytes]:
  `is_bytestring_type sty` by
    (gvs[type_widens_to_def] >>
     metis_tac[memoryLocalRhsPropsTheory.arg_type_fits_bytestring_source]) >>
  `compile_store_memory_typed cenv dp dty sp sty a = ((),b)` by
    (simp[Once compile_store_memory_typed_def] >>
     gvs[compile_store_memory_def]) >>
  drule_all typed_memory_bytestring_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[typed_copy_effect_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED
Finalise compile_store_memory_nonword_effect
