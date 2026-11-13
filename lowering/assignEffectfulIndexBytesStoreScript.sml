Theory assignEffectfulIndexBytesStore
Ancestors
  assignEffectfulIndexOwnedStore aggregateStoreSizePath valueCopyBytes
  aggregateEvaluatedLayout placeMemoryCopyEffect context vyperTypeSystem
  eventTopicValueProps

Theorem bytes_store_size_effect[local]:
  is_bytestring_type dty /\ is_bytestring_type sty /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ val_wf stv v /\ value_has_type dtv v /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size stv + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  compile_store_memory cenv src dst dty sty sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv)
Proof
  strip_tac >>
  `~is_word_type sty /\ ~is_word_type dty` by
    metis_tac[bytestring_type_not_word] >>
  `compile_store_memory cenv src dst sty sty sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  drule compile_store_memory_same_type_size_forward >>
  disch_then (qspec_then `v` mp_tac) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  simp[] >> disch_then (qspecl_then [`func`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  `type_memory_size stv <= type_memory_size dtv` by
    (Cases_on `sty = dty` >- gvs[] >>
     irule (cj 1 arg_fits_evaluated_memory_size) >>
     qexistsl_tac [`sty`, `tenv`, `dty`] >> fs[type_widens_to_def]) >>
  qexists_tac `t` >> conj_tac
  >- (irule bytestring_val_in_memory_transfer >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[SF SFY_ss]) >>
  simp[typed_copy_effect_def] >> conj_tac
  >- (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. z with <|vs_prev_bb := s.vs_prev_bb;
         vs_current_bb := s.vs_current_bb|>`) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
