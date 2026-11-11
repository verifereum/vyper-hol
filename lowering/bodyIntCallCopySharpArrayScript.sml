Theory bodyIntCallCopySharpArray
Ancestors
  bodyIntCallCopySharpChild placeMemoryArrayForward placeMemoryArrayControl
  placeMemoryCopyEffect venomState exprLoweringProps freshWrites

Theorem typed_memory_array_element_forward_sharp:
  (do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
      doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),b4) /\
  compile_store_memory_typed cenv dp dt sp st b4 = ((),b5) /\
  typed_memory_child_forward_sharp cenv tenv ctx func dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw + i * type_memory_size stv) s.vs_memory /\
  (w2n sw + i * type_memory_size stv + type_memory_size stv <=
     w2n dw + i * type_memory_size dtv \/
   w2n dw + i * type_memory_size dtv + type_memory_size dtv <=
     w2n sw + i * type_memory_size stv) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv < dimword (:256) /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv < dimword (:256) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\
  fn_has_code sa b4 func /\ fn_has_code b4 b5 func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw + i * type_memory_size dtv) t.vs_memory /\
      typed_copy_effect ctx func sa b5 s t
        (w2n dw + i * type_memory_size dtv) (type_memory_size dtv)
Proof
  strip_tac >>
  drule_all typed_memory_array_addresses_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule typed_memory_array_addresses_fresh >> strip_tac >>
  `u.vs_memory = s.vs_memory` by
    (qpat_x_assum `(_ with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `w2n (sw + n2w (i * type_memory_size stv)) = w2n sw + i * type_memory_size stv /\
   w2n (dw + n2w (i * type_memory_size dtv)) = w2n dw + i * type_memory_size dtv` by
    (`w2n sw + i * type_memory_size stv < dimword (:256) /\
      w2n dw + i * type_memory_size dtv < dimword (:256) /\
      i * type_memory_size stv < dimword (:256) /\
      i * type_memory_size dtv < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `?t. val_in_memory dtv v (w2n (dw + n2w (i * type_memory_size dtv))) t.vs_memory /\
       typed_copy_effect ctx func b4 b5 u t
         (w2n (dw + n2w (i * type_memory_size dtv))) (type_memory_size dtv)` by
    (irule typed_memory_child_forward_sharp_apply >> simp[] >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> gvs[] >> decide_tac) >>
  `typed_copy_effect ctx func sa b4 s u
      (w2n dw + i * type_memory_size dtv) (type_memory_size dtv)` by
    (simp[typed_copy_effect_def] >>
     qpat_x_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  (qexists_tac `t` >> conj_tac
   >- (qpat_x_assum `val_in_memory dtv v _ t.vs_memory` mp_tac >> simp[]) >>
   irule placeMemoryCopyEffectTheory.typed_copy_effect_then >>
   qexistsl_tac [`b4`, `b4`, `u`] >> gvs[] >>
   metis_tac[not_fresh_at_mono])
QED
