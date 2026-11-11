Theory bodyIntCallCopySharpFields
Ancestors
  bodyIntCallCopySharpChild placeMemoryFieldsForward placeMemoryCopyEffect
  placeMemoryTypedBase placeMemoryCopyFrames context compileEnv emitHelper
  emitHelperProps exprLoweringProps venomState venomExecSemantics freshWrites
  valueEncoding valueEncodingTyping vyperTyping fragExec list

Theorem typed_memory_fields_forward_sharp:
  !dts sts dtvs stvs vs doff soff sa sb s.
  LIST_REL (\dt tv. evaluate_type tenv dt = SOME tv /\
                       type_memory_bytes cenv dt = type_memory_size tv) dts dtvs /\
  LIST_REL (\st tv. evaluate_type tenv st = SOME tv /\
                       type_memory_bytes cenv st = type_memory_size tv) sts stvs /\
  LIST_REL (\dt st. type_widens_to tenv st dt) dts sts /\
  values_have_types dtvs vs /\ tuple_val_wf vs dtvs /\
  values_have_types stvs vs /\ tuple_val_wf vs stvs /\
  tuple_in_memory vs stvs (w2n sw + soff) s.vs_memory /\
  (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
   w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
  w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
  w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
  compile_typed_copy_fields cenv dst src dts sts doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dt. MEM dt dts ==> typed_memory_child_forward_sharp cenv tenv ctx func dt) ==>
  ?t. tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw + doff) (type_memory_size_list dtvs)
Proof
  Induct
  >- (Cases_on `sts` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
      simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def,
           valueEncodingDefsTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def,
           cj 2 compile_store_memory_typed_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      irule typed_copy_effect_identity >> simp[]) >>
  pop_assum (mk_asm "ih") >>
  Cases_on `sts` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def,
       valueEncodingTheory.type_memory_size_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> gnvs[] >>
  rename1 `compile_typed_copy_fields cenv dst src (dt::dts) (st::sts) doff soff sa = ((),sb)` >>
  rename1 `tuple_in_memory (v::vs) (stv::stvs) _ s.vs_memory` >>
  rename1 `evaluate_type tenv dt = SOME dtv` >>
  qmatch_goalsub_rename_tac `tuple_in_memory (v::vs) (dtv::dtvs)` >>
  drule typed_memory_fields_cons_compile >> strip_tac >>
  `cs_extends sa b /\ cs_extends sa c` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa b func /\ fn_has_code b c func /\ fn_has_code c sb func` by
    metis_tac[fn_has_code_split] >>
  `(do dp <- compile_with_byte_offset dst doff;
       sp <- compile_with_byte_offset src soff;
       return (dp,sp) od) sa = ((dp,sp),b)` by
    simp[comp_bind_def, comp_return_def] >>
  drule_all typed_memory_fields_addresses_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `eval_operand dp u = SOME (dw + n2w doff)` >>
  drule_all typed_memory_fields_addresses_fresh >> strip_tac >>
  `w2n (dw + n2w doff) = w2n dw + doff /\
   w2n (sw + n2w soff) = w2n sw + soff` by
    (`w2n dw + doff < dimword (:256) /\ w2n sw + soff < dimword (:256)` by decide_tac >>
     `doff < dimword (:256) /\ soff < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `val_in_memory stv v (w2n (sw + n2w soff)) u.vs_memory /\
   tuple_in_memory vs stvs (w2n sw + soff + type_memory_size stv) u.vs_memory` by
    gvs[valueEncodingDefsTheory.val_in_memory_def] >>
  `typed_memory_child_forward_sharp cenv tenv ctx func dt` by metis_tac[] >>
  `(w2n (sw + n2w soff) + type_memory_size stv <= w2n (dw + n2w doff) \/
    w2n (dw + n2w doff) + type_memory_size dtv <= w2n (sw + n2w soff)) /\
   w2n (sw + n2w soff) + type_memory_size stv < dimword (:256) /\
   w2n (dw + n2w doff) + type_memory_size dtv < dimword (:256)` by
    (simp[] >> decide_tac) >>
  `?z. val_in_memory dtv v (w2n (dw + n2w doff)) z.vs_memory /\
       typed_copy_effect ctx func b c u z (w2n (dw + n2w doff)) (type_memory_size dtv)` by
    (suspend "head") >>
  `sa.cs_next_var <= c.cs_next_var` by
    (qspec_then `cenv` (qspecl_then [`dp`,`dt`,`sp`,`st`,`b`] mp_tac)
       (cj 1 ci_mono_typed_memory_family) >>
     simp[ci_mono_def] >> decide_tac) >>
  `?t. tuple_in_memory vs dtvs (w2n dw + (doff + type_memory_size dtv)) t.vs_memory /\
       typed_copy_effect ctx func c sb z t (w2n dw + (doff + type_memory_size dtv))
         (type_memory_size_list dtvs)` by
    (suspend "tail") >>
  suspend "composition"
QED

Resume typed_memory_fields_forward_sharp[head]:
  markerLib.RESUME_TAC >>
  irule typed_memory_child_forward_sharp_apply >> simp[] >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> gvs[] >> decide_tac
QED

Resume typed_memory_fields_forward_sharp[tail]:
  markerLib.RESUME_TAC >>
  `tuple_in_memory vs stvs (w2n sw + soff + type_memory_size stv) z.vs_memory` by
    (irule typed_memory_tuple_outside_write >> simp[] >>
     qexistsl_tac [`w2n dw + doff`, `u.vs_memory`, `type_memory_size dtv`] >>
     gvs[] >> qx_gen_tac `addr` >> qx_gen_tac `len` >> strip_tac >>
     `mem_bytes_at addr len z.vs_memory = mem_bytes_at addr len u.vs_memory` suffices_by simp[] >>
     irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    metis_tac[typed_copy_effect_lookup, not_fresh_at_mono] >>
  `z.vs_labels = s.vs_labels` by
    (drule typed_copy_effect_record >>
     qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand dst z = SOME dw /\ eval_operand src z = SOME sw` by
    (conj_tac
     >- (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  (asm "ih" irule >> simp[] >>
   conj_tac >- metis_tac[not_fresh_at_mono] >>
   conj_tac >- metis_tac[not_fresh_at_mono] >>
   qexistsl_tac [`soff + type_memory_size stv`, `sts`, `stvs`] >>
   gvs[] >> decide_tac)
QED

Resume typed_memory_fields_forward_sharp[composition]:
  markerLib.RESUME_TAC >>
  `val_in_memory dtv v (w2n dw + doff) t.vs_memory` by
    (irule val_in_memory_outside_write >> simp[] >>
     qexistsl_tac [`w2n dw + (doff + type_memory_size dtv)`,
                   `z.vs_memory`, `type_memory_size_list dtvs`] >>
     gvs[] >> rpt strip_tac >> irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  (qexists_tac `t` >> conj_tac
   >- gvs[valueEncodingDefsTheory.val_in_memory_def] >>
   asm_x "ih" kall_tac >>
   `typed_copy_effect ctx func sa b s u (w2n dw + doff)
      (type_memory_size dtv + type_memory_size_list dtvs)` by
     (simp[typed_copy_effect_def] >>
      qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
   `typed_copy_effect ctx func b c u z (w2n dw + doff)
      (type_memory_size dtv + type_memory_size_list dtvs)` by
     (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
   `typed_copy_effect ctx func c sb z t (w2n dw + doff)
      (type_memory_size dtv + type_memory_size_list dtvs)` by
     (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> decide_tac) >>
   `typed_copy_effect ctx func sa c s z (w2n dw + doff)
      (type_memory_size dtv + type_memory_size_list dtvs)` by
     (irule placeMemoryCopyEffectTheory.typed_copy_effect_then >>
      qexistsl_tac [`b`, `b`, `u`] >> simp[] >> metis_tac[not_fresh_at_mono]) >>
   irule placeMemoryCopyEffectTheory.typed_copy_effect_then >>
   qexistsl_tac [`c`, `c`, `z`] >> gvs[] >> metis_tac[not_fresh_at_mono])
QED

Finalise typed_memory_fields_forward_sharp

Theorem typed_memory_struct_forward_sharp:
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) fields /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv /\
                        type_memory_bytes cenv ty = type_memory_size tv)
    (MAP (FST o SND) fields) tvs /\
  LENGTH tvs = LENGTH fields /\
  struct_has_type (ZIP (MAP FST fields,tvs)) vals /\
  fields_val_wf vals (ZIP (MAP FST fields,tvs)) /\
  fields_in_memory vals (ZIP (MAP FST fields,tvs)) (w2n sw + soff) s.vs_memory /\
  (w2n sw + soff + type_memory_size_list tvs <= w2n dw + doff \/
   w2n dw + doff + type_memory_size_list tvs <= w2n sw + soff) /\
  w2n sw + soff + type_memory_size_list tvs < dimword (:256) /\
  w2n dw + doff + type_memory_size_list tvs < dimword (:256) /\
  compile_struct_typed_copy cenv dst src fields fields doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dt. MEM dt (MAP (FST o SND) fields) ==>
        typed_memory_child_forward_sharp cenv tenv ctx func dt) ==>
  ?t. fields_in_memory vals (ZIP (MAP FST fields,tvs))
        (w2n dw + doff) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw + doff) (type_memory_size_list tvs)
Proof
  strip_tac >>
  `?vs. vals = ZIP (MAP FST fields,vs) /\ LENGTH vs = LENGTH (MAP FST fields) /\
        values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    (irule typed_memory_struct_values >> simp[]) >>
  gvs[] >>
  `compile_struct_typed_copy cenv dst src fields fields doff soff =
   compile_typed_copy_fields cenv dst src
      (MAP (FST o SND) fields) (MAP (FST o SND) fields) doff soff` by
    (irule typed_memory_struct_copy_fields >> simp[EVERY_MEM]) >>
  gvs[typed_memory_fields_tuple_zip] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule typed_memory_fields_forward_sharp >> simp[] >>
  goal_assum $ drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`) >>
  qexistsl_tac [`tvs`, `sw`, `tenv`] >>
  simp[LIST_REL_refl, EVERY_MEM] >> decide_tac
QED
