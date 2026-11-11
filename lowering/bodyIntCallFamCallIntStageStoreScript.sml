(* Single-endpoint effect interface for argument staging stores. *)
Theory bodyIntCallFamCallIntStageStore
Ancestors
  bodyIntCallAggregateStoreFrame bodyIntCallWidenedChildStore
  memoryLocalRhsProps

Theorem intcall_stage_store_effect:
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  value_has_type dtv v /\ value_has_type stv v /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  (if is_word_type sty then sw = typed_val_to_w256 stv v
   else val_in_memory stv v (w2n sw) s.vs_memory) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    regions_disjoint b sz (w2n dw) (type_memory_size dtv)) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n dw) (type_memory_size dtv)) /\
  (~(dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) ==>
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    (!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes ce ty = type_memory_size tv) /\
    type_widens_to tenv sty dty /\ val_wf dtv v /\ val_wf stv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256)) ==>
  ?u. val_in_memory dtv v (w2n dw) u.vs_memory /\
    typed_copy_effect ctx func sa sb s u (w2n dw) (type_memory_size dtv) /\
    stmt_state_rel ctx func ce cx es u
Proof
  strip_tac >>
  Cases_on `dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty`
  >- (mp_tac (Q.INST
        [`P` |-> `\b n. regions_disjoint b n (w2n dw) (type_memory_size dtv)`,
         `reserved` |-> `\op:operand. F`]
        (SPEC_ALL protected_compatible_store_state_landing)) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >> qexists `u` >>
      simp[placeMemoryCopyEffectTheory.typed_copy_effect_def,
           compileEnvTheory.regions_disjoint_def]) >>
  qpat_x_assum `~_ ==> _` (mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
  `~is_word_type dty` by
    metis_tac[compileEnvTheory.type_widens_to_word] >>
  `~is_bytestring_type dty` by
    metis_tac[vyperTypeSystemTheory.type_widens_to_def,
              memoryLocalRhsPropsTheory.arg_type_fits_bytestring_source] >>
  `compile_store_memory_typed ce dst dty src sty sa = ((),sb)` by
    fs[contextTheory.compile_store_memory_def] >>
  `!name b sz. local_region ce es.scopes s name b sz ==>
    b + sz <= w2n dw \/ w2n dw + type_memory_size dtv <= b` by
    metis_tac[compileEnvTheory.regions_disjoint_def] >>
  `type_memory_bytes ce sty = type_memory_size stv` by metis_tac[] >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
    intcall_widened_child_store_frame >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `type_widens_to _ _ _`)) >>
  simp[] >> disch_then (qspec_then `v` mp_tac) >>
  (impl_tac >- (simp[] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- (qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _ \/ _`
      mp_tac >> simp[arithmeticTheory.ADD_COMM]) >>
    first_assum ACCEPT_TAC)) >> simp[]
QED
