Theory typedCopyFieldsSemanticCounted
Ancestors
  typedCopyFieldsCounted placeMemoryFieldsForward placeMemoryCopyEffect
  fragGasMode fragGasPathMem instMemFrontier context compileEnv venomState
  valueEncoding words arithmetic exprLoweringProps fragExec freshWrites venomMemDefs

Theorem typed_fields_offset_natural[local]:
  w2n (w:bytes32) + off < dimword (:256) ==>
  w2n (w + n2w off) = w2n w + off
Proof
  strip_tac >> `off < dimword (:256)` by decide_tac >>
  simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, LESS_MOD]
QED

Theorem typed_fields_address_effect[local]:
  gas_path_mem ctx func s 0 (OK u) /\
  (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  typed_copy_effect ctx func sa sb s u d n
Proof
  strip_tac >> simp[typed_copy_effect_def] >>
  conj_tac >- metis_tac[gas_marked_path_from_mem] >>
  qpat_x_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
  simp[venom_state_component_equality] >> metis_tac[]
QED

Theorem typed_fields_head_path_mem[local]:
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw + soff) s.vs_memory /\
  (w2n sw + soff + type_memory_size stv <= w2n dw + doff \/
   w2n dw + doff + type_memory_size dtv <= w2n sw + soff) /\
  w2n sw + soff + type_memory_size stv < dimword (:256) /\
  w2n dw + doff + type_memory_size dtv + 64 < dimword (:256) /\
  w2n sw + soff + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + doff + type_memory_size dtv <= s.vs_alloca_next /\
  (do dp <- compile_with_byte_offset dst doff;
      sp <- compile_with_byte_offset src soff;
      compile_store_memory_typed cenv dp dt sp st od) sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!st dtv stv v dp sp a b u dw sw.
    type_widens_to tenv st dt /\
    evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
    type_memory_bytes cenv dt = type_memory_size dtv /\
    type_memory_bytes cenv st = type_memory_size stv /\
    value_has_type dtv v /\ val_wf dtv v /\
    value_has_type stv v /\ val_wf stv v /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
    compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
    alloca_history func u /\ alloca_inv u /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv) /\
        gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t) ==>
  ?z. val_in_memory dtv v (w2n dw + doff) z.vs_memory /\
      typed_copy_effect ctx func sa sb s z (w2n dw + doff) (type_memory_size dtv) /\
      gas_path_mem ctx func s 0 (OK z) /\ alloca_history func z
Proof
  strip_tac >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_with_byte_offset dst doff sa = (dp,a)` >>
  rename1 `compile_with_byte_offset src soff a = (sp,b)` >>
  `cs_extends sa a /\ cs_extends a b /\ cs_extends b sb` by
    (conj_tac >- metis_tac[compile_with_byte_offset_extends] >>
     conj_tac >- metis_tac[compile_with_byte_offset_extends] >>
     mp_tac (cj 1 ci_mono_typed_memory_family) >>
     simp[ci_mono_def] >> metis_tac[pairTheory.SND]) >>
  `cs_extends sa b` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa b func /\ fn_has_code b sb func` by metis_tac[fn_has_code_split] >>
  `(do dp <- compile_with_byte_offset dst doff;
       sp <- compile_with_byte_offset src soff; comp_return (dp,sp) od) sa = ((dp,sp),b)` by
    simp[comp_bind_def, comp_return_def] >>
  drule_all typed_memory_fields_addresses_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `eval_operand dp u = SOME (dw + n2w doff)` >>
  drule_all typed_memory_fields_addresses_fresh >> strip_tac >>
  `w2n (dw + n2w doff) = w2n dw + doff /\
   w2n (sw + n2w soff) = w2n sw + soff` by
    (conj_tac >> irule typed_fields_offset_natural >> decide_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\ alloca_inv u` by
    (qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     qpat_assum `alloca_inv s` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[venom_state_component_equality, alloca_inv_def,
          allocas_non_overlapping_def, alloca_next_valid_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `?z. val_in_memory dtv v (w2n dw + doff) z.vs_memory /\
       typed_copy_effect ctx func b sb u z (w2n dw + doff) (type_memory_size dtv) /\
       gas_path_mem ctx func u 0 (OK z) /\ alloca_history func z` by
    (qpat_assum `w2n (dw + n2w doff) = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     first_x_assum irule >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> decide_tac) >>
  `typed_copy_effect ctx func sa b s u (w2n dw + doff) (type_memory_size dtv)` by
    (irule typed_fields_address_effect >> simp[]) >>
  qexists `z` >> fs[] >> (conj_tac
  >- (irule typed_copy_effect_then >> qexistsl [`b`, `b`, `u`] >>
      simp[] >> metis_tac[not_fresh_at_mono])) >>
  `gas_path_mem ctx func s (0 + 0) (OK z)` by
    (irule gas_path_mem_then >> qexists `u` >> simp[]) >> gvs[]
QED

Theorem typed_fields_source_tail_frame[local]:
  tuple_in_memory vs tvs p s.vs_memory /\ tuple_val_wf vs tvs /\
  (p + type_memory_size_list tvs <= d \/ d + n <= p) /\
  typed_copy_effect ctx func sa sb s t d n ==>
  tuple_in_memory vs tvs p t.vs_memory
Proof
  strip_tac >> irule typed_memory_tuple_outside_write >> simp[] >>
  qexistsl [`d`, `s.vs_memory`, `n`] >> simp[] >>
  rpt strip_tac >> irule typed_copy_effect_bytes >>
  goal_assum (drule_at Any) >> simp[]
QED
