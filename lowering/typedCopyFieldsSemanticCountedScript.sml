Theory typedCopyFieldsSemanticCounted
Ancestors
  typedCopyFieldsCounted placeMemoryFieldsForward placeMemoryCopyEffect placeMemoryCopyFrames
  fragGasMode fragGasPathMem instMemFrontier context compileEnv venomState
  valueEncoding words arithmetic exprLoweringProps fragExec freshWrites venomMemDefs
  placeMemoryTypedBase list

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

Theorem typed_fields_effect_state[local]:
  typed_copy_effect ctx func sa sb s t d n /\ alloca_inv s /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
  alloca_inv t /\ t.vs_alloca_next = s.vs_alloca_next /\
  eval_operand dst t = SOME dw /\ eval_operand src t = SOME sw
Proof
  strip_tac >> drule typed_copy_effect_record >>
  simp[venom_state_component_equality] >> strip_tac >>
  `alloca_inv t /\ t.vs_alloca_next = s.vs_alloca_next` by
    (fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     metis_tac[]) >>
  simp[] >> conj_tac
  >- (Cases_on `dst` >> fs[eval_operand_def] >>
      metis_tac[typed_copy_effect_lookup]) >>
  Cases_on `src` >> fs[eval_operand_def] >> metis_tac[typed_copy_effect_lookup]
QED

Theorem typed_fields_head_tail_finish[local]:
  val_wf dtv v /\ val_in_memory dtv v d z.vs_memory /\
  tuple_in_memory vs dtvs (d + type_memory_size dtv) t.vs_memory /\
  typed_copy_effect ctx func sa mid s z d (type_memory_size dtv) /\
  typed_copy_effect ctx func mid sb z t (d + type_memory_size dtv)
    (type_memory_size_list dtvs) /\
  sa.cs_next_var <= mid.cs_next_var /\
  gas_path_mem ctx func s 0 (OK z) /\ gas_path_mem ctx func z 0 (OK t) ==>
  tuple_in_memory (v::vs) (dtv::dtvs) d t.vs_memory /\
  typed_copy_effect ctx func sa sb s t d
    (type_memory_size dtv + type_memory_size_list dtvs) /\
  gas_path_mem ctx func s 0 (OK t)
Proof
  strip_tac >>
  `val_in_memory dtv v d t.vs_memory` by
    (irule val_in_memory_outside_write >> simp[] >>
     qexistsl [`d + type_memory_size dtv`, `z.vs_memory`, `type_memory_size_list dtvs`] >>
     simp[] >> rpt strip_tac >> irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >> simp[]) >>
  `typed_copy_effect ctx func sa mid s z d
     (type_memory_size dtv + type_memory_size_list dtvs)` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  `typed_copy_effect ctx func mid sb z t d
     (type_memory_size dtv + type_memory_size_list dtvs)` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  simp[valueEncodingTheory.val_in_memory_def] >> conj_tac
  >- (irule typed_copy_effect_then >> qexistsl [`mid`, `mid`, `z`] >>
      simp[] >> metis_tac[not_fresh_at_mono]) >>
  `gas_path_mem ctx func s (0 + 0) (OK t)` by
    (irule gas_path_mem_then >> qexists `z` >> simp[]) >> fs[]
QED

Theorem typed_memory_fields_forward_counted:
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
  w2n dw + doff + type_memory_size_list dtvs + 64 < dimword (:256) /\
  compile_typed_copy_fields cenv dst src dts sts doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  w2n sw + soff + type_memory_size_list stvs <= s.vs_alloca_next /\
  w2n dw + doff + type_memory_size_list dtvs <= s.vs_alloca_next /\
  (!dt. MEM dt dts ==>
    !st dtv stv v dp sp a b u dw sw.
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
  ?t. tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw + doff) (type_memory_size_list dtvs) /\
      gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t
Proof
  Induct
  >- (Cases_on `sts` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
      simp[vyperTypingTheory.value_has_type_def, valueEncodingTheory.val_wf_def,
           valueEncodingTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def,
           cj 2 compile_store_memory_typed_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists `s` >> simp[gas_path_mem_rules] >>
      irule typed_copy_effect_identity >> simp[]) >>
  pop_assum (mk_asm "ih") >> Cases_on `sts` >> Cases_on `dtvs` >>
  Cases_on `stvs` >> Cases_on `vs` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingTheory.val_wf_def,
       valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >> gvs[] >> rename1 `compile_typed_copy_fields cenv dst src (dt::dts) (st::sts) doff soff sa = ((),sb)` >>
  rename1 `tuple_in_memory (v::vs) (stv::stvs) _ s.vs_memory` >> rename1 `evaluate_type tenv dt = SOME dtv` >>
  qmatch_goalsub_rename_tac `tuple_in_memory (v::vs) (dtv::dtvs)` >>
  drule typed_memory_fields_cons_compile >> strip_tac >>
  `cs_extends sa c` by metis_tac[cs_extends_trans] >>
  `sa.cs_next_var <= c.cs_next_var` by
    (qspecl_then [`dst`, `doff`, `sa`] mp_tac ci_mono_compile_with_byte_offset >>
     qspecl_then [`src`, `soff`, `a`] mp_tac ci_mono_compile_with_byte_offset >>
     qspecl_then [`cenv`, `dp`, `dt`] mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`sp`, `st`, `b`] mp_tac) >>
     simp[ci_mono_def] >> decide_tac) >>
  `fn_has_code sa c func /\ fn_has_code c sb func` by metis_tac[fn_has_code_split] >>
  `?z. val_in_memory dtv v (w2n dw + doff) z.vs_memory /\
       typed_copy_effect ctx func sa c s z (w2n dw + doff) (type_memory_size dtv) /\
       gas_path_mem ctx func s 0 (OK z) /\ alloca_history func z` by
    (irule typed_fields_head_path_mem >> simp[comp_bind_def, comp_ignore_bind_def] >>
     rpt (goal_assum (drule_at Any)) >> gvs[valueEncodingTheory.val_in_memory_def] >>
     qexists `soff` >> simp[] >> qpat_x_assum `ih :- _` kall_tac >>
     qpat_x_assum `!dt'. _` (qspec_then `dt` mp_tac) >> simp[]) >>
  `tuple_in_memory vs stvs (w2n sw + soff + type_memory_size stv) z.vs_memory` by
    (irule typed_fields_source_tail_frame >> rpt (goal_assum (drule_at Any)) >>
     fs[valueEncodingTheory.val_in_memory_def] >> decide_tac) >>
  `alloca_inv z /\ z.vs_alloca_next = s.vs_alloca_next /\
   eval_operand dst z = SOME dw /\ eval_operand src z = SOME sw` by
    (irule typed_fields_effect_state >> rpt (goal_assum (drule_at Any))) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  asm_x "ih" (qspecl_then [`sts`, `dtvs`, `stvs`, `vs`,
    `doff + type_memory_size dtv`, `soff + type_memory_size stv`, `c`, `sb`, `z`] mp_tac) >>
  (impl_tac >- (asm_simp_tac std_ss [ADD_ASSOC] >> reverse (rpt conj_tac)
    >- (qx_gen_tac `dt'` >> strip_tac >>
        qpat_x_assum `!dt'. _` (qspec_then `dt'` mp_tac) >>
        asm_simp_tac std_ss [ADD_COMM, ADD_ASSOC]) >>
    qpat_x_assum `!dt'. _` kall_tac >>
    full_simp_tac std_ss [AC ADD_ASSOC ADD_COMM] >>
    fs[] >> metis_tac[not_fresh_at_mono])) >>
  strip_tac >> qexists `t` >> simp[] >> irule typed_fields_head_tail_finish >>
  full_simp_tac std_ss [AC ADD_ASSOC ADD_COMM] >> qexistsl [`c`, `z`] >>
  asm_simp_tac std_ss []
QED

Theorem typed_memory_struct_forward_counted:
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
  w2n dw + doff + type_memory_size_list tvs + 64 < dimword (:256) /\
  compile_struct_typed_copy cenv dst src fields fields doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  w2n sw + soff + type_memory_size_list tvs <= s.vs_alloca_next /\
  w2n dw + doff + type_memory_size_list tvs <= s.vs_alloca_next /\
  (!dt. MEM dt (MAP (FST o SND) fields) ==>
    !st dtv stv v dp sp a b u dw sw.
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
  ?t. fields_in_memory vals (ZIP (MAP FST fields,tvs))
        (w2n dw + doff) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw + doff) (type_memory_size_list tvs) /\
      gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t
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
  irule typed_memory_fields_forward_counted >> simp[] >>
  goal_assum $ drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`) >>
  qexistsl_tac [`tvs`, `sw`, `tenv`] >>
  simp[LIST_REL_refl, EVERY_MEM] >> gvs[]
QED
