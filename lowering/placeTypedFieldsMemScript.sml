(* Memory-safe field addressing and representation reassembly. *)
Theory placeTypedFieldsMem
Ancestors
  placeTypedCopyPrimitiveMem placeMemoryFieldsForward placeMemoryCopyEffect
  placeMemoryCopyFrames placeMemoryTypedBase
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomExecSemantics fragGasPathMem valueEncodingProps
  list finite_map freshWrites fragExec

Theorem typed_fields_addresses_path_mem[local]:
  compile_with_byte_offset dst doff sa = (dp,mid) /\
  compile_with_byte_offset src soff mid = (sp,sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa mid func /\ fn_has_code mid sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand dp t = SOME (dw + n2w doff) /\
      eval_operand sp t = SOME (sw + n2w soff) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all compile_with_byte_offset_fresh >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at mid x` by
    metis_tac[not_fresh_at_mono] >>
  drule_all compile_with_byte_offset_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand src t = SOME sw` by
    (Cases_on `src` >> gvs[eval_operand_def, venom_state_component_equality] >> metis_tac[]) >>
  `?u. gas_path_mem ctx func t 0 (OK u) /\
       eval_operand sp u = SOME (sw + n2w soff) /\
       (u with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>) = t /\
       (!x. not_fresh_at mid x ==> lookup_var x u = lookup_var x t) /\
       ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule compile_with_byte_offset_path_mem >> rpt (goal_assum (drule_at Any))) >>
  qexists_tac `u` >>
  `eval_operand dp u = eval_operand dp t` by
    (Cases_on `dp` >> gvs[eval_operand_def, venom_state_component_equality] >> metis_tac[]) >>
  conj_tac >- metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[] >> conj_tac
  >- (gvs[venom_state_component_equality]) >>
  metis_tac[not_fresh_at_mono]
QED

Theorem typed_fields_cons_reassemble[local]:
  val_in_memory dtv v d z.vs_memory /\ val_wf dtv v /\
  tuple_in_memory vs dtvs (d + type_memory_size dtv) t.vs_memory /\
  typed_copy_effect ctx func sa sb z t (d + type_memory_size dtv)
    (type_memory_size_list dtvs) ==>
  tuple_in_memory (v::vs) (dtv::dtvs) d t.vs_memory
Proof
  strip_tac >> simp[valueEncodingTheory.val_in_memory_def] >>
  irule val_in_memory_outside_write >> simp[] >>
  qexistsl_tac [`d + type_memory_size dtv`, `z.vs_memory`,
                `type_memory_size_list dtvs`] >>
  simp[] >> rpt strip_tac >> irule typed_copy_effect_bytes >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem typed_fields_child_suffix_memory[local]:
  tuple_in_memory (v::vs) (stv::stvs) p u.vs_memory /\
  tuple_val_wf vs stvs /\
  (p + type_memory_size stv + type_memory_size_list stvs <= d \/
   d + type_memory_size dtv + tail <= p) /\
  typed_copy_effect ctx func sa sb u z d (type_memory_size dtv) ==>
  tuple_in_memory vs stvs (p + type_memory_size stv) z.vs_memory
Proof
  strip_tac >>
  `!a len. a + len <= d \/ d + type_memory_size dtv <= a ==>
     mem_bytes_at a len z.vs_memory = mem_bytes_at a len u.vs_memory` by
    (rpt strip_tac >> irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >> simp[]) >>
  irule typed_memory_tuple_outside_write >> simp[] >>
  qexistsl_tac [`d`, `u.vs_memory`, `type_memory_size dtv`] >>
  gvs[valueEncodingTheory.val_in_memory_def] >> gvs[]
QED

Theorem typed_fields_child_suffix_frame[local]:
  tuple_in_memory (v::vs) (stv::stvs) p u.vs_memory /\
  tuple_val_wf vs stvs /\
  (p + type_memory_size stv + type_memory_size_list stvs <= d \/
   d + type_memory_size dtv + tail <= p) /\
  typed_copy_effect ctx func sa sb u z d (type_memory_size dtv) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst u = SOME dw /\ eval_operand src u = SOME sw ==>
  tuple_in_memory vs stvs (p + type_memory_size stv) z.vs_memory /\
  eval_operand dst z = SOME dw /\ eval_operand src z = SOME sw /\
  z.vs_alloca_next = u.vs_alloca_next /\
  ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `tuple_in_memory vs stvs (p + type_memory_size stv) z.vs_memory` by
    (irule typed_fields_child_suffix_memory >> rpt (goal_assum (drule_at Any)) >>
     metis_tac[]) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  drule typed_copy_effect_record >> strip_tac >>
  `z.vs_labels = u.vs_labels /\ z.vs_alloca_next = u.vs_alloca_next` by
    gvs[venom_state_component_equality] >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u` by
    metis_tac[typed_copy_effect_lookup] >>
  `eval_operand dst z = SOME dw` by
    (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `eval_operand src z = SOME sw` by
    (Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >> simp[]
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
  conj_tac >- metis_tac[fragGasModeTheory.gas_marked_path_from_mem] >>
  gvs[venom_state_component_equality]
QED

Theorem typed_fields_addresses_normalized_mem[local]:
  compile_with_byte_offset dst doff sa = (dp,a) /\
  compile_with_byte_offset src soff a = (sp,b) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  w2n dw + doff < dimword (:256) /\ w2n sw + soff < dimword (:256) /\
  fn_has_code sa a func /\ fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
    eval_operand dp u = SOME (dw + n2w doff) /\
    eval_operand sp u = SOME (sw + n2w soff) /\
    w2n (dw + n2w doff) = w2n dw + doff /\
    w2n (sw + n2w soff) = w2n sw + soff /\
    sa.cs_next_var <= b.cs_next_var /\
    (!x. dp = Var x ==> not_fresh_at b x) /\
    (!x. sp = Var x ==> not_fresh_at b x) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  drule_all typed_fields_addresses_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `(do dp <- compile_with_byte_offset dst doff;
       sp <- compile_with_byte_offset src soff; return (dp,sp) od) sa = ((dp,sp),b)` by
    simp[comp_bind_def, comp_return_def] >>
  drule_all typed_memory_fields_addresses_fresh >> strip_tac >>
  `doff < dimword (:256) /\ soff < dimword (:256)` by decide_tac >>
  qexists_tac `t` >>
  simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  gvs[venom_state_component_equality]
QED

Theorem typed_fields_head_transition_mem[local]:
  evaluate_type tenv dt = SOME dtv /\ type_memory_bytes cenv dt = type_memory_size dtv /\
  LIST_REL (\dt tv. evaluate_type tenv dt = SOME tv /\
                       type_memory_bytes cenv dt = type_memory_size tv) dts dtvs /\
  evaluate_type tenv st = SOME stv /\ type_memory_bytes cenv st = type_memory_size stv /\
  LIST_REL (\st tv. evaluate_type tenv st = SOME tv /\
                       type_memory_bytes cenv st = type_memory_size tv) sts stvs /\
  type_widens_to tenv st dt /\ LIST_REL (\dt st. type_widens_to tenv st dt) dts sts /\
  value_has_type dtv v /\ values_have_types dtvs vs /\ val_wf dtv v /\ tuple_val_wf vs dtvs /\
  value_has_type stv v /\ values_have_types stvs vs /\ val_wf stv v /\ tuple_val_wf vs stvs /\
  tuple_in_memory (v::vs) (stv::stvs) (w2n sw + soff) s.vs_memory /\
  (w2n sw + soff + (type_memory_size stv + type_memory_size_list stvs) <= w2n dw + doff \/
   w2n dw + doff + (type_memory_size dtv + type_memory_size_list dtvs) <= w2n sw + soff) /\
  w2n sw + soff + (type_memory_size stv + type_memory_size_list stvs) < dimword (:256) /\
  w2n dw + doff + (type_memory_size dtv + type_memory_size_list dtvs) + 64 < dimword (:256) /\
  w2n sw + soff + (type_memory_size stv + type_memory_size_list stvs) <= s.vs_alloca_next /\
  w2n dw + doff + (type_memory_size dtv + type_memory_size_list dtvs) <= s.vs_alloca_next /\
  compile_typed_copy_fields cenv dst src (dt::dts) (st::sts) doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!child st dtv stv v dp sp a b u dw sw.
    MEM child (dt::dts) /\
    type_widens_to tenv st child /\
    evaluate_type tenv child = SOME dtv /\ evaluate_type tenv st = SOME stv /\
    type_memory_bytes cenv child = type_memory_size dtv /\
    type_memory_bytes cenv st = type_memory_size stv /\
    value_has_type dtv v /\ val_wf dtv v /\
    value_has_type stv v /\ val_wf stv v /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    compile_store_memory_typed cenv dp child sp st a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. gas_path_mem ctx func u 0 (OK t) /\
        val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)) ==>
  ?c z. compile_typed_copy_fields cenv dst src dts sts
          (doff + type_memory_size dtv) (soff + type_memory_size stv) c = ((),sb) /\
    gas_path_mem ctx func s 0 (OK z) /\
    val_in_memory dtv v (w2n dw + doff) z.vs_memory /\
    typed_copy_effect ctx func sa c s z (w2n dw + doff) (type_memory_size dtv) /\
    tuple_in_memory vs stvs (w2n sw + soff + type_memory_size stv) z.vs_memory /\
    eval_operand dst z = SOME dw /\ eval_operand src z = SOME sw /\
    z.vs_alloca_next = s.vs_alloca_next /\
    (!x. dst = Var x ==> not_fresh_at c x) /\
    (!x. src = Var x ==> not_fresh_at c x) /\
    fn_has_code c sb func /\ cs_extends sa c /\ sa.cs_next_var <= c.cs_next_var /\
    ~z.vs_halted /\ z.vs_current_bb = c.cs_current_bb /\
    z.vs_inst_idx = LENGTH c.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule typed_memory_fields_cons_compile >> strip_tac >>
  `cs_extends sa b /\ cs_extends sa c` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa a func /\ fn_has_code a b func /\
   fn_has_code b c func /\ fn_has_code c sb func` by metis_tac[fn_has_code_split] >>
  `w2n dw + doff < dimword (:256) /\ w2n sw + soff < dimword (:256)` by decide_tac >>
  drule_all typed_fields_addresses_normalized_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `eval_operand dp u = SOME (dw + n2w doff)` >>
  `?z. gas_path_mem ctx func u 0 (OK z) /\
       val_in_memory dtv v (w2n dw + doff) z.vs_memory /\
       typed_copy_effect ctx func b c u z (w2n dw + doff) (type_memory_size dtv)` by
    (qpat_assum `w2n (dw + n2w doff) = _` (fn th => rewrite_tac[GSYM th]) >>
     first_x_assum irule >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >>
     gvs[valueEncodingTheory.val_in_memory_def] >> decide_tac) >>
  `typed_copy_effect ctx func sa b s u (w2n dw + doff) (type_memory_size dtv)` by
    (irule typed_fields_address_effect >> rpt (goal_assum (drule_at Any))) >>
  `!x. dst = Var x ==> not_fresh_at b x` by metis_tac[not_fresh_at_mono] >>
  `!x. src = Var x ==> not_fresh_at b x` by metis_tac[not_fresh_at_mono] >>
  `u.vs_labels = s.vs_labels` by gvs[venom_state_component_equality] >>
  `eval_operand dst u = SOME dw` by
    (qpat_x_assum `eval_operand dst s = SOME dw` mp_tac >>
     Cases_on `dst` >> simp[eval_operand_def] >> metis_tac[]) >>
  `eval_operand src u = SOME sw` by
    (qpat_x_assum `eval_operand src s = SOME sw` mp_tac >>
     Cases_on `src` >> simp[eval_operand_def] >> metis_tac[]) >>
  `tuple_in_memory vs stvs (w2n sw + soff + type_memory_size stv) z.vs_memory /\
   eval_operand dst z = SOME dw /\ eval_operand src z = SOME sw /\
   z.vs_alloca_next = u.vs_alloca_next /\ ~z.vs_halted /\
   z.vs_current_bb = c.cs_current_bb /\ z.vs_inst_idx = LENGTH c.cs_current_insts` by
    (irule typed_fields_child_suffix_frame >>
     qpat_assum `typed_copy_effect _ _ b c u z _ _` (irule_at Any) >>
     gvs[] >> rpt (goal_assum (drule_at Any)) >>
     qexists_tac `type_memory_size_list dtvs` >> decide_tac) >>
  `gas_path_mem ctx func s 0 (OK z)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  `typed_copy_effect ctx func sa c s z (w2n dw + doff) (type_memory_size dtv)` by
    (irule typed_copy_effect_then >> rpt (goal_assum (drule_at Any)) >>
     metis_tac[not_fresh_at_mono]) >>
  `sa.cs_next_var <= c.cs_next_var` by
    (qspec_then `cenv` (qspecl_then [`dp`,`dt`,`sp`,`st`,`b`] mp_tac)
       (cj 1 ci_mono_typed_memory_family) >>
     simp[ci_mono_def] >> decide_tac) >>
  qexistsl_tac [`c`, `z`] >>
  gns[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  conj_tac >> metis_tac[not_fresh_at_mono]
QED

Theorem typed_memory_fields_forward_mem:
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
  w2n sw + soff + type_memory_size_list stvs <= s.vs_alloca_next /\
  w2n dw + doff + type_memory_size_list dtvs <= s.vs_alloca_next /\
  compile_typed_copy_fields cenv dst src dts sts doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dt st dtv stv v dp sp a b u dw sw.
    MEM dt dts /\
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
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. gas_path_mem ctx func u 0 (OK t) /\
        val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw + doff) (type_memory_size_list dtvs)
Proof
  Induct >- suspend "nil" >>
  pop_assum (mk_asm "ih") >>
  Cases_on `sts` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingTheory.val_wf_def,
       valueEncodingTheory.type_memory_size_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `compile_typed_copy_fields cenv dst src (dt::dts) (st::sts) doff soff sa = ((),sb)` >>
  rename1 `tuple_in_memory (v::vs) (stv::stvs) _ s.vs_memory` >>
  rename1 `evaluate_type tenv dt = SOME dtv` >>
  qmatch_goalsub_rename_tac `tuple_in_memory (v::vs) (dtv::dtvs)` >>
  mp_tac typed_fields_head_transition_mem >>
  impl_tac >- (asm_x "ih" kall_tac >>
    simp_tac pure_ss [MEM, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
    rule_assum_tac (SIMP_RULE pure_ss [MEM,
      AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  asm_x "ih" (qspecl_then [`sts`,`dtvs`,`stvs`,`vs`] mp_tac) >>
  disch_then (qspecl_then [`doff + type_memory_size dtv`,
    `soff + type_memory_size stv`,`c`,`sb`,`z`] mp_tac) >>
  impl_tac >-
    (qpat_x_assum `!dt' st dtv stv v dp sp a b u dw sw. _`
       (mk_asm "child") >>
     simp_tac pure_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
     rule_assum_tac (SIMP_RULE pure_ss
       [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- decide_tac >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     ntac 2 (conj_tac >- simp[]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >> asm_x "child" irule >>
     rpt (goal_assum (drule_at Any)) >> simp[MEM]) >>
  strip_tac >>
  qpat_x_assum `!dt' st dtv stv v dp sp a b u dw sw. _` kall_tac >>
  rule_assum_tac (SIMP_RULE pure_ss
    [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  qexists_tac `t` >>
  conj_tac >- metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  conj_tac >-
    (irule typed_fields_cons_reassemble >>
     simp_tac pure_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  irule typed_copy_effect_then >> qexistsl_tac [`c`,`c`,`z`] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac >> irule typed_copy_effect_enlarge >>
  rpt (goal_assum (drule_at Any)) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Resume typed_memory_fields_forward_mem[nil]:
  Cases_on `sts` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingTheory.val_wf_def,
       valueEncodingTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def,
       cj 2 compile_store_memory_typed_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >> qexists_tac `s` >>
  conj_tac >- (irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  irule typed_copy_effect_identity >> simp[]
QED

Finalise typed_memory_fields_forward_mem

Theorem typed_memory_struct_forward_mem:
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
  w2n sw + soff + type_memory_size_list tvs <= s.vs_alloca_next /\
  w2n dw + doff + type_memory_size_list tvs <= s.vs_alloca_next /\
  compile_struct_typed_copy cenv dst src fields fields doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dt st dtv stv v dp sp a b u dw sw.
    MEM dt (MAP (FST o SND) fields) /\
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
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. gas_path_mem ctx func u 0 (OK t) /\
        val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      fields_in_memory vals (ZIP (MAP FST fields,tvs))
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
  irule typed_memory_fields_forward_mem >> simp[] >>
  goal_assum $ drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`) >>
  qexistsl_tac [`tvs`, `sw`, `tenv`] >>
  simp[LIST_REL_refl, EVERY_MEM] >> gvs[]
QED
