(* Checked address execution for recursive tuple and nominal field copies. *)
Theory typedCopyFieldsPathMem
Ancestors
  typedCopyControlPathMem placeMemoryFieldsForward placeMemoryCopyEffect placeMemoryCopyFrames
  placeMemoryTypedBase placeMemoryChildForward bodyDeclMemoryCounted
  context compileEnv exprLoweringProps emitHelper emitHelperProps
  venomState venomInst venomExecSemantics venomExecProofs fragExecMem
  fragGasMode fragGasPathMem fragExec instMemFrontier freshWrites
  ASCIInumbers list rich_list arithmetic finite_map

Theorem typed_memory_fields_addresses_mem_ok[local]:
  (do dp <- compile_with_byte_offset dst doff;
      sp <- compile_with_byte_offset src soff;
      return (dp,sp)
   od) sa = ((dp,sp),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `doff = 0` >> Cases_on `soff = 0` >>
  simp[compile_with_byte_offset_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def] >>
  rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >> simp[]
QED

Theorem typed_memory_fields_addresses_forward_mem:
  (do dp <- compile_with_byte_offset dst doff;
      sp <- compile_with_byte_offset src soff;
      return (dp,sp)
   od) sa = ((dp,sp),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
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
  strip_tac >> drule_all typed_memory_fields_addresses_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule typed_memory_fields_addresses_mem_ok >> goal_assum (drule_at Any)) >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule (cj 1 body_decl_cursor_path) >> simp[] >>
     qexists_tac `sa` >> gvs[EVERY_MEM]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(u with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> conj_tac
  >- (qpat_x_assum `(u with vs_vars := _) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  metis_tac[lookup_var_def]
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
    MEM dt dts /\ type_widens_to tenv st dt /\
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
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv) /\
        gas_path_mem ctx func u 0 (OK t)) ==>
  ?t. tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw + doff) (type_memory_size_list dtvs) /\
      gas_path_mem ctx func s 0 (OK t)
Proof
  Induct
  >- (Cases_on `sts` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
      simp[vyperTypingTheory.value_has_type_def, valueEncodingTheory.val_wf_def,
           valueEncodingTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def,
           cj 2 compile_store_memory_typed_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >> conj_tac
      >- (irule typed_copy_effect_identity >> simp[]) >>
      simp[Once gas_path_mem_cases]) >>
  pop_assum (mk_asm "ih") >>
  Cases_on `sts` >> simp[] >>
  Cases_on `dtvs` >> simp[] >>
  Cases_on `stvs` >> simp[] >>
  Cases_on `vs` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingTheory.val_wf_def,
       valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >> gvs[] >>
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
  drule_all typed_memory_fields_addresses_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `eval_operand dp u = SOME (dw + n2w doff)` >>
  drule_all typed_memory_fields_addresses_fresh >> strip_tac >>
  suspend "child"
QED

Resume typed_memory_fields_forward_mem[child]:
  markerLib.RESUME_TAC >> (
  `w2n (dw + n2w doff) = w2n dw + doff /\
   w2n (sw + n2w soff) = w2n sw + soff` by
    (`w2n dw + doff < dimword (:256) /\ w2n sw + soff < dimword (:256)` by decide_tac >>
     `doff < dimword (:256) /\ soff < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, LESS_MOD]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `val_in_memory stv v (w2n (sw + n2w soff)) u.vs_memory /\
   tuple_in_memory vs stvs (w2n sw + soff + type_memory_size stv) u.vs_memory` by
    (qpat_assum `tuple_in_memory (v::vs) _ _ s.vs_memory`
       (mp_tac o SRULE [valueEncodingTheory.val_in_memory_def]) >>
     simp[AC ADD_ASSOC ADD_COMM]) >>
  `?z. val_in_memory dtv v (w2n (dw + n2w doff)) z.vs_memory /\
       typed_copy_effect ctx func b c u z (w2n (dw + n2w doff)) (type_memory_size dtv) /\
       gas_path_mem ctx func u 0 (OK z)` by
    (qpat_assum `!dt st dtv stv v dp sp a b u dw sw. _` (qspec_then `dt` mp_tac) >>
     simp[] >> disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then (qspec_then `v` mp_tac) >> simp[] >>
     disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     disch_then (qspec_then `u` mp_tac) >> simp[] >>
     impl_tac >- gvs[] >> simp[]) >>
  suspend "tail")
QED

Resume typed_memory_fields_forward_mem[tail]:
  markerLib.RESUME_TAC >> (
  `tuple_in_memory vs stvs (w2n sw + soff + type_memory_size stv) z.vs_memory` by
    (irule typed_memory_tuple_outside_write >> simp[] >>
     qexistsl_tac [`w2n dw + doff`, `u.vs_memory`, `type_memory_size dtv`] >>
     conj_tac
     >- (rpt strip_tac >> irule typed_copy_effect_bytes >>
         goal_assum (drule_at Any) >> simp[]) >>
     gvs[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    (qpat_assum `typed_copy_effect ctx func b c u z _ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` mp_tac >>
     qpat_assum `sa.cs_next_var <= b.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[typed_copy_effect_lookup, not_fresh_at_mono]) >>
  `z.vs_labels = s.vs_labels /\ z.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand dst z = SOME dw /\ eval_operand src z = SOME sw` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _` mp_tac >>
     qpat_assum `eval_operand dst s = _` mp_tac >>
     qpat_assum `eval_operand src s = _` mp_tac >>
     qpat_assum `!x. dst = Var x ==> _` mp_tac >>
     qpat_assum `!x. src = Var x ==> _` mp_tac >>
     qpat_assum `z.vs_labels = s.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `dst` >> Cases_on `src` >>
     simp[eval_operand_def] >> metis_tac[]) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  `sa.cs_next_var <= c.cs_next_var` by
    (qspec_then `cenv` (qspecl_then [`dp`,`dt`,`sp`,`st`,`b`] mp_tac)
       (cj 1 ci_mono_typed_memory_family) >>
     simp[ci_mono_def] >> decide_tac) >>
  suspend "recurse")
QED

Resume typed_memory_fields_forward_mem[recurse]:
  markerLib.RESUME_TAC >> (
  `?t. tuple_in_memory vs dtvs (w2n dw + (doff + type_memory_size dtv)) t.vs_memory /\
       typed_copy_effect ctx func c sb z t (w2n dw + (doff + type_memory_size dtv))
         (type_memory_size_list dtvs) /\ gas_path_mem ctx func z 0 (OK t)` by
    (asm "ih" irule >> simp[] >>
     conj_tac >- metis_tac[not_fresh_at_mono] >>
     conj_tac >- metis_tac[not_fresh_at_mono] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!dt st dtv stv v dp sp a b u dw sw. _` irule >> simp[] >>
         goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >> simp[]) >>
     qexistsl_tac [`soff + type_memory_size stv`, `sts`, `stvs`] >>
     gvs[] >> decide_tac) >>
  suspend "compose")
QED

Resume typed_memory_fields_forward_mem[compose]:
  markerLib.RESUME_TAC >> (
  `val_in_memory dtv v (w2n dw + doff) t.vs_memory` by
    (irule val_in_memory_outside_write >> simp[] >>
     qexistsl_tac [`w2n dw + (doff + type_memory_size dtv)`,
                   `z.vs_memory`, `type_memory_size_list dtvs`] >>
     gvs[] >> rpt strip_tac >> irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qexists_tac `t` >> conj_tac
  >- gvs[valueEncodingTheory.val_in_memory_def] >>
  reverse conj_tac
  >- (qpat_assum `gas_path_mem ctx func s 0 (OK u)` mp_tac >>
      qpat_assum `gas_path_mem ctx func u 0 (OK z)` mp_tac >>
      qpat_assum `gas_path_mem ctx func z 0 (OK t)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      metis_tac[gas_path_mem_then, ADD]) >>
  asm_x "ih" kall_tac >>
  `typed_copy_effect ctx func sa b s u (w2n dw + doff)
     (type_memory_size dtv + type_memory_size_list dtvs)` by
    (`gas_marked_path F ctx func s 0 (OK u)` by
       (irule gas_marked_path_from_mem >> simp[]) >>
     qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >>
     simp[typed_copy_effect_def, venom_state_component_equality]) >>
  `typed_copy_effect ctx func b c u z (w2n dw + doff)
     (type_memory_size dtv + type_memory_size_list dtvs)` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  `typed_copy_effect ctx func c sb z t (w2n dw + doff)
     (type_memory_size dtv + type_memory_size_list dtvs)` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> decide_tac) >>
  `typed_copy_effect ctx func sa c s z (w2n dw + doff)
     (type_memory_size dtv + type_memory_size_list dtvs)` by
    (match_mp_tac (GEN_ALL typed_copy_effect_then) >>
     qexistsl_tac [`u`, `b`, `b`] >> simp[] >> metis_tac[not_fresh_at_mono]) >>
  match_mp_tac (GEN_ALL typed_copy_effect_then) >>
  qexistsl_tac [`z`, `c`, `c`] >> gvs[] >> metis_tac[not_fresh_at_mono])
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
    MEM dt (MAP (FST o SND) fields) /\ type_widens_to tenv st dt /\
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
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv) /\
        gas_path_mem ctx func u 0 (OK t)) ==>
  ?t. fields_in_memory vals (ZIP (MAP FST fields,tvs))
        (w2n dw + doff) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw + doff) (type_memory_size_list tvs) /\
      gas_path_mem ctx func s 0 (OK t)
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
