Theory tuplePlaceDynarraySize
Ancestors
  tuplePlaceArraySize placeMemoryArrayForward placeMemoryArrayControl
  placeMemoryTypedBase placeMemoryCodeLayout placeMemoryCopyEffect
  placeMemoryCopyFrames placeMemoryDynarrayForward context compileEnv
  emitHelper emitHelperProps exprLoweringProps venomState venomInst
  venomExecSemantics freshWrites ASCIInumbers list arithmetic

Theorem tuple_place_dynarray_slow_size_forward:
  compile_copy_dynarray_typed cenv dst dt cap src st sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\ dt = st) /\
  tuple_place_child_size_forward cenv tenv ctx func dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= w2n sw) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) < dimword (:256) /\
  type_memory_size (ArrayTV dtv (Dynamic cap)) + 64 < dimword (:256) /\
  type_memory_size (ArrayTV stv (Dynamic scap)) + 64 < dimword (:256) /\
  cap < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs))
        (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw)
        (type_memory_size (ArrayTV dtv (Dynamic cap)))
Proof
  strip_tac >> (
  drule_all typed_memory_dynarray_slow_compile >> strip_tac >>
  `fn_has_code sm sb func` by
    (qpat_x_assum `fn_has_code sa sb func` mp_tac >>
     gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def, same_blocks_def]) >>
  drule_all typed_copy_dynarray_slow_code_lookup >> strip_tac >>
  `isPREFIX sm.cs_current_insts st1.cs_current_insts /\
   st1.cs_current_bb = sm.cs_current_bb` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`fresh_label "typed_dyn_cond" _ = _`,
        `fresh_label "typed_dyn_body" _ = _`,
        `fresh_label "typed_dyn_exit" _ = _`,
        `fresh_var _ = _`, `emit_inst ASSIGN [Lit 0w] _ _ = _`,
        `emit_inst JMP [Label hdr] _ st0 = _`] >>
     rpt (first_x_assum kall_tac) >>
     simp[fresh_label_def, fresh_var_def, emit_inst_def, fresh_id_def,
          emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sa sm func` by
    (simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
     gvs[same_blocks_def] >> metis_tac[listTheory.isPREFIX_TRANS]) >>
  drule_all typed_copy_slow_array_control_layout >> strip_tac >>
  `(do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
       doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
       sp <- emit_op ADD [src_data; so]; dp <- emit_op ADD [dst_data; doff];
       return (sp,dp) od) stb = ((sp,dp),b4)` by
    simp[comp_bind_def, comp_return_def] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `lookup_block st1.cs_current_bb _ = _` kall_tac >>
  qpat_x_assum `lookup_block st2.cs_current_bb _ = _` kall_tac >>
  qpat_x_assum `lookup_block st3.cs_current_bb _ = _` kall_tac >>
  `LENGTH vs <= cap /\ LENGTH vs <= scap` by metis_tac[typed_memory_dynarray_length] >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    gvs[valueEncodingTheory.val_in_memory_def, valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  drule_all typed_memory_dynarray_setup_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `typed_copy_effect ctx func sa sm s t (w2n dw)
     (type_memory_size (ArrayTV dtv (Dynamic cap)))` by
    (simp[typed_copy_effect_def] >> conj_tac
     >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
         simp[venom_state_component_equality]) >>
     conj_tac
     >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
         simp[venom_state_component_equality]) >>
     rpt strip_tac >>
     qpat_x_assum `!a len. _` (qspecl_then [`a`, `len`] mp_tac) >>
     simp[] >> gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `?u. typed_copy_effect ctx func sm sth t u (w2n dw + 32)
        (LENGTH vs * type_memory_size dtv) /\
       lookup_var counter u = SOME 0w /\ u.vs_memory = t.vs_memory` by
    (suspend "initial") >>
  suspend "integration")
QED

Resume tuple_place_dynarray_slow_size_forward[initial]:
  markerLib.RESUME_TAC >> (
  `gas_marked_path F ctx func t 0
     (OK (jump_to hdr ((update_var counter 0w t) with
                       vs_inst_idx := t.vs_inst_idx + 1)))` by
    (irule typed_memory_array_init_forward >> simp[] >>
     qexistsl_tac [`id1`, `id2`] >> simp[]) >>
  qexists_tac `jump_to hdr ((update_var counter 0w t) with
                       vs_inst_idx := t.vs_inst_idx + 1)` >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> first_x_assum drule >> simp[])
QED

Resume tuple_place_dynarray_slow_size_forward[integration]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `lookup_block sb.cs_current_bb _ = SOME bb` kall_tac >>
  qpat_x_assum `isPREFIX sb.cs_current_insts _` kall_tac >>
  qpat_x_assum `isPREFIX sm.cs_current_insts st1.cs_current_insts` kall_tac >>
  qpat_x_assum `st1.cs_current_bb = _` kall_tac >>
  `val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
     (w2n sw) u.vs_memory` by
    (simp[] >> irule val_in_memory_outside_write >> simp[] >>
     qexistsl_tac [`w2n dw`, `s.vs_memory`, `type_memory_size (ArrayTV dtv (Dynamic cap))`] >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!a len. _` (qspecl_then [`a`, `len`] mp_tac) >>
     simp[] >> gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  qabbrev_tac `elem = \i. EL i vs` >>
  `!i. i < LENGTH vs ==>
       value_has_type stv (elem i) /\ val_wf stv (elem i) /\
       value_has_type dtv (elem i) /\ val_wf dtv (elem i)` by
    (simp[Abbr `elem`, NoAsms] >>
     map_every (fn q => qpat_assum q mp_tac)
       [`value_has_type (ArrayTV dtv _) _`, `value_has_type (ArrayTV stv _) _`,
        `val_wf (ArrayTV dtv _) _`, `val_wf (ArrayTV stv _) _`] >>
     rpt (first_x_assum kall_tac) >>
     simp[valueEncodingTheory.val_wf_def, vyperTypingTheory.value_has_type_def] >>
     qid_spec_tac `vs` >> Induct >> simp[valueEncodingTheory.val_wf_def,
       vyperTypingTheory.value_has_type_def] >> rpt strip_tac >>
     Cases_on `i` >> gvs[] >> metis_tac[]) >>
  `?z. val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
          (w2n sw) z.vs_memory /\
       (!j. j < LENGTH vs ==> val_in_memory dtv (elem j)
          (w2n dw + 32 + j * type_memory_size dtv) z.vs_memory) /\
       typed_copy_effect ctx func sm sth t z (w2n dw + 32)
          (LENGTH vs * type_memory_size dtv) /\
       lookup_var counter z = SOME (n2w (LENGTH vs))` by
    (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)
       typed_memory_array_iteration_forward >>
     disch_then irule >>
     (conj_tac >- suspend "round") >>
     (conj_tac >- metis_tac[]) >>
     (conj_tac >- simp[]) >>
     (conj_tac >- (gvs[valueEncodingTheory.type_memory_size_def] >>
       `LENGTH vs * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
       decide_tac)) >> simp[]) >>
  suspend "exit")
QED

Resume tuple_place_dynarray_slow_size_forward[round]:
  markerLib.RESUME_TAC >>
  simp[valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >>
  `~a.vs_halted /\ a.vs_current_bb = hdr /\ a.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `!x. not_fresh_at sm x ==> lookup_var x a = lookup_var x t` by
    metis_tac[typed_copy_effect_lookup] >>
  `a.vs_labels = t.vs_labels` by
    (drule_at (Pat `typed_copy_effect _ _ _ _ t a _ _`) typed_copy_effect_record >>
     disch_then (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  `!oper w. eval_operand oper t = SOME w /\
      (!x. oper = Var x ==> not_fresh_at sm x) ==>
      eval_operand oper a = SOME w` by
    (qpat_x_assum `!x. not_fresh_at sm x ==> lookup_var x a = _` mp_tac >>
     qpat_x_assum `a.vs_labels = t.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> Cases_on `oper` >> gvs[eval_operand_def]) >>
  `eval_operand length a = SOME (n2w (LENGTH vs))` by metis_tac[] >>
  drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_round_effect >>
  disch_then irule >> simp[eval_operand_def] >>
  qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  rpt strip_tac >> (
  `w2n (sw + 32w) = w2n sw + 32 /\
   w2n (dw + 32w) = w2n dw + 32` by
    (`w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256)` by
       (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
     simp[wordsTheory.w2n_add_2]) >>
  `?v. val_in_memory dtv (elem i)
        (w2n (dw + 32w) + i * type_memory_size dtv) v.vs_memory /\
       typed_copy_effect ctx func stb b5 a' v
        (w2n (dw + 32w) + i * type_memory_size dtv) (type_memory_size dtv)`
    suffices_by (simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  irule tuple_place_array_element_size_forward >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type tenv st = SOME stv` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexists_tac `sw + 32w` >>
  `eval_operand src_data a' = SOME (sw + 32w) /\
   eval_operand dst_data a' = SOME (dw + 32w)` by
    (qpat_x_assum `typed_copy_effect ctx func sm sth t a _ _` mp_tac >>
     qpat_x_assum `typed_copy_effect ctx func sm stb a a' _ _` mp_tac >>
     qpat_x_assum `eval_operand src_data t = SOME (sw + 32w)` mp_tac >>
     qpat_x_assum `eval_operand dst_data t = SOME (dw + 32w)` mp_tac >>
     qpat_x_assum `!x. src_data = Var x ==> _` mp_tac >>
     qpat_x_assum `!x. dst_data = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `src_data` >> Cases_on `dst_data` >>
     simp[eval_operand_def, typed_copy_effect_def,
          venom_state_component_equality] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `i * type_memory_size stv + type_memory_size stv <= scap * type_memory_size stv /\
   i * type_memory_size dtv + type_memory_size dtv <= cap * type_memory_size dtv` by
    (`SUC i <= scap /\ SUC i <= cap` by decide_tac >>
     `SUC i * type_memory_size stv <= scap * type_memory_size stv /\
      SUC i * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC i * type_memory_size stv <= _` mp_tac >>
     qpat_x_assum `SUC i * type_memory_size dtv <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `val_in_memory stv (elem i) (w2n sw + 32 + i * type_memory_size stv) a.vs_memory` by
    (qpat_x_assum `val_in_memory (ArrayTV stv _) _ _ a.vs_memory` mp_tac >>
     simp[valueEncodingPropsTheory.val_in_memory_dynarray] >> strip_tac >>
     drule exprSimAggregateEncodingTheory.elems_in_memory_EL >>
     disch_then (qspec_then `i` mp_tac) >>
     simp[Abbr `elem`, AC ADD_ASSOC ADD_COMM]) >>
  gvs[typed_copy_effect_def, valueEncodingTheory.type_memory_size_def] >> decide_tac)
QED

Resume tuple_place_dynarray_slow_size_forward[exit]:
  markerLib.RESUME_TAC >> (
  `~z.vs_halted /\ z.vs_current_bb = hdr /\ z.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `eval_operand length z = SOME (n2w (LENGTH vs))` by
    (qpat_x_assum `typed_copy_effect ctx func sm sth t z _ _` mp_tac >>
     qpat_x_assum `eval_operand length t = SOME (n2w (LENGTH vs))` mp_tac >>
     qpat_x_assum `!x. length = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `length` >>
     simp[eval_operand_def, typed_copy_effect_def, venom_state_component_equality] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `?r. typed_copy_effect ctx func sm sb z r (w2n dw + 32)
         (LENGTH vs * type_memory_size dtv) /\
       lookup_var counter r = SOME (n2w (LENGTH vs)) /\ r.vs_memory = z.vs_memory` by
    (drule_at (Pat `hbb.bb_instructions = _`)
       (Q.INST [`N` |-> `LENGTH (vs:value list)`, `i` |-> `LENGTH (vs:value list)`]
         typed_memory_array_condition_effect) >>
     disch_then (qspec_then `vs` irule) >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  `typed_copy_effect ctx func sm sb t r (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv)` by
    (qpat_assum `typed_copy_effect ctx func sm sth t z _ _`
       (mp_then Any mp_tac typed_copy_effect_then) >>
     disch_then (qspecl_then [`r`, `sb`, `sm`] mp_tac) >> simp[]) >>
  `mem_bytes_at (w2n dw) 32 r.vs_memory = mem_bytes_at (w2n dw) 32 t.vs_memory` by
    (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `r` >> conj_tac
  >- (simp[valueEncodingPropsTheory.val_in_memory_dynarray] >> conj_tac
      >- (qpat_x_assum `mem_bytes_at _ _ r.vs_memory = _` mp_tac >>
          gvs[valueEncodingTheory.mem_word_at_def, valueEncodingTheory.mem_bytes_at_def]) >>
      irule exprSimAggregateEncodingTheory.elems_in_memory_intro >>
      qpat_x_assum `!j. j < LENGTH vs ==> val_in_memory _ _ _ _` mp_tac >>
      simp[Abbr `elem`]) >>
  qpat_assum `typed_copy_effect ctx func sa sm s t _ _`
    (mp_then Any mp_tac typed_copy_effect_then) >>
  disch_then (qspecl_then [`r`, `sb`, `sm`] mp_tac) >>
  (impl_tac >- (conj_tac
    >- (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >>
        simp[valueEncodingTheory.type_memory_size_def] >>
        `LENGTH vs * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
        decide_tac) >> metis_tac[not_fresh_at_mono])) >> simp[])
QED

Finalise tuple_place_dynarray_slow_size_forward
