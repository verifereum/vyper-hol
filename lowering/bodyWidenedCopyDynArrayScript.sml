Theory bodyWidenedCopyDynArray
Ancestors
  bodyWidenedCopyArrays bodyWidenedCopyPrimitive placeMemoryArrayForward
  placeMemoryArrayControl placeMemoryChildForward placeMemoryCodeLayout
  placeMemoryCopyEffect placeMemoryCopyFrames placeMemoryTypedBase placeMemoryDynarrayForward
  placeMemoryForwardPath context compileEnv loweringStateRelDefs fragExec
  emitHelper emitHelperProps exprLoweringProps freshWrites ASCIInumbers
  venomState venomInst venomExecSemantics fragGasMode list rich_list arithmetic

val M_margin = ``\k:num. \cenv tenv ctx func dt.
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
    w2n dw + type_memory_size dtv + k < dimword (:256) /\
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
        gas_marked_path T ctx func u 0 (OK t)``;

Theorem typed_memory_dynarray_slow_margin_forward_mem:
  compile_copy_dynarray_typed cenv dst dt cap src st sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\ dt = st) /\
  ^M_margin k cenv tenv ctx func dt /\
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
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) + k < dimword (:256) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= s.vs_alloca_next /\
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
        (type_memory_size (ArrayTV dtv (Dynamic cap))) /\
      gas_marked_path T ctx func s 0 (OK t)
Proof
  strip_tac >> (
  drule_all typed_memory_dynarray_slow_compile >> strip_tac >>
  `fn_has_code sm sb func` by
    (qpat_x_assum `fn_has_code sa sb func` mp_tac >>
     gvs[fn_has_code_def, emitted_blocks_def, same_blocks_def]) >>
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
     rpt strip_tac >> gvs[] >> simp[IS_PREFIX_APPEND]) >>
  `fn_has_code sa sm func` by
    (simp[fn_has_code_def, emitted_blocks_def] >>
     gvs[same_blocks_def] >> metis_tac[isPREFIX_TRANS]) >>
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
  `LENGTH vs <= cap /\ LENGTH vs <= scap` by
    metis_tac[typed_memory_dynarray_length] >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    gvs[valueEncodingDefsTheory.val_in_memory_def, valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  drule_all typed_memory_dynarray_setup_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (simp[gas_marked_path_def] >> metis_tac[gas_marked_path_exec]) >>
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
       lookup_var counter u = SOME 0w /\ u.vs_memory = t.vs_memory /\
       gas_marked_path T ctx func t 0 (OK u)` by
    (
  `gas_marked_path T ctx func t 0
     (OK (jump_to hdr ((update_var counter 0w t) with
                       vs_inst_idx := t.vs_inst_idx + 1)))` by
    (irule typed_memory_array_init_forward_mem >> simp[] >>
     qexistsl_tac [`id1`, `id2`] >> simp[]) >>
  `gas_marked_path F ctx func t 0
     (OK (jump_to hdr ((update_var counter 0w t) with
                       vs_inst_idx := t.vs_inst_idx + 1)))` by
    (simp[gas_marked_path_def] >> metis_tac[gas_marked_path_exec]) >>
  qexists_tac `jump_to hdr ((update_var counter 0w t) with
                       vs_inst_idx := t.vs_inst_idx + 1)` >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> first_x_assum drule >> simp[]) >>
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
     simp[valueEncodingDefsTheory.val_wf_def, vyperTypingTheory.value_has_type_def] >>
     qid_spec_tac `vs` >> Induct >> simp[valueEncodingDefsTheory.val_wf_def,
       vyperTypingTheory.value_has_type_def] >> rpt strip_tac >>
     Cases_on `i` >> gvs[] >> metis_tac[]) >>
  `(w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw + 32 \/
    w2n dw + 32 + LENGTH vs * type_memory_size dtv <= w2n sw)` by
    (gvs[valueEncodingTheory.type_memory_size_def] >>
     `LENGTH vs * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
     decide_tac) >>
  `?z. val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
          (w2n sw) z.vs_memory /\
       (!j. j < LENGTH vs ==> val_in_memory dtv (elem j)
          (w2n dw + 32 + j * type_memory_size dtv) z.vs_memory) /\
       typed_copy_effect ctx func sm sth t z (w2n dw + 32)
          (LENGTH vs * type_memory_size dtv) /\
       gas_marked_path T ctx func t 0 (OK z) /\
       lookup_var counter z = SOME (n2w (LENGTH vs))` by
    (irule typed_memory_array_iteration_forward_mem >>
     qpat_assum `typed_copy_effect ctx func sm sth t u _ _` (irule_at Any) >>
     reverse conj_tac >- (simp[] >> metis_tac[]) >> (
  rpt gen_tac >> strip_tac >>
  `~a.vs_halted /\ a.vs_current_bb = hdr /\ a.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `eval_operand length a = SOME (n2w (LENGTH vs))` by
    (qpat_x_assum `typed_copy_effect ctx func sm sth t a _ _` mp_tac >>
     qpat_x_assum `eval_operand length t = SOME (n2w (LENGTH vs))` mp_tac >>
     qpat_x_assum `!x. length = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `length` >>
     simp[eval_operand_def, typed_copy_effect_def, venom_state_component_equality] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  CONV_TAC (BINDER_CONV (RAND_CONV (RAND_CONV (REWR_CONV CONJ_COMM)))) >>
  irule typed_memory_array_round_effect_mem >>
  qpat_assum `hbb.bb_instructions = _` (irule_at Any) >>
  qrefinel [`_`, `_`, `_`, `_`, `_`, `stb`, `b5`, `LENGTH vs`] >>
  qpat_assum `sth.cs_current_bb = hdr` (fn th => rewrite_tac [th]) >>
  qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  reverse conj_tac >- simp[] >>
  gen_tac >> strip_tac >>
  `w2n (sw + 32w) = w2n sw + 32 /\ w2n (dw + 32w) = w2n dw + 32` by
    (`w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256)` by
       (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
     simp[wordsTheory.w2n_add_2]) >>
  qpat_assum `w2n (dw + 32w) = _`
    (fn th => pure_rewrite_tac [GSYM th]) >>
  irule typed_memory_array_element_margin_forward_mem >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> qexists_tac `sw + 32w` >>
  `eval_operand src_data a' = SOME (sw + 32w) /\
   eval_operand dst_data a' = SOME (dw + 32w)` by
    (qpat_x_assum `typed_copy_effect ctx func sm sth t a _ _` mp_tac >>
     qpat_x_assum `typed_copy_effect ctx func sm stb a a' _ _` mp_tac >>
     qpat_x_assum `eval_operand src_data t = SOME (sw + 32w)` mp_tac >>
     qpat_x_assum `eval_operand dst_data t = SOME (dw + 32w)` mp_tac >>
     qpat_x_assum `!x. src_data = Var x ==> _` mp_tac >>
     qpat_x_assum `!x. dst_data = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `src_data` >> Cases_on `dst_data` >>
     simp[eval_operand_def, typed_copy_effect_def, venom_state_component_equality] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
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
     pure_rewrite_tac[valueEncodingPropsTheory.val_in_memory_dynarray] >> strip_tac >>
     drule_all exprSimAggregateEncodingTheory.elems_in_memory_EL >>
     unabbrev_all_tac >> BETA_TAC >> disch_then ACCEPT_TAC) >>
  qpat_x_assum `(^M_margin k) cenv tenv ctx func dt` kall_tac >>
  gvs[typed_copy_effect_def, valueEncodingTheory.type_memory_size_def,
      venom_state_component_equality] >> decide_tac)) >>
  `~z.vs_halted /\ z.vs_current_bb = hdr /\ z.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `eval_operand length z = SOME (n2w (LENGTH vs))` by
    (qpat_x_assum `typed_copy_effect ctx func sm sth t z _ _` mp_tac >>
     qpat_x_assum `eval_operand length t = SOME _` mp_tac >>
     qpat_x_assum `!x. length = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `length` >>
     simp[eval_operand_def, typed_copy_effect_def, venom_state_component_equality] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `mem_word_at (w2n dw) z.vs_memory = n2w (LENGTH vs)` by
    (`mem_bytes_at (w2n dw) 32 z.vs_memory = mem_bytes_at (w2n dw) 32 t.vs_memory` by
       (irule typed_copy_effect_bytes >>
        qpat_assum `typed_copy_effect ctx func sm sth t z _ _` (irule_at Any) >> simp[]) >>
     qpat_x_assum `mem_word_at (w2n dw) t.vs_memory = _` mp_tac >>
     pure_rewrite_tac[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
     qpat_assum `mem_bytes_at (w2n dw) 32 z.vs_memory = _` (fn th => rewrite_tac[th])) >>
  `?r. typed_copy_effect ctx func sm sb z r (w2n dw + 32)
          (LENGTH vs * type_memory_size dtv) /\
       lookup_var counter r = SOME (n2w (LENGTH vs)) /\ r.vs_memory = z.vs_memory /\
       gas_marked_path T ctx func z 0 (OK r)` by
    (drule_at (Pat `hbb.bb_instructions = _`)
       (Q.INST [`N` |-> `LENGTH (vs: value list)`, `i` |-> `LENGTH (vs: value list)`]
         typed_memory_array_condition_effect_mem) >>
     disch_then irule >> gvs[]) >>
  qexists_tac `r` >> (conj_tac
  >- (simp[valueEncodingPropsTheory.val_in_memory_dynarray] >>
      irule exprSimAggregateEncodingTheory.elems_in_memory_intro >>
      qpat_x_assum `!j. j < LENGTH vs ==> val_in_memory _ _ _ _` mp_tac >>
      simp[Abbr `elem`]) >>
  `typed_copy_effect ctx func sm sb t r (w2n dw + 32)
       (LENGTH vs * type_memory_size dtv)` by
    (irule typed_copy_effect_then >>
     qpat_assum `typed_copy_effect ctx func sm sth t z _ _` (irule_at Any) >>
     qpat_assum `typed_copy_effect ctx func sm sb z r _ _` (irule_at Any) >> simp[]) >>
  `typed_copy_effect ctx func sm sb t r (w2n dw)
       (type_memory_size (ArrayTV dtv (Dynamic cap)))` by
    (irule typed_copy_effect_enlarge >>
     qpat_assum `typed_copy_effect ctx func sm sb t r _ _` (irule_at Any) >>
     simp[valueEncodingTheory.type_memory_size_def]) >>
  conj_tac
  >- (irule typed_copy_effect_then >>
      qpat_assum `typed_copy_effect ctx func sa sm s t _ _` (irule_at Any) >>
      qpat_assum `typed_copy_effect ctx func sm sb t r (w2n dw) _` (irule_at Any) >>
      simp[not_fresh_at_def]) >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]))
QED


(* Compatibility at the original margin; the constructor proof is shared. *)
val M = ``\cenv tenv ctx func dt.
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
        gas_marked_path T ctx func u 0 (OK t)``;

Theorem typed_memory_dynarray_slow_forward_mem:
  compile_copy_dynarray_typed cenv dst dt cap src st sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\ dt = st) /\
  ^M cenv tenv ctx func dt /\
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
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) + 64 < dimword (:256) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= s.vs_alloca_next /\
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
        (type_memory_size (ArrayTV dtv (Dynamic cap))) /\
      gas_marked_path T ctx func s 0 (OK t)
Proof
  mp_tac (Q.INST [`k` |-> `64`] typed_memory_dynarray_slow_margin_forward_mem) >>
  BETA_TAC >> rewrite_tac[arithmeticTheory.ADD_CLAUSES]
QED

Theorem typed_memory_dynarray_slow_frontier_forward_mem:
  compile_copy_dynarray_typed cenv dst dt cap src st sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\ dt = st) /\
  ^M_margin 0 cenv tenv ctx func dt /\
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
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= s.vs_alloca_next /\
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
        (type_memory_size (ArrayTV dtv (Dynamic cap))) /\
      gas_marked_path T ctx func s 0 (OK t)
Proof
  mp_tac (Q.INST [`k` |-> `0`] typed_memory_dynarray_slow_margin_forward_mem) >>
  BETA_TAC >> rewrite_tac[arithmeticTheory.ADD_CLAUSES]
QED
