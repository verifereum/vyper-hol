(* Exact store arm used after the destination ADD and delayed unwrap. *)
Theory exprExtRequestTupleStore
Ancestors
  exprExtRequestJointUnwrap exprExtRequestStrongCapture exprExtRequestShape
  exprSimBufferStore exprBopSimProps loweringPosts valueEncodingProps
  exprExtRequestHistory freshWrites
  valueEncodingProofs emitHelperProps
Libs
  wordsLib

Theorem extrequest_store_cell_encoding:
  (if is_word_type ty then emit_void MSTORE [dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src dst
   else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes cenv ty))])
      sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  val_wf tv v /\ expr_val_rel cx ty v src s /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[] >> drule_all expr_val_rel_typed >> strip_tac >>
      drule_at (Pat `evaluate_type _ _ = _`) buffer_store_word_encoding >>
      disch_then drule >> simp[] >>
      disch_then (qspecl_then [`s`, `d`, `v`] mp_tac) >> simp[] >> strip_tac >>
      `q.vs_vars = s.vs_vars` by
        (qpat_x_assum `q with vs_memory := _ = s` mp_tac >>
         simp[Once venomStateTheory.venom_state_component_equality]) >>
      qexists_tac `q` >> simp[venomStateTheory.lookup_var_def] >>
      conj_tac
      >- (qpat_x_assum `q with vs_memory := _ = s` mp_tac >>
          simp[venomStateTheory.venom_state_component_equality]) >>
      metis_tac[]) >>
  Cases_on `is_bytestring_type ty`
  >- (gvs[] >>
      `?w. eval_operand src s = SOME w /\
           val_in_memory tv v (w2n w) s.vs_memory` by
        fs[expr_val_rel_def] >>
      drule_all buffer_typed_bytestring_header >> strip_tac >>
      drule_all (SRULE [] buffer_store_bytestring_encoding) >> simp[arithmeticTheory.ADD_COMM]) >>
  gvs[] >>
  `?w. eval_operand src s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory` by fs[expr_val_rel_def] >>
  drule buffer_emit_mcopy_run >>
  disch_then (qspecl_then [`d`, `w`, `n2w (type_memory_size tv)`, `s`] mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >> strip_tac >>
  conj_tac
  >- (irule buffer_mcopy_encoding >> simp[exprSimPropsTheory.val_footprint_le]) >>
  conj_tac
  >- simp[venomExecSemanticsTheory.mcopy_def,
          venomStateTheory.write_memory_with_expansion_def] >>
  conj_tac
  >- simp[venomStateTheory.lookup_var_def, venomExecSemanticsTheory.mcopy_def,
          venomStateTheory.write_memory_with_expansion_def] >>
  metis_tac[buffer_mcopy_exterior, arithmeticTheory.ADD_COMM]
QED

(* The tuple allocation is newer than a captured producer, not necessarily
   newer than the current instruction.  Frame only the producer's regions. *)
Theorem extrequest_history_store_frame:
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  sn.cs_next_var <= sm.cs_next_var /\ sn.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved cenv sm /\
  (q with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) = t /\
  (!x. not_fresh_at sn x ==> lookup_var x q = lookup_var x t) /\
  (!a k. regions_disjoint a k dst n ==>
     mem_bytes_at a k q.vs_memory = mem_bytes_at a k t.vs_memory) /\
  (!name b sz. local_region cenv ec.scopes tc name b sz ==>
     regions_disjoint b sz dst n) /\
  (!aid b sz. FLOOKUP tc.vs_allocas aid = SOME (b,sz) /\
     aid < sc.cs_next_id /\
     (!name lb lsz. local_region cenv ec.scopes tc name lb lsz ==>
        regions_disjoint b sz lb lsz) ==> regions_disjoint b sz dst n) /\
  (cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ec.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) dst n) ==>
  extrequest_history_frame cenv cx ec sc tc ee sm q
Proof
  strip_tac >>
  `q.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _|> = t` mp_tac >>
     simp[Once venomStateTheory.venom_state_component_equality]) >>
  fs[extrequest_history_frame_def] >>
  simp[extrequest_history_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn x` by metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem extrequest_history_store_alloca:
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ec tc /\
  venomMemDefs$allocas_non_overlapping t /\
  FLOOKUP t.vs_allocas live = SOME (tuple_base,sz) /\ sc.cs_next_id <= live /\
  tuple_base <= dst /\ dst + n <= tuple_base + sz /\
  sn.cs_next_var <= sm.cs_next_var /\ sn.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved cenv sm /\
  (q with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) = t /\
  (!x. not_fresh_at sn x ==> lookup_var x q = lookup_var x t) /\
  (!a k. loweringStateRelDefs$regions_disjoint a k dst n ==>
     mem_bytes_at a k q.vs_memory = mem_bytes_at a k t.vs_memory) /\
  (!name b len. local_region cenv ee.scopes t name b len ==>
     loweringStateRelDefs$regions_disjoint b len dst n) /\
  (cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
     loweringStateRelDefs$regions_disjoint off (type_memory_size tv) dst n) ==>
  extrequest_history_frame cenv cx ec sc tc ee sm q
Proof
  strip_tac >> irule extrequest_history_store_frame >>
  first_assum (irule_at (Pat `extrequest_history_frame _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexistsl_tac [`n`, `dst`] >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `local_region cenv ee.scopes t name b sz'` by
        metis_tac[extrequest_history_local_regions] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (b,sz')` by
        (fs[extrequest_history_frame_def] >> metis_tac[]) >>
      `aid <> live` by decide_tac >>
      fs[venomMemDefsTheory.allocas_non_overlapping_def,
         loweringStateRelDefsTheory.regions_disjoint_def] >>
      `b + sz' <= tuple_base \/ tuple_base + sz <= b` by metis_tac[] >> decide_tac) >>
  gvs[extrequest_history_frame_def,
      exprExtRequestReadProbeTheory.extrequest_read_frame_def] >> metis_tac[]
QED

Theorem extrequest_store_cell_code:
  (if is_word_type ty then emit_void MSTORE [dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src dst
   else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes cenv ty))])
      sa = ((),sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  Cases_on `is_word_type ty` >> simp[]
  >- (strip_tac >>
      drule exprLoweringPropsTheory.emit_void_same_blocks >> strip_tac >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  Cases_on `is_bytestring_type ty` >> simp[]
  >- (simp[contextTheory.compile_store_bytestring_def,
          contextTheory.compile_bytestring_copy_len_def,
          emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_return_def, compileEnvTheory.emit_def,
          compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def] >>
      strip_tac >> gvs[] >>
      `!m k:num. m - (m+k) = 0` by (rpt gen_tac >> decide_tac) >>
      pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
      simp[exprLoweringPropsTheory.same_blocks_def,
           exprLoweringPropsTheory.emitted_insts_def,
           listTheory.DROP_APPEND, arithmeticTheory.SUB_EQ_0,
           venomInstTheory.mk_inst_def,
           venomInstTheory.is_terminator_def]) >>
  strip_tac >>
      drule exprLoweringPropsTheory.emit_void_same_blocks >> strip_tac >>
      drule emitted_insts_emit_void >> strip_tac >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem extrequest_store_cell_memory_nondecreasing:
  (if is_word_type ty then emit_void MSTORE [dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src dst
   else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes cenv ty))])
      sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  val_wf tv v /\ expr_val_rel cx ty v src s /\
  type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  run_inst_seq (emitted_insts sa sb) s = OK q ==>
  LENGTH s.vs_memory <= LENGTH q.vs_memory
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[] >> drule_all expr_val_rel_typed >> strip_tac >>
      drule_all exprSimLiteralBufferTheory.literal_emit_mstore_run >>
      strip_tac >> gvs[] >>
      simp[venomMemPropsTheory.mstore_memory_nondecreasing]) >>
  Cases_on `is_bytestring_type ty`
  >- (gvs[] >>
      `?w. eval_operand src s = SOME w /\
           val_in_memory tv v (w2n w) s.vs_memory` by fs[expr_val_rel_def] >>
      drule_all buffer_typed_bytestring_header >> strip_tac >>
      `32 + 32 * word_size len < dimword (:256)` by
        (drule exprSimPropsTheory.val_store_size_le >> simp[] >> decide_tac) >>
      drule buffer_store_bytestring_run >>
      disch_then (qspecl_then [`s`, `w`, `d`, `len`] mp_tac) >>
      simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
      simp[venomExecSemanticsTheory.mcopy_def,
           venomMemPropsTheory.write_memory_with_expansion_nondecreasing]) >>
  gvs[] >>
  `?w. eval_operand src s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory` by fs[expr_val_rel_def] >>
  drule buffer_emit_mcopy_run >>
  disch_then (qspecl_then [`d`, `w`, `n2w (type_memory_bytes cenv ty)`, `s`] mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >> strip_tac >> gvs[] >>
  simp[venomExecSemanticsTheory.mcopy_def,
       venomMemPropsTheory.write_memory_with_expansion_nondecreasing]
QED

Theorem extrequest_store_cell_path:
  (if is_word_type ty then emit_void MSTORE [dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src dst
   else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes cenv ty))])
      sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  val_wf tv v /\ expr_val_rel cx ty v src s /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  (!name b sz. local_region cenv ee.scopes s name b sz ==>
     b + sz <= w2n d \/ w2n d + type_memory_size tv <= b) /\
  (cenv.ce_is_ctor ==> !name tv' v' off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv',v') ==>
     regions_disjoint off (type_memory_size tv') (w2n d) (type_memory_size tv)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
      stmt_state_rel ctx func cenv cx ee q /\
      val_in_memory tv v (w2n d) q.vs_memory /\ 
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH q.vs_memory /\
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all extrequest_store_cell_encoding >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by
    (drule_at (Pat `evaluate_type _ _ = _`)
       extrequest_store_cell_memory_nondecreasing >>
     disch_then drule >> disch_then drule >> simp[] >>
     disch_then drule >> simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ee q` by
    (irule buffer_store_state_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[] >>
     qexistsl_tac [`w2n d`, `type_memory_size tv`, `sa`] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule extrequest_store_cell_code >> strip_tac >>
  drule_all exprExtRequestMaterializeTheory.extrequest_straight_run_path >>
  strip_tac >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[venomStateTheory.lookup_var_def] >>
  `q.vs_halted = s.vs_halted /\ q.vs_current_bb = s.vs_current_bb /\
   (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
             vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  fs[exprLoweringPropsTheory.same_blocks_def,
     exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  metis_tac[venomStateTheory.lookup_var_def, arithmeticTheory.ADD_COMM]
QED
