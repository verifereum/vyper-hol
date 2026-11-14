(*
 * The joint (gas-origin and pointer-ghost) run of a Log statement's whole
 * data store, compile_log_store_data: per field the base-plus-offset ADD
 * and the field's store, into the data buffer's tuple layout.
 *
 * TOP-LEVEL:
 *   log_field_src_def -- what one data field needs before its store
 *   compile_log_store_data_origin_ptr_path -- the joint run of the store
 * Helper:
 *   log_field_src_frame -- a field's source survives a store into the buffer
 *   log_field_store_origin_ptr_path -- one field's store, word or not
 *   log_data_field_origin_ptr_path -- one field's ADD and store
 *)
Theory logStoreDataFieldsOriginPtr
Ancestors
  logStoreDataOriginPtr typedCopyOriginPtrFields typedCopyOriginPtrBase typedCopyOriginPtrBytes
  typedMemoryCopy fragGasOriginPtr fragGasOriginPtrDead bodyPtrDefs
  robustCopyTransportPtr ptrDiscipline stmtLowering eventLoweringStructure
  exprLoweringProps localValueStoreProps exprSimProps loweringShapeDefs
  fragExec valueEncoding valueEncodingDefs vyperValue compileEnv emitHelper
  venomState stmtSimLogDataFrame exprSimMemDefs allocationPtr
  exprSimAggregateChildren placeMemoryTypeInterfaces representationCleanPtr
  exprPtrUnwrapFacts valueCopyBytes valueEncodingProps typedLogFieldChecked
  bytesCopyProps vyperTypeSystem venomMemDefs memoryLocalRhsProps
  loweringPosts loweringStateRelDefs vyperTyping vyperEventArgCompat

(* A data field f = (operand, source type) about to be stored as dty into
   the buffer [b, b + cap): a word is the operand's value, clean; any other
   value sits robustly at a covered pointer outside the buffer. *)
Definition log_field_src_def:
  log_field_src cenv tenv b cap sa G tn s f dty dtv v <=>
    evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\ val_wf dtv v /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    (!x. FST f = Var x ==> not_fresh_at sa x) /\
    (is_word_type dty ==>
       eval_operand (FST f) s = SOME (typed_val_to_w256 dtv v) /\
       op_taint tn (FST f) = {}) /\
    (~is_word_type dty ==>
       ?xs stv sw. FST f = Var xs /\
         (is_bytestring_type dty ==> is_bytestring_type (SND f)) /\
         type_widens_to tenv (SND f) dty /\
         evaluate_type tenv (SND f) = SOME stv /\
         value_has_type stv v /\ val_wf stv v /\
         lookup_var xs s = SOME sw /\
         (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                val_in_memory stv v (w2n sw) mem) /\
         w2n sw + (if is_bytestring_type dty then val_store_size stv v
                   else type_memory_size stv) < dimword (:256) /\
         ((if is_bytestring_type dty then val_store_size stv v
           else type_memory_size stv) = 0 \/
          w2n sw + (if is_bytestring_type dty then val_store_size stv v
                    else type_memory_size stv) <= s.vs_alloca_next) /\
         (w2n sw + (if is_bytestring_type dty then val_footprint stv v
                   else type_memory_size stv) <= b \/ b + cap <= w2n sw) /\
         ptr_covers G tn xs s
           (if is_bytestring_type dty then val_store_size stv v
            else type_memory_size stv))
End

(* Logical capture and actual allocation ownership supply a physical store input. *)
Theorem log_field_src_from_capture:
  stmt_state_rel H ctx func cenv cx ee s /\
  expr_val_rel cx lty v op s /\
  expr_val_at cenv cx lty sa sb ee v op s /\
  expr_store_bound cx lty v op s /\
  ptr_val_ok cx lty v op G tn s /\
  evaluate_type (get_tenv cx) lty = SOME ltv /\
  value_has_type ltv v /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type stv v /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type dtv v /\
  assignable_type (get_tenv cx) dty /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  event_arg_compatible dty lty /\
  type_widens_to (get_tenv cx) sty dty /\
  (~is_word_type dty /\ ~is_bytestring_type dty ==> sty = lty) /\
  (!x. op = Var x ==> not_fresh_at packing_sa x) /\
  FLOOKUP s.vs_allocas dest = SOME (b,cap) /\
  sb.cs_next_id <= dest /\
  (!name a n. local_region cenv ee.scopes s name a n ==>
     a + n <= b \/ b + cap <= a) ==>
  log_field_src cenv (get_tenv cx) b cap packing_sa G tn s
    (op,sty) dty dtv v
Proof
  rpt strip_tac >>
  `val_wf ltv v /\ val_wf stv v /\ val_wf dtv v` by
    metis_tac[CONJUNCT1 typed_value_wf] >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  `allocas_non_overlapping s` by
    fs[stmt_state_rel_def, state_rel_def, alloca_inv_def] >>
  `log_source_apart cx b cap (op,lty) v s` by
    (mp_tac (Q.INST [`ty` |-> `lty`, `sm` |-> `sb`,
      `es` |-> `ee`, `n` |-> `cap`] log_allocated_source_apart) >>
     simp[] >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  Cases_on `is_word_type dty`
  >- (`dty = lty` by metis_tac[word_event_compatible_same] >>
      gvs[] >> simp[log_field_src_def] >> gvs[expr_val_rel_def]) >>
  `~is_word_type lty` by
    metis_tac[CONJUNCT1 event_arg_compatible_word_shape] >>
  `?sw. eval_operand op s = SOME sw` by gvs[expr_val_rel_def] >>
  `ptr_mem_ok cx lty v op G tn s` by fs[ptr_val_ok_def] >>
  Cases_on `is_bytestring_type dty`
  >- suspend "bytes" >>
  suspend "aggregate"
QED

Resume log_field_src_from_capture[bytes]:
  `is_bytestring_type lty` by metis_tac[event_arg_compatible_bytestring] >>
  `arg_type_fits sty dty` by fs[type_widens_to_def] >>
  `is_bytestring_type sty` by
    metis_tac[compileEnvTheory.arg_type_fits_bytestring_source] >>
  `val_footprint ltv v <> 0 /\ val_store_size ltv v <> 0` by
    (qspecl_then [`get_tenv cx`, `lty`, `ltv`] mp_tac bytestring_type_value >>
     simp[] >> strip_tac >> gvs[] >>
     Cases_on `v` >> gvs[value_has_type_def, val_footprint_def, val_store_size_def]) >>
  `val_store_size stv v = val_store_size ltv v /\
   val_footprint stv v = val_footprint ltv v` by
    metis_tac[bytestring_val_store_size_eq, bytestring_val_footprint_eq] >>
  `?xs. op = Var xs /\ ptr_covers G tn xs s (val_store_size ltv v)` by
    (mp_tac (Q.INST [`t` |-> `lty`, `tv` |-> `ltv`,
      `n` |-> `val_store_size ltv v`, `w` |-> `sw`] ptr_mem_ok_read_covers) >>
     simp[]) >>
  `lookup_var xs s = SOME sw` by gvs[eval_operand_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory ltv v (w2n sw) mem` by
    (fs[ptr_mem_ok_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `w2n sw + val_store_size ltv v <= s.vs_alloca_next` by
    (fs[expr_store_bound_def] >> metis_tac[]) >>
  `w2n sw + val_footprint stv v <= b \/ b + cap <= w2n sw` by
    (qpat_x_assum `log_source_apart _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [log_source_apart_def]) >>
     disch_then (qspecl_then [`ltv`, `sw`] mp_tac) >> simp[]) >>
  simp[log_field_src_def] >>
  qexistsl_tac [`xs`, `stv`, `sw`] >> asm_rewrite_tac [] >> decide_tac
QED

Resume log_field_src_from_capture[aggregate]:
  `sty = lty` by metis_tac[] >>
  `stv = ltv` by metis_tac[optionTheory.SOME_11] >>
  `~is_bytestring_type lty` by
    (fs[event_arg_compatible_alias_def] >>
     metis_tac[memoryLocalRhsPropsTheory.arg_type_fits_bytestring_target]) >>
  `0 < type_memory_size dtv` by
    (irule (CONJUNCT1 type_memory_size_pos) >>
     metis_tac[assignable_type_slot_size_pos]) >>
  `0 < type_memory_size stv` by
    metis_tac[type_widens_to_zero_memory_size, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  `val_footprint ltv v = type_memory_size stv` by
    metis_tac[evaluated_nonbytes_footprint] >>
  `?xs. op = Var xs /\ ptr_covers G tn xs s (type_memory_size stv)` by
    (mp_tac (Q.INST [`ty` |-> `lty`, `tv` |-> `ltv`,
      `m` |-> `type_memory_size stv`, `w` |-> `sw`]
      (SPEC_ALL ptr_val_ok_read_covers)) >> simp[] >>
     metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
  `lookup_var xs s = SOME sw` by gvs[eval_operand_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem` by
    (fs[ptr_mem_ok_def] >> metis_tac[]) >>
  `w2n sw <= w2n sw + type_memory_size stv - 1 /\
   w2n sw + type_memory_size stv - 1 < w2n sw + val_footprint ltv v` by
    decide_tac >>
  `w2n sw + type_memory_size stv - 1 < s.vs_alloca_next` by
    (mp_tac (Q.INST [`t` |-> `lty`, `tv` |-> `ltv`,
      `es` |-> `ee`, `w` |-> `sw`,
      `i` |-> `w2n (sw : bytes32) + type_memory_size stv - 1`]
      (SPEC_ALL expr_val_at_below_frontier)) >> simp[] >> gvs[] >> decide_tac) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by decide_tac >>
  `w2n sw + type_memory_size stv <= b \/ b + cap <= w2n sw` by
    (qpat_x_assum `log_source_apart _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [log_source_apart_def]) >>
     disch_then (qspecl_then [`ltv`, `sw`] mp_tac) >> simp[] >>
     gvs[] >> decide_tac) >>
  simp[log_field_src_def] >> gvs[] >> decide_tac
QED

Finalise log_field_src_from_capture

(* Helper: a store into a window of the buffer keeps every field source. *)
Theorem log_field_src_frame:
  log_field_src cenv tenv b cap sa G tn s f dty dtv v /\
  ci_mono sa sb /\ typed_copy_state_frame sa w len s t /\
  b <= w /\ w + len <= b + cap /\
  (!i. ~(w <= i /\ i < w + len) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!q. not_fresh_at sa q ==>
     FLOOKUP Gf q = FLOOKUP G q /\ op_taint tnf (Var q) = op_taint tn (Var q)) ==>
  log_field_src cenv tenv b cap sb Gf tnf t f dty dtv v
Proof
  simp[log_field_src_def] >> strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> res_tac >> res_tac)
  >- (strip_tac >> `eval_operand (FST f) t = eval_operand (FST f) s` by
        metis_tac[typed_copy_state_frame_operand] >>
      Cases_on `FST f` >> gvs[op_taint_def] >>
      metis_tac[op_taint_def]) >>
  strip_tac >>
  qpat_x_assum `~is_word_type dty ==> _` (fn th =>
    first_assum (assume_tac o MATCH_MP th)) >>
  pop_assum (qx_choosel_then [`xs`, `stv`, `sw`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `not_fresh_at sa xs` by metis_tac[] >>
  `lookup_var xs t = SOME sw` by gvs[typed_copy_state_frame_def] >>
  suspend "robust"
QED

Resume log_field_src_frame[robust]:
  qpat_assum `val_wf stv v`
    (assume_tac o MATCH_MP exprSimPropsTheory.val_footprint_le) >>
  qexistsl_tac [`xs`, `stv`, `sw`] >> simp[] >>
  Cases_on `is_bytestring_type dty` >> fs[] >>
  (conj_tac
  >- (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
        `{i | w <= i /\ i < w + len}`] >>
      simp[] >> gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
      rpt strip_tac >> TRY (first_x_assum irule) >> decide_tac) >>
  gvs[ptr_covers_def] >> metis_tac[])
QED

Finalise log_field_src_frame

(* Helper: one field's store at a covered destination inside the buffer,
   word or not. *)
Theorem log_field_store_origin_ptr_path:
  compile_store_memory cenv (FST f) (Var xd) dty (SND f) sa = ((),sb) /\
  log_field_src cenv tenv b cap sa G tn s f dty dtv v /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  not_fresh_at sa xd /\ lookup_var xd s = SOME dw /\
  b <= w2n dw /\ w2n dw + type_memory_size dtv <= b + cap /\
  b + cap < dimword (:256) /\ b + cap <= s.vs_alloca_next /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `log_field_src _ _ _ _ _ _ _ _ _ _ _ _`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac o REWRITE_RULE [log_field_src_def]) >>
  Cases_on `is_word_type dty`
  >- (`type_memory_size dtv = 32` by
        metis_tac[localValueStorePropsTheory.evaluated_word_memory_size] >>
      qpat_x_assum `is_word_type dty ==> _` (fn th =>
        first_assum (strip_assume_tac o MATCH_MP th)) >>
      qpat_x_assum `type_memory_size dtv = 32` (fn eq =>
        RULE_ASSUM_TAC (REWRITE_RULE [eq]) >> assume_tac eq) >>
      mp_tac (Q.INST [`src` |-> `FST (f : operand # type)`,
                     `sty` |-> `SND (f : operand # type)`]
        compile_store_memory_word_origin_ptr_path) >>
      impl_tac >- (rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC, (asm_rewrite_tac [] >> decide_tac)]) >>
      strip_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> asm_rewrite_tac []) >>
  qpat_x_assum `~is_word_type dty ==> _` (fn th =>
    first_assum (assume_tac o MATCH_MP th)) >>
  pop_assum (qx_choosel_then [`xs`, `stv`, `sw`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `not_fresh_at sa xs` by metis_tac[] >>
  qpat_x_assum `FST f = Var xs` (fn eq =>
    qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [eq]) >> assume_tac eq) >>
  Cases_on `is_bytestring_type dty`
  >- (fs[] >> (
      `compile_store_bytestring (Var xs) (Var xd) sa = ((),sb)` by
        gvs[contextTheory.compile_store_memory_def] >>
      mp_tac (Q.INST [`sty` |-> `SND (f : operand # type)`]
        (SPEC_ALL compile_store_bytestring_value_origin_ptr_path)) >>
      impl_tac >- (asm_rewrite_tac [] >> decide_tac) >>
      strip_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> simp[] >>
      gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
      first_assum ACCEPT_TAC)) >>
  fs[] >> (
  mp_tac (Q.INST [`sty` |-> `SND (f : operand # type)`]
    compile_store_memory_origin_ptr_path) >>
  impl_tac >- (asm_rewrite_tac [] >> decide_tac) >>
  strip_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> simp[])
QED

(* Helper: one field's base-plus-offset ADD and store. *)
Theorem log_data_field_origin_ptr_path:
  compile_log_store_data cenv [f] [dty] (Var xb) off sa = ((),sb) /\
  log_field_src cenv tenv (w2n bw) cap sa G tn s f dty dtv v /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  not_fresh_at sa xb /\ lookup_var xb s = SOME bw /\
  ptr_covers G tn xb s cap /\ off + type_memory_size dtv <= cap /\
  w2n bw + cap < dimword (:256) /\ w2n bw + cap <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    typed_copy_state_frame sa (w2n bw + off) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n bw + off <= i /\ i < w2n bw + off + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n bw + off) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_log_store_data _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_log_store_data_def, comp_bind_def, comp_ignore_bind_def,
       compile_log_store_data_def, comp_return_def] >>
  Cases_on `emit_op ADD [Var xb; Lit (n2w off)] sa` >>
  rename1 `emit_op ADD _ sa = (dst,s1)` >> simp[] >>
  Cases_on `compile_store_memory cenv (FST f) dst dty (SND f) s1` >>
  rename1 `compile_store_memory _ _ dst _ _ s1 = (u,s2)` >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `compile_store_memory _ _ dst _ _ s1 = (_,sb)` >>
  suspend "add"
QED

Resume log_data_field_origin_ptr_path[add]:
  `ci_mono sa s1` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono s1 sb` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `w2n bw + off < dimword (:256)` by decide_tac >>
  mp_tac (Q.SPECL [`xb`, `off`, `type_memory_size dtv`, `cap`, `sa`, `dst`,
    `s1`, `bw`, `lo`, `explicit`, `ctx`, `func`, `PG`, `s`, `G`, `tn`,
    `w2n (bw:bytes32) + off`, `type_memory_size dtv`]
    typed_copy_origin_ptr_add_path) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac]) >>
  disch_then (qx_choosel_then [`p`, `t1`, `G1`, `tn1`] strip_assume_tac) >>
  gvs[] >>
  `w2n (n2w (w2n (bw:bytes32) + off) : bytes32) = w2n bw + off` by
    (rewrite_tac [wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >>
     decide_tac) >>
  `log_field_src cenv tenv (w2n bw) cap s1 G1 tn1 t1 f dty dtv v` by
    (irule log_field_src_frame >>
     qexistsl_tac [`G`, `type_memory_size dtv`, `s`, `sa`, `tn`, `w2n bw + off`] >>
     simp[] >> decide_tac) >>
  suspend "store"
QED

Resume log_data_field_origin_ptr_path[store]:
  mp_tac (Q.INST [`sa` |-> `s1`, `G` |-> `G1`, `tn` |-> `tn1`, `s` |-> `t1`,
    `xd` |-> `p`, `dw` |-> `n2w (w2n (bw:bytes32) + off)`,
    `b` |-> `w2n (bw:bytes32)`]
    log_field_store_origin_ptr_path) >>
  impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, (asm_rewrite_tac [] >> decide_tac),
           (gvs[allocas_from_def] >> NO_TAC)]) >>
  disch_then (qx_choosel_then [`t2`, `G2`, `tn2`] strip_assume_tac) >>
  qexistsl_tac [`t2`, `G2`, `tn2`] >>
  RULE_ASSUM_TAC (REWRITE_RULE [ASSUME
    ``w2n (n2w (w2n (bw:bytes32) + off) : bytes32) = w2n bw + off``]) >>
  conj_tac
  >- (gen_tac >>
      `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t1,G1,tn1)` by
        (irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
      pop_assum (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
      disch_then (qspecl_then [`t1`, `G1`, `tn1`, `[]`, `OK t2`, `G2`, `tn2`]
        mp_tac) >> simp[]) >>
  conj_tac
  >- (irule typed_copy_state_frame_trans >> qexists_tac `t1` >> simp[] >>
      irule typed_copy_state_frame_mono >> qexists_tac `s1` >> simp[] >>
      qpat_x_assum `typed_copy_state_frame s1 _ _ t1 _` mp_tac >> simp[]) >>
  ntac 6 (conj_tac >- simp[]) >>
  conj_tac
  >- (qpat_x_assum `!i. _ ==> (_ IN tn2.t_mem <=> _)` mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!mem. mem_agree_outside tn2.t_mem _ _ ==> _` mp_tac >>
      simp[]) >>
  rpt strip_tac >>
  `not_fresh_at s1 p'` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  simp[]
QED

Finalise log_data_field_origin_ptr_path


(* TOP-LEVEL: the joint run of a Log statement's data store: from offset
   off on, the buffer holds the fields' tuple robustly. *)
Theorem compile_log_store_data_origin_ptr_path:
  !fs dtys dtvs vs off sa sb s G tn.
  compile_log_store_data cenv fs dtys (Var xb) off sa = ((),sb) /\
  LENGTH dtys = LENGTH fs /\ LENGTH dtvs = LENGTH fs /\ LENGTH vs = LENGTH fs /\
  (!i. i < LENGTH fs ==>
     log_field_src cenv tenv (w2n bw) cap sa G tn s (EL i fs) (EL i dtys)
       (EL i dtvs) (EL i vs)) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  not_fresh_at sa xb /\ lookup_var xb s = SOME bw /\
  ptr_covers G tn xb s cap /\ off + type_memory_size_list dtvs <= cap /\
  w2n bw + cap < dimword (:256) /\ w2n bw + cap <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    typed_copy_state_frame sa (w2n bw + off) (type_memory_size_list dtvs) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n bw + off <= i /\ i < w2n bw + off + type_memory_size_list dtvs) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           tuple_in_memory vs dtvs (w2n bw + off) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[listTheory.LENGTH_NIL] >>
      gvs[compile_log_store_data_def, comp_return_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >>
      simp[gas_origin_ptr_path_rules, val_in_memory_def]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  namedCases_on `dtys` ["", "dty dtys"] >> gvs[] >>
  namedCases_on `dtvs` ["", "dtv dtvs"] >> gvs[] >>
  namedCases_on `vs` ["", "v vs"] >> gvs[] >>
  rename1 `compile_log_store_data cenv (f::fs) (dty::dtys) _ _ _ = _` >>
  rename1 `tuple_in_memory (v::vs) (dtv::dtvs) _ _` >>
  qpat_x_assum `compile_log_store_data _ _ _ _ _ _ = _`
    (strip_assume_tac o ONCE_REWRITE_RULE [compile_log_store_data_split]) >>
  rename1 `compile_log_store_data cenv [f] [dty] _ off sa = ((),mid)` >>
  `log_field_src cenv tenv (w2n bw) cap sa G tn s f dty dtv v` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `!i. i < LENGTH fs ==>
     log_field_src cenv tenv (w2n bw) cap sa G tn s (EL i fs) (EL i dtys)
       (EL i dtvs) (EL i vs)` by
    (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  qpat_x_assum `!i. i < SUC _ ==> _` kall_tac >>
  suspend "field"
QED

Resume compile_log_store_data_origin_ptr_path[field]:
  `type_memory_size_list (dtv::dtvs) =
     type_memory_size dtv + type_memory_size_list dtvs` by
    simp[type_memory_size_def] >>
  `ci_mono sa mid /\ ci_mono mid sb` by
    metis_tac[compile_log_store_data_ci_mono, pairTheory.SND] >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    fs[log_field_src_def] >>
  mp_tac (Q.INST [`sb` |-> `mid`] log_data_field_origin_ptr_path) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac]) >>
  disch_then (qx_choosel_then [`t1`, `G1`, `tn1`] strip_assume_tac) >>
  `lookup_var xb t1 = SOME bw /\ t1.vs_allocas = s.vs_allocas /\
   t1.vs_alloca_next = s.vs_alloca_next` by
    gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `not_fresh_at mid xb` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  `ptr_covers G1 tn1 xb t1 cap` by (gvs[ptr_covers_def] >> metis_tac[]) >>
  `allocas_from lo t1` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     pure_rewrite_tac [allocas_from_def] >> asm_rewrite_tac []) >>
  `!i. i < LENGTH fs ==>
     log_field_src cenv tenv (w2n bw) cap mid G1 tn1 t1 (EL i fs) (EL i dtys)
       (EL i dtvs) (EL i vs)` by
    (rpt strip_tac >> irule log_field_src_frame >>
     qexistsl_tac [`G`, `type_memory_size dtv`, `s`, `sa`, `tn`,
                   `w2n bw + off`] >>
     simp[] >> decide_tac) >>
  suspend "rest"
QED

Resume compile_log_store_data_origin_ptr_path[rest]:
  qpat_x_assum `type_memory_bytes cenv dty = _` (fn eq =>
    RULE_ASSUM_TAC (REWRITE_RULE [eq]) >> assume_tac eq) >>
  first_x_assum (qspecl_then [`dtys`, `dtvs`, `vs`, `off + type_memory_size dtv`,
    `mid`, `sb`, `t1`, `G1`, `tn1`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac]) >>
  disch_then (qx_choosel_then [`t2`, `G2`, `tn2`] strip_assume_tac) >>
  qexistsl_tac [`t2`, `G2`, `tn2`] >>
  conj_tac
  >- (gen_tac >>
      qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
        (mp_tac o MATCH_MP gas_origin_ptr_path_append o Q.SPEC `D`) >>
      disch_then (qspecl_then [`t1`, `G1`, `tn1`, `[]`, `OK t2`, `G2`, `tn2`]
        mp_tac) >> simp[]) >>
  conj_tac
  >- (irule typed_copy_state_frame_trans >> qexists_tac `t1` >> conj_tac
      >- (irule typed_copy_state_frame_subinterval >>
          qexistsl_tac [`w2n bw + off`, `type_memory_size dtv`] >> simp[]) >>
      irule typed_copy_state_frame_subinterval >>
      qexistsl_tac [`w2n bw + (off + type_memory_size dtv)`,
                    `type_memory_size_list dtvs`] >> simp[] >>
      irule typed_copy_state_frame_mono >> qexists_tac `mid` >> simp[] >>
      qpat_x_assum `typed_copy_state_frame mid _ _ t1 _` mp_tac >> simp[]) >>
  ntac 6 (conj_tac >- simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. _ ==> (_ IN tn2.t_mem <=> _ IN tn1.t_mem)`
        (qspec_then `i` mp_tac) >>
      qpat_x_assum `!i. _ ==> (_ IN tn1.t_mem <=> _ IN tn.t_mem)`
        (qspec_then `i` mp_tac) >>
      simp[]) >>
  conj_tac >- suspend "tuple" >>
  rpt strip_tac >>
  `not_fresh_at mid p` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  simp[]
QED

Resume compile_log_store_data_origin_ptr_path[tuple]:
  `val_wf dtv v` by fs[log_field_src_def] >>
  qpat_assum `val_wf dtv v`
    (assume_tac o MATCH_MP exprSimPropsTheory.val_footprint_le) >>
  `!mem. mem_agree_outside tn2.t_mem t2.vs_memory mem ==>
     val_in_memory dtv v (w2n bw + off) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`t1.vs_memory`, `t2.vs_memory`, `tn1.t_mem`, `tn2.t_mem`,
       `{i | w2n bw + (off + type_memory_size dtv) <= i /\
             i < w2n bw + (off + type_memory_size dtv) +
                 type_memory_size_list dtvs}`] >>
     simp[] >> gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> simp[Once val_in_memory_def] >>
  `w2n bw + (off + type_memory_size dtv) = w2n bw + off + type_memory_size dtv` by
    decide_tac >>
  gvs[]
QED

Finalise compile_log_store_data_origin_ptr_path
