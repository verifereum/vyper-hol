Theory bodyFullAppendNestedFrames
Ancestors
  keyUpdateFold[qualified,ignore_grammar]
  appendStorageStageTransportPtr fragGasSeqPtrContext fragGasCopyLoop fragGasCopySeqLiftProps
  appendStorageAggregateRel[qualified,ignore_grammar]
  bodyFullStoreSlotsStatic[qualified,ignore_grammar]
  stmtReasonLitFragMemory exprLoweringProps venomInst venomState fragGasSeqPtr
  contextCodegenRel fragExecMem fragExec ptrSafeRun
  placeStoreSlots placeStoreStorage accountsRelProps
  vyperStorageAccessFrame vyperStorageFootprint vyperStoragePlaceRegion
  vyperStorageWritePreservation
  vyperLookupStorage vyperEncodeDecode loweringStateRelDefs ptrDiscipline
  vyperStorageFrame vyperStorage vyperValue words pred_set list arithmetic vfmState

Theorem append_observed_child:
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n (slot:bytes32) = w2n (rootk:bytes32) + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  0 < type_slot_size tv /\ len < cap /\
  k = slot + n2w (1+len*type_slot_size tv) ==>
  storage_subregion root (path ++ [ValueSubscript (IntV (&len))])
    (delta+(1+len*type_slot_size tv)) tv /\
  w2n k = w2n rootk + (delta+(1+len*type_slot_size tv)) /\
  w2n k + type_slot_size tv <= dimword (:256)
Proof
  strip_tac >>
  `storage_subregion (ArrayTV tv (Dynamic cap)) [ValueSubscript (IntV (&len))]
    (1+len*type_slot_size tv) tv` by
    (simp[Once vyperStoragePlaceRegionTheory.storage_subregion_def] >>
     simp[Once vyperStoragePlaceRegionTheory.storage_subregion_def] >> decide_tac) >>
  drule_all_then assume_tac vyperStoragePlaceRegionTheory.storage_subregion_append >>
  `delta+(1+len*type_slot_size tv) + type_slot_size tv <= type_slot_size root` by
    (irule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> metis_tac[]) >>
  `1+len*type_slot_size tv < dimword (:256) /\
    w2n slot + (1+len*type_slot_size tv) < dimword (:256)` by decide_tac >>
  `w2n k = w2n slot + (1+len*type_slot_size tv)` by
    simp[wordsTheory.word_add_def,wordsTheory.w2n_n2w] >> simp[] >> decide_tac
QED

Theorem append_subregion_header_storage_dead:
  MEM (tr,(rootk:bytes32),root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta ==>
  (storage_dead H tr (update_storage slot h st) j b <=> storage_dead H tr st j b)
Proof
  strip_tac >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `w2n rootk + type_slot_size root <= dimword (:256)` by
    metis_tac[vyperStorageFootprintTheory.regions_consistent_def] >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256)` by decide_tac >>
  Cases_on `w2n slot <= j /\ j < w2n slot + type_slot_size (ArrayTV tv (Dynamic cap))`
  >- (`!raw. storage_dead H tr raw j b <=>
          dead_bytes raw (w2n slot) (ArrayTV tv (Dynamic cap)) j b` by
        (gen_tac >>
         mp_tac (Q.INST [`rootk` |-> `(rootk:bytes32)`, `root` |-> `root`,
           `path` |-> `path`, `delta` |-> `delta`, `tv` |-> `ArrayTV tv (Dynamic cap)`,
           `start` |-> `w2n (slot:bytes32)`, `st` |-> `raw`]
           bodyFullStoreSlotsStaticTheory.store_slots_subregion_dead_iff) >> simp[]) >>
      simp[] >>
      mp_tac (Q.INST [`slot` |-> `(slot:bytes32)`, `h` |-> `h`,
        `st` |-> `st`, `tv` |-> `tv`, `cap` |-> `cap`, `j` |-> `j`, `b` |-> `b`]
        appendStorageAggregateRelTheory.append_aggregate_header_dead) >> simp[]) >>
  `!q. ~(w2n rootk + delta <= w2n q /\
      w2n q < w2n rootk + delta + type_slot_size (ArrayTV tv (Dynamic cap))) ==>
     lookup_storage q (update_storage slot h st) = lookup_storage q st` by
    (rpt strip_tac >> `q <> slot` by
       (strip_tac >> gvs[vyperValueTheory.type_slot_size_def]) >>
     simp[vfmStateTheory.lookup_storage_def,vfmStateTheory.update_storage_def,combinTheory.APPLY_UPDATE_THM]) >>
  `!before after.
     (!q. ~(w2n rootk + delta <= w2n q /\
          w2n q < w2n rootk + delta + type_slot_size (ArrayTV tv (Dynamic cap))) ==>
       lookup_storage q after = lookup_storage q before) /\
     storage_dead H tr before j b ==>
     storage_dead H tr after j b` by
    (rpt strip_tac >> irule placeStoreStorageTheory.place_store_storage_dead_subregion_frame >>
     goal_assum (drule_at (Pat `MEM (_,_,_) (FST _)`)) >>
     qexistsl_tac [`delta`,`ArrayTV tv (Dynamic cap)`,`path`,`before`] >>
     asm_rewrite_tac[] >>
     conj_tac
     >- (qpat_assum `w2n slot = _` (fn th => rewrite_tac[GSYM th]) >>
         first_assum ACCEPT_TAC) >>
     simp[vyperValueTheory.type_slot_size_def]) >>
  metis_tac[]
QED

Theorem append_subregion_sparse_keys_dead:
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\ w2n rootk + type_slot_size root <= dimword (:256) /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
  len < cap /\ k = slot+n2w (1+len*type_slot_size tv) /\
  encode_value tv v = SOME writes /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  X SUBSET {(q,b) | storage_dead H tr st (w2n q) b} /\
  (!j b. j < type_slot_size tv /\ b < 32 /\ MEM j (MAP FST writes) /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b ==>
    off+32*j+b NOTIN M) ==>
  key_update
    (FOLDL (\Y j. key_update Y (k+n2w j) (mem_word_taint M (off+32*j))) X ks)
    slot {} SUBSET
  {(q,b) | storage_dead H tr
    (update_storage slot h (apply_writes k writes st)) (w2n q) b}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac append_observed_child >>
  `!i. MEM i (MAP FST writes) ==> i < type_slot_size tv` by
    metis_tac[cj 1 vyperEncodeDecodeTheory.encode_writes_bounded] >>
  `!i. i < type_slot_size tv ==> w2n (k+n2w i) = w2n k+i` by
    (rpt strip_tac >>
     `i < dimword (:256) /\ w2n k+i < dimword (:256)` by decide_tac >>
     simp[wordsTheory.word_add_def,wordsTheory.w2n_n2w]) >>
  `!raw j b. storage_dead H tr (update_storage slot h raw) j b <=> storage_dead H tr raw j b` by
    (rpt gen_tac >>
     mp_tac (Q.INST [`H` |-> `H`,`tr` |-> `tr`,`rootk` |-> `(rootk:bytes32)`,
       `root` |-> `root`,`path` |-> `path`,`delta` |-> `delta`,`tv` |-> `tv`,
       `cap` |-> `cap`,`slot` |-> `(slot:bytes32)`,`st` |-> `raw`,`h` |-> `h`]
       append_subregion_header_storage_dead) >> simp[]) >>
  `!raw j b. w2n k <= j /\ j < w2n k + type_slot_size tv ==>
    (storage_dead H tr raw j b <=> dead_bytes raw (w2n k) tv j b)` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`H` |-> `H`,`tr` |-> `tr`,`rootk` |-> `(rootk:bytes32)`,
       `root` |-> `root`,`path` |-> `path ++ [ValueSubscript (IntV (&len))]`,
       `delta` |-> `delta + (1+len*type_slot_size tv)`,`tv` |-> `tv`,
       `start` |-> `w2n (k:bytes32)`,`st` |-> `raw`]
       bodyFullStoreSlotsStaticTheory.store_slots_subregion_dead_iff) >> simp[]) >>
  simp_tac (srw_ss()) [pred_setTheory.SUBSET_DEF,pairTheory.FORALL_PROD,Once ptrDisciplineTheory.key_update_def] >>
  qx_genl_tac [`q`,`b`] >> strip_tac >>
  qpat_x_assum `!raw j b. storage_dead H tr (update_storage slot h raw) j b <=> _`
    (fn th => rewrite_tac[th]) >>
  qspecl_then [`\j. k+n2w j`, `\j. mem_word_taint M (off+32*j)`]
    (drule o BETA_RULE) keyUpdateFoldTheory.key_update_fold_cases >> strip_tac
  >- suspend "retained" >> suspend "written"
QED

Resume append_subregion_sparse_keys_dead[retained]:
  `storage_dead H tr st (w2n q) b` by
    (qpat_x_assum `X SUBSET _` mp_tac >>
     simp_tac (srw_ss()) [pred_setTheory.SUBSET_DEF, pairTheory.FORALL_PROD] >>
     disch_then drule >> simp[]) >>
  Cases_on `w2n k <= w2n q /\ w2n q < w2n k+type_slot_size tv`
  >- suspend "retained_inside" >>
  `!a. ~(w2n k <= w2n a /\ w2n a < w2n k+type_slot_size tv) ==>
    lookup_storage a (apply_writes k writes st) = lookup_storage a st` by
    (rpt strip_tac >> irule vyperStorageAccessFrameTheory.apply_writes_word_frame >>
     rpt strip_tac >> rename1 `MEM j (MAP FST writes)` >>
     `j < type_slot_size tv` by metis_tac[] >>
     `w2n (k+n2w j) = w2n k+j` by metis_tac[] >>
     qpat_x_assum `_ = k+n2w j` SUBST_ALL_TAC >> decide_tac) >>
  mp_tac (Q.SPECL [`H`,`tr`,`rootk`,`root`,
    `path ++ [ValueSubscript (IntV (&len))]`,`delta + (1+len*type_slot_size tv)`,
    `tv`,`st`,`apply_writes k writes st`,`w2n (q:bytes32)`,`b`]
      (INST_TYPE [alpha |-> ``:256``]
        placeStoreStorageTheory.place_store_storage_dead_subregion_frame)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    qpat_assum `w2n k = _` (fn th => rewrite_tac[GSYM th]) >>
    first_assum ACCEPT_TAC) >>
  simp[]
QED

Resume append_subregion_sparse_keys_dead[retained_inside]:
  qabbrev_tac `d = w2n q-w2n k` >>
  `d < type_slot_size tv /\ w2n q = w2n k+d` by
    (simp[Abbr `d`] >> decide_tac) >>
  `q = k+n2w d` by metis_tac[wordsTheory.w2n_11] >>
  `~MEM d (MAP FST writes)` by metis_tac[] >>
  `dead_bytes st (w2n k) tv (w2n q) b` by metis_tac[] >>
  `b < 32` by metis_tac[cj 1 accountsRelPropsTheory.dead_bytes_range] >>
  `dead_bytes (apply_writes k writes st) (w2n k) tv (w2n q) b` by
    (spose_not_then assume_tac >>
     mp_tac (Q.SPECL [`tv`,`v`,`writes`,`st`,`w2n (k:bytes32)`,`d`,`b`]
       placeStoreSlotsTheory.place_store_unwritten_live_preserved) >>
     qpat_assum `w2n q = w2n k+d` (fn th => rewrite_tac[GSYM th,wordsTheory.n2w_w2n]) >>
     asm_rewrite_tac[]) >>
  metis_tac[]
QED

Resume append_subregion_sparse_keys_dead[written]:
  `MEM j (MAP FST writes) /\ j < type_slot_size tv` by metis_tac[] >>
  `b < 32 /\ off+32*j+b IN M` by fs[ptrDisciplineTheory.mem_word_taint_def] >>
  `dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b` by metis_tac[] >>
  `w2n q = w2n k+j` by metis_tac[] >>
  `w2n k <= w2n q /\ w2n q < w2n k+type_slot_size tv` by decide_tac >>
  metis_tac[]
QED

Finalise append_subregion_sparse_keys_dead

Theorem append_sparse_keys_dead_subset:
  !H tr slot tv cap len k v writes off M X ks st.
    MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
    len = w2n (lookup_storage slot st) /\ len < cap /\
    k = slot+n2w (1+len*type_slot_size tv) /\
    encode_value tv v = SOME writes /\
    (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
    X SUBSET {(q,b) | storage_dead H tr st (w2n q) b} /\
    (!j b. j < type_slot_size tv /\ b < 32 /\ MEM j (MAP FST writes) /\
      ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b
      ==> off+32*j+b NOTIN M) ==>
    key_update
      (FOLDL (\Y j. key_update Y (k+n2w j) (mem_word_taint M (off+32*j))) X ks)
      slot {} SUBSET
    {(q,b) | storage_dead H tr
      (update_storage slot (n2w (len+1)) (apply_writes k writes st)) (w2n q) b}
Proof
  rpt gen_tac >> strip_tac >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256)` by
    metis_tac[regions_consistent_def] >>
  mp_tac (Q.INST [`rootk` |-> `slot`, `root` |-> `ArrayTV tv (Dynamic cap)`,
    `path` |-> `[]`, `delta` |-> `0`, `h` |-> `n2w (len+1)`]
    append_subregion_sparse_keys_dead) >>
  simp[storage_subregion_def]
QED

(* This prefix neither allocates nor calls; the canonical context-restoration
   boundary therefore upgrades its existing pointer certificate. *)
Theorem append_guard_conditional_code[local]:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  emit_void ASSERT [valid] st2 = ((),st3) ==>
  st3.cs_current_bb = st0.cs_current_bb /\
  st3.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 st3 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st0 st3) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode /\ i.inst_opcode <> SETFMP /\
    i.inst_opcode <> DALLOCA) (emitted_insts st0 st3) /\
  (!s. run_inst_seq_mem_ok (emitted_insts st0 st3) s)
Proof
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
    compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
    compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  Cases_on `tr` >>
  simp[mk_inst_def, is_terminator_def, is_alloca_op_def] >>
  gen_tac >> irule fragExecMemTheory.run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def] >>
  rpt conj_tac >> irule instMemFrontierTheory.below_frontier_no_ranges >>
  simp[mk_inst_def]
QED

Theorem append_storage_guard_conditional_uniform:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  emit_void ASSERT [valid] st2 = ((),st3) /\
  eval_operand bop s = SOME slot /\
  (!x. bop = Var x ==> not_fresh_at st0 x) /\ cap < dimword (:256) /\
  w2n (if tr then tload slot s else sload slot s) < cap /\
  op_taint tn bop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  fn_has_code st0 st3 func /\ s.vs_current_bb = st0.cs_current_bb /\
  s.vs_inst_idx = LENGTH st0.cs_current_insts ==>
  ?t Gf tf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH st3.cs_current_insts),Gf,tf)) /\
    run_inst_seq (emitted_insts st0 st3) s = OK t /\
    state_frame t = state_frame s /\
    eval_operand lop t = SOME (if tr then tload slot s else sload slot s) /\
    op_taint tf lop = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at st0 x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ctx_has_dalloca (ctx with ctx_functions := []) ==> allocas_below_fmp s`
    by simp[ctx_has_dalloca_def] >>
  drule_all (Q.INST [`ctx` |-> `ctx with ctx_functions := []`]
    append_storage_guard_actual) >>
  disch_then (qspecl_then [`func`,`PG`,`G`,`ARB`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st0 st3) s = OK t` >>
  rename1 `op_taint tf lop = {}` >>
  rename1 `!k. inst_seq_ptr ARB 0 (ctx with ctx_functions := []) func PG G tn
    (emitted_insts st0 st3) (s with vs_inst_idx := k) Gf tf` >>
  drule_all append_guard_conditional_code >> strip_tac >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st0 st3) s Gf tf`
    by suspend "pointer" >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st0 st3) (DROP s.vs_inst_idx bb.bb_instructions)`
    by metis_tac[fn_has_code_code] >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> reverse conj_tac
  >- (asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >>
  `LENGTH st3.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts st0 st3)`
    by metis_tac[LENGTH_APPEND] >>
  qpat_x_assum `LENGTH st3.cs_current_insts = _`
    (fn th => pure_once_rewrite_tac[th]) >>
  `ctx_has_dalloca ctx ==> !pre i post u.
    emitted_insts st0 st3 = pre ++ [i] ++ post /\ run_inst_seq pre s = OK u ==>
    unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts st0 st3)` by simp[] >> fs[EVERY_MEM]) >>
  irule (cj 1 run_inst_seq_origin_ptr_lift) >> simp[] >>
  conj_tac
  >- first_assum ACCEPT_TAC >>
  gvs[]
QED

Resume append_storage_guard_conditional_uniform[pointer]:
  gen_tac >>
  drule_all append_storage_guard_actual >>
  disch_then (qspecl_then [`func`,`PG`,`G`,`D`] strip_assume_tac) >>
  `G' = Gf /\ tn' = tf` by metis_tac[inst_seq_ptr_ghost_unique] >>
  gvs[] >> irule inst_seq_ptr_restore_ctx >> simp[] >>
  first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]
QED
Finalise append_storage_guard_conditional_uniform

Theorem append_storage_guard_abort_conditional_uniform:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  emit_void ASSERT [valid] st2 = ((),st3) /\
  eval_operand bop s = SOME slot /\
  (!x. bop = Var x ==> not_fresh_at st0 x) /\ cap < dimword (:256) /\
  ~(w2n (if tr then tload slot s else sload slot s) < cap) /\
  op_taint tn bop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  fn_has_code st0 st3 func /\ s.vs_current_bb = st0.cs_current_bb /\
  s.vs_inst_idx = LENGTH st0.cs_current_insts ==>
  ?t j Gf tf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (t with vs_inst_idx := j),Gf,tf)) /\
    run_inst_seq (emitted_insts st0 st3) s = Abort Revert_abort t /\
    op_taint tf lop = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at st0 x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ctx_has_dalloca (ctx with ctx_functions := []) ==> allocas_below_fmp s`
    by simp[ctx_has_dalloca_def] >>
  drule_all (Q.INST [`ctx` |-> `ctx with ctx_functions := []`]
    append_storage_guard_abort_actual) >>
  disch_then (qspecl_then [`func`,`PG`,`G`,`ARB`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st0 st3) s = Abort Revert_abort t` >>
  rename1 `op_taint tf lop = {}` >>
  rename1 `!k. inst_seq_ptr ARB 0 (ctx with ctx_functions := []) func PG G tn
    (emitted_insts st0 st3) (s with vs_inst_idx := k) Gf tf` >>
  drule_all append_guard_conditional_code >> strip_tac >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st0 st3) s Gf tf`
    by suspend "pointer" >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st0 st3) (DROP s.vs_inst_idx bb.bb_instructions)`
    by metis_tac[fn_has_code_code] >>
  `run_inst_seq_mem_ok (emitted_insts st0 st3) s` by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts st0 st3)` by fs[EVERY_MEM] >>
  `ctx_has_dalloca ctx ==> !pre i post u.
    emitted_insts st0 st3 = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts st0 st3)` by simp[] >> fs[EVERY_MEM]) >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >> strip_tac >>
  qexistsl_tac [`t`,`j`,`Gf`,`tf`] >> reverse conj_tac
  >- (asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> first_x_assum irule >>
  irule inst_seq_ptr_lower_bound_transport >>
  simp[] >> conj_tac >- fs[EVERY_MEM] >> qexists_tac `0` >> simp[]
QED

Resume append_storage_guard_abort_conditional_uniform[pointer]:
  gen_tac >>
  drule_all append_storage_guard_abort_actual >>
  disch_then (qspecl_then [`func`,`PG`,`G`,`D`] strip_assume_tac) >>
  `G' = Gf /\ tn' = tf` by metis_tac[inst_seq_ptr_ghost_unique] >>
  gvs[] >> irule inst_seq_ptr_restore_ctx >> simp[] >>
  first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]
QED
Finalise append_storage_guard_abort_conditional_uniform
