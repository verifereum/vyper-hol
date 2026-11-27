(* Joint storage continuations for aggregate Assign. *)
Theory bodyFullAssignTopCopyTail
Ancestors
  keyUpdateFold[qualified,ignore_grammar]
  stmtSimAssignStorage augAssignFullStore augAssignFullStoreGhost
  bodyMemoryDefs bodySimFull gasOutcomeFull gasOutcomeFullCompose accountsRelProps stmtSimProps
  allocaHistory exprLoweringProps vyperTyping loweringPosts stmtSimDefs
  vyperStorageFootprint vyperStorageBackend vyperState emitHelper
  compileEnv context emitHelperProps venomInst loweringStateRelDefs stmtSimDeclMem
  entryDecoderHistoryFrame fragExec venomExecSemantics venomState bodyPtrDefs ptrDiscipline
  list finite_map pred_set bodyFullHashKeccakFixed loweringHalt
  vyperEncodeDecode[qualified,ignore_grammar] vyperStorageAccessFrame[qualified,ignore_grammar] bodyFullStoreSlotsPath bodyFullStoreSlotsStatic bodyFullStoreSlotsFrame bodyFullPathHistory
  bodyFullGhostFrame placeStoreStorage haltExitProj stmtSimStoreCopy stateRelProj stateRelProjStorage
  exprSimDefs[qualified,ignore_grammar] placeStoreSlots[qualified,ignore_grammar] representationCleanPtr[qualified,ignore_grammar] sourceUnitExecution[qualified,ignore_grammar] valueEncodingDefs[qualified,ignore_grammar] valueEncodingProofs[qualified,ignore_grammar]
  valueEncodingProps[qualified,ignore_grammar] venomMemProofs[qualified,ignore_grammar] vyperStorage[qualified,ignore_grammar] vyperStorageFrame[qualified,ignore_grammar] vyperStoragePlaceRegion[qualified,ignore_grammar] vyperTypeValues[qualified,ignore_grammar]
  exprSimHypsDefs[qualified]

Theorem body_assign_slots_full_static_exit:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
                            sz = type_memory_size rt) fields) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  cx.txn.is_static /\
  (type_slot_size tv = 0 ==>
    local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    sa.cs_next_var <= sb.cs_next_var /\ return_buf_frame d cenv sa s /\
    alloca_history func s /\ alloca_inv s) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        ((if type_slot_size tv = 0 then OK t
          else Abort ExHalt_abort (halt_state (set_returndata [] t))),Gf,tnf)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ tnf.t_mem = tn.t_mem /\
    t.vs_call_ctx.cc_static /\
    (type_slot_size tv = 0 ==>
     ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     return_buf_frame d cenv sb t /\ alloca_history func t /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     (!H. stmt_state_rel H ctx func cenv cx ee s ==>
          stmt_state_rel H ctx func cenv cx ee t) /\
     (!D. ghost_inv_at D lo d cenv cx ee G tn s ==>
          ghost_inv_at D lo d cenv cx ee Gf tnf t)) /\
    (type_slot_size tv <> 0 ==>
     (?bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb t.vs_inst_idx = SOME inst /\
       inst.inst_opcode = (if tr then TSTORE else SSTORE) /\
       step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))) /\
     write_storage_slot cx tr dw tv v ee =
       (INR (Error (RuntimeError "write in static context")),ee) /\
     exit_result (Abort ExHalt_abort (halt_state (set_returndata [] t))) /\
     (!H tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail)
       (INR (Error (RuntimeError "write in static context"))) tnf
       (Abort ExHalt_abort (halt_state (set_returndata [] t)))) /\
     (!H. halt_exit H cx ee (INR (Error (RuntimeError "write in static context")))
       (Abort ExHalt_abort (halt_state (set_returndata [] t)))) /\
     (ctx_has_dalloca ctx ==>
      !u. (Abort ExHalt_abort (halt_state (set_returndata [] t)) = Halt u \/
           ?ir. Abort ExHalt_abort (halt_state (set_returndata [] t)) = IntRet ir u) ==>
          allocas_below_fmp u))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`] (SPEC_ALL compile_store_slots_static_origin_ptr_path)) >>
  impl_tac >- (pure_asm_rewrite_tac[] >> simp[]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  Cases_on `type_slot_size tv = 0` >> simp[]
  >- (qpat_x_assum `type_slot_size tv = 0 ==> local_ptrs_reserved _ _ /\ _`
        mp_tac >> simp[] >> strip_tac >>
      conj_tac >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> simp[]) >>
      conj_tac >- (`gas_origin_ptr_path (ARB,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)`
                   by gvs[] >>
                   drule_all body_full_path_alloca_history >> simp[]) >>
      conj_tac >- metis_tac[store_slots_normalize_allocas_below_fmp] >>
      conj_tac >- (rpt strip_tac >> irule place_store_normalized_stmt_state >>
                   qexistsl_tac [`s`,`sa`] >> simp[]) >>
      `t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
       t.vs_immutables = s.vs_immutables` by
        (qpat_assum `store_copy_normalize s t = s`
           (mp_tac o BETA_RULE o AP_TERM ``\z:venom_state. (z.vs_accounts,z.vs_transient,z.vs_immutables)``) >>
         simp[NoAsms, store_copy_normalize_def]) >>
      rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G`,`ee`,`s`,`sa`,`tn`] >> simp[]) >>
  gvs[write_storage_slot_eq, exit_result_def, stmt_exit_ptr_def,
       exprSimDefsTheory.expr_exit_def, halt_exit_not_halt, halt_state_def, set_returndata_def]
QED

Theorem assign_slots_sparse_stmt_post[local]:
  !mods.
  expr_sim_inv_mods mods cenv cx env ee /\
  stmt_state_rel H ctx func cenv cx ee s /\
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ start + type_slot_size tv <= dimword (:256) /\
  encode_value tv v = SOME writes /\ value_has_type tv v /\
  well_formed_type_value tv /\ val_in_memory tv v off s.vs_memory /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  store_copy_normalize s t =
    FOLDL (\q i. (if tr then tstore else sstore) (n2w (start+i))
              (mload (off+32*i) s) q) s ks /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel H ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule place_store_normalized_stmt_state >> qexistsl_tac [`s`,`sa`] >>
  `start < dimword (:256)` by decide_tac >>
  qpat_assum `store_copy_normalize s t = _` (fn th => pure_rewrite_tac [th]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  ho_match_mp_tac placeStoreSlotsTheory.place_store_encoded_leaf_state_sparse >>
  qexistsl_tac [`env`,`rootk`,`root`,`path`,`delta`,`tv`,`v`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt strip_tac >> irule place_store_memory_live_at >>
  metis_tac[]
QED

Theorem assign_slots_robust_byte_clean[local]:
  b < 32 /\
  (!mem. mem_agree_outside M s.vs_memory mem ==>
     EL b (mem_bytes_at a 32 mem) = value) ==>
  a+b NOTIN M
Proof
  strip_tac >> spose_not_then assume_tac >>
  `!x. mem_agree_outside M s.vs_memory
       (write_memory_with_expansion (a+b) [x] s).vs_memory` by
    (rpt gen_tac >> irule representationCleanPtrTheory.mem_agree_outside_write_byte >> simp[]) >>
  `!x. EL b (mem_bytes_at a 32
    (write_memory_with_expansion (a+b) [x] s).vs_memory) = x` by
    (gen_tac >>
     qspecl_then [`a+b`, `[x]`, `s`]
       (mp_tac o Q.AP_TERM `EL 0`) valueEncodingPropsTheory.write_memory_mem_bytes_at_same >>
     qpat_assum `b < 32` (fn th => simp[NoAsms, th, valueEncodingProofsTheory.EL_mem_bytes_at])) >>
  `value = 0w /\ value = 1w` by metis_tac[] >> fs[]
QED

Theorem assign_slots_written_byte_dead[local]:
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  (!mem. mem_agree_outside M s.vs_memory mem ==> val_in_memory tv v off mem) /\
  start + type_slot_size tv <= dimword (:256) /\ i < type_slot_size tv /\
  MEM i (MAP FST writes) /\ b IN mem_word_taint M (off+32*i) ==>
  dead_bytes (apply_writes (n2w start) writes st) start tv (start+i) b
Proof
  simp[mem_word_taint_def] >> strip_tac >> spose_not_then assume_tac >>
  `start < dimword (:256)` by decide_tac >>
  `off+32*i+b NOTIN M` suffices_by simp[] >>
  irule assign_slots_robust_byte_clean >> simp[] >>
  qexistsl_tac [`s`, `EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes st)) T)`] >>
  rpt strip_tac >> sym_tac >>
  `word_to_bytes (mload (off + 32*i) (s with vs_memory := mem)) T =
    mem_bytes_at (off + 32*i) 32 mem` by
    (simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload, valueEncodingDefsTheory.mem_word_at_def] >>
     simp[GSYM valueEncodingDefsTheory.mem_bytes_at_def] >>
     irule venomMemProofsTheory.word_bytes_roundtrip_proof >>
     simp[valueEncodingDefsTheory.mem_bytes_at_def, dividesTheory.divides_def]) >>
  `EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes st)) T) =
    EL b (word_to_bytes (mload (off+32*i) (s with vs_memory := mem)) T)`
    suffices_by simp[] >>
  irule place_store_memory_live_at >>
  `val_in_memory tv v off mem` by metis_tac[] >>
  simp[] >> qexistsl_tac [`tv`,`v`] >> simp[]
QED

Theorem assign_slots_sparse_taint[local]:
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ start + type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ value_has_type tv v /\ encode_value tv v = SOME writes /\
  (!mem. mem_agree_outside M s.vs_memory mem ==> val_in_memory tv v off mem) /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  X SUBSET {(k,b) | storage_dead H tr st (w2n k) b} ==>
  FOLDL (\Z i. key_update Z (n2w (start+i):bytes32) (mem_word_taint M (off+32*i))) X ks
    SUBSET {(k,b) | storage_dead H tr (apply_writes (n2w start) writes st) (w2n k) b}
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!i. MEM i (MAP FST writes) ==> i < type_slot_size tv` by
    metis_tac[cj 1 vyperEncodeDecodeTheory.encode_writes_bounded] >>
  `!i. i < type_slot_size tv ==> w2n (n2w (start+i):bytes32) = start+i` by
    (rpt strip_tac >> `start+i < dimword (:256)` by decide_tac >>
     simp_tac (srw_ss()) [wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD, ASSUME ``start+i < dimword (:256)``]) >>
  simp_tac (srw_ss()) [SUBSET_DEF, pairTheory.FORALL_PROD, cardinalTheory.IN_ELIM_PAIR_THM] >>
  qx_gen_tac `k` >> qx_gen_tac `b` >> disch_tac >>
  qspecl_then [`\i. n2w (start+i):bytes32`, `\i. mem_word_taint M (off+32*i)`]
    (drule o BETA_RULE) keyUpdateFoldTheory.key_update_fold_cases >>
  disch_then (DISJ_CASES_THEN STRIP_ASSUME_TAC)
  >- suspend "unwritten" >> suspend "written"
QED

Resume assign_slots_sparse_taint[unwritten]:
  `storage_dead H tr st (w2n k) b` by
    (qpat_assum `X SUBSET _` (mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
     disch_then (qspec_then `(k,b)` mp_tac) >> simp[cardinalTheory.IN_ELIM_PAIR_THM]) >>
  Cases_on `start <= w2n k /\ w2n k < start + type_slot_size tv`
  >- suspend "inside" >> suspend "outside"
QED

Resume assign_slots_sparse_taint[inside]:
  `?i. w2n k = start+i /\ i < type_slot_size tv` by
    (qexists_tac `w2n k - start` >> decide_tac) >>
  `~MEM i (MAP FST writes)` by
    (strip_tac >> `MEM i ks` by metis_tac[] >>
     `n2w (start+i) = k` by metis_tac[wordsTheory.n2w_w2n] >>
     qpat_x_assum `!j. MEM j ks ==> k <> _` (qspec_then `i` mp_tac) >>
     simp[]) >>
  `b < 32 /\ dead_bytes st start tv (start+i) b` by
    (`dead_bytes st start tv (w2n k) b` by metis_tac[bodyFullStoreSlotsStaticTheory.store_slots_subregion_dead_iff] >>
     drule (cj 1 dead_bytes_range) >> simp[] >>
     gvs[bodyFullStoreSlotsStaticTheory.store_slots_subregion_dead_iff, cj 1 dead_bytes_range]) >>
  `dead_bytes (apply_writes (n2w start) writes st) start tv (start+i) b` by
    metis_tac[placeStoreSlotsTheory.place_store_unwritten_live_preserved] >>
  metis_tac[bodyFullStoreSlotsStaticTheory.store_slots_subregion_dead_iff]
QED

Resume assign_slots_sparse_taint[outside]:
  `!q:bytes32. ~(start <= w2n q /\ w2n q < start + type_slot_size tv) ==>
     lookup_storage q (apply_writes (n2w start) writes st) = lookup_storage q st` by
    (qx_gen_tac `q` >> disch_tac >>
     irule vyperStorageAccessFrameTheory.apply_writes_word_frame >>
     qx_gen_tac `i` >> disch_tac >>
     `i < type_slot_size tv` by metis_tac[] >>
     strip_tac >>
     `w2n q = start+i` by metis_tac[wordsTheory.word_add_n2w] >> decide_tac) >>
  irule place_store_storage_dead_subregion_frame >>
  qexistsl_tac [`delta`,`tv`,`path`,`root`,`rootk`,`st`] >>
  qpat_assum `start = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  asm_rewrite_tac[]
QED

Resume assign_slots_sparse_taint[written]:
  `MEM j (MAP FST writes) /\ j < type_slot_size tv` by metis_tac[] >>
  `dead_bytes (apply_writes (n2w start) writes st) start tv (start+j) b` by
    (irule assign_slots_written_byte_dead >>
     (metis_tac[])) >>
  `w2n k = start+j` by metis_tac[] >>
  `start <= w2n k /\ w2n k < start + type_slot_size tv` by decide_tac >>
  metis_tac[bodyFullStoreSlotsStaticTheory.store_slots_subregion_dead_iff]
QED

Finalise assign_slots_sparse_taint

Theorem assign_slots_state_dead_mask[local]:
  stmt_state_rel H ctx func cenv cx ee s /\
  s.vs_call_ctx.cc_address = cx.txn.target ==>
  storage_dead H tr (if tr then contract_transient s else contract_storage s) =
  storage_dead H tr (get_storage cx ee tr)
Proof
  strip_tac >> drule stmt_state_rel_state_rel >> strip_tac >>
  Cases_on `tr`
  >- (drule state_rel_transient_rel >>
      simp[transient_rel_def, get_storage_def] >>
      metis_tac[storage_agree_storage_dead]) >>
  drule state_rel_storage_rel >>
  simp[storage_rel_def, get_storage_def, vfmStateTheory.lookup_account_def] >>
  metis_tac[storage_agree_storage_dead]
QED

Theorem assign_slots_ghost_frame[local]:
  ghost_inv_at D lo d cenv cx ee G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
  ef.scopes = ee.scopes /\ t.vs_memory = s.vs_memory /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  tnf.t_mem = tn.t_mem /\ stor_taint_ok_at D tnf t ==>
  ghost_inv_at D lo d cenv cx ef Gf tnf t
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
           ptr_covers Gf tnf p t sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[])
  >> metis_tac[]
QED

Theorem assign_slots_post_stor_taint[local]:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx ee s /\
  stmt_state_rel H ctx func cenv cx ef t /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
  dead_lo_ok H D lo cenv cx /\ stor_taint_ok_at D tn s /\
  tnf.t_imm = tn.t_imm /\
  (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
  get_storage cx ef (~tr) = get_storage cx ee (~tr) /\
  ((if tr then tn.t_trans else tn.t_stor) SUBSET
       {(k,b) | storage_dead H tr (get_storage cx ee tr) (w2n k) b} ==>
   (if tr then tnf.t_trans else tnf.t_stor) SUBSET
       {(k,b) | storage_dead H tr (get_storage cx ef tr) (w2n k) b}) ==>
  stor_taint_ok_at D tnf t
Proof
  strip_tac >>
  `!b. storage_dead H b (if b then contract_transient s else contract_storage s) =
       storage_dead H b (get_storage cx ee b)` by metis_tac[assign_slots_state_dead_mask] >>
  `!b. storage_dead H b (if b then contract_transient t else contract_storage t) =
       storage_dead H b (get_storage cx ef b)` by metis_tac[assign_slots_state_dead_mask] >>
  rpt (qpat_x_assum `!b. storage_dead H b _ = _`
    (fn th => map_every (fn b => qspec_then b assume_tac th) [`T`,`F`])) >>
  Cases_on `tr` >>
  gvs[dead_lo_ok_def, stor_taint_ok_at_def, sourceUnitExecutionTheory.cx_dead_def,
      contract_storage_def, contract_transient_def, vfmStateTheory.lookup_account_def]
QED

Theorem assign_slots_fold_immutables[local]:
  !(ks:num list) u.
    (FOLDL (\q j. (if tr then tstore else sstore) (key j) (value j) q) u ks).vs_immutables =
    u.vs_immutables
Proof
  Induct >> simp[FOLDL] >> Cases_on `tr` >> simp[tstore_def,sstore_def]
QED

(* The runtime copy may use a smaller source layout when both layouts have
   identical live encodings. The storage relation uses the declared layout. *)
Theorem body_assign_slots_full_layout_frame_path:
  !mods.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
                            sz = type_memory_size rt) fields) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  well_formed_type_value dtv /\ value_has_type dtv v /\
  encode_value dtv v = SOME writes /\
  type_slot_size tv <= type_slot_size dtv /\
  w2n dw + type_slot_size dtv <= dimword (:256) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory dtv v (w2n sw) mem) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sb.cs_next_var /\ return_buf_frame d cenv sa s /\
  alloca_history func s /\ alloca_inv s ==>
  ?t ks Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ tnf.t_mem = tn.t_mem /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    return_buf_frame d cenv sb t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!H ee env rootk root path delta.
       expr_sim_inv_mods mods cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
       dead_lo_ok H (DF H) lo cenv cx /\ ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
       (0 < type_slot_size dtv ==>
          MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
          storage_locks_separated (FST H) (SND H) /\ storage_subregion root path delta dtv /\
          w2n dw = w2n rootk + delta) ==>
       ?ef. write_storage_slot cx tr dw dtv v ee = (INL (),ef) /\
            stmt_state_rel H ctx func cenv cx ef t /\
            ghost_inv_at (DF H) lo d cenv cx ef Gf tnf t)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`] (SPEC_ALL compile_store_slots_origin_ptr_path)) >>
  impl_tac >- (pure_asm_rewrite_tac[] >> simp[] >> decide_tac) >>
  disch_then (qx_choose_then `t` (qx_choose_then `ks` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qexistsl_tac [`t`,`ks`,`Gf`,`tnf`] >> asm_rewrite_tac[] >>
  conj_tac >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> simp[]) >>
  conj_tac >- (`gas_origin_ptr_path (ARB,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)` by simp[] >>
               drule_all body_full_path_alloca_history >> simp[]) >>
  conj_tac >- (drule store_slots_normalize_allocas_below_fmp >>
               simp[store_slots_fold_allocas_below_fmp]) >>
  map_every qx_gen_tac [`H`,`ee`,`env`,`rootk`,`root`,`path`,`delta`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ ~cx.txn.is_static` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def] >> metis_tac[]) >>
  simp[write_storage_slot_eq] >>
  Cases_on `type_slot_size dtv = 0`
  >- suspend "zero" >> suspend "positive"
QED

Resume body_assign_slots_full_layout_frame_path[zero]:
  `!i. MEM i (MAP FST writes) ==> i < type_slot_size dtv` by
    metis_tac[cj 1 vyperEncodeDecodeTheory.encode_writes_bounded] >>
  `writes = []` by
    (Cases_on `writes` >> gvs[] >>
     first_x_assum (qspec_then `FST h` mp_tac) >> simp[]) >>
  `ks = []` by
    (Cases_on `ks` >> gvs[] >> first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  gnvs[vyperStorageTheory.apply_writes_def, wordsTheory.n2w_w2n] >>
  `set_storage cx ee tr (get_storage cx ee tr) = ee` by
    (Cases_on `tr` >> simp[set_storage_def,get_storage_def,place_store_update_identity]) >>
  qpat_assum `set_storage _ _ _ _ = ee` (fn th => pure_rewrite_tac [th]) >>
  conj_tac
  >- (irule place_store_normalized_stmt_state >> qexistsl_tac [`s`,`sa`] >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  `t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_immutables = s.vs_immutables` by
    (qpat_assum `store_copy_normalize s t = s`
       (mp_tac o BETA_RULE o AP_TERM ``\z:venom_state. (z.vs_accounts,z.vs_transient,z.vs_immutables)``) >>
     simp[NoAsms,store_copy_normalize_def]) >>
  `stor_taint_ok_at (DF H) tnf t` by
    (`stor_taint_ok_at (DF H) tn s` by fs[ghost_inv_at_def] >>
     Cases_on `tr` >> gvs[stor_taint_ok_at_def] >> metis_tac[SUBSET_TRANS]) >>
  irule assign_slots_ghost_frame >> asm_rewrite_tac[] >>
  qexistsl_tac [`G`,`ee`,`s`,`sa`,`tn`] >> asm_rewrite_tac[]
QED

Resume body_assign_slots_full_layout_frame_path[positive]:
  `0 < type_slot_size dtv` by decide_tac >>
  qpat_x_assum `0 < type_slot_size dtv ==> _` mp_tac >>
  asm_rewrite_tac[] >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by metis_tac[mem_agree_outside_def] >>
  `dw = n2w (w2n dw):bytes32` by simp[] >>
  qabbrev_tac `start = w2n dw` >>
  `!i. dw + n2w i = n2w (start+i)` by
    (gen_tac >> qpat_assum `dw = n2w start` (fn th => simp[Once th,wordsTheory.word_add_n2w])) >>
  qpat_x_assum `start = w2n rootk + delta` (mk_asm "start") >>
  `store_copy_normalize s t =
   FOLDL (\q j. (if tr then tstore else sstore) (n2w (start+j))
                 (mload (w2n sw + 32*j) s) q) s ks` by
    (qpat_assum `!i. dw + n2w i = _` (fn th =>
       qpat_assum `store_copy_normalize s t = _`
          (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel H ctx func cenv cx ef t` >>
  conj_asm1_tac
  >- (simp[Abbr `ef`] >>
      qpat_assum `dw = n2w start` (fn th => pure_once_rewrite_tac [th]) >>
      irule assign_slots_sparse_stmt_post >> asm_rewrite_tac[] >>
      conj_tac >- (qexists `env` >> asm_rewrite_tac[]) >>
      qexistsl_tac [`delta`,`ks`,`w2n sw`,`path`,`root`,`rootk`,`s`,`sa`,`dtv`,`v`] >>
      asm "start" mp_tac >> asm_rewrite_tac[] >> metis_tac[]) >>
  reverse (irule assign_slots_ghost_frame >> conj_tac)
  >- (qexistsl_tac [`G`,`ee`,`s`,`sa`,`tn`] >> asm_rewrite_tac[] >> simp[Abbr `ef`]) >>
  `t.vs_immutables = s.vs_immutables` by
    (qpat_assum `store_copy_normalize s t = FOLDL _ _ _`
       (mp_tac o BETA_RULE o AP_TERM ``\z:venom_state. z.vs_immutables``) >>
     simp[NoAsms,store_copy_normalize_def,assign_slots_fold_immutables]) >>
  `stor_taint_ok_at (DF H) tn s` by fs[ghost_inv_at_def] >>
  irule assign_slots_post_stor_taint >> asm_rewrite_tac[] >>
  qexistsl_tac [`H`,`cenv`,`ctx`,`cx`,`ee`,`ef`,`func`,`lo`,`s`,`tn`,`tr`] >>
  asm_rewrite_tac[] >>
  simp[Abbr `ef`,get_storage_after_set] >>
  conj_tac >- (irule get_storage_after_set_other >> Cases_on `tr` >> simp[]) >>
  disch_tac >>
  irule SUBSET_TRANS >>
  qexists `FOLDL (\X j. key_update X (dw + n2w j) (mem_word_taint tn.t_mem (w2n sw + 32*j)))
    (if tr then tn.t_trans else tn.t_stor) ks` >>
  asm_rewrite_tac[] >>
  qpat_assum `!i. dw + n2w i = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `dw = n2w start` (fn th => pure_once_rewrite_tac[th]) >>
  irule assign_slots_sparse_taint >> asm_rewrite_tac[] >>
  qexistsl_tac [`delta`,`path`,`root`,`rootk`,`s`,`dtv`,`v`] >>
  asm "start" mp_tac >> asm_rewrite_tac[]
QED

Finalise body_assign_slots_full_layout_frame_path

Theorem body_assign_slots_full_frame_path:
  !mods.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
                            sz = type_memory_size rt) fields) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sb.cs_next_var /\ return_buf_frame d cenv sa s /\
  alloca_history func s /\ alloca_inv s ==>
  ?t ks Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ tnf.t_mem = tn.t_mem /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    return_buf_frame d cenv sb t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!H ee env rootk root path delta.
       expr_sim_inv_mods mods cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
       dead_lo_ok H (DF H) lo cenv cx /\ ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
       (0 < type_slot_size tv ==>
          MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
          storage_locks_separated (FST H) (SND H) /\ storage_subregion root path delta tv /\
          w2n dw = w2n rootk + delta) ==>
       ?ef. write_storage_slot cx tr dw tv v ee = (INL (),ef) /\
            stmt_state_rel H ctx func cenv cx ef t /\
            ghost_inv_at (DF H) lo d cenv cx ef Gf tnf t)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `well_formed_type_value tv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  mp_tac (Q.INST [`dtv` |-> `tv`] body_assign_slots_full_layout_frame_path) >>
  simp[] >> disch_then match_mp_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_assign_slots_positive_endpoint_post:
  !mods.
  expr_sim_inv_mods mods cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
  ghost_inv_at D lo d cenv cx ee G tn s /\ dead_lo_ok H D lo cenv cx /\
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\ storage_subregion root path delta tv /\
  w2n k = w2n rootk + delta /\ 0 < type_slot_size tv /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ value_has_type tv v /\ encode_value tv v = SOME writes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v off mem) /\
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (k+n2w j) (mload (off+32*j) s) q) s ks /\
  (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_call_ctx = s.vs_call_ctx /\
  tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
  (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
  (if tr then tnf.t_trans else tnf.t_stor) SUBSET
    FOLDL (\X j. key_update X (k+n2w j) (mem_word_taint tn.t_mem (off+32*j)))
      (if tr then tn.t_trans else tn.t_stor) ks ==>
  stmt_state_rel H ctx func cenv cx
    (set_storage cx ee tr (apply_writes k writes (get_storage cx ee tr))) t /\
  ghost_inv_at D lo d cenv cx
    (set_storage cx ee tr (apply_writes k writes (get_storage cx ee tr))) Gf tnf t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> simp[] >>
  `val_in_memory tv v off s.vs_memory` by metis_tac[mem_agree_outside_def] >>
  `k = n2w (w2n k):bytes32` by simp[] >>
  qabbrev_tac `start = w2n k` >>
  `!i. k + n2w i = n2w (start+i)` by
    (gen_tac >> qpat_assum `k = n2w start` (fn th => simp[Once th,wordsTheory.word_add_n2w])) >>
  qpat_x_assum `start = w2n rootk + delta` (mk_asm "start") >>
  `store_copy_normalize s t =
   FOLDL (\q j. (if tr then tstore else sstore) (n2w (start+j))
                (mload (off+32*j) s) q) s ks` by
    (qpat_assum `!i. k + n2w i = _` (fn th =>
       qpat_assum `store_copy_normalize s t = _`
          (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel H ctx func cenv cx ef t` >>
  conj_asm1_tac
  >- (simp[Abbr `ef`] >>
      qpat_assum `k = n2w start` (fn th => pure_once_rewrite_tac [th]) >>
      irule assign_slots_sparse_stmt_post >> asm_rewrite_tac[] >>
      conj_tac >- (qexists `env` >> asm_rewrite_tac[]) >>
      qexistsl [`delta`,`ks`,`off`,`path`,`root`,`rootk`,`s`,`sa`,`tv`,`v`] >>
      asm "start" mp_tac >> asm_rewrite_tac[] >> metis_tac[]) >>
  reverse (irule assign_slots_ghost_frame >> conj_tac)
  >- (qexistsl [`G`,`ee`,`s`,`sa`,`tn`] >> asm_rewrite_tac[] >>
      Cases_on `tr` >> simp[Abbr `ef`,set_storage_def]) >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def]) >>
  `t.vs_immutables = s.vs_immutables` by
    (qpat_assum `store_copy_normalize s t = FOLDL _ _ _`
       (mp_tac o BETA_RULE o AP_TERM ``\z:venom_state. z.vs_immutables``) >>
     simp[NoAsms,store_copy_normalize_def,assign_slots_fold_immutables]) >>
  `stor_taint_ok_at D tn s` by fs[ghost_inv_at_def] >>
  irule assign_slots_post_stor_taint >> asm_rewrite_tac[] >>
  qexistsl [`H`,`cenv`,`ctx`,`cx`,`ee`,`ef`,`func`,`lo`,`s`,`tn`,`tr`] >>
  asm_rewrite_tac[] >> simp[Abbr `ef`,get_storage_after_set] >>
  conj_tac >- (irule get_storage_after_set_other >> Cases_on `tr` >> simp[]) >>
  disch_tac >> irule SUBSET_TRANS >>
  qexists `FOLDL (\X j. key_update X (k+n2w j) (mem_word_taint tn.t_mem (off+32*j)))
    (if tr then tn.t_trans else tn.t_stor) ks` >>
  asm_rewrite_tac[] >>
  qpat_assum `!i. k + n2w i = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `k = n2w start` (fn th => pure_once_rewrite_tac[th]) >>
  irule assign_slots_sparse_taint >> asm_rewrite_tac[] >>
  qexistsl [`delta`,`path`,`root`,`rootk`,`s`,`tv`,`v`] >>
  asm "start" mp_tac >> asm_rewrite_tac[]
QED
