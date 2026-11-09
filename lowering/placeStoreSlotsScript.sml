(*
 * place_store_value_run (placeStore) at a slot in storage or transient
 * storage: a word by one SSTORE or TSTORE; any other value laid out at the
 * place's type in memory (through a fresh buffer when the value's type
 * differs and is not a bytestring), then copied to the slots by
 * compile_store_slots, which writes only the slots live in the value: a
 * DynArray's length and its first length elements, a bytestring's length
 * word and the words holding its bytes, at any depth.
 *
 * store_slots_entry says what compile_store_slots does for one type and
 * value: it stores memory word j at slot dw + j for each j of a list ks,
 * and ks holds exactly the slots the value's encoding writes.
 * store_slots_rank_entry proves it for every type by induction on
 * type_rank; place_store_value_storage_run uses it.
 *
 * TOP-LEVEL: place_store_value_storage_run
 *)

Theory placeStoreSlots
Ancestors
  placeStoreCopyPath placeStoreStorage exprSimAlloc loweringSlice emitHelperProps fragExec
  localPtrsProps venomInstProofs exprSimAggregateEncoding vyperStorageBackend vfmState venomMemDefs
  stmtSimDefs exprSimHypsDefs typedCopyDomain vyperStoragePlaceProvenance vyperStoragePlaceRegion vyperStorageFrame
  loweringPosts fragGasMode accountsRelProps copyExecution stmtSimStoreCopy
  placeStoreCopyChunk fragGasSeq typedMemoryCopy placeMemoryArrayControl
  stmtLowering exprLowering compileEnv context
  vyperInterpreter vyperState vyperValue vyperTypeSystem vyperTyping
  vyperStorage valueEncoding valueEncodingProps valueEncodingTyping
  venomState fragGasPath arithmetic venomExecSemantics venomInst
  exprLoweringProps emitHelper list rich_list vyperTypeValues vyperTypeDefaults
Libs
  stepInstBaseLib

(* wordsLib, which the type-value ancestors load, evaluates dimword (:256)
   in simp; the bounds reasoning here keeps it symbolic. *)
val _ = diminish_srw_ss ["sizes"]

(* Operand reads after an update split on the operand, as in
   slotCopyExecution. *)
val _ = augment_srw_ss [rewrites [slotCopyExecutionTheory.slot_copy_operand_update]];

(* compile_store_slots run from memory holding v at src (type tv) to the
   slots from dw: it stores exactly the slots v's encoding writes, each
   holding the memory word at the same offset. *)
Definition store_slots_entry_def:
  store_slots_entry cenv ctx ty tv v <=>
    !src slot tr sa sb func s sw dw writes.
      compile_store_slots cenv src slot ty tr sa = ((),sb) /\
      (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
      eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
      val_in_memory tv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size tv < dimword (:256) /\
      w2n dw + type_slot_size tv <= dimword (:256) /\
      encode_value tv v = SOME writes /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      ~s.vs_call_ctx.cc_static ==>
      ?t ks.
        gas_marked_path F ctx func s 0 (OK t) /\
        store_copy_normalize s t =
          FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                   (mload (w2n sw + 32 * j) s) q) s ks /\
        (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
        t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
End

(* A type with no DynArray or bytestring inside: copied whole. *)
Theorem store_slots_static_entry:
  !cenv tenv ctx ty tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    ~is_abi_dynamic cenv.ce_struct_fields ty /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    store_slots_entry cenv ctx ty tv v
Proof
  rpt gen_tac >> strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (irule typed_copy_memory_size >> metis_tac[]) >>
  `~vyper_is_dynamic tenv ty` by
    (drule_all abiTypeBoundPropsTheory.abi_props_vyper_typed >> simp[]) >>
  rewrite_tac[store_slots_entry_def] >> rpt gen_tac >> strip_tac >>
  `!j. MEM j (MAP FST writes) <=> j < type_slot_size tv` by
    (gen_tac >> eq_tac
     >- metis_tac[CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded] >>
     strip_tac >> irule vyperStorageCoverageTheory.encode_value_live_written >>
     metis_tac[]) >>
  `type_memory_bytes cenv ty DIV 32 = type_slot_size tv` by
    simp[type_memory_size_slots] >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, comp_bind_def, comp_return_def] >>
  Cases_on `type_slot_size tv = 1`
  >- (simp[comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
      rename1 `emit_op MLOAD [src] sa = (loaded,sm)` >>
      `ci_mono sa sm /\ ci_mono sm sb` by
        metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
                  ci_mono_emit_void, pairTheory.SND] >>
      `fn_has_code sa sm func /\ fn_has_code sm sb func` by
        (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
      `!x. slot = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all place_store_load_emit_path >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      qexistsl_tac [`t`, `[0]`] >> simp[] >>
      qpat_x_assum `store_copy_normalize _ _ = _` mp_tac >>
      Cases_on `tr` >>
      simp[store_copy_normalize_def, sstore_def, tstore_def,
           venom_state_component_equality]) >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `type_slot_size tv < dimword (:256) /\
   w2n sw + 32 * type_slot_size tv < dimword (:256)` by
    (fs[type_memory_size_slots] >> decide_tac) >>
  drule_all place_store_memory_to_slots_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`t`, `COUNT_LIST (type_slot_size tv)`] >>
  simp[MEM_COUNT_LIST]
QED

Theorem store_slots_bytes_footprint:
  (tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)) /\
  value_has_type tv v /\ val_in_memory tv v off mem /\
  off + type_memory_size tv < dimword (:256) /\
  encode_value tv v = SOME writes ==>
  ?L. mem_word_at off mem = n2w L /\
      (!j. MEM j (MAP FST writes) <=> j < 1 + word_size L) /\
      32 * (1 + word_size L) <= type_memory_size tv /\
      L + 63 < dimword (:256) /\
      1 + word_size L < dimword (:256)
Proof
  strip_tac >> Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, type_memory_size_def,
      encode_value_def] >>
  drule vyperEncodeDecodeTheory.encode_dyn_bytes_slots_keys >> strip_tac >>
  gvs[] >> rename1 `mem_word_at off mem = n2w len` >>
  qexists_tac `len` >> simp[] >>
  fs[vfmConstantsTheory.word_size_def] >>
  qspec_then `len + 31` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
  qspec_then `cap + 31` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
  simp[] >> rpt strip_tac >>
  rpt conj_tac >>
  fs[wordsTheory.dimword_def] >> intLib.ARITH_TAC
QED

Theorem store_slots_bytes_count_path[local]:
  compile_bytestring_word_count src sa = (cnt,sm) /\
  eval_operand src s = SOME sw /\
  mem_word_at (w2n sw) s.vs_memory = n2w L /\
  L + 63 < dimword (:256) /\ fn_has_code sa sm func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
      eval_operand cnt u = SOME (n2w (1 + word_size L)) /\
      u.vs_memory = s.vs_memory /\
      (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s u) /\
      ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
      u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >>
  qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
  simp[compile_bytestring_word_count_def, comp_bind_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [src] sa = (loaded,a)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [loaded; Lit 63w] a = (sum,b)` >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b sm` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono] >>
  `fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b sm func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split,
                                  cs_extends_trans]) >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       eval_operand loaded t = SOME (n2w L) /\
       t.vs_memory = s.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s t) /\
       ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
       t.vs_inst_idx = LENGTH a.cs_current_insts` by
    (irule place_store_emit_op_path >> simp[] >>
     qexistsl_tac [`[src]`, `MLOAD`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_read1_def, GSYM mem_word_at_eq_mload]) >>
  suspend "rest"
QED
Resume store_slots_bytes_count_path[rest]:
  `?r. gas_marked_path F ctx func t 0 (OK r) /\
       eval_operand sum r = SOME (n2w (L + 63)) /\
       r.vs_memory = t.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame a off len t r) /\
       ~r.vs_halted /\ r.vs_current_bb = b.cs_current_bb /\
       r.vs_inst_idx = LENGTH b.cs_current_insts` by
    (irule place_store_emit_op_path >> simp[] >>
     qexistsl_tac [`[loaded; Lit 63w]`, `ADD`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def, GSYM wordsTheory.word_add_n2w]) >>
  `(n2w (L + 63):bytes32) >>> 5 = n2w (1 + word_size L)` by
    (once_rewrite_tac[GSYM wordsTheory.w2n_11] >>
     simp[Excl "w2n_11", wordsTheory.w2n_lsr, wordsTheory.w2n_n2w,
          arithmeticTheory.LESS_MOD, vfmConstantsTheory.word_size_def] >>
     qspec_then `L + 31` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
     qspec_then `L + 63` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
     rpt strip_tac >>
     `(L + 31) DIV 32 + 1 < dimword (:256)` by intLib.ARITH_TAC >>
     simp[arithmeticTheory.LESS_MOD] >> intLib.ARITH_TAC) >>
  `?u. gas_marked_path F ctx func r 0 (OK u) /\
       eval_operand cnt u = SOME (n2w (1 + word_size L)) /\
       u.vs_memory = r.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame b off len r u) /\
       ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
       u.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (irule place_store_emit_op_path >> simp[] >>
     qexistsl_tac [`[Lit 5w; sum]`, `SHR`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def]) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `t` >> simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `r` >> simp[]) >>
  rpt gen_tac >>
  metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_trans,
            typedMemoryCopyTheory.typed_copy_state_frame_mono]
QED
Finalise store_slots_bytes_count_path

(* A bytestring: its length word and the words holding its bytes. *)
Theorem store_slots_bytes_entry:
  !cenv tenv ctx ty tv v.
    is_bytestring_type ty /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    store_slots_entry cenv ctx ty tv v
Proof
  rpt gen_tac >> strip_tac >>
  `?cap. tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def, evaluate_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     gvs[is_bytestring_type_def, evaluate_type_def]) >>
  rewrite_tac[store_slots_entry_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `val_in_memory _ _ _ _`) store_slots_bytes_footprint >>
  disch_then (qspecl_then [`writes`, `cap`] mp_tac) >>
  simp[] >> strip_tac >>
  `is_abi_dynamic cenv.ce_struct_fields ty` by
    (qpat_x_assum `is_bytestring_type ty` mp_tac >>
     Cases_on `ty` >> simp[is_bytestring_type_def, is_abi_dynamic_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[is_bytestring_type_def, is_abi_dynamic_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     simp[is_bytestring_type_def, is_abi_dynamic_def]) >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_bytestring_word_count src sa = (cnt,sm)` >>
  fs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `ci_mono sa sm /\ (!x. cnt = Var x ==> not_fresh_at sm x)` by
    (qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
     simp[compile_bytestring_word_count_def, comp_bind_def] >>
     pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
     pairarg_tac >> gvs[] >>
     imp_res_tac typedMemoryCopyTheory.typed_copy_emit_op_mono >>
     conj_tac
     >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
     metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh]) >>
  rename1 `compile_word_copy_loop_op _ _ _ _ _ _ sm = (res,sb)` >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_word_copy_loop_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  drule_all store_slots_bytes_count_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand src u = SOME sw /\ eval_operand slot u = SOME dw` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  `!x. src = Var x \/ slot = Var x \/ cnt = Var x ==> not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `u.vs_call_ctx = s.vs_call_ctx` by
    (fs[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
     gvs[venomStateTheory.venom_state_component_equality]) >>
  `1 + word_size L < dimword (:256) /\
   w2n sw + 32 * (1 + word_size L) < dimword (:256)` by intLib.ARITH_TAC >>
  `~u.vs_call_ctx.cc_static` by simp[] >>
  drule_all place_store_memory_to_slots_op_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "compose"
QED
Resume store_slots_bytes_entry[compose]:
  markerLib.RESUME_TAC >> (
  qexistsl_tac [`t`, `COUNT_LIST (1 + word_size L)`] >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `u` >> simp[]) >>
  reverse conj_tac
  >- (conj_tac >- simp[rich_listTheory.MEM_COUNT_LIST] >>
      qpat_x_assum `store_copy_normalize _ _ = _` kall_tac >>
      fs[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
      gvs[venomStateTheory.venom_state_component_equality] >>
      rpt strip_tac >>
      `not_fresh_at sm x` by
        metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
      metis_tac[]) >>
  `!ks q. store_copy_normalize s
     (FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                      (mload (32*j + w2n sw) s) q) q ks) =
     FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                      (mload (32*j + w2n sw) s) q)
       (store_copy_normalize s q) ks` by
    (Induct >> simp[] >> rpt gen_tac >>
     Cases_on `tr` >> simp[store_copy_normalize_def, sstore_def, tstore_def]) >>
  `store_copy_normalize s u = s` by
    (qpat_x_assum `!off len. typedMemoryCopy$typed_copy_state_frame _ _ _ _ _`
       (qspecl_then [`0`, `0`] mp_tac) >>
     simp[typedMemoryCopyTheory.typed_copy_state_frame_def, store_copy_normalize_def,
          venomStateTheory.venom_state_component_equality]) >>
  `store_copy_normalize s t = store_copy_normalize s (store_copy_normalize u t)` by
    simp[NoAsms, store_copy_normalize_def] >>
  pop_assum SUBST1_TAC >>
  asm_rewrite_tac[] >>
  `!j. mload (w2n sw + 32*j) u = mload (32*j + w2n sw) s` by
    metis_tac[GSYM mem_word_at_eq_mload, arithmeticTheory.ADD_COMM] >>
  asm_rewrite_tac[])
QED
Finalise store_slots_bytes_entry

Theorem store_slots_elements_layout[local]:
  compile_copy_elements_to_slots cenv src slot elem cnt tr sa = ((),sb) ==>
  ?hdr body exit cv a b c init p q h lt h1 done h2 hj body_start
   so b1 sp b2 doff b3 dp sc sd inc tail1 tail2 tail3.
    ci_mono sa sc /\ ci_mono sc sd /\ ci_mono sd sb /\
    not_fresh_at sc cv /\ ~not_fresh_at sa cv /\
    (fn_has_code sa sb func ==> fn_has_code sc sd func) /\
    fresh_label "dyn_cond" sa = (hdr,a) /\
    fresh_label "dyn_body" a = (body,b) /\
    fresh_label "dyn_exit" b = (exit,c) /\
    fresh_var c = (cv,init) /\
    emit_inst ASSIGN [Lit 0w] [cv] init = ((),p) /\
    emit_inst JMP [Label hdr] [] p = ((),q) /\
    new_block hdr q = (q.cs_current_bb,h) /\
    emit_op LT [Var cv;cnt] h = (lt,h1) /\
    emit_op ISZERO [lt] h1 = (done,h2) /\
    emit_inst JNZ [done;Label exit;Label body] [] h2 = ((),hj) /\
    new_block body hj = (hj.cs_current_bb,body_start) /\
    emit_op MUL [Var cv;Lit (n2w (type_memory_bytes cenv elem))]
      body_start = (so,b1) /\
    emit_op ADD [src;so] b1 = (sp,b2) /\
    emit_op MUL [Var cv;Lit (n2w (type_memory_bytes cenv elem DIV 32))]
      b2 = (doff,b3) /\
    emit_op ADD [slot;doff] b3 = (dp,sc) /\
    compile_store_slots cenv sp dp elem tr sc = ((),sd) /\
    emit_op ADD [Var cv;Lit 1w] sd = (inc,tail1) /\
    emit_inst ASSIGN [inc] [cv] tail1 = ((),tail2) /\
    emit_inst JMP [Label hdr] [] tail2 = ((),tail3) /\
    new_block exit tail3 = (tail3.cs_current_bb,sb)
Proof
  simp[Once compile_store_slots_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_store_slots cenv sp dp elem tr sc = ((),sd)` >>
  `ci_mono sc sd` by
    metis_tac[cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots,
              pairTheory.SND] >>
  rpt (goal_assum (drule_at Any)) >>
  gvs[fresh_label_def, fresh_var_def, emit_inst_def, emit_op_def,
      fresh_id_def, emit_def, new_block_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `ci_mono sc sd` >>
  qmatch_goalsub_abbrev_tac `ci_mono sd sf` >>
  `ci_mono sa sc` by
    (simp[ci_mono_def, cs_extends_def, Abbr `sc`] >>
     qexists_tac `TAKE 2 sc.cs_blocks` >>
     simp[Abbr `sc`, APPEND_ASSOC]) >>
  `ci_mono sd sf` by
    (simp[ci_mono_def, cs_extends_def, Abbr `sf`] >>
     qexists_tac `TAKE 1 sf.cs_blocks` >>
     simp[Abbr `sf`, APPEND_ASSOC]) >>
  simp[] >>
  conj_tac
  >- simp[not_fresh_at_def, Abbr `sc`, emitHelperPropsTheory.fresh_var_distinct] >>
  conj_tac
  >- (simp[not_fresh_at_def] >> qexists_tac `sa.cs_next_var` >> simp[]) >>
  strip_tac >> irule fragExecTheory.fn_has_code_mid >>
  gvs[ci_mono_def] >> qexistsl_tac [`sf`, `sa`] >> simp[]
QED

Theorem store_slots_normalize_fold:
  store_copy_normalize s
    (FOLDL (\q j. (if tr then tstore else sstore) (key j) (value j) q) a (ks:num list)) =
  FOLDL (\q j. (if tr then tstore else sstore) (key j) (value j) q)
    (store_copy_normalize s a) ks
Proof
  qid_spec_tac `a` >> Induct_on `ks` >> simp[FOLDL] >>
  rpt gen_tac >> Cases_on `tr` >>
  simp[store_copy_normalize_def, tstore_def, sstore_def]
QED

Theorem store_slots_shift_fold[local]:
  a.vs_memory = s.vs_memory /\
  w2n sw + i * type_memory_size tv < dimword (:256) ==>
  FOLDL (\q j. (if tr then tstore else sstore)
    ((dw + n2w (i * type_slot_size tv)) + n2w j)
    (mload (w2n (n2w (w2n sw + i * type_memory_size tv) : bytes32) + 32*j) a) q)
    acc js =
  FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
    (mload (w2n sw + 32*j) s) q)
    acc (MAP (\j. i * type_slot_size tv + j) js)
Proof
  strip_tac >> simp[FOLDL_MAP, wordsTheory.w2n_n2w] >>
  irule FOLDL_CONG >> simp[] >> rpt strip_tac >>
  `dw + n2w (i * type_slot_size tv) + n2w x =
   dw + n2w (x + i * type_slot_size tv)` by
    (rewrite_tac[GSYM wordsTheory.WORD_ADD_ASSOC,
                 wordsTheory.word_add_n2w] >> simp[ADD_COMM]) >>
  `dw + n2w x + n2w (i * type_slot_size tv) =
   dw + n2w (x + i * type_slot_size tv)` by
    rewrite_tac[GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w] >>
  `32*x + (w2n sw + i * type_memory_size tv) =
   w2n sw + 32 * (x + i * type_slot_size tv)` by
    (pure_rewrite_tac[type_memory_size_slots, LEFT_ADD_DISTRIB] >>
     CONV_TAC (AC_CONV (MULT_ASSOC, MULT_COMM) ORELSEC
       (DEPTH_CONV (AC_CONV (MULT_ASSOC, MULT_COMM)))) >>
     decide_tac) >>
  simp[mload_def]
QED

Theorem store_slots_compose_fold[local]:
  a.vs_memory = s.vs_memory /\
  w2n sw + i * type_memory_size tv < dimword (:256) /\
  store_copy_normalize s a =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s ks /\
  store_copy_normalize a t =
    FOLDL (\q j. (if tr then tstore else sstore)
      ((dw + n2w (i * type_slot_size tv)) + n2w j)
      (mload (w2n (n2w (w2n sw + i * type_memory_size tv) : bytes32) + 32*j) a) q)
      a js ==>
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q)
      s (ks ++ MAP (\j. i * type_slot_size tv + j) js)
Proof
  strip_tac >>
  `store_copy_normalize s t =
   store_copy_normalize s (store_copy_normalize a t)` by
    simp[NoAsms, store_copy_normalize_def] >>
  pop_assum SUBST1_TAC >>
  asm_rewrite_tac[] >>
  rewrite_tac[BETA_RULE (Q.INST
    [`key` |-> `\j. dw + n2w (i * type_slot_size tv) + n2w j`,
     `value` |-> `\j. mload (w2n (n2w (w2n sw + i * type_memory_size tv) : bytes32) + 32*j) a`]
    (SPEC_ALL store_slots_normalize_fold))] >>
  asm_rewrite_tac[rich_listTheory.FOLDL_APPEND] >>
  irule store_slots_shift_fold >> simp[]
QED

Theorem store_slots_element_bounds[local]:
  i < N /\
  w2n (sw:bytes32) + N * type_memory_size tv < dimword (:256) /\
  w2n (dw:bytes32) + N * type_slot_size tv <= dimword (:256) ==>
  w2n sw + i * type_memory_size tv < dimword (:256) /\
  w2n (n2w (w2n sw + i * type_memory_size tv) : bytes32) =
    w2n sw + i * type_memory_size tv /\
  w2n (n2w (w2n sw + i * type_memory_size tv) : bytes32) +
    type_memory_size tv < dimword (:256) /\
  w2n (dw + n2w (i * type_slot_size tv)) =
    w2n dw + i * type_slot_size tv /\
  w2n (dw + n2w (i * type_slot_size tv)) + type_slot_size tv <= dimword (:256)
Proof
  strip_tac >>
  `i * type_memory_size tv + type_memory_size tv <= N * type_memory_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `i * type_slot_size tv + type_slot_size tv <= N * type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `w2n sw + i * type_memory_size tv < dimword (:256)` by decide_tac >>
  `w2n dw + i * type_slot_size tv < dimword (:256)` by
    (Cases_on `type_slot_size tv = 0` >- simp[wordsTheory.w2n_lt] >>
     decide_tac) >>
  `w2n (dw + n2w (i * type_slot_size tv)) = w2n dw + i * type_slot_size tv` by
    simp[wordsTheory.w2n_add_2] >>
  simp[wordsTheory.w2n_n2w] >> decide_tac
QED

Theorem store_slots_addresses_sequence:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      sp <- emit_op ADD [src; so];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      dp <- emit_op ADD [dst; doff]; comp_return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\j. j.inst_opcode <> GAS) (emitted_insts sa sb) /\
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      eval_operand sp u = SOME (sw + n2w (i * ss)) /\
      eval_operand dp u = SOME (dw + n2w (i * ds)) /\
      (u with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  simp[comp_bind_def, comp_return_def, emit_op_def, fresh_var_def,
    emit_inst_def, fresh_id_def, emit_def, comp_ignore_bind_def] >> strip_tac >>
  gvs[] >>
  simp[emitted_insts_def, same_blocks_def, APPEND_ASSOC, mk_inst_def,
    is_terminator_def, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def] >>
  `!x k. not_fresh_at sa x ==> x <> STRING #"%" (toString (sa.cs_next_var + k))` by
    (simp[not_fresh_at_def] >> metis_tac[DECIDE ``n <= n + k``]) >>
  `!k. src <> Var (STRING #"%" (toString (sa.cs_next_var+k))) /\
       dst <> Var (STRING #"%" (toString (sa.cs_next_var+k)))` by metis_tac[] >>
  `src <> Var (STRING #"%" (toString sa.cs_next_var)) /\
   dst <> Var (STRING #"%" (toString sa.cs_next_var)) /\
   counter <> STRING #"%" (toString sa.cs_next_var)` by
    metis_tac[ADD_0] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def] >>
  simp[exec_pure2_def, eval_operand_def, wordsTheory.word_mul_n2w] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
    emitHelperPropsTheory.lookup_var_update_var,
    emitHelperPropsTheory.eval_operand_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
    eval_operand_def, emitHelperPropsTheory.lookup_var_update_var,
    wordsTheory.word_mul_n2w] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
    emitHelperPropsTheory.lookup_var_update_var] >>
  simp[run_inst_seq_def, emitHelperPropsTheory.lookup_var_update_var,
    emitHelperPropsTheory.fresh_var_distinct] >>
  conj_tac >- simp[update_var_def] >>
  rpt strip_tac >>
  simp[emitHelperPropsTheory.lookup_var_update_var] >>
  metis_tac[ADD_0]
QED

Theorem store_slots_addresses_forward[local]:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      sp <- emit_op ADD [src; so];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      dp <- emit_op ADD [dst; doff]; comp_return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
      eval_operand sp u = SOME (sw + n2w (i * ss)) /\
      eval_operand dp u = SOME (dw + n2w (i * ds)) /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all store_slots_addresses_sequence >> strip_tac >>
  `LENGTH (FILTER (\j. j.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `EVERY (\j. j.inst_opcode <> GAS) _` mp_tac >>
     simp[LENGTH_NIL, FILTER_EQ_NIL]) >>
  drule_all place_store_emitted_seq_path >> strip_tac >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[eval_operand_def, lookup_var_def, same_blocks_def] >>
  qpat_x_assum `u with vs_vars := _ = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >> simp[]
QED

Theorem store_slots_element_forward[local]:
  store_slots_entry cenv ctx elem tv v /\
  compile_store_slots cenv sp dp elem tr sc = ((),sd) /\
  (!x. sp = Var x \/ dp = Var x ==> not_fresh_at sc x) /\
  eval_operand sp a = SOME (sw + n2w (i * type_memory_size tv)) /\
  eval_operand dp a = SOME (dw + n2w (i * type_slot_size tv)) /\
  val_in_memory tv v (w2n sw + i * type_memory_size tv) s.vs_memory /\
  encode_value tv v = SOME writes /\ a.vs_memory = s.vs_memory /\
  i < N /\
  w2n sw + N * type_memory_size tv < dimword (:256) /\
  w2n dw + N * type_slot_size tv <= dimword (:256) /\
  fn_has_code sc sd func /\ fn_inst_ids_distinct func /\
  ~a.vs_halted /\ a.vs_current_bb = sc.cs_current_bb /\
  a.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~a.vs_call_ctx.cc_static /\
  store_copy_normalize s a =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s ks ==>
  ?t js. gas_marked_path F ctx func a 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q)
        s (ks ++ MAP (\j. i * type_slot_size tv + j) js) /\
    (!j. MEM j js <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x a) /\
    t.vs_allocas = a.vs_allocas /\ t.vs_memory = a.vs_memory /\
    t.vs_labels = a.vs_labels /\ t.vs_call_ctx = a.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts
Proof
  strip_tac >> drule_all store_slots_element_bounds >> strip_tac >>
  `sw + n2w (i * type_memory_size tv) =
   n2w (w2n sw + i * type_memory_size tv)` by
    simp[GSYM wordsTheory.word_add_n2w] >>
  gvs[] >>
  qpat_x_assum `store_slots_entry _ _ _ _ _` mp_tac >>
  rewrite_tac[store_slots_entry_def] >>
  disch_then drule >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  simp[] >>
  disch_then drule >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  qexistsl_tac [`t`,`ks'`] >> simp[] >>
  `w2n sw + i * type_memory_size tv < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`js` |-> `ks'`, `sw` |-> `sw:bytes32`]
    (INST_TYPE [``:'a`` |-> ``:256``] store_slots_compose_fold)) >>
  simp[]
QED

Definition store_slots_loop_code_def:
  store_slots_loop_code cenv src slot elem cnt tr sa sb func
    (hdr,body,exit,cv,lv,dv,iv,bs,sc,sd,sp,dp) <=>
  ?ibb hbb tbb id1 id2 hid1 hid2 hid3 tid1 tid2 tid3.
    lookup_block sa.cs_current_bb func.fn_blocks = SOME ibb /\
    DROP (LENGTH sa.cs_current_insts) ibb.bb_instructions =
      [mk_inst id1 ASSIGN [Lit 0w] [cv]; mk_inst id2 JMP [Label hdr] []] /\
    lookup_block hdr func.fn_blocks = SOME hbb /\
    hbb.bb_instructions =
      [mk_inst hid1 LT [Var cv;cnt] [lv];
       mk_inst hid2 ISZERO [Var lv] [dv];
       mk_inst hid3 JNZ [Var dv;Label exit;Label body] []] /\
    (do so <- emit_op MUL [Var cv;Lit (n2w (type_memory_bytes cenv elem))];
        sp <- emit_op ADD [src;so];
        doff <- emit_op MUL [Var cv;Lit (n2w (type_memory_bytes cenv elem DIV 32))];
        dp <- emit_op ADD [slot;doff]; comp_return (sp,dp)
     od) bs = ((sp,dp),sc) /\
    fn_has_code bs sc func /\
    compile_store_slots cenv sp dp elem tr sc = ((),sd) /\
    fn_has_code sc sd func /\
    lookup_block sd.cs_current_bb func.fn_blocks = SOME tbb /\
    DROP (LENGTH sd.cs_current_insts) tbb.bb_instructions =
      [mk_inst tid1 ADD [Var cv;Lit 1w] [iv];
       mk_inst tid2 ASSIGN [Var iv] [cv]; mk_inst tid3 JMP [Label hdr] []] /\
    bs.cs_current_bb = body /\ bs.cs_current_insts = [] /\
    sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
    ci_mono sa bs /\ ci_mono bs sc /\ ci_mono sc sd /\ ci_mono sd sb /\
    not_fresh_at bs cv /\ not_fresh_at sc cv /\
    (!x. sp = Var x \/ dp = Var x ==> not_fresh_at sc x) /\
    ~not_fresh_at sa cv /\ ~not_fresh_at sa lv /\
    ~not_fresh_at sa dv /\ ~not_fresh_at sa iv /\
    lv <> cv /\ dv <> cv
End

Theorem store_slots_loop_code:
  compile_copy_elements_to_slots cenv src slot elem cnt tr sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func ==>
  ?layout. store_slots_loop_code cenv src slot elem cnt tr sa sb func layout
Proof
  strip_tac >> drule store_slots_elements_layout >>
  disch_then (qspec_then `func` strip_assume_tac) >>
  `cs_extends sa q` by
    (gvs[fresh_label_def, fresh_var_def, emit_inst_def, fresh_id_def,
        emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        cs_extends_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends h hj` by
    (gvs[emit_op_def, fresh_var_def, emit_inst_def, fresh_id_def,
        emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        cs_extends_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends body_start sc` by
    (gvs[emit_op_def, fresh_var_def, emit_inst_def, fresh_id_def,
        emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        cs_extends_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sd tail3` by
    (gvs[emit_op_def, fresh_var_def, emit_inst_def, fresh_id_def,
        emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        cs_extends_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  imp_res_tac cs_extends_new_block >>
  fs[ci_mono_def] >>
  `cs_extends h sb /\ cs_extends body_start sb` by
    metis_tac[cs_extends_trans] >>
  `lookup_block q.cs_current_bb func.fn_blocks =
     SOME <|bb_label := q.cs_current_bb; bb_instructions := q.cs_current_insts|>` by
    (irule placeMemoryCodeLayoutTheory.fn_has_code_finished_mid >>
     metis_tac[]) >>
  `cs_extends sa hj` by metis_tac[cs_extends_trans] >>
  `lookup_block hj.cs_current_bb func.fn_blocks =
     SOME <|bb_label := hj.cs_current_bb; bb_instructions := hj.cs_current_insts|>` by
    (irule placeMemoryCodeLayoutTheory.fn_has_code_finished_mid >> metis_tac[]) >>
  `cs_extends sa tail3` by metis_tac[cs_extends_trans] >>
  `lookup_block tail3.cs_current_bb func.fn_blocks =
     SOME <|bb_label := tail3.cs_current_bb; bb_instructions := tail3.cs_current_insts|>` by
    (irule placeMemoryCodeLayoutTheory.fn_has_code_finished_mid >>
     metis_tac[cs_extends_refl]) >>
  `cs_extends sa body_start` by metis_tac[cs_extends_trans] >>
  `fn_has_code body_start sc func` by
    (irule fragExecTheory.fn_has_code_mid >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sc sd func` by simp[] >>
  imp_res_tac emitHelperPropsTheory.fresh_label_props >>
  imp_res_tac emitHelperPropsTheory.emit_inst_extends >>
  imp_res_tac emitHelperPropsTheory.new_block_props >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
  imp_res_tac loweringShapeRulesTheory.emit_op_facts >>
  `init.cs_current_bb = c.cs_current_bb /\
   init.cs_current_insts = c.cs_current_insts /\
   init.cs_next_var = c.cs_next_var + 1 /\
   init.cs_next_id = c.cs_next_id` by
    (qpat_x_assum `fresh_var c = _` mp_tac >>
     simp_tac (srw_ss()) [fresh_var_def, LET_THM] >>
     disch_then (SUBST1_TAC o SYM o CONJUNCT2) >> simp[]) >>
  rename1 `new_block blabel hj = (hj.cs_current_bb,body_start)` >>
  qexists_tac `(hdr,blabel,exit,cv,
    STRCAT "%" (toString h.cs_next_var),
    STRCAT "%" (toString h1.cs_next_var),
    STRCAT "%" (toString sd.cs_next_var),body_start,sc,sd,sp,dp)` >>
  simp[store_slots_loop_code_def] >>
  qexistsl_tac [
    `<|bb_label := q.cs_current_bb; bb_instructions := q.cs_current_insts|>`,
    `<|bb_label := hj.cs_current_bb; bb_instructions := hj.cs_current_insts|>`,
    `<|bb_label := tail3.cs_current_bb; bb_instructions := tail3.cs_current_insts|>`,
    `init.cs_next_id`,`p.cs_next_id`,`h.cs_next_id`,`h1.cs_next_id`,
    `h2.cs_next_id`,`sd.cs_next_id`,`tail1.cs_next_id`,`tail2.cs_next_id`] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  fs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  `cv = STRCAT "%" (toString sa.cs_next_var)` by
    (qpat_x_assum `fresh_var c = _` mp_tac >>
     simp_tac (srw_ss()) [fresh_var_def, LET_THM, pairTheory.PAIR_EQ] >>
     strip_tac >>
     qpat_x_assum `STRING _ _ = cv` (fn th => rewrite_tac[GSYM th]) >>
     simp[]) >>
  fs[ci_mono_def, not_fresh_at_def,
     emitHelperPropsTheory.fresh_var_distinct] >>
  rpt strip_tac >> gvs[] >>
  irule emitHelperPropsTheory.fresh_var_distinct >> decide_tac
QED

Definition store_slots_prefix_def:
  store_slots_prefix sa etv el tr (sw:bytes32) dw s i ks u <=>
    store_copy_normalize s u =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q) s ks /\
    (!k. MEM k ks <=> ?r writes j. r < i /\
      encode_value etv (el r) = SOME writes /\
      MEM j (MAP FST writes) /\ k = r * type_slot_size etv + j) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory /\
    u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
    ~u.vs_halted
End

Theorem store_slots_prefix_empty:
  ~s.vs_halted ==> store_slots_prefix sa etv el tr sw dw s 0 [] s
Proof
  simp[store_slots_prefix_def, store_copy_normalize_def]
QED

Theorem store_slots_prefix_transfer[local]:
  store_slots_prefix sa etv el tr sw dw s i ks u /\
  store_copy_normalize s v = store_copy_normalize s u /\
  (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x u) /\
  v.vs_allocas = u.vs_allocas /\ v.vs_memory = u.vs_memory /\
  v.vs_labels = u.vs_labels /\ v.vs_call_ctx = u.vs_call_ctx /\
  ~v.vs_halted ==>
  store_slots_prefix sa etv el tr sw dw s i ks v
Proof
  simp[store_slots_prefix_def] >> metis_tac[]
QED

Theorem store_slots_prefix_control:
  store_slots_prefix sa etv el tr sw dw s i ks u /\
  (!x. not_fresh_at sa x ==> x <> a /\ x <> b) ==>
  store_slots_prefix sa etv el tr sw dw s i ks
    (jump_to lbl ((update_var b wb (update_var a wa u)) with vs_inst_idx := idx))
Proof
  strip_tac >>
  `~u.vs_halted` by gvs[store_slots_prefix_def] >>
  irule store_slots_prefix_transfer >>
  simp[jump_to_def, update_var_def] >> qexists_tac `u` >>
  simp[store_copy_normalize_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem store_slots_prefix_init_control:
  store_slots_prefix sa etv el tr sw dw s i ks u /\
  (!x. not_fresh_at sa x ==> x <> a) ==>
  store_slots_prefix sa etv el tr sw dw s i ks
    (jump_to lbl ((update_var a wa u) with vs_inst_idx := idx))
Proof
  strip_tac >>
  `~u.vs_halted` by gvs[store_slots_prefix_def] >>
  irule store_slots_prefix_transfer >>
  simp[jump_to_def, update_var_def] >> qexists_tac `u` >>
  simp[store_copy_normalize_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem store_slots_prefix_members_step[local]:
  (!k. MEM k ks <=> ?r writes j. r < i /\
    encode_value etv (el r) = SOME writes /\
    MEM j (MAP FST writes) /\ k = r * type_slot_size etv + j) /\
  encode_value etv (el i) = SOME writes /\
  (!j. MEM j js <=> MEM j (MAP FST writes)) ==>
  (!k. MEM k (ks ++ MAP (\j. i * type_slot_size etv + j) js) <=>
    ?r writes j. r < SUC i /\ encode_value etv (el r) = SOME writes /\
      MEM j (MAP FST writes) /\ k = r * type_slot_size etv + j)
Proof
  strip_tac >>
  `!r. r < SUC i <=> r < i \/ r = i` by decide_tac >>
  simp[MEM_APPEND, MEM_MAP, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
       EXISTS_OR_THM] >> metis_tac[]
QED

Theorem store_slots_loop_init[local]:
  !cenv src slot elem cnt tr sa sb func hdr body exit cv lv dv iv bs sc sd sp dp
   s ctx etv el sw dw.
  store_slots_loop_code cenv src slot elem cnt tr sa sb func
    (hdr,body,exit,cv,lv,dv,iv,bs,sc,sd,sp,dp) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    store_slots_prefix sa etv el tr sw dw s 0 [] u /\
    lookup_var cv u = SOME 0w /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0
Proof
  rpt gen_tac >> strip_tac >> fs[store_slots_loop_code_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME ibb /\
   DROP s.vs_inst_idx ibb.bb_instructions =
     [mk_inst id1 ASSIGN [Lit 0w] [cv]; mk_inst id2 JMP [Label hdr] []]` by simp[] >>
  drule_all typed_memory_array_init_forward >> strip_tac >>
  qexists_tac `jump_to hdr ((update_var cv 0w s) with
    vs_inst_idx := s.vs_inst_idx + 1)` >>
  conj_tac >- simp[] >>
  reverse conj_tac
  >- simp[jump_to_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
  irule store_slots_prefix_init_control >>
  simp[store_slots_prefix_empty] >> metis_tac[]
QED

Theorem store_slots_loop_exit[local]:
  !cenv src slot elem cnt tr sa sb func hdr body exit cv lv dv iv bs sc sd sp dp
   s ctx etv el sw dw N ks u.
  store_slots_loop_code cenv src slot elem cnt tr sa sb func
    (hdr,body,exit,cv,lv,dv,iv,bs,sc,sd,sp,dp) /\
  store_slots_prefix sa etv el tr sw dw s N ks u /\
  (!x. cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand cnt s = SOME (n2w N) /\ N < dimword (:256) /\
  lookup_var cv u = SOME (n2w N) /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 ==>
  ?t. gas_marked_path F ctx func u 0 (OK t) /\
    store_slots_prefix sa etv el tr sw dw s N ks t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> fs[store_slots_loop_code_def] >>
  `~u.vs_halted /\ eval_operand cnt u = SOME (n2w N)` by
    (fs[store_slots_prefix_def] >> Cases_on `cnt` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME hbb /\
   eval_operand (Var cv) u = SOME (n2w N)` by simp[eval_operand_def] >>
  `N <= N` by simp[] >>
  drule_all typed_memory_array_condition_forward >> simp[] >> strip_tac >>
  qexists_tac `jump_to exit ((update_var dv (bool_to_word T)
    (update_var lv (bool_to_word F) u)) with vs_inst_idx := 2)` >>
  conj_tac >- simp[] >>
  reverse conj_tac >- simp[jump_to_def] >>
  irule store_slots_prefix_control >> simp[] >> metis_tac[]
QED

Theorem store_slots_loop_round[local]:
  !cenv src slot elem cnt tr sa sb func hdr body exit cv lv dv iv bs sc sd sp dp
   s ctx etv el sw dw N i ks u.
  store_slots_loop_code cenv src slot elem cnt tr sa sb func
    (hdr,body,exit,cv,lv,dv,iv,bs,sc,sd,sp,dp) /\
  type_memory_bytes cenv elem = type_memory_size etv /\
  (!r. r < N ==> store_slots_entry cenv ctx elem etv (el r) /\
    IS_SOME (encode_value etv (el r)) /\
    val_in_memory etv (el r) (w2n sw + r * type_memory_size etv) s.vs_memory) /\
  (!x. src = Var x \/ slot = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  eval_operand cnt s = SOME (n2w N) /\ N < dimword (:256) /\
  w2n sw + N * type_memory_size etv < dimword (:256) /\
  w2n dw + N * type_slot_size etv <= dimword (:256) /\
  fn_inst_ids_distinct func /\ ~s.vs_call_ctx.cc_static /\
  i < N /\ store_slots_prefix sa etv el tr sw dw s i ks u /\
  lookup_var cv u = SOME (n2w i) /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 ==>
  ?v ks'. gas_marked_path F ctx func u 0 (OK v) /\
    store_slots_prefix sa etv el tr sw dw s (SUC i) ks' v /\
    lookup_var cv v = SOME (n2w (SUC i)) /\ v.vs_current_bb = hdr /\ v.vs_inst_idx = 0
Proof
  rpt gen_tac >> strip_tac >> fs[store_slots_loop_code_def] >>
  `~u.vs_halted /\ eval_operand cnt u = SOME (n2w N) /\
   eval_operand src u = SOME sw /\ eval_operand slot u = SOME dw` by
    (fs[store_slots_prefix_def] >>
     conj_tac >- (Cases_on `cnt` >> fs[eval_operand_def] >> metis_tac[]) >>
     conj_tac >- (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `slot` >> fs[eval_operand_def] >> metis_tac[]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME hbb /\
   eval_operand (Var cv) u = SOME (n2w i) /\ i <= N` by
    (simp[eval_operand_def] >> decide_tac) >>
  drule_all typed_memory_array_condition_forward >> simp[] >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func u 0 (OK hu)` >>
  `store_slots_prefix sa etv el tr sw dw s i ks hu` by
    (simp[Abbr `hu`] >> irule store_slots_prefix_control >> simp[] >> metis_tac[]) >>
  suspend "body"
QED

Resume store_slots_loop_round[body]:
  `lookup_var cv hu = SOME (n2w i) /\ ~hu.vs_halted /\
   hu.vs_current_bb = bs.cs_current_bb /\
   hu.vs_inst_idx = LENGTH bs.cs_current_insts` by
    (simp[Abbr `hu`, jump_to_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  `eval_operand src hu = SOME sw /\ eval_operand slot hu = SOME dw` by
    (fs[store_slots_prefix_def] >>
     conj_tac >- (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `slot` >> fs[eval_operand_def] >> metis_tac[]) >>
  `(!x. src = Var x ==> not_fresh_at bs x) /\
   (!x. slot = Var x ==> not_fresh_at bs x)` by
    (fs[ci_mono_def] >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  drule_all store_slots_addresses_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path F ctx func hu 0 (OK a)` >>
  `a.vs_memory = hu.vs_memory /\ a.vs_call_ctx = hu.vs_call_ctx /\
   a.vs_allocas = hu.vs_allocas /\ a.vs_labels = hu.vs_labels /\
   store_copy_normalize s a = store_copy_normalize s hu` by
    (qpat_x_assum `a with <|vs_vars := _; vs_inst_idx := _|> = hu` mp_tac >>
     simp[venom_state_component_equality, store_copy_normalize_def] >> metis_tac[]) >>
  `store_slots_prefix sa etv el tr sw dw s i ks a` by
    (irule store_slots_prefix_transfer >> simp[] >> qexists_tac `hu` >>
     simp[] >> fs[ci_mono_def] >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `a.vs_memory = s.vs_memory /\ ~a.vs_call_ctx.cc_static /\
   store_copy_normalize s a =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s ks` by fs[store_slots_prefix_def] >>
  `type_memory_size etv DIV 32 = type_slot_size etv` by
    simp[type_memory_size_slots] >>
  `eval_operand dp a = SOME (dw + n2w (i * type_slot_size etv))` by fs[] >>
  qpat_x_assum `!r. r < N ==> _` (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `encode_value etv (el i)` >> fs[] >>
  rename1 `encode_value etv (el i) = SOME writes` >>
  drule store_slots_element_forward >>
  disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`s`,`ks`,`func`,`N`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  suspend "backedge"
QED

Resume store_slots_loop_round[backedge]:
  `store_slots_prefix sa etv el tr sw dw s (SUC i)
     (ks ++ MAP (\j. i * type_slot_size etv + j) js) t` by
    (pure_rewrite_tac[store_slots_prefix_def] >>
     conj_tac >- (pure_once_rewrite_tac[ADD_COMM] >>
       first_assum ACCEPT_TAC) >>
     conj_tac >- (irule store_slots_prefix_members_step >>
       fs[store_slots_prefix_def] >> metis_tac[]) >>
     fs[store_slots_prefix_def, ci_mono_def] >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `lookup_var cv t = SOME (n2w i)` by metis_tac[] >>
  `SUC i < dimword (:256)` by decide_tac >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME tbb /\
   DROP t.vs_inst_idx tbb.bb_instructions =
     [mk_inst tid1 ADD [Var cv; Lit 1w] [iv];
      mk_inst tid2 ASSIGN [Var iv] [cv]; mk_inst tid3 JMP [Label hdr] []]` by simp[] >>
  drule_all typed_memory_array_backedge_forward >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func t 0 (OK v)` >>
  qexistsl_tac [`v`, `ks ++ MAP (\j. i * type_slot_size etv + j) js`] >>
  reverse conj_tac
  >- (conj_tac
      >- (qunabbrev_tac `v` >> match_mp_tac store_slots_prefix_control >>
          conj_tac >- first_assum ACCEPT_TAC >> metis_tac[]) >>
      simp[Abbr `v`, jump_to_def, lookup_var_def, update_var_def,
           finite_mapTheory.FLOOKUP_UPDATE]) >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `hu` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `a` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `t` >> conj_tac >> first_assum ACCEPT_TAC
QED
Finalise store_slots_loop_round

(* The element loop over count elements el 0, ..., el (N - 1) of type etv,
   element i at memory src + i * size and at slot dw + i * slots. *)
Theorem store_slots_elements_run:
  !cenv ctx elem etv el N src slot cnt tr sa sb func s sw dw.
    compile_copy_elements_to_slots cenv src slot elem cnt tr sa = ((),sb) /\
    type_memory_bytes cenv elem = type_memory_size etv /\
    (!i. i < N ==>
       store_slots_entry cenv ctx elem etv (el i) /\
       IS_SOME (encode_value etv (el i)) /\
       val_in_memory etv (el i) (w2n sw + i * type_memory_size etv)
         s.vs_memory) /\
    (!x. src = Var x \/ slot = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
    eval_operand cnt s = SOME (n2w N) /\ N < dimword (:256) /\
    w2n sw + N * type_memory_size etv < dimword (:256) /\
    w2n dw + N * type_slot_size etv <= dimword (:256) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_call_ctx.cc_static ==>
    ?t ks.
      gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                 (mload (w2n sw + 32 * j) s) q) s ks /\
      (!k. MEM k ks <=>
         ?i writes j. i < N /\ encode_value etv (el i) = SOME writes /\
           MEM j (MAP FST writes) /\ k = i * type_slot_size etv + j) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule_all store_slots_loop_code >> strip_tac >>
  PairCases_on `layout` >>
  `!i. i <= N ==> ?u ks.
    gas_marked_path F ctx func s 0 (OK u) /\
    store_slots_prefix sa etv el tr sw dw s i ks u /\
    lookup_var layout3 u = SOME (n2w i) /\
    u.vs_current_bb = layout0 /\ u.vs_inst_idx = 0` by
    (Induct_on `i`
     >- (strip_tac >> drule_all store_slots_loop_init >>
         disch_then (qspecl_then [`ctx`,`etv`,`el`,`sw`,`dw`] strip_assume_tac) >>
         qexistsl_tac [`u`,`[]`] >> fs[]) >>
     strip_tac >> `i <= N /\ i < N` by decide_tac >>
     first_x_assum drule >> strip_tac >>
     drule_all store_slots_loop_round >> strip_tac >>
     qexistsl_tac [`v`,`ks'`] >> simp[] >>
     metis_tac[gas_marked_path_then, ADD_0]) >>
  first_x_assum (qspec_then `N` mp_tac) >> simp[] >> strip_tac >>
  `!x. cnt = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all store_slots_loop_exit >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`t`,`ks`] >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_0] >>
  fs[store_slots_prefix_def]
QED

Theorem store_slots_dyn_element_encoded[local]:
  !vs tv off ws i.
    encode_dyn_array tv off vs = SOME ws /\ i < LENGTH vs ==>
    IS_SOME (encode_value tv (EL i vs))
Proof
  Induct_on `vs` >- simp[] >>
  rpt gen_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `i` >> gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem store_slots_dyn_encoding_support[local]:
  !vs tv off ws.
    encode_dyn_array tv off vs = SOME ws ==>
    !k. MEM k (MAP FST ws) <=>
      ?i ew j. i < LENGTH vs /\ encode_value tv (EL i vs) = SOME ew /\
        MEM j (MAP FST ew) /\ k = off + i * type_slot_size tv + j
Proof
  Induct_on `vs` >- simp[Once encode_value_def] >>
  rpt gen_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  simp[MAP_APPEND, MEM_APPEND, MAP_MAP_o, combinTheory.o_DEF] >>
  gen_tac >> eq_tac
  >- (strip_tac
      >- (gvs[MEM_MAP, pairTheory.EXISTS_PROD] >>
          qexists_tac `0` >> simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
          metis_tac[ADD_COMM]) >>
      qexists_tac `SUC i` >> simp[ADD_CLAUSES, MULT_CLAUSES] >>
      metis_tac[ADD_ASSOC, ADD_COMM]) >>
  strip_tac >> Cases_on `i` >> gvs[ADD_CLAUSES, MULT_CLAUSES]
  >- (disj1_tac >> simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
      gvs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[ADD_COMM]) >>
  disj2_tac >> goal_assum (drule_at Any) >>
  simp[ADD_ASSOC, ADD_COMM] >> metis_tac[]
QED

Theorem store_slots_dynarray_encoding_support[local]:
  encode_value (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) = SOME ws ==>
  !k. MEM k (MAP FST ws) <=> k = 0 \/
    ?i ew j. i < LENGTH vs /\ encode_value tv (EL i vs) = SOME ew /\
      MEM j (MAP FST ew) /\ k = 1 + i * type_slot_size tv + j
Proof
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  drule store_slots_dyn_encoding_support >> gvs[]
QED

Theorem store_slots_dyn_prefix_fresh[local]:
  emit_op MLOAD [src] sa = (cnt,s1) /\
  emit_op ADD [src; Lit 32w] s1 = (data,s2) /\
  emit_op ADD [slot; Lit 1w] s2 = (dst,sc) /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) ==>
  !x. data = Var x \/ dst = Var x \/ cnt = Var x \/ slot = Var x ==>
    not_fresh_at sc x
Proof
  strip_tac >>
  imp_res_tac typed_copy_emit_op_mono >>
  imp_res_tac typed_copy_emit_op_fresh >>
  gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem store_slots_dyn_prefix_path[local]:
  emit_op MLOAD [src] sa = (cnt,s1) /\
  emit_op ADD [src; Lit 32w] s1 = (data,s2) /\
  emit_op ADD [slot; Lit 1w] s2 = (dst,sc) /\
  fn_has_code sa sc func /\ fn_inst_ids_distinct func /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p. gas_marked_path F ctx func s 0 (OK p) /\
    store_copy_normalize s p = s /\
    eval_operand cnt p = SOME (mload (w2n sw) s) /\
    eval_operand data p = SOME (sw + 32w) /\
    eval_operand dst p = SOME (dw + 1w) /\
    eval_operand slot p = SOME dw /\
    (!x. not_fresh_at sa x ==> lookup_var x p = lookup_var x s) /\
    p.vs_allocas = s.vs_allocas /\ p.vs_memory = s.vs_memory /\
    p.vs_labels = s.vs_labels /\ p.vs_call_ctx = s.vs_call_ctx /\
    ~p.vs_halted /\ p.vs_current_bb = sc.cs_current_bb /\
    p.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  strip_tac >>
  imp_res_tac typed_copy_emit_op_mono >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sc` by
    gvs[ci_mono_def] >>
  `cs_extends s1 sc` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 sc func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `!out. step_inst_base (mk_inst sa.cs_next_id MLOAD [src] [out]) s =
    OK (update_var out (mload (w2n sw) s) s)` by
    (gen_tac >> irule emitHelperPropsTheory.step_MLOAD >> simp[eval_operands_def]) >>
  drule_all (SRULE [is_terminator_def]
    (Q.INST [`opc` |-> `MLOAD`] place_store_emit_op_path)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path F ctx func s 0 (OK u)` >>
  qpat_x_assum `!off len. typed_copy_state_frame sa off len s u`
    (qspecl_then [`0`,`0`] assume_tac) >>
  `eval_operand src u = SOME sw /\ eval_operand slot u = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `!out. step_inst_base (mk_inst s1.cs_next_id ADD [src; Lit 32w] [out]) u =
    OK (update_var out (sw + 32w) u)` by
    (gen_tac >> irule emitHelperPropsTheory.step_ADD >> simp[eval_operand_def]) >>
  drule_all (SRULE [is_terminator_def]
    (Q.INST [`opc` |-> `ADD`, `sa` |-> `s1`] place_store_emit_op_path)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path F ctx func u 0 (OK w)` >>
  qpat_x_assum `!off len. typed_copy_state_frame s1 off len u w`
    (qspecl_then [`0`,`0`] assume_tac) >>
  `!x. slot = Var x ==> not_fresh_at s1 x` by
    (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `eval_operand slot w = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `!out. step_inst_base (mk_inst s2.cs_next_id ADD [slot; Lit 1w] [out]) w =
    OK (update_var out (dw + 1w) w)` by
    (gen_tac >> irule emitHelperPropsTheory.step_ADD >> simp[eval_operand_def]) >>
  drule_all (SRULE [is_terminator_def]
    (Q.INST [`opc` |-> `ADD`, `sa` |-> `s2`] place_store_emit_op_path)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "compose"
QED

Resume store_slots_dyn_prefix_path[compose]:
  rename1 `gas_marked_path F ctx func w 0 (OK t)` >>
  qpat_x_assum `!off len. typed_copy_state_frame s2 off len w t`
    (qspecl_then [`0`,`0`] assume_tac) >>
  `!x. cnt = Var x ==> not_fresh_at s1 x` by
    metis_tac[typed_copy_emit_op_fresh] >>
  `!x. data = Var x \/ cnt = Var x \/ slot = Var x ==>
     not_fresh_at s2 x` by
    (imp_res_tac typed_copy_emit_op_fresh >>
     gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `eval_operand cnt w = SOME (mload (w2n sw) s)` by
    metis_tac[typed_copy_state_frame_operand] >>
  `eval_operand cnt t = SOME (mload (w2n sw) s) /\
   eval_operand data t = SOME (sw + 32w) /\ eval_operand slot t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `typed_copy_state_frame sa 0 0 s t` by
    metis_tac[typed_copy_state_frame_mono, typed_copy_state_frame_trans] >>
  qexists_tac `t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  gvs[typed_copy_state_frame_def, store_copy_normalize_def,
      venom_state_component_equality]
QED

Finalise store_slots_dyn_prefix_path

Theorem store_slots_normalize_compose[local]:
  store_copy_normalize a (store_copy_normalize b t) = store_copy_normalize a t
Proof
  simp[store_copy_normalize_def]
QED

Theorem store_slots_normalize_store[local]:
  store_copy_normalize a ((if tr then tstore else sstore) k v t) =
    (if tr then tstore else sstore) k v (store_copy_normalize a t)
Proof
  Cases_on `tr` >> simp[store_copy_normalize_def, tstore_def, sstore_def]
QED

Theorem store_slots_dyn_fold_header[local]:
  store_copy_normalize s p = s /\ p.vs_memory = s.vs_memory /\
  w2n (sw:bytes32) + 32 < dimword (:256) /\
  store_copy_normalize p u =
    FOLDL (\q j. (if tr then tstore else sstore) ((dw + 1w) + n2w j)
      (mload (w2n (sw + 32w) + 32*j) p) q) p ks /\
  store_copy_normalize u t =
    (if tr then tstore else sstore) dw (mload (w2n sw) s) u ==>
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s (MAP SUC ks ++ [0])
Proof
  strip_tac >>
  `store_copy_normalize s u =
    FOLDL (\q j. (if tr then tstore else sstore) ((dw + 1w) + n2w j)
      (mload (w2n (sw + 32w) + 32*j) p) q) s ks` by
    (qpat_x_assum `store_copy_normalize p u = _`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     simp[store_slots_normalize_compose, store_slots_normalize_fold]) >>
  qpat_x_assum `store_copy_normalize u t = _`
    (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
  simp[store_slots_normalize_compose, store_slots_normalize_store,
       FOLDL_APPEND, FOLDL_MAP] >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (gvs[wordsTheory.word_add_def, wordsTheory.dimword_def]) >>
  `!j. dw + n2w (SUC j) = (dw + 1w) + n2w j` by
    (gen_tac >> simp[wordsTheory.n2w_SUC] >> wordsLib.WORD_DECIDE_TAC) >>
  `!j. mload (32*j + w2n (sw + 32w)) p =
        mload (32*SUC j + w2n sw) s` by
    (gen_tac >> `32*j + w2n (sw + 32w) = 32*SUC j + w2n sw` by decide_tac >>
     simp[mload_def]) >>
  asm_rewrite_tac[wordsTheory.WORD_ADD_0] >> simp[]
QED

(* A DynArray: its live elements, then its length word. *)
Theorem store_slots_dynarray_entry:
  !cenv tenv ctx elem n tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    evaluate_type tenv (ArrayT elem (Dynamic n)) = SOME tv /\
    value_has_type tv v /\
    (!cty ctv cv.
       type_rank cenv.ce_struct_fields cty <
         type_rank cenv.ce_struct_fields (ArrayT elem (Dynamic n)) /\
       evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
       store_slots_entry cenv ctx cty ctv cv) ==>
    store_slots_entry cenv ctx (ArrayT elem (Dynamic n)) tv v
Proof
  rpt gen_tac >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `evaluate_type tenv elem = SOME etv` >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV av)` >>
  Cases_on `av` >> gvs[value_has_type_def] >>
  rewrite_tac[store_slots_entry_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, is_abi_dynamic_def,
       is_bytestring_type_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, AllCaseEqs()] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `emit_op MLOAD [src] sa = (cnt,s1)` >>
  rename1 `emit_op ADD [src; Lit 32w] s1 = (data,s2)` >>
  rename1 `emit_op ADD [slot; Lit 1w] s2 = (dst,sc)` >>
  rename1 `emit_void (if tr then TSTORE else SSTORE) [slot; cnt] se = ((),sb)` >>
  Cases_on `_0` >>
  imp_res_tac typed_copy_emit_op_mono >>
  `ci_mono sc se` by
    (mp_tac (cj 3 stmtLoweringMonoTheory.ci_mono_compile_store_slots) >>
     disch_then (qspecl_then [`cenv`,`data`,`dst`,`elem`,`cnt`,`tr`,`sc`] mp_tac) >>
     simp[]) >>
  `ci_mono se sb` by
    (mp_tac (Q.SPECL [`if tr then TSTORE else SSTORE`,`[slot; cnt]`,`se`]
      ci_mono_emit_void) >> simp[]) >>
  `cs_extends sa sc /\ cs_extends sc se /\ cs_extends se sb` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sc func /\ fn_has_code sc se func /\ fn_has_code se sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  drule_all store_slots_dyn_prefix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path F ctx func s 0 (OK p)` >>
  suspend "elements"
QED

(* Successful type evaluation guards the literal element count, even for
   nested array types whose raw layout could otherwise have zero size. *)
Theorem store_slots_fixed_count_bound[local]:
  evaluate_type tenv (ArrayT elem (Fixed n)) = SOME tv ==>
  n < dimword (:256)
Proof
  simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
  rename1 `evaluate_type tenv elem = SOME etv` >>
  gvs[type_slot_size_def] >>
  `n <= n * type_slot_size etv` by
    (Cases_on `type_slot_size etv` >> gvs[MULT_CLAUSES]) >>
  decide_tac
QED

Theorem store_slots_sparse_support[local]:
  !sparse tv offset writes.
    encode_static_array tv offset sparse = SOME writes ==>
    !k. MEM k (MAP FST writes) <=>
      ?i v ew j. MEM (i,v) sparse /\ encode_value tv v = SOME ew /\
        MEM j (MAP FST ew) /\ k = offset + i * type_slot_size tv + j
Proof
  Induct >> simp[Once encode_value_def] >>
  Cases_on `h` >> simp[Once encode_value_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then (fn th => rewrite_tac[th]) >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
  eq_tac >> rpt strip_tac >> gvs[]
  >- (rename1 `MEM (off,w) slots` >>
      qexistsl_tac [`q`, `r`, `slots`, `off`] >>
      simp[AC ADD_ASSOC ADD_COMM] >> metis_tac[])
  >- metis_tac[]
  >- (disj1_tac >> rename1 `MEM (j,w) ew` >>
      qexistsl_tac [`w`, `j`] >> simp[AC ADD_ASSOC ADD_COMM])
  >> disj2_tac >> metis_tac[]
QED

Theorem store_slots_sarray_support[local]:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) /\
  encode_value (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) = SOME writes ==>
  !k. MEM k (MAP FST writes) <=>
    ?i ew j. i < n /\
      encode_value tv (case ALOOKUP sparse i of NONE => default_value tv
                      | SOME v => v) = SOME ew /\
      MEM j (MAP FST ew) /\ k = i * type_slot_size tv + j
Proof
  simp[Once encode_value_def, AllCaseEqs(), value_has_type_def] >>
  rpt strip_tac >> gvs[] >>
  drule store_slots_sparse_support >> strip_tac >>
  drule SORTED_lt_ALL_DISTINCT >> strip_tac >>
  simp[MEM_MAP, MEM_FLAT, MEM_GENLIST, pairTheory.EXISTS_PROD] >>
  eq_tac >> rpt strip_tac >> gvs[]
  >- (rename1 `ix < n` >>
      Cases_on `?v. MEM (ix,v) sparse` >> gvs[] >>
      gvs[MEM_MAP, pairTheory.EXISTS_PROD] >>
      `ALOOKUP sparse ix = NONE` by simp[alistTheory.ALOOKUP_NONE, MEM_MAP, pairTheory.EXISTS_PROD] >>
      qexistsl_tac [`ix`, `defaults`] >> simp[] >> metis_tac[ADD_COMM])
  >- (rename1 `MEM (i,v) sparse` >>
      `ALOOKUP sparse i = SOME v` by metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM] >>
      `i < n` by
        (drule sparse_has_type_all_less >> simp[EVERY_MEM] >>
         disch_then (qspec_then `(i,v)` mp_tac) >> simp[]) >>
      qexistsl_tac [`i`, `ew`] >> simp[] >> metis_tac[])
  >> Cases_on `ALOOKUP sparse i` >> gvs[]
  >- (disj1_tac >> rename1 `MEM (j,w) defaults` >>
      qexistsl_tac [`w`, `MAP (\(off,s). (off + i * type_slot_size tv,s)) defaults`] >>
      conj_tac
      >- (qexists_tac `i` >>
          gvs[alistTheory.ALOOKUP_NONE, MEM_MAP, pairTheory.EXISTS_PROD])
      >> simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[])
  >> disj2_tac >> rename1 `ALOOKUP sparse i = SOME v` >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  qexistsl_tac [`i`, `v`, `ew`, `j`] >> simp[] >> metis_tac[]

QED
Resume store_slots_dynarray_entry[elements]:
  `type_memory_bytes cenv elem = type_memory_size etv` by
    (irule typed_copy_memory_size >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  `mload (w2n sw) s = n2w (LENGTH l) /\
   elems_in_memory l (w2n sw + 32) etv s.vs_memory` by
    gvs[val_in_memory_dynarray, mem_word_at_eq_mload] >>
  `!i. i < LENGTH l ==> store_slots_entry cenv ctx elem etv (EL i l) /\
      IS_SOME (encode_value etv (EL i l)) /\
      val_in_memory etv (EL i l) (w2n sw + 32 + i * type_memory_size etv)
        p.vs_memory` by
    (gen_tac >> strip_tac >> conj_tac
     >- (first_x_assum irule >> simp[type_rank_def] >>
         gvs[all_have_type_EVERY, EVERY_EL]) >>
     conj_tac
     >- (irule store_slots_dyn_element_encoded >>
         gvs[Once encode_value_def, AllCaseEqs()] >> metis_tac[]) >>
     drule_all exprSimAggregateEncodingTheory.elems_in_memory_EL >>
     metis_tac[ADD_ASSOC]) >>
  `LENGTH l * type_slot_size etv <= n * type_slot_size etv` by
    simp[] >>
  `LENGTH l <= LENGTH l * type_slot_size etv` by
    simp[] >>
  `w2n sw + 32 + LENGTH l * type_memory_size etv < dimword (:256) /\
   w2n dw + 1 + LENGTH l * type_slot_size etv <= dimword (:256) /\
   LENGTH l < dimword (:256) /\ w2n sw + 32 < dimword (:256)` by
    (qpat_x_assum `w2n sw + type_memory_size _ < _` mp_tac >>
     qpat_x_assum `w2n dw + type_slot_size _ <= _` mp_tac >>
     pure_rewrite_tac[type_memory_size_slots, type_slot_size_def, LEFT_ADD_DISTRIB, MULT_ASSOC] >>
     rpt strip_tac >> decide_tac) >>
  `0 < n * type_slot_size etv` by simp[] >>
  `w2n dw + 1 < dimword (:256)` by
    (qpat_x_assum `w2n dw + type_slot_size _ <= _` mp_tac >>
     pure_rewrite_tac[type_slot_size_def] >> decide_tac) >>
  `w2n (sw + 32w) = w2n sw + 32 /\ w2n (dw + 1w) = w2n dw + 1` by
    (gvs[wordsTheory.word_add_def, wordsTheory.dimword_def]) >>
  `!x. data = Var x \/ dst = Var x \/ cnt = Var x \/ slot = Var x ==>
       not_fresh_at sc x` by
    metis_tac[store_slots_dyn_prefix_fresh] >>
  mp_tac (Q.INST [`el` |-> `\i. EL i (l:value list)`, `N` |-> `LENGTH (l:value list)`,
                  `s` |-> `p`, `sw` |-> `sw + 32w`, `dw` |-> `dw + 1w`,
                  `src` |-> `data`, `slot` |-> `dst`,
                  `sa` |-> `sc`, `sb` |-> `se`]
    (SPEC_ALL store_slots_elements_run)) >>
  (impl_tac >- (asm_rewrite_tac[] >> BETA_TAC >> metis_tac[])) >>
  strip_tac >>
  suspend "header"
QED

Resume store_slots_dynarray_entry[header]:
  rename1 `gas_marked_path F ctx func p 0 (OK u)` >>
  `eval_operand slot u = SOME dw /\
   eval_operand cnt u = SOME (mload (w2n sw) s)` by
    (conj_tac
     >- (Cases_on `slot` >> gvs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `cnt` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `~u.vs_call_ctx.cc_static` by metis_tac[] >>
  drule_all place_store_emit_slot_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "finish"
QED

Resume store_slots_dynarray_entry[finish]:
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func u 0 (OK t)` >>
  `store_copy_normalize u t =
    (if tr then tstore else sstore) dw (mload (w2n sw) s) u` by
    (Cases_on `tr` >>
     simp[Abbr `t`, store_copy_normalize_def, sstore_def, tstore_def,
          venom_state_component_equality]) >>
  `store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s (MAP SUC ks ++ [0])` by
    (irule store_slots_dyn_fold_header >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  qexistsl_tac [`t`, `MAP SUC ks ++ [0]`] >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  conj_tac >- (qpat_x_assum `store_copy_normalize s t = _` mp_tac >>
                 simp[Once ADD_COMM]) >>
  conj_tac >- suspend "support" >>
  suspend "frame"
QED

Resume store_slots_dynarray_entry[support]:
  drule store_slots_dynarray_encoding_support >> strip_tac >>
  simp[MEM_APPEND, MEM_MAP] >>
  qpat_x_assum `!k. MEM k ks <=> _` mp_tac >>
  BETA_TAC >> rpt strip_tac >>
  eq_tac >> strip_tac >> gvs[] >>
  metis_tac[ADD1, ADD_ASSOC]
QED

Resume store_slots_dynarray_entry[frame]:
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    metis_tac[] >>
  Cases_on `tr` >>
  simp[Abbr `t`, sstore_def, tstore_def, lookup_var_def] >>
  metis_tac[lookup_var_def]
QED

Finalise store_slots_dynarray_entry

(* A static array with a DynArray or bytestring inside: each element. *)
Theorem store_slots_sarray_entry:
  !cenv tenv ctx elem n tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_abi_dynamic cenv.ce_struct_fields (ArrayT elem (Fixed n)) /\
    evaluate_type tenv (ArrayT elem (Fixed n)) = SOME tv /\
    value_has_type tv v /\
    (!cty ctv cv.
       type_rank cenv.ce_struct_fields cty <
         type_rank cenv.ce_struct_fields (ArrayT elem (Fixed n)) /\
       evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
       store_slots_entry cenv ctx cty ctv cv) ==>
    store_slots_entry cenv ctx (ArrayT elem (Fixed n)) tv v
Proof
  rpt strip_tac >>
  `n < dimword (:256)` by metis_tac[store_slots_fixed_count_bound] >>
  qpat_x_assum `evaluate_type tenv (ArrayT elem (Fixed n)) = SOME tv` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `evaluate_type tenv elem = SOME etv` >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `value_has_type (ArrayTV etv (Fixed n)) (ArrayV av)` >>
  Cases_on `av` >> gvs[value_has_type_def] >>
  rename1 `sparse_has_type etv n sparse` >>
  simp[store_slots_entry_def] >> rpt strip_tac >>
  `type_memory_bytes cenv elem = type_memory_size etv` by
    (irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, is_abi_dynamic_def, is_bytestring_type_def] >>
  strip_tac >>
  `!i. i < n ==>
     value_has_type etv (case ALOOKUP sparse i of NONE => default_value etv | SOME v => v)` by
    (rpt strip_tac >> Cases_on `ALOOKUP sparse i` >>
     simp[default_value_well_typed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
  `!i. i < n ==>
     val_in_memory etv (case ALOOKUP sparse i of NONE => default_value etv | SOME v => v)
       (w2n sw + i * type_memory_size etv) s.vs_memory` by
    (gvs[val_in_memory_sarray] >> rpt strip_tac >>
     Cases_on `ALOOKUP sparse i` >> simp[] >>
     metis_tac[valueEncodingProofsTheory.kvs_in_memory_lookup]) >>
  drule store_slots_elements_run >>
  disch_then (qspecl_then [`ctx`, `etv`,
    `\i. case ALOOKUP sparse i of NONE => default_value etv | SOME v => v`,
    `n`, `func`, `s`, `sw`, `dw`] mp_tac) >>
  (impl_tac >-
    (simp[eval_operand_def] >> rpt conj_tac
     >- (gen_tac >> disch_tac >> simp[] >> conj_tac
         >- (qpat_x_assum `!cty ctv cv. _ ==> store_slots_entry _ _ _ _ _` irule >>
             simp[type_rank_def])
         >> metis_tac[value_has_type_equiv])
     >> gvs[type_memory_size_def, type_slot_size_def])) >>
  strip_tac >> qexistsl_tac [`t`, `ks`] >> simp[] >>
  mp_tac (Q.INST [`tv` |-> `etv`] store_slots_sarray_support) >>
  simp[value_has_type_def, ADD_COMM]
QED

Theorem store_slots_lit_offset_path[local]:
  !ptr off sa op sb s w func ctx.
  compile_lit_byte_offset ptr off sa = (op,sb) /\
  eval_operand ptr s = SOME w /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand op t = SOME (w + n2w off) /\
      t.vs_memory = s.vs_memory /\
      (!dst len. typed_copy_state_frame sa dst len s t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  map_every qx_gen_tac [`ptr0`, `off`, `sa`, `op`, `sb`, `s`, `w`, `func`, `ctx`] >>
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules,
           typed_copy_state_frame_def, typed_copy_frame_def,
           wordsTheory.WORD_ADD_0, venom_state_component_equality]) >>
  Cases_on `ptr0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def, eval_operand_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules,
           eval_operand_def, typed_copy_state_frame_def, typed_copy_frame_def,
           wordsTheory.WORD_ADD_0, venom_state_component_equality]) >>
  simp[compile_lit_byte_offset_def] >> strip_tac >>
  irule place_store_offset_path >>
  simp[compile_with_byte_offset_def] >> metis_tac[]
QED

Theorem store_slots_lit_offset_fresh:
  !ptr0 off sa op sb.
  compile_lit_byte_offset ptr0 off sa = (op,sb) /\
  (!x. ptr0 = Var x ==> not_fresh_at sa x) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  rpt gen_tac >> Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >> metis_tac[]) >>
  Cases_on `ptr0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  simp[compile_lit_byte_offset_def] >> rpt strip_tac >>
  drule typed_copy_emit_op_fresh >> simp[]
QED

Theorem store_slots_member_offset_run[local]:
  compile_lit_byte_offset src mo sa = (ms,a) /\
  compile_lit_byte_offset slot so a = (ds,b) /\
  compile_store_slots cenv ms ds ty tr b = ((),sc) /\
  store_slots_entry cenv ctx ty tv v /\ encode_value tv v = SOME writes /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  val_in_memory tv v (w2n sw + mo) s.vs_memory /\
  w2n sw + mo + type_memory_size tv < dimword (:256) /\
  w2n dw + so + type_slot_size tv <= dimword (:256) /\
  fn_has_code sa sc func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
  ?t ks. gas_marked_path F ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) ((dw + n2w so) + n2w j)
        (mload (w2n sw + mo + 32 * j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  strip_tac >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b sc` by
    metis_tac[ci_mono_compile_lit_byte_offset,
              cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots, pairTheory.SND] >>
  `fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b sc func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]) >>
  `(!x. slot = Var x ==> not_fresh_at a x) /\
   (!x. ms = Var x ==> not_fresh_at a x) /\
   (!x. ms = Var x \/ ds = Var x ==> not_fresh_at b x)` by
    metis_tac[store_slots_lit_offset_fresh, typed_copy_operand_fresh_mono] >>
  qpat_assum `compile_lit_byte_offset src _ _ = _` mp_tac >>
  disch_then (mp_then Any mp_tac store_slots_lit_offset_path) >>
  disch_then (qspecl_then [`s`, `sw`, `func`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `q1` strip_assume_tac) >>
  `eval_operand slot q1 = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  qpat_assum `compile_lit_byte_offset slot _ _ = _` mp_tac >>
  disch_then (mp_then Any mp_tac store_slots_lit_offset_path) >>
  disch_then (qspecl_then [`q1`, `dw`, `func`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `q2` strip_assume_tac) >>
  `eval_operand ms q2 = SOME (sw + n2w mo)` by
    metis_tac[typed_copy_state_frame_operand] >>
  `w2n (sw + n2w mo) = w2n sw + mo` by
    (irule typed_copy_offset_nonwrap >> decide_tac) >>
  `w2n (dw + n2w so) + type_slot_size tv <= dimword (:256)` by
    (simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >>
     mp_tac (Q.INST [`x` |-> `so + w2n (dw:bytes32)`, `y` |-> `dimword (:256)`]
       arithmeticTheory.MOD_LESS_EQ) >> simp[] >> decide_tac) >>
  `q2.vs_call_ctx = s.vs_call_ctx` by
    (fs[typed_copy_state_frame_def, venom_state_component_equality]) >>
  qpat_x_assum `store_slots_entry _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[store_slots_entry_def] >>
  disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`func`, `q2`, `sw + n2w mo`, `dw + n2w so`, `writes`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[ADD_COMM])) >>
  disch_then (qx_choose_then `t` (qx_choose_then `ks` strip_assume_tac)) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  `!dst len. typed_copy_state_frame sa dst len s q2` by
    metis_tac[typed_copy_state_frame_trans, typed_copy_state_frame_mono] >>
  `!x. not_fresh_at sa x ==> not_fresh_at b x` by
    (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qexistsl_tac [`t`, `ks`] >> simp[] >>
  reverse conj_tac
  >- (fs[typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  `store_copy_normalize s q2 = s` by
    (fs[typed_copy_state_frame_def, store_copy_normalize_def,
        venom_state_component_equality] >> metis_tac[]) >>
  qpat_x_assum `store_copy_normalize q2 t = _`
    (mp_tac o AP_TERM ``store_copy_normalize s``) >>
  simp[store_slots_normalize_fold] >>
  simp[store_copy_normalize_def, mload_def]
QED

Theorem store_slots_fold_compose:
  u.vs_memory = s.vs_memory /\
  store_copy_normalize s u =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32 * j) s) q) s hs /\
  store_copy_normalize u t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32 * j) u) q) u ts ==>
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32 * j) s) q) s (hs ++ ts)
Proof
  strip_tac >>
  qpat_x_assum `store_copy_normalize u t = _`
    (mp_tac o AP_TERM ``store_copy_normalize s``) >>
  simp[store_slots_normalize_fold, FOLDL_APPEND, mload_def] >>
  simp[store_copy_normalize_def]
QED

(* Struct or tuple members as (type, memory size) pairs, member i at
   memory src + mo + its memory prefix and at slot dw + so + its slot
   prefix. *)
Theorem store_slots_members_run:
  !members tvs vs cenv ctx mo so src slot tr sa sb func s sw dw.
    compile_store_slots_members cenv src slot members mo so tr sa = ((),sb) /\
    LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
                               store_slots_entry cenv ctx ty tv v /\
                               IS_SOME (encode_value tv v))
      members (ZIP (tvs,vs)) /\
    LENGTH vs = LENGTH tvs /\ mo = 32 * so /\
    tuple_in_memory vs tvs (w2n sw + mo) s.vs_memory /\
    (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
    w2n sw + mo + type_memory_size_list tvs < dimword (:256) /\
    w2n dw + so + type_slot_size_list tvs <= dimword (:256) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_call_ctx.cc_static ==>
    ?t ks.
      gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                 (mload (w2n sw + 32 * j) s) q) s ks /\
      (!k. MEM k ks <=>
         ?i writes j. i < LENGTH tvs /\
           encode_value (EL i tvs) (EL i vs) = SOME writes /\
           MEM j (MAP FST writes) /\ k = so + tuple_prefix_slot_size i tvs + j) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Induct_on `members`
  >- (rpt gen_tac >>
      simp[Once compile_store_slots_def, comp_return_def] >> strip_tac >>
      `tvs = [] /\ vs = []` by
        (Cases_on `tvs` >> Cases_on `vs` >> gvs[]) >>
      gvs[] >> qexistsl_tac [`s`, `[]`] >>
      simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules,
           store_copy_normalize_def, venom_state_component_equality]) >>
  qx_gen_tac `hdmem` >> PairCases_on `hdmem` >>
  Cases_on `tvs` >> Cases_on `vs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[Once compile_store_slots_def, comp_bind_def, comp_ignore_bind_def,
      AllCaseEqs()] >>
  rename1 `store_slots_entry cenv ctx ty tv v` >>
  rename1 `ZIP (tvs,vs)` >>
  Cases_on `compile_lit_byte_offset src (32 * so) sa` >>
  rename1 `compile_lit_byte_offset src (32 * so) sa = (ms,a)` >>
  Cases_on `compile_lit_byte_offset slot so a` >>
  rename1 `compile_lit_byte_offset slot so a = (ds,b)` >>
  Cases_on `compile_store_slots cenv ms ds ty tr b` >>
  rename1 `compile_store_slots cenv ms ds ty tr b = (u,sc)` >>
  Cases_on `u` >> gvs[] >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b sc /\ ci_mono sc sb` by
    metis_tac[ci_mono_compile_lit_byte_offset,
      cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots,
      cj 2 stmtLoweringMonoTheory.ci_mono_compile_store_slots, pairTheory.SND] >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]) >>
  gvs[Once val_in_memory_def, type_memory_size_def, type_slot_size_def,
      type_memory_size_slots] >>
  `?writes. encode_value tv v = SOME writes` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
  `w2n sw + 32 * so + type_memory_size tv < dimword (:256) /\
   w2n dw + so + type_slot_size tv <= dimword (:256)` by
    (fs[type_memory_size_slots] >> decide_tac) >>
  `val_in_memory tv v (w2n sw + 32 * so) s.vs_memory` by metis_tac[ADD_COMM] >>
  drule_all store_slots_member_offset_run >>
  disch_then (qx_choose_then `u` (qx_choose_then `hs` strip_assume_tac)) >>
  `eval_operand src u = SOME sw /\ eval_operand slot u = SOME dw` by
    (conj_tac >> Cases_on `src` >> Cases_on `slot` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. src = Var x \/ slot = Var x ==> not_fresh_at sc x` by
    (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qpat_x_assum `!tvs vs cenv ctx so src slot tr sa sb func s sw dw. _`
    (qspecl_then [`tvs`, `vs`, `cenv`, `ctx`, `so + type_slot_size tv`,
                  `src`, `slot`, `tr`, `sc`, `sb`, `func`, `u`, `sw`, `dw`] mp_tac) >>
  (impl_tac >- metis_tac[LEFT_ADD_DISTRIB, ADD_ASSOC]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `ts` strip_assume_tac)) >>
  `store_copy_normalize s u =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32 * j) s) q) s (MAP ((+) so) hs)` by
    (qpat_x_assum `store_copy_normalize s u = _` mp_tac >>
     pure_rewrite_tac[FOLDL_MAP] >> BETA_TAC >>
     pure_rewrite_tac[GSYM wordsTheory.word_add_n2w, LEFT_ADD_DISTRIB,
       ADD_ASSOC, GSYM wordsTheory.WORD_ADD_ASSOC] >> simp[NoAsms]) >>
  `store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32 * j) s) q) s (MAP ((+) so) hs ++ ts)` by
    (irule store_slots_fold_compose >> qexists_tac `u` >> simp[] >>
     qpat_x_assum `store_copy_normalize u t = _` mp_tac >>
     simp[NoAsms, ADD_COMM]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  qexistsl_tac [`t`, `MAP ((+) so) hs ++ ts`] >> simp[] >>
  reverse conj_tac
  >- (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qpat_x_assum `!k. MEM k ts <=> _` mp_tac >>
  qpat_x_assum `!j. MEM j hs <=> _` mp_tac >>
  qpat_x_assum `encode_value tv v = SOME writes` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  simp[MEM_MAP] >>
  CONV_TAC (RHS_CONV (HO_REWR_CONV arithmeticTheory.EXISTS_NUM)) >>
  simp[tuple_prefix_slot_size_def] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  rpt (pop_assum kall_tac) >>
  metis_tac[ADD_COMM]
QED

Theorem store_slots_tuple_support:
  !tvs vs off writes.
    LENGTH vs = LENGTH tvs /\ encode_tuple off tvs vs = SOME writes ==>
    !k. MEM k (MAP FST writes) <=>
      ?i child j. i < LENGTH tvs /\
        encode_value (EL i tvs) (EL i vs) = SOME child /\
        MEM j (MAP FST child) /\
        k = off + tuple_prefix_slot_size i tvs + j
Proof
  Induct_on `tvs` >- simp[encode_value_def] >>
  Cases_on `vs` >> simp[encode_value_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  rename1 `encode_value headtv headv = SOME slots` >>
  rename1 `encode_tuple (off + type_slot_size headtv) tvs tailvs = SOME rest` >>
  first_x_assum (qspecl_then [`tailvs`, `off + type_slot_size headtv`, `rest`] mp_tac) >>
  simp[] >> disch_tac >> gen_tac >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MEM_MAP, pairTheory.EXISTS_PROD] >>
  eq_tac
  >- (strip_tac
      >- (qexists_tac `0` >> simp[tuple_prefix_slot_size_def] >> metis_tac[ADD_COMM]) >>
      first_x_assum (qspec_then `k` mp_tac) >> simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
      strip_tac >> qexists_tac `SUC i` >>
      simp[tuple_prefix_slot_size_def] >> metis_tac[ADD_ASSOC, ADD_COMM]) >>
  strip_tac >> Cases_on `i` >> gvs[tuple_prefix_slot_size_def]
  >- (disj1_tac >> rename1 `MEM (j,word) child` >>
      qexistsl_tac [`word`, `j`] >> simp[]) >>
  rename1 `idx < LENGTH tvs` >>
  disj2_tac >> qexistsl_tac [`idx`, `child`, `j`] >> simp[] >> metis_tac[]
QED

(* A tuple with a DynArray or bytestring inside: each member. *)
Theorem store_slots_tuple_entry:
  !cenv tenv ctx tys tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_abi_dynamic cenv.ce_struct_fields (TupleT tys) /\
    evaluate_type tenv (TupleT tys) = SOME tv /\ value_has_type tv v /\
    (!cty ctv cv.
       type_rank cenv.ce_struct_fields cty <
         type_rank cenv.ce_struct_fields (TupleT tys) /\
       evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
       store_slots_entry cenv ctx cty ctv cv) ==>
    store_slots_entry cenv ctx (TupleT tys) tv v
Proof
  rpt gen_tac >> strip_tac >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `value_has_type (TupleTV tvs) (ArrayV av)` >>
  Cases_on `av` >> gvs[value_has_type_def] >>
  rename1 `values_have_types tvs vs` >>
  `LENGTH vs = LENGTH tvs` by metis_tac[values_have_types_length] >>
  `LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
       store_slots_entry cenv ctx ty tv v /\ IS_SOME (encode_value tv v))
       (MAP (\ty. (ty,type_memory_bytes cenv ty)) tys) (ZIP (tvs,vs))` by
    (gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
     simp[LIST_REL_EL_EQN, EL_MAP, EL_ZIP] >> rpt strip_tac >>
     rename1 `idx < LENGTH tvs` >>
     `evaluate_type tenv (EL idx tys) = SOME (EL idx tvs)` by metis_tac[] >>
     `value_has_type (EL idx tvs) (EL idx vs)` by metis_tac[] >>
     rpt conj_tac
     >- (irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[])
     >- (first_x_assum irule >> simp[] >> irule member_rank_lt_tuple >> simp[EL_MEM]) >>
     metis_tac[value_has_type_equiv]) >>
  rewrite_tac[store_slots_entry_def] >> rpt gen_tac >> strip_tac >>
  gvs[Once compile_store_slots_def, is_bytestring_type_def,
      val_in_memory_def, type_memory_size_def, type_slot_size_def, encode_value_def] >>
  drule store_slots_members_run >>
  disch_then (qspecl_then [`tvs`, `vs`, `ctx`, `func`, `s`, `sw`, `dw`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl_tac [`t`, `ks`] >> simp[] >>
  drule_all store_slots_tuple_support >> simp[]
QED

Theorem store_slots_fields_align[local]:
  !fields tvs vs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    values_have_types tvs vs /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields /\
    (!fname ty sz tv v. MEM (fname,ty,sz) fields /\
      evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
      store_slots_entry cenv ctx ty tv v) ==>
    LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
      store_slots_entry cenv ctx ty tv v /\ IS_SOME (encode_value tv v))
      (MAP SND fields) (ZIP (tvs,vs))
Proof
  Induct
  >- (simp[] >> rpt strip_tac >> Cases_on `vs` >>
      gvs[value_has_type_def]) >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `vs` >> gvs[value_has_type_def] >>
  simp[] >> conj_tac
  >- metis_tac[value_has_type_equiv] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem store_slots_struct_align[local]:
  !cenv tenv ctx nsid tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    evaluate_type tenv (StructT nsid) = SOME tv /\ value_has_type tv v /\
    (!cty ctv cv. type_rank cenv.ce_struct_fields cty <
       type_rank cenv.ce_struct_fields (StructT nsid) /\
       evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
       store_slots_entry cenv ctx cty ctv cv) ==>
    ?fields tvs vals.
      FLOOKUP cenv.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
      tv = StructTV (ZIP (MAP FST fields,tvs)) /\ v = StructV vals /\
      LENGTH fields = LENGTH tvs /\ LENGTH vals = LENGTH tvs /\
      LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
        store_slots_entry cenv ctx ty tv v /\ IS_SOME (encode_value tv v))
        (MAP SND fields) (ZIP (tvs,MAP SND vals))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv nsid = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `struct_has_type _ vals` >>
  `fields_val_wf vals (ZIP (MAP FST args,tvs))` by
    metis_tac[cj 5 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `values_have_types tvs (MAP SND vals) /\ LENGTH vals = LENGTH tvs` by
    metis_tac[place_store_struct_tuple_values, listTheory.LENGTH_MAP] >>
  qexists_tac `tvs` >> simp[] >>
  conj_tac >- metis_tac[listTheory.LENGTH_MAP] >>
  irule store_slots_fields_align >> simp[] >> qexists_tac `tenv` >>
  fs[evaluate_types_OPT_MMAP] >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >>
      once_rewrite_tac[type_rank_nsid] >> irule member_rank_lt_struct >>
      simp[get_struct_fields_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem store_slots_struct_support:
  !fts vals off writes.
    encode_struct off fts vals = SOME writes ==>
    !k. MEM k (MAP FST writes) <=>
      ?i ws j. i < LENGTH fts /\
        encode_value (SND (EL i fts)) (SND (EL i vals)) = SOME ws /\
        MEM j (MAP FST ws) /\
        k = off + tuple_prefix_slot_size i (MAP SND fts) + j
Proof
  Induct
  >- (Cases_on `vals` >> simp[encode_value_def]) >>
  rpt gen_tac >> PairCases_on `h` >> Cases_on `vals`
  >- simp[encode_value_def] >>
  rename1 `encode_struct off ((nm,tv)::fts) (p::vals)` >>
  PairCases_on `p` >>
  simp[encode_value_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then (qspec_then `k` mp_tac) >>
  simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD,
       listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  strip_tac >> eq_tac
  >- (strip_tac
      >- (qexists_tac `0` >> simp[tuple_prefix_slot_size_def] >> metis_tac[ADD_COMM]) >>
      qexists_tac `SUC i` >> simp[tuple_prefix_slot_size_def] >>
      metis_tac[]) >>
  strip_tac >> Cases_on `i` >>
  gvs[tuple_prefix_slot_size_def] >> metis_tac[ADD_COMM]
QED

(* A struct with a DynArray or bytestring inside: each field. *)
Theorem store_slots_struct_entry:
  !cenv tenv ctx nsid tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_abi_dynamic cenv.ce_struct_fields (StructT nsid) /\
    evaluate_type tenv (StructT nsid) = SOME tv /\ value_has_type tv v /\
    (!cty ctv cv.
       type_rank cenv.ce_struct_fields cty <
         type_rank cenv.ce_struct_fields (StructT nsid) /\
       evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
       store_slots_entry cenv ctx cty ctv cv) ==>
    store_slots_entry cenv ctx (StructT nsid) tv v
Proof
  rpt gen_tac >> strip_tac >>
  `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields` by
    metis_tac[] >>
  drule_all store_slots_struct_align >> strip_tac >> gvs[] >>
  simp[store_slots_entry_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, is_bytestring_type_def,
       get_struct_fields_def] >> strip_tac >>
  fs[valueEncodingTheory.val_in_memory_def,
     valueEncodingProofsTheory.fields_in_memory_tuple, listTheory.MAP_ZIP,
     valueEncodingTheory.type_memory_size_def,
     valueEncodingTypingTheory.type_memory_size_fields_zip,
     type_slot_size_def, vyperStorageRegionWriteTheory.type_slot_size_fields_list] >>
  `LENGTH (MAP FST fields) = LENGTH tvs` by simp[] >>
  fs[listTheory.MAP_ZIP, valueEncodingTypingTheory.type_memory_size_fields_zip] >>
  drule store_slots_members_run >>
  disch_then (qspecl_then [`tvs`, `MAP SND vals`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qspecl_then [`func`, `s`, `sw`, `dw`] mp_tac) >>
  simp[] >> (impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[])) >>
  strip_tac >> qexistsl_tac [`t`, `ks`] >> simp[] >>
  `!i. i < LENGTH tvs ==>
    SND (EL i (ZIP (MAP FST fields,tvs))) = EL i tvs /\
    SND (EL i vals) = EL i (MAP SND vals)` by
    (rpt strip_tac >> simp[listTheory.EL_ZIP, listTheory.EL_MAP]) >>
  fs[encode_value_def] >> drule store_slots_struct_support >>
  simp[listTheory.MAP_ZIP] >>
  disch_then (fn th => assume_tac th) >>
  gen_tac >> first_x_assum (qspec_then `j` mp_tac) >>
  simp[SF CONJ_ss]
QED

Theorem store_slots_rank_entry:
  !n cenv tenv ctx ty tv v.
    type_rank cenv.ce_struct_fields ty = n /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    store_slots_entry cenv ctx ty tv v
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `is_abi_dynamic cenv.ce_struct_fields ty`
  >- suspend "dynamic" >>
  irule store_slots_static_entry >> gvs[] >> qexists_tac `tenv` >> asm_rewrite_tac[]
QED
Resume store_slots_rank_entry[dynamic]:
  `!cty ctv cv.
     type_rank cenv.ce_struct_fields cty < type_rank cenv.ce_struct_fields ty /\
     evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
     store_slots_entry cenv ctx cty ctv cv` by
    (rpt strip_tac >>
     last_x_assum (qspec_then `type_rank cenv.ce_struct_fields cty` mp_tac) >>
     simp[] >> disch_then irule >> gvs[] >> qexists_tac `tenv` >> asm_rewrite_tac[]) >>
  Cases_on `is_bytestring_type ty`
  >- (irule store_slots_bytes_entry >> gvs[] >> qexists_tac `tenv` >> asm_rewrite_tac[]) >>
  Cases_on `ty`
  >~ [`ArrayT elem bd`]
  >- (Cases_on `bd`
      >- (irule store_slots_sarray_entry >> gvs[] >> qexists_tac `tenv` >> asm_rewrite_tac[])
      >> irule store_slots_dynarray_entry >> gvs[] >> qexists_tac `tenv` >> asm_rewrite_tac[])
  >~ [`TupleT tys`]
  >- (irule store_slots_tuple_entry >> gvs[] >> qexists_tac `tenv` >> asm_rewrite_tac[])
  >~ [`StructT nsid`]
  >- (irule store_slots_struct_entry >> gvs[] >> qexists_tac `tenv` >> asm_rewrite_tac[])
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_abi_dynamic_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_abi_dynamic_def, is_bytestring_type_def]) >>
  gvs[is_abi_dynamic_def]
QED
Finalise store_slots_rank_entry

Theorem place_store_dead_bytes_write_frame[local]:
  !base sz writes delta tv st j b.
    base + sz <= dimword (:256) /\
    (!off. MEM off (MAP FST writes) ==> off < sz) /\
    delta + type_slot_size tv <= sz /\
    (!off. MEM off (MAP FST writes) ==>
       off < delta \/ delta + type_slot_size tv <= off) ==>
    (dead_bytes (apply_writes (n2w base) writes st)
       (base + delta) tv j b <=> dead_bytes st (base + delta) tv j b)
Proof
  rpt strip_tac >>
  irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
  rename1 `apply_writes (n2w root) writes st` >>
  `i = root + (i - root)` by decide_tac >>
  once_asm_rewrite_tac [] >>
  irule vyperEncodeDecodeTheory.apply_writes_lookup_miss_num >>
  gen_tac >> disch_tac >>
  irule vyperEncodeDecodeTheory.n2w_add_cancel >>
  `off < sz` by metis_tac [] >>
  `off < delta \/ delta + type_slot_size tv <= off` by metis_tac [] >>
  decide_tac
QED

Theorem place_store_bytes_unwritten_dead[local]:
  !max bs writes base i b st.
    encode_dyn_bytes_slots max bs = SOME writes /\
    base + (1 + word_size max) <= dimword (:256) /\
    i < 1 + word_size max /\ b < 32 /\ ~MEM i (MAP FST writes) ==>
    dyn_bytes_dead (apply_writes (n2w base) writes st) base max (base + i) b
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `apply_writes (n2w root) writes st` >>
  drule vyperEncodeDecodeTheory.encode_dyn_bytes_slots_keys >>
  disch_then (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  `lookup_storage (n2w root) (apply_writes (n2w root) writes st) =
     n2w (LENGTH bs)` by
    (irule place_store_dyn_bytes_header >>
     qexists_tac `max` >> simp[wordsTheory.w2n_n2w] >>
     `root < dimword (:256)` by decide_tac >>
     simp[LESS_MOD] >> decide_tac) >>
  `LENGTH bs <= 32 * word_size (LENGTH bs)` by
    simp[exprSimPropsTheory.le_word_size_mul] >>
  simp[dyn_bytes_dead_def, wordsTheory.w2n_n2w] >>
  `LENGTH bs MOD dimword (:256) <= LENGTH bs` by simp[MOD_LESS_EQ] >>
  decide_tac
QED

Theorem place_store_tuple_unwritten_dead[local]:
  !tvs offset vs writes root st j b.
    (!tv. MEM tv tvs ==> !v ws bs s k c.
      encode_value tv v = SOME ws /\ value_has_type tv v /\
      bs + type_slot_size tv <= dimword (:256) /\
      ~MEM (k - bs) (MAP FST ws) /\ dead_bytes s bs tv k c ==>
      dead_bytes (apply_writes (n2w bs) ws s) bs tv k c) /\
    encode_tuple offset tvs vs = SOME writes /\ values_have_types tvs vs /\
    root + offset + type_slot_size_list tvs <= dimword (:256) /\
    ~MEM (j - root) (MAP FST writes) /\
    dead_bytes_list st (root + offset) tvs j b ==>
    dead_bytes_list (apply_writes (n2w root) writes st) (root + offset) tvs j b
Proof
  Induct >> simp[Once encode_value_def, dead_bytes_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `vs` >> gvs[value_has_type_def, Once encode_value_def, AllCaseEqs()] >>
  `!off. MEM off (MAP FST slots) ==> off < type_slot_size h` by
    metis_tac[vyperEncodeDecodeTheory.encode_writes_bounded] >>
  `!off. MEM off (MAP FST rest) ==> offset + type_slot_size h <= off /\
     off < offset + type_slot_size h + type_slot_size_list tvs` by
    metis_tac[vyperEncodeDecodeTheory.encode_writes_bounded]
  >- (disj1_tac >>
      rewrite_tac[vyperEncodeDecodeTheory.apply_writes_append] >>
      `dead_bytes (apply_writes (n2w root) rest
          (apply_writes (n2w root) (MAP (\(off,s). (off + offset,s)) slots) st))
          (root + offset) h j b <=>
       dead_bytes (apply_writes (n2w root) (MAP (\(off,s). (off + offset,s)) slots) st)
          (root + offset) h j b` by
        (irule place_store_dead_bytes_write_frame >>
         conj_tac >- metis_tac[] >>
         qexists_tac `offset + type_slot_size_list (h::tvs)` >>
         simp[type_slot_size_def] >>
         conj_tac >- (rpt strip_tac >> gvs[]) >>
         gvs[type_slot_size_def]) >>
      fs[ADD_COMM, vyperEncodeDecodeTheory.apply_writes_shift] >>
      drule (cj 1 dead_bytes_range) >> strip_tac >>
      `~MEM (j - (offset + root)) (MAP FST slots)` by
        (strip_tac >> drule MEM_shifted_write >>
         disch_then (qspec_then `offset` mp_tac) >>
         `j - (offset + root) + offset = j - root` by decide_tac >>
         gvs[ADD_COMM]) >>
      qpat_x_assum `!tv. tv = h \/ _ ==> _` (qspec_then `h` mp_tac) >>
      simp[] >> disch_then irule >>
      simp[] >> conj_tac
      >- (gvs[type_slot_size_def] >> decide_tac) >>
      qexists_tac `h'` >> simp[]) >>
  disj2_tac >> rewrite_tac[vyperEncodeDecodeTheory.apply_writes_append] >>
  `dead_bytes_list
     (apply_writes (n2w root) (MAP (\(off,s). (off + offset,s)) slots) st)
     (offset + (root + type_slot_size h)) tvs j b` by
    (`dead_bytes
       (apply_writes (n2w root) (MAP (\(off,s). (off + offset,s)) slots) st)
       (root + (offset + type_slot_size h)) (TupleTV tvs) j b <=>
      dead_bytes st (root + (offset + type_slot_size h)) (TupleTV tvs) j b` by
       (irule place_store_dead_bytes_write_frame >>
        conj_tac
        >- (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
            rename1 `MEM (key,word) slots` >>
            `MEM key (MAP FST slots)` by
              (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
            `key < type_slot_size h` by metis_tac[] >> decide_tac) >>
        qexists_tac `offset + type_slot_size_list (h::tvs)` >>
        simp[type_slot_size_def, MEM_MAP, pairTheory.EXISTS_PROD] >>
        reverse conj_tac >- gvs[type_slot_size_def] >>
        rpt strip_tac >> rename1 `MEM (key,word) slots` >>
        `MEM key (MAP FST slots)` by
          (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
        `key < type_slot_size h` by metis_tac[] >> decide_tac) >>
     gvs[dead_bytes_def, AC ADD_ASSOC ADD_COMM]) >>
  qpat_x_assum `!offset' vs writes' root' st' j' b'. _`
    (qspec_then `offset + type_slot_size h` mp_tac) >>
  simp[AC ADD_ASSOC ADD_COMM] >> disch_then irule >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[type_slot_size_def] >> qexists_tac `t` >> simp[]
QED

Theorem place_store_struct_tuple_encoding[local]:
  !fts vals off ws.
    struct_has_type fts vals /\ encode_struct off fts vals = SOME ws ==>
    values_have_types (MAP SND fts) (MAP SND vals) /\
    encode_tuple off (MAP SND fts) (MAP SND vals) = SOME ws
Proof
  Induct >- (Cases >> simp[value_has_type_def, encode_value_def]) >>
  gen_tac >> Cases >- simp[value_has_type_def] >>
  rename1 `struct_has_type (ft::fts) (fv::vals)` >>
  PairCases_on `ft` >> PairCases_on `fv` >>
  simp[value_has_type_def, Once encode_value_def, AllCaseEqs()] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >>
  disch_then (qspecl_then [`off + type_slot_size ft1`, `rest`] mp_tac) >>
  simp[] >> strip_tac >> simp[encode_value_def]
QED

Theorem place_store_struct_tuple_dead[local]:
  !fts st root j b.
    (dead_bytes_fields st root fts j b <=> dead_bytes_list st root (MAP SND fts) j b)
Proof
  Induct >> simp[dead_bytes_def] >>
  Cases >> simp[dead_bytes_def]
QED

Theorem place_store_struct_unwritten_dead[local]:
  !fts offset vals writes root st j b.
    (!tv. MEM tv (MAP SND fts) ==> !v ws bs s k c.
      encode_value tv v = SOME ws /\ value_has_type tv v /\
      bs + type_slot_size tv <= dimword (:256) /\
      ~MEM (k - bs) (MAP FST ws) /\ dead_bytes s bs tv k c ==>
      dead_bytes (apply_writes (n2w bs) ws s) bs tv k c) /\
    encode_struct offset fts vals = SOME writes /\ struct_has_type fts vals /\
    root + offset + type_slot_size_fields fts <= dimword (:256) /\
    ~MEM (j - root) (MAP FST writes) /\
    dead_bytes_fields st (root + offset) fts j b ==>
    dead_bytes_fields (apply_writes (n2w root) writes st) (root + offset) fts j b
Proof
  rpt gen_tac >> strip_tac >>
  drule_all place_store_struct_tuple_encoding >> strip_tac >>
  gvs[place_store_struct_tuple_dead,
      vyperStorageRegionWriteTheory.type_slot_size_fields_list] >>
  mp_tac (Q.SPECL [`MAP SND (fts : (string # type_value) list)`, `offset`] place_store_tuple_unwritten_dead) >>
  simp[AC ADD_ASSOC ADD_COMM] >> disch_then irule >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `MAP SND vals` >> simp[]
QED

Theorem place_store_dyn_tuple_encoding[local]:
  !vs tv offset.
    encode_dyn_array tv offset vs = encode_tuple offset (REPLICATE (LENGTH vs) tv) vs /\
    (all_have_type tv vs <=> values_have_types (REPLICATE (LENGTH vs) tv) vs)
Proof
  Induct >> simp[encode_value_def, value_has_type_def] >>
  rpt gen_tac >> simp[Once encode_value_def] >>
  Cases_on `encode_value tv h` >> simp[] >>
  Cases_on `encode_dyn_array tv (offset + type_slot_size tv) vs` >>
  gvs[]
QED

Theorem place_store_replicate_dead[local]:
  !n tv st root j b.
    (dead_bytes_list st root (REPLICATE n tv) j b <=>
     ?k. k < n /\ dead_bytes st (root + k * type_slot_size tv) tv j b)
Proof
  Induct >> simp[dead_bytes_def] >> rpt gen_tac >>
  eq_tac
  >- (strip_tac >- (qexists_tac `0` >> simp[]) >>
      qexists_tac `SUC k` >> simp[MULT]) >>
  strip_tac >> Cases_on `k` >- gvs[] >>
  rename1 `SUC idx < SUC n` >> gvs[MULT] >>
  disj2_tac >> qexists_tac `idx` >> simp[]
QED

Theorem place_store_replicate_slot_size[local]:
  !n tv. type_slot_size_list (REPLICATE n tv) = n * type_slot_size tv
Proof
  Induct >> simp[type_slot_size_def, MULT]
QED

Theorem place_store_dyn_prefix_unwritten_dead[local]:
  !tv vs offset writes root n st j b.
    (!v ws bs s k c.
      encode_value tv v = SOME ws /\ value_has_type tv v /\
      bs + type_slot_size tv <= dimword (:256) /\
      ~MEM (k - bs) (MAP FST ws) /\ dead_bytes s bs tv k c ==>
      dead_bytes (apply_writes (n2w bs) ws s) bs tv k c) /\
    encode_dyn_array tv offset vs = SOME writes /\ all_have_type tv vs /\
    LENGTH vs <= n /\ root + offset + n * type_slot_size tv <= dimword (:256) /\
    ~MEM (j - root) (MAP FST writes) /\
    dead_bytes_list st (root + offset) (REPLICATE n tv) j b ==>
    dead_bytes_list (apply_writes (n2w root) writes st)
      (root + offset) (REPLICATE n tv) j b
Proof
  rpt gen_tac >> strip_tac >>
  fs[place_store_replicate_dead] >>
  Cases_on `k < LENGTH vs`
  >- (`dead_bytes_list st (root + offset) (REPLICATE (LENGTH vs) tv) j b` by
        (simp[place_store_replicate_dead] >> qexists_tac `k` >> simp[]) >>
      `dead_bytes_list (apply_writes (n2w root) writes st)
         (root + offset) (REPLICATE (LENGTH vs) tv) j b` by
        (irule place_store_tuple_unwritten_dead >>
         simp[MEM_REPLICATE, place_store_replicate_slot_size] >>
         conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[] >>
           qexists_tac `v` >> simp[]) >>
         conj_tac >- (irule LESS_EQ_TRANS >>
           qexists_tac `root + offset + n * type_slot_size tv` >> simp[]) >>
         qexists_tac `vs` >> gvs[place_store_dyn_tuple_encoding]) >>
      fs[place_store_replicate_dead] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  qexists_tac `k` >> simp[] >>
  `dead_bytes (apply_writes (n2w root) writes st)
       (root + (offset + k * type_slot_size tv)) tv j b <=>
   dead_bytes st (root + (offset + k * type_slot_size tv)) tv j b` suffices_by
    simp[] >>
  `!off. MEM off (MAP FST writes) ==> off < offset + LENGTH vs * type_slot_size tv` by
    metis_tac[vyperEncodeDecodeTheory.encode_writes_bounded] >>
  `LENGTH vs * type_slot_size tv <= k * type_slot_size tv` by simp[] >>
  `SUC k * type_slot_size tv <= n * type_slot_size tv` by simp[] >>
  irule place_store_dead_bytes_write_frame >>
  conj_tac >- (rpt strip_tac >> disj1_tac >>
    `off < offset + LENGTH vs * type_slot_size tv` by metis_tac[] >> decide_tac) >>
  qexists_tac `offset + n * type_slot_size tv` >>
  conj_tac >- (rpt strip_tac >>
    `off < offset + LENGTH vs * type_slot_size tv` by metis_tac[] >>
    `LENGTH vs * type_slot_size tv <= n * type_slot_size tv` by simp[] >> decide_tac) >>
  conj_tac >- simp[] >>
  qpat_x_assum `SUC k * _ <= _` mp_tac >> pure_rewrite_tac[MULT] >> decide_tac
QED

Theorem place_store_dynarray_unwritten_dead[local]:
  !tv n vs writes root st j b.
    (!v ws bs s k c.
      encode_value tv v = SOME ws /\ value_has_type tv v /\
      bs + type_slot_size tv <= dimword (:256) /\
      ~MEM (k - bs) (MAP FST ws) /\ dead_bytes s bs tv k c ==>
      dead_bytes (apply_writes (n2w bs) ws s) bs tv k c) /\
    encode_value (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) = SOME writes /\
    value_has_type (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) /\
    root + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword (:256) /\
    ~MEM (j - root) (MAP FST writes) /\
    dead_bytes st root (ArrayTV tv (Dynamic n)) j b ==>
    dead_bytes (apply_writes (n2w root) writes st) root (ArrayTV tv (Dynamic n)) j b
Proof
  rpt gen_tac >> strip_tac >>
  gvs[Once encode_value_def, value_has_type_def, AllCaseEqs()] >>
  once_rewrite_tac[apply_writes_def] >>
  simp_tac pure_ss [LET_THM, ADD_0, wordsTheory.n2w_w2n] >>
  `dead_bytes_list (apply_writes (n2w root) [(0,n2w (LENGTH vs))] st)
     (root + 1) (REPLICATE n tv) j b` by
    (`dead_bytes (apply_writes (n2w root) [(0,n2w (LENGTH vs))] st)
       (root + 1) (TupleTV (REPLICATE n tv)) j b <=>
      dead_bytes st (root + 1) (TupleTV (REPLICATE n tv)) j b` by
       (irule place_store_dead_bytes_write_frame >> simp[] >>
        qexists_tac `type_slot_size (ArrayTV tv (Dynamic n))` >>
        gvs[type_slot_size_def, place_store_replicate_slot_size]) >>
     gvs[dead_bytes_def, place_store_replicate_dead] >> metis_tac[]) >>
  simp[dead_bytes_def, GSYM place_store_replicate_dead] >>
  irule place_store_dyn_prefix_unwritten_dead >>
  simp[apply_writes_def, type_slot_size_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- gvs[type_slot_size_def] >>
  reverse conj_tac >- gvs[apply_writes_def, wordsTheory.n2w_mod] >>
  qexists_tac `vs` >> simp[]
QED

Theorem place_store_array_element_unwritten_dead[local]:
  !tv v ws root n idx k st j b.
    (!v ws bs s k c.
      encode_value tv v = SOME ws /\ value_has_type tv v /\
      bs + type_slot_size tv <= dimword (:256) /\
      ~MEM (k - bs) (MAP FST ws) /\ dead_bytes s bs tv k c ==>
      dead_bytes (apply_writes (n2w bs) ws s) bs tv k c) /\
    encode_value tv v = SOME ws /\ value_has_type tv v /\
    root + n * type_slot_size tv <= dimword (:256) /\ idx < n /\ k < n /\
    ~MEM (j - root) (MAP FST (MAP (\(off,s). (off + idx * type_slot_size tv,s)) ws)) /\
    dead_bytes st (root + k * type_slot_size tv) tv j b ==>
    dead_bytes (apply_writes (n2w root)
      (MAP (\(off,s). (off + idx * type_slot_size tv,s)) ws) st)
      (root + k * type_slot_size tv) tv j b
Proof
  rpt gen_tac >> strip_tac >>
  `!off. MEM off (MAP FST ws) ==> off < type_slot_size tv` by
    metis_tac[vyperEncodeDecodeTheory.encode_writes_bounded] >>
  Cases_on `k = idx`
  >- (gvs[] >>
      fs[ADD_COMM, vyperEncodeDecodeTheory.apply_writes_shift] >>
      drule (cj 1 dead_bytes_range) >> strip_tac >>
      `~MEM (j - (root + idx * type_slot_size tv)) (MAP FST ws)` by
        (strip_tac >> drule MEM_shifted_write >>
         disch_then (qspec_then `idx * type_slot_size tv` mp_tac) >>
         `j - (root + idx * type_slot_size tv) + idx * type_slot_size tv = j - root` by
           decide_tac >> gvs[]) >>
      first_x_assum irule >> simp[] >>
      conj_tac >- (`SUC idx * type_slot_size tv <= n * type_slot_size tv` by simp[] >>
        pop_assum mp_tac >> pure_rewrite_tac[MULT] >> decide_tac) >>
      qexists_tac `v` >> simp[]) >>
  `dead_bytes (apply_writes (n2w root)
      (MAP (\(off,s). (off + idx * type_slot_size tv,s)) ws) st)
      (root + k * type_slot_size tv) tv j b <=>
   dead_bytes st (root + k * type_slot_size tv) tv j b` suffices_by simp[] >>
  `SUC k * type_slot_size tv <= n * type_slot_size tv` by simp[] >>
  `SUC idx * type_slot_size tv <= n * type_slot_size tv` by simp[] >>
  irule place_store_dead_bytes_write_frame >>
  conj_tac
  >- (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
      rename1 `MEM (key,word) ws` >>
      `key < type_slot_size tv` by
        (`MEM key (MAP FST ws)` by
           (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >> metis_tac[]) >>
      Cases_on `idx < k`
      >- (`SUC idx * type_slot_size tv <= k * type_slot_size tv` by simp[] >>
          pop_assum mp_tac >> pure_rewrite_tac[MULT] >> decide_tac) >>
      `SUC k * type_slot_size tv <= idx * type_slot_size tv` by simp[] >>
      pop_assum mp_tac >> pure_rewrite_tac[MULT] >> decide_tac) >>
  qexists_tac `n * type_slot_size tv` >>
  conj_tac
  >- (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
      rename1 `MEM (key,word) ws` >>
      `key < type_slot_size tv` by
        (`MEM key (MAP FST ws)` by
           (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >> metis_tac[]) >>
      qpat_x_assum `SUC idx * _ <= _` mp_tac >> pure_rewrite_tac[MULT] >> decide_tac) >>
  conj_tac >- simp[] >>
  qpat_x_assum `SUC k * _ <= _` mp_tac >> pure_rewrite_tac[MULT] >> decide_tac
QED

Theorem place_store_static_batch_unwritten_dead[local]:
  !sparse tv n writes root k st j b.
    (!v ws bs s k c.
      encode_value tv v = SOME ws /\ value_has_type tv v /\
      bs + type_slot_size tv <= dimword (:256) /\
      ~MEM (k - bs) (MAP FST ws) /\ dead_bytes s bs tv k c ==>
      dead_bytes (apply_writes (n2w bs) ws s) bs tv k c) /\
    encode_static_array tv 0 sparse = SOME writes /\ sparse_has_type tv n sparse /\
    root + n * type_slot_size tv <= dimword (:256) /\ k < n /\
    ~MEM (j - root) (MAP FST writes) /\
    dead_bytes st (root + k * type_slot_size tv) tv j b ==>
    dead_bytes (apply_writes (n2w root) writes st) (root + k * type_slot_size tv) tv j b
Proof
  Induct >- simp[Once encode_value_def, apply_writes_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once encode_value_def, value_has_type_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >> rewrite_tac[vyperEncodeDecodeTheory.apply_writes_append] >>
  `dead_bytes (apply_writes (n2w root)
     (MAP (\(off,s). (off + h0 * type_slot_size tv,s)) slots) st)
     (root + k * type_slot_size tv) tv j b` by
    (irule place_store_array_element_unwritten_dead >> simp[] >>
     metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem place_store_default_batch_unwritten_dead[local]:
  !m tv defaults P n root k st j b.
    (!v ws bs s k c.
      encode_value tv v = SOME ws /\ value_has_type tv v /\
      bs + type_slot_size tv <= dimword (:256) /\
      ~MEM (k - bs) (MAP FST ws) /\ dead_bytes s bs tv k c ==>
      dead_bytes (apply_writes (n2w bs) ws s) bs tv k c) /\
    encode_value tv (default_value tv) = SOME defaults /\ m <= n /\
    root + n * type_slot_size tv <= dimword (:256) /\ k < n /\
    ~MEM (j - root) (MAP FST (FLAT (GENLIST (\idx.
      if P idx then [] else
      MAP (\(off,s). (off + idx * type_slot_size tv,s)) defaults) m))) /\
    dead_bytes st (root + k * type_slot_size tv) tv j b ==>
    dead_bytes (apply_writes (n2w root) (FLAT (GENLIST (\idx.
      if P idx then [] else
      MAP (\(off,s). (off + idx * type_slot_size tv,s)) defaults) m)) st)
      (root + k * type_slot_size tv) tv j b
Proof
  Induct >- simp[apply_writes_def] >>
  rpt gen_tac >> simp[GENLIST, SNOC_APPEND, FLAT_APPEND] >> strip_tac >>
  `m <= n /\ m < n` by decide_tac >>
  rewrite_tac[vyperEncodeDecodeTheory.apply_writes_append] >>
  `dead_bytes (apply_writes (n2w root) (FLAT (GENLIST (\idx.
      if P idx then [] else
      MAP (\(off,s). (off + idx * type_slot_size tv,s)) defaults) m)) st)
      (root + k * type_slot_size tv) tv j b` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  Cases_on `P m` >- simp[apply_writes_def] >> simp[] >>
  irule place_store_array_element_unwritten_dead >> simp[] >>
  metis_tac[vyperTypingTheory.default_value_well_typed]
QED

Theorem place_store_fixedarray_unwritten_dead[local]:
  !tv n v writes st base j b.
    (!v ws bs s k c.
      encode_value tv v = SOME ws /\ value_has_type tv v /\
      bs + type_slot_size tv <= dimword (:256) /\
      ~MEM (k - bs) (MAP FST ws) /\ dead_bytes s bs tv k c ==>
      dead_bytes (apply_writes (n2w bs) ws s) bs tv k c) /\
    encode_value (ArrayTV tv (Fixed n)) v = SOME writes /\
    value_has_type (ArrayTV tv (Fixed n)) v /\
    base + type_slot_size (ArrayTV tv (Fixed n)) <= dimword (:256) /\
    ~MEM (j - base) (MAP FST writes) /\
    dead_bytes st base (ArrayTV tv (Fixed n)) j b ==>
    dead_bytes (apply_writes (n2w base) writes st) base (ArrayTV tv (Fixed n)) j b
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  fs[Once encode_value_def, AllCaseEqs()] >> gvs[] >>
  fs[dead_bytes_def, type_slot_size_def] >>
  rename1 `k < n` >> qexists_tac `k` >> simp[] >>
  rename1 `apply_writes (n2w root) _ st` >>
  rewrite_tac[vyperEncodeDecodeTheory.apply_writes_append] >>
  `dead_bytes (apply_writes (n2w root) (FLAT (GENLIST (\idx.
      if MEM idx (MAP FST l) then [] else
      MAP (\(off,s). (off + idx * type_slot_size tv,s)) defaults) n)) st)
      (root + k * type_slot_size tv) tv j b` by
    (ho_match_mp_tac place_store_default_batch_unwritten_dead >> simp[] >>
     qexists_tac `n` >> simp[] >> first_assum ACCEPT_TAC) >>
  irule place_store_static_batch_unwritten_dead >> simp[] >> metis_tac[]
QED

Theorem place_store_encoding_unwritten_dead[local]:
  !tv v writes base st j b.
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    base + type_slot_size tv <= dimword (:256) /\
    ~MEM (j - base) (MAP FST writes) /\ dead_bytes st base tv j b ==>
    dead_bytes (apply_writes (n2w base) writes st) base tv j b
Proof
  completeInduct_on `type_value_size tv` >>
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  Cases_on `tv`
  >- (rename1 `BaseTV bt` >>
      drule (cj 1 dead_bytes_range) >> strip_tac >>
      Cases_on `bt` >> gvs[dead_bytes_def]
      >- (Cases_on `v'` >> gvs[value_has_type_def, Once encode_value_def] >>
          rename1 `dyn_bytes_dead _ root cap j b` >>
          `dyn_bytes_dead (apply_writes (n2w root) writes st) root cap
             (root + (j - root)) b` suffices_by simp[] >>
          irule place_store_bytes_unwritten_dead >>
          gvs[type_slot_size_def] >> metis_tac[])
      >> rename1 `BytesT bd` >> Cases_on `bd` >> gvs[dead_bytes_def] >>
      Cases_on `v'` >> gvs[value_has_type_def, Once encode_value_def] >>
      rename1 `dyn_bytes_dead _ root cap j b` >>
      `dyn_bytes_dead (apply_writes (n2w root) writes st) root cap
         (root + (j - root)) b` suffices_by simp[] >>
      irule place_store_bytes_unwritten_dead >>
      gvs[type_slot_size_def] >> metis_tac[])
  >- (rename1 `TupleTV tvs` >>
      Cases_on `v'` >> gvs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
      fs[Once encode_value_def, dead_bytes_def, type_slot_size_def] >>
      qspecl_then [`tvs`, `0`] mp_tac place_store_tuple_unwritten_dead >>
      simp[] >> disch_then irule >> simp[] >>
      conj_tac >- (rpt strip_tac >>
        `type_value_size tv < type_value_size (TupleTV tvs)` by
          metis_tac[vyperEncodeDecodeTheory.MEM_TupleTV_type_value_size] >>
        qpat_x_assum `!m. _` (qspec_then `type_value_size tv` mp_tac) >>
        gvs[] >> disch_then (qspec_then `tv` mp_tac) >> simp[] >>
        disch_then irule >> simp[] >> metis_tac[]) >>
      metis_tac[])
  >- (rename1 `ArrayTV elem bd` >>
      `!v ws bs s k c.
        encode_value elem v = SOME ws /\ value_has_type elem v /\
        bs + type_slot_size elem <= dimword (:256) /\
        ~MEM (k - bs) (MAP FST ws) /\ dead_bytes s bs elem k c ==>
        dead_bytes (apply_writes (n2w bs) ws s) bs elem k c` by
        (qpat_x_assum `!m. _` (qspec_then `type_value_size elem` mp_tac) >>
         gvs[type_value_size_def] >>
         disch_then (qspec_then `elem` mp_tac) >> simp[]) >>
      Cases_on `bd`
      >- (irule place_store_fixedarray_unwritten_dead >> simp[] >> metis_tac[]) >>
      Cases_on `v'` >> gvs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
      irule place_store_dynarray_unwritten_dead >> simp[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `l` >> simp[value_has_type_def])
  >- (rename1 `StructTV fts` >>
      Cases_on `v'` >> gvs[value_has_type_def] >>
      fs[Once encode_value_def, dead_bytes_def, type_slot_size_def] >>
      qspecl_then [`fts`, `0`] mp_tac place_store_struct_unwritten_dead >>
      simp[] >> disch_then irule >> simp[] >>
      conj_tac >- (rpt strip_tac >>
        `type_value_size tv < type_value_size (StructTV fts)` by
          (irule vyperEncodeDecodeTheory.MEM_StructTV_type_value_size >>
           fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
        qpat_x_assum `!m. _` (qspec_then `type_value_size tv` mp_tac) >>
        gvs[] >> disch_then (qspec_then `tv` mp_tac) >> simp[] >>
        disch_then irule >> simp[] >> metis_tac[]) >>
      metis_tac[])
  >> gvs[dead_bytes_def]
QED

(* An unwritten slot keeps its liveness: if a byte of it is live after a
   value's encoding is written, it was live before.  Only lengths decide
   which bytes are dead, and every length the write can change is in a
   slot it writes. *)
Theorem place_store_unwritten_live_preserved:
  !tv v writes st base i b.
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    base + type_slot_size tv <= dimword (:256) /\
    i < type_slot_size tv /\ b < 32 /\ ~MEM i (MAP FST writes) /\
    ~dead_bytes (apply_writes (n2w base) writes st) base tv (base + i) b ==>
    ~dead_bytes st base tv (base + i) b
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  rename1 `apply_writes (n2w root) writes st` >>
  `dead_bytes (apply_writes (n2w root) writes st) root tv (root + i) b` by
    (irule place_store_encoding_unwritten_dead >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

(* A byte live in a declared region's subregion is not dead in the
   storage: the regions on a backend are disjoint, so the only region that
   could make it dead is its own root. *)
Theorem place_store_subregion_not_dead[local]:
  !cx tr mid name subs rootk root path delta leaf st j b.
    declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
    storage_subregion root path delta leaf /\
    (!mid' name' subs' k' tv'.
       declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (rootk,root) ==>
       ranges_disjoint (w2n rootk) (type_slot_size root)
                       (w2n k') (type_slot_size tv')) /\
    w2n rootk + delta <= j /\ j < w2n rootk + delta + type_slot_size leaf /\
    ~dead_bytes st (w2n rootk + delta) leaf j b ==>
    ~storage_dead cx tr st j b
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [storage_dead_def] >>
  rpt gen_tac >> CCONTR_TAC >> gvs[] >>
  rename1 `declared_storage_region cx mid2 n2 subs2 = SOME (tr,k2,tv2)` >>
  drule (cj 1 dead_bytes_range) >> strip_tac >>
  drule_all storage_subregion_bounds >> strip_tac >>
  Cases_on `(k2,tv2) = (rootk,root)`
  >- (gvs[] >> drule storage_subregion_dead_bytes >>
      disch_then (qspecl_then [`st`, `w2n k2`, `j`, `b`] mp_tac) >>
      simp[]) >>
  qpat_x_assum `!mid' name' subs' k' tv'. _ ==> ranges_disjoint _ _ _ _`
    (qspecl_then [`mid2`, `n2`, `subs2`, `k2`, `tv2`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[ranges_disjoint_def] >> decide_tac
QED


(* place_store_encoded_copy_agree with the copied slots ks those the
   encoding writes. *)
Theorem place_store_encoded_copy_agree_sparse:
  !cx tr mid name subs rootk root path delta tv base writes v ks read_word st1 st2.
    declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
    storage_subregion root path delta tv /\
    base = w2n rootk + delta /\ 0 < type_slot_size tv /\
    w2n rootk + type_slot_size root <= dimword (:256) /\
    (!mid' name' subs' k' tv'.
       declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (rootk,root) ==>
       ranges_disjoint (w2n rootk) (type_slot_size root)
                       (w2n k') (type_slot_size tv')) /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    base + type_slot_size tv <= dimword (:256) /\
    (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
    (!i b. i < type_slot_size tv /\ b < 32 /\ MEM i (MAP FST writes) /\
       ~dead_bytes (apply_writes (n2w base) writes st1) base tv (base+i) b ==>
       EL b (word_to_bytes (lookup_storage (n2w (base+i))
         (apply_writes (n2w base) writes st1)) T) =
       EL b (word_to_bytes (read_word i) T)) /\
    storage_agree (storage_dead cx tr st1) st1 st2 ==>
    storage_agree (storage_dead cx tr (apply_writes (n2w base) writes st1))
      (apply_writes (n2w base) writes st1)
      (FOLDL (\st i. update_storage (n2w (base+i)) (read_word i) st) st2 ks)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `apply_writes (n2w start) writes st1` >>
  `start < dimword (:256)` by decide_tac >>
  `EVERY (\i. i < type_slot_size tv) ks` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
     metis_tac[]) >>
  irule place_store_subregion_agree >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  qexists_tac `(n2w start):bytes32` >>
  goal_assum (drule_at (Pat `storage_agree _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  `w2n ((n2w start):bytes32) = start` by simp[wordsTheory.w2n_n2w] >>
  qpat_x_assum `start = _` (mk_asm "origin") >>
  simp[wordsTheory.w2n_n2w, GSYM wordsTheory.word_add_n2w] >>
  conj_tac >- suspend "frame" >> suspend "live"
QED
Resume place_store_encoded_copy_agree_sparse[frame]:
  gen_tac >> disch_tac >> conj_tac
  >- (rewrite_tac[place_store_apply_writes_fold] >>
      irule place_store_updates_miss >>
      simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MEM_MAP,
           pairTheory.EXISTS_PROD] >>
      rpt strip_tac >>
      rename1 `MEM (off,word) writes` >>
      `off < type_slot_size tv` by
        (irule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
         goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
         simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
      `start + off < dimword (:256)` by decide_tac >>
      gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >> decide_tac) >>
  rename1 `FOLDL (\st i. update_storage (n2w i + n2w start) (rd i) st) st2 ks` >>
  `~MEM q (MAP FST (MAP (\i. ((n2w i + n2w start):bytes32,rd i)) ks))` by
    (rewrite_tac[listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MEM_MAP] >>
     BETA_TAC >> rewrite_tac[pairTheory.FST] >> rpt strip_tac >>
     rename1 `MEM j ks` >>
     `j < type_slot_size tv` by
       (qpat_x_assum `EVERY _ ks` mp_tac >>
        rewrite_tac[listTheory.EVERY_MEM] >> BETA_TAC >>
        disch_then irule >> first_assum ACCEPT_TAC) >>
     `start + j < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >> decide_tac) >>
  drule place_store_updates_miss >>
  disch_then (qspec_then `st2` mp_tac) >> simp[rich_listTheory.FOLDL_MAP]
QED
Resume place_store_encoded_copy_agree_sparse[live]:
  reverse conj_tac >- (asm "origin" mp_tac >> simp[ADD_COMM]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `FOLDL (\st j. update_storage (n2w j + n2w start) (rd j) st) st2 ks` >>
  Cases_on `MEM i ks` >- suspend "written" >> suspend "unwritten"
QED
Resume place_store_encoded_copy_agree_sparse[written]:
  `MEM i (MAP FST writes)` by metis_tac[] >>
  qpat_x_assum `!i. MEM i ks <=> _` kall_tac >>
  `EL b (word_to_bytes (lookup_storage (n2w (start+i))
     (apply_writes (n2w start) writes st1)) T) =
   EL b (word_to_bytes (rd i) T)` by
    (first_x_assum irule >> simp[ADD_COMM]) >>
  `lookup_storage (n2w i + n2w start)
     (FOLDL (\st j. update_storage (n2w j + n2w start) (rd j) st) st2 ks) =
   rd i` suffices_by gvs[GSYM wordsTheory.word_add_n2w, ADD_COMM] >>
  `MEM ((n2w i + n2w start):bytes32,rd i) (MAP (\j. (n2w j + n2w start,rd j)) ks)` by
    (simp[listTheory.MEM_MAP] >> qexists_tac `i` >> simp[]) >>
  drule place_store_updates_hit >>
  disch_then (qspec_then `st2` mp_tac) >>
  simp[rich_listTheory.FOLDL_MAP, listTheory.MEM_MAP] >>
  impl_tac >- (rpt strip_tac >> gvs[listTheory.EVERY_MEM] >> res_tac >>
    `i < dimword (:256)` by simp[] >>
    `j < dimword (:256)` by simp[] >>
    gvs[wordsTheory.n2w_11]) >> simp[]
QED
Resume place_store_encoded_copy_agree_sparse[unwritten]:
  `~MEM i (MAP FST writes)` by metis_tac[] >>
  `start + i < dimword (:256)` by decide_tac >>
  `~dead_bytes st1 start tv (start + i) b` by
    (irule place_store_unwritten_live_preserved >>
     rpt conj_tac >- simp[] >- simp[] >- simp[] >>
     qexistsl_tac [`v`, `writes`] >> gvs[ADD_COMM]) >>
  `~storage_dead cx tr st1 (start + i) b` by
    (irule place_store_subregion_not_dead >>
     qexistsl_tac [`delta`, `tv`, `mid`, `name`, `path`, `root`, `rootk`,
                   `subs`] >>
     asm "origin" SUBST_ALL_TAC >> gvs[] >> metis_tac[]) >>
  `lookup_storage (n2w i + n2w start) (apply_writes (n2w start) writes st1) =
   lookup_storage (n2w i + n2w start) st1` by
    (rewrite_tac[place_store_apply_writes_fold] >>
     irule place_store_updates_miss >>
     simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MEM_MAP,
          pairTheory.EXISTS_PROD] >>
     rpt strip_tac >> rename1 `MEM (off,word) writes` >>
     `off < type_slot_size tv` by
       (irule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
        goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
        simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
     `start + off < dimword (:256)` by decide_tac >>
     `off <> i` by
       (strip_tac >> qpat_x_assum `~MEM i (MAP FST writes)` mp_tac >>
        rewrite_tac[listTheory.MEM_MAP] >> simp_tac bool_ss [] >>
        qexists_tac `(off,word)` >> rewrite_tac[pairTheory.FST] >>
        conj_tac >- first_assum (ACCEPT_TAC o SYM) >>
        first_assum ACCEPT_TAC) >>
     gvs[wordsTheory.word_add_n2w]) >>
  `lookup_storage (n2w i + n2w start)
     (FOLDL (\st j. update_storage (n2w j + n2w start) (rd j) st) st2 ks) =
   lookup_storage (n2w i + n2w start) st2` by
    (`~MEM ((n2w i + n2w start):bytes32)
        (MAP FST (MAP (\j. ((n2w j + n2w start):bytes32,rd j)) ks))` by
       (rewrite_tac[listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MEM_MAP] >>
        BETA_TAC >> rewrite_tac[pairTheory.FST] >> rpt strip_tac >>
        rename1 `MEM j ks` >>
        `j < type_slot_size tv` by
          (qpat_x_assum `EVERY _ ks` mp_tac >>
           rewrite_tac[listTheory.EVERY_MEM] >> BETA_TAC >>
           disch_then irule >> first_assum ACCEPT_TAC) >>
        `start + j < dimword (:256)` by decide_tac >>
        `j <> i` by (strip_tac >> metis_tac[]) >>
        gvs[wordsTheory.word_add_n2w]) >>
     drule place_store_updates_miss >>
     disch_then (qspec_then `st2` mp_tac) >> simp[rich_listTheory.FOLDL_MAP]) >>
  qpat_x_assum `storage_agree _ st1 st2` mp_tac >>
  simp_tac (srw_ss()) [storage_agree_def] >>
  disch_then (qspecl_then [`n2w (start + i)`, `b`] mp_tac) >>
  gvs[wordsTheory.word_add_n2w, ADD_COMM]
QED
Finalise place_store_encoded_copy_agree_sparse

(* place_store_encoded_leaf_state with the stored slots ks those the
   encoding writes. *)
Theorem place_store_encoded_leaf_state_sparse:
  !cenv cx env ee ctx func s mid name subs tr rootk root path delta tv
   start writes v ks rd.
  expr_sim_inv cenv cx env ee /\
  stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\
  start = w2n rootk + delta /\ 0 < type_slot_size tv /\
  encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  (!i b. i < type_slot_size tv /\ b < 32 /\ MEM i (MAP FST writes) /\
    ~dead_bytes (apply_writes (n2w start) writes (get_storage cx ee tr))
       start tv (start+i) b ==>
    EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (rd i) T)) ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (FOLDL (\t i. (if tr then tstore else sstore)
       (n2w (start+i)) (rd i) t) s ks)
Proof
  rpt gen_tac >> strip_tac >>
  `storage_agree (storage_dead cx tr (get_storage cx ee tr))
    (get_storage cx ee tr)
    (if tr then contract_transient s else contract_storage s)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     Cases_on `tr` >>
     simp[stmt_state_rel_def, state_rel_def, accounts_rel_def,
          accounts_agree_def, transient_agree_def,
          vyperStorageBackendTheory.get_storage_def,
          vfmStateTheory.lookup_account_def,
          contract_storage_def, contract_transient_def,
          call_ctx_rel_def] >> metis_tac[]) >>
  drule_all place_store_root_layout >> strip_tac >>
  `storage_agree
    (storage_dead cx tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (apply_writes (n2w start) writes (get_storage cx ee tr))
    (FOLDL (\st i. update_storage (n2w (start+i)) (rd i) st)
      (if tr then contract_transient s else contract_storage s) ks)` by
    (qspecl_then [`cx`, `tr`, `mid`, `name`, `subs`, `rootk`, `root`, `path`,
                  `delta`, `tv`, `start`, `writes`, `v`, `ks`, `rd`,
                  `get_storage cx ee tr`,
                  `if tr then contract_transient s else contract_storage s`]
       mp_tac place_store_encoded_copy_agree_sparse >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `!is s. FOLDL (\t i. (if tr then tstore else sstore)
        (n2w (start+i)) (rd i) t) s is =
     if tr then s with vs_transient :=
       (s.vs_call_ctx.cc_address =+
         FOLDL (\st i. update_storage (n2w (start+i)) (rd i) st)
           (contract_transient s) is) s.vs_transient
     else s with vs_accounts :=
       (s.vs_call_ctx.cc_address =+
         (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage :=
           FOLDL (\st i. update_storage (n2w (start+i)) (rd i) st)
             (contract_storage s) is)) s.vs_accounts` by
    (Induct
     >- (gen_tac >> pure_rewrite_tac[listTheory.FOLDL] >> Cases_on `tr` >>
         simp[contract_storage_def, contract_transient_def,
              vfmStateTheory.lookup_account_def, place_store_update_identity]) >>
     map_every qx_gen_tac [`h`, `acc`] >>
     once_rewrite_tac[listTheory.FOLDL] >>
     first_x_assum (qspec_then `(if tr then tstore else sstore)
       (n2w (start+h)) (rd h) acc` mp_tac) >>
     Cases_on `tr` >>
     simp[sstore_def, tstore_def, contract_storage_def, contract_transient_def,
          vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
          combinTheory.UPDATE_EQ]) >>
  drule_all place_store_storage_replace >> Cases_on `tr` >> gvs[]
QED

(* The store of a value of type tv laid out at src in memory: a state
   related at the source state after the write. *)
Theorem place_store_slots_suffix_run:
  !cenv src dst dty tr sa sb tv func s sw start ctx cx env ee mid name subs
   rootk root path delta writes v.
  compile_store_slots cenv src dst dty tr sa = ((),sb) /\
  evaluate_type (get_tenv cx) dty = SOME tv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `store_slots_entry cenv ctx dty tv v` by
    (irule store_slots_rank_entry >> simp[] >> qexists_tac `get_tenv cx` >>
     asm_rewrite_tac[]) >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  qpat_x_assum `store_slots_entry _ _ _ _ _` mp_tac >>
  simp_tac std_ss [store_slots_entry_def] >>
  disch_then (qspecl_then [`src`, `dst`, `tr`, `sa`, `sb`, `func`, `s`, `sw`,
    `n2w start`, `writes`] mp_tac) >>
  (impl_tac >- (simp[wordsTheory.w2n_n2w] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t`, `ks`] strip_assume_tac) >>
  qspecl_then [`cenv`, `cx`, `env`, `ee`, `ctx`, `func`, `s`, `mid`, `name`,
    `subs`, `tr`, `rootk`, `root`, `path`, `delta`, `tv`, `start`, `writes`,
    `v`, `ks`, `\i. mload (w2n sw + 32*i) s`]
    mp_tac place_store_encoded_leaf_state_sparse >>
  impl_tac
  >- (rpt conj_tac
      >~ [`EL _ (word_to_bytes _ _)`]
      >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
          irule place_store_memory_live_at >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qexistsl_tac [`tv`, `v`] >> pure_asm_rewrite_tac[] >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexists_tac `s` >> simp[] >>
  qpat_x_assum `store_copy_normalize _ _ = _` SUBST1_TAC >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  qpat_x_assum `start = _` SUBST1_TAC >>
  simp_tac (bool_ss ++ ARITH_ss) [wordsTheory.word_add_n2w]
QED

(* Bytestring code uses the runtime length, independently of capacity. *)
Theorem store_slots_bytes_compile_eq[local]:
  !cenv src dst dty sty tr.
    is_bytestring_type dty /\ is_bytestring_type sty ==>
    compile_store_slots cenv src dst dty tr =
    compile_store_slots cenv src dst sty tr
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dty` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT db)` >> Cases_on `db` >> gvs[is_bytestring_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  Cases_on `sty` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT sbt)` >> Cases_on `sbt` >> gvs[is_bytestring_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  simp[Once compile_store_slots_def, is_abi_dynamic_def,
       is_bytestring_type_def] >>
  simp[Once compile_store_slots_def, is_abi_dynamic_def,
       is_bytestring_type_def]
QED

Theorem store_slots_bytes_encoding[local]:
  !tenv sty dty stv tv v.
    is_bytestring_type sty /\ is_bytestring_type dty /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME tv /\
    value_has_type stv v /\ value_has_type tv v ==>
    type_slot_size stv <= type_slot_size tv /\
    encode_value stv v = encode_value tv v
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dty` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT db)` >> Cases_on `db` >> gvs[is_bytestring_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  Cases_on `sty` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT sbt)` >> Cases_on `sbt` >> gvs[is_bytestring_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  gvs[evaluate_type_def, type_widens_to_def, arg_type_fits_def] >>
  Cases_on `v` >>
  gvs[value_has_type_def, type_slot_size_def, encode_value_def,
      encode_dyn_bytes_slots_def] >>
  metis_tac[exprSimHypsTheory.word_size_monotone]
QED

(* place_store_slots_suffix_run for a bytestring laid out at its source
   type stv, of a capacity at most the place's. *)
Theorem place_store_slots_bytes_run:
  !cenv src dst dty sty tr sa sb stv tv func s sw start ctx cx env ee mid name
   subs rootk root path delta writes v.
  compile_store_slots cenv src dst dty tr sa = ((),sb) /\
  is_bytestring_type dty /\ is_bytestring_type sty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME tv /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\
  value_has_type stv v /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  val_in_memory stv v (w2n sw) s.vs_memory ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  `type_slot_size stv <= type_slot_size tv /\
   encode_value stv v = encode_value tv v` by
    (irule store_slots_bytes_encoding >> metis_tac[]) >>
  `compile_store_slots cenv src dst sty tr sa = ((),sb)` by
    metis_tac[store_slots_bytes_compile_eq] >>
  `store_slots_entry cenv ctx sty stv v` by
    (irule store_slots_bytes_entry >> metis_tac[]) >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by
    (irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
     metis_tac[]) >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  qpat_x_assum `store_slots_entry _ _ _ _ _` mp_tac >>
  simp_tac std_ss [store_slots_entry_def] >>
  disch_then (qspecl_then [`src`, `dst`, `tr`, `sa`, `sb`, `func`, `s`, `sw`,
    `n2w start`, `writes`] mp_tac) >>
  (impl_tac >- (simp[wordsTheory.w2n_n2w] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`t`, `ks`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (FOLDL (\q i. (if tr then tstore else sstore)
       (n2w (start+i)) (mload (w2n sw + 32*i) s) q) s ks)` by
    (ho_match_mp_tac place_store_encoded_leaf_state_sparse >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
     asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
     irule place_store_memory_live_at >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tv`, `v`] >> pure_asm_rewrite_tac[] >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexists_tac `s` >> simp[] >>
  qpat_x_assum `store_copy_normalize _ _ = _` SUBST1_TAC >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  qpat_x_assum `start = _` SUBST1_TAC >>
  simp_tac (bool_ss ++ ARITH_ss) [wordsTheory.word_add_n2w]
QED

Theorem place_store_storage_compile:
  compile_assign_value cenv dst (slot_loc tr) src (is_word_type dty)
    src_loc dty sty (type_memory_bytes cenv dty) sa = ((), sb) ==>
  ?src' sc.
    (((~is_word_type dty /\ dty <> sty /\
       ~(is_bytestring_type dty /\ is_bytestring_type sty)) /\
      ?a sm. compile_alloc_buffer (type_memory_bytes cenv dty) sa = (a,sm) /\
        compile_store_memory_typed cenv a.buf_operand dty src sty sm = ((),sc) /\
        src' = a.buf_operand) \/
     ((is_word_type dty \/ dty = sty \/
       (is_bytestring_type dty /\ is_bytestring_type sty)) /\ src' = src /\ sc = sa)) /\
    (if is_word_type dty then
       emit_void (if tr then TSTORE else SSTORE) [dst;src'] sc = ((),sb)
     else compile_store_slots cenv src' dst dty tr sc = ((),sb))
Proof
  strip_tac >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[slot_loc_def, stmtLoweringTheory.compile_assign_value_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `~is_word_type dty /\ dty <> sty /\
    ~(is_bytestring_type dty /\ is_bytestring_type sty)` >>
  gvs[] >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_word_type dty` >> gvs[] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

(* compile_assign_value into (transient) storage. *)
Theorem place_store_value_storage_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (type_memory_bytes cenv dty) sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
              evaluate_type (get_tenv cx) dty = SOME dtv ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= w2n w \/
              w2n w + type_memory_size dtv <= w2n sw \/
              sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size stv <= s.vs_alloca_next /\
          !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                     sa.cs_next_id <= aid ==>
                     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==>
     !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           0 < type_slot_size dtv) /\
    (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
     type_alloc_ok cenv dty) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_store_storage_destination >> strip_tac >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
  drule_all place_store_storage_write_inv >> strip_tac >> gvs[] >>
  drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >> gvs[] >>
  drule_all place_store_storage_leaf_bounds >> strip_tac >>
  Cases_on `is_word_type dty`
  >- suspend "word"
  >> suspend "memory"
QED
Resume place_store_value_storage_run[word]:
  drule_all place_store_storage_compile >> simp[] >> strip_tac >>
  `sty = dty` by metis_tac[compileEnvTheory.type_widens_to_word] >> gvs[] >>
  `eval_operand op s = SOME (typed_val_to_w256 dtv v)` by
    fs[expr_val_rel_def] >>
  drule_all place_store_emit_slot_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
      (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
       (n2w (w2n root+delta+i)) (typed_val_to_w256 dtv v) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST [`rd` |-> `\i. typed_val_to_w256 dtv v`]
       (SPEC_ALL place_store_encoded_leaf_state))) >>
     conj_tac >- metis_tac[] >>
     reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> rpt strip_tac >>
     drule_all place_store_word_live_copy >>
     disch_then (qspecl_then [`get_storage cx ee tr`, `root+n2w delta`, `b`] mp_tac) >>
     simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func s 0 (OK t)` >>
  qexists_tac `t` >> simp[] >>
  reverse conj_tac
  >- (unabbrev_all_tac >> Cases_on `tr` >>
      simp[tstore_def, sstore_def, lookup_var_def]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >>
  simp[] >>
  unabbrev_all_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
       wordsTheory.WORD_ADD_COMM]
QED
Resume place_store_value_storage_run[memory]:
  drule_all place_store_storage_compile >> simp[] >>
  disch_then (qx_choose_then `src` (qx_choose_then `sc`
    (map_every assume_tac o CONJUNCTS))) >>
  Cases_on `dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty)`
  >- suspend "normalize"
  >> suspend "direct"
QED
Resume place_store_value_storage_run[direct]:
  gvs[]
  >- suspend "equal"
  >> suspend "bytes"
QED
Resume place_store_value_storage_run[equal]:
  fs[expr_val_rel_def] >>
  `val_in_memory dtv v (w2n w) s.vs_memory` by metis_tac[] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n w + type_memory_size dtv < dimword (:256)` by
    (first_x_assum (qspec_then `w` mp_tac) >> simp[] >> strip_tac >>
     fs[] >> decide_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  qspecl_then [`cenv`, `op`, `dst_op`, `dty`, `tr`, `sa`, `sb`, `dtv`, `func`, `s`,
      `w`, `w2n root + delta`, `ctx`, `cx`, `env`, `ee`, `mid`, `var_name`, `keys`,
      `root`, `tv`, `path`, `delta`, `writes`, `v`] mp_tac
    place_store_slots_suffix_run >>
  (impl_tac >- (fs[] >> metis_tac[])) >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED
Resume place_store_value_storage_run[bytes]:
  fs[expr_val_rel_def] >>
  `~is_word_type sty` by
    (Cases_on `sty` >> fs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     fs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT (BytesT bound)` >> Cases_on `bound` >>
     fs[is_bytestring_type_def, is_word_type_def]) >>
  qpat_assum `!tv. evaluate_type _ sty = SOME tv ==> _`
    (qspec_then `stv` assume_tac) >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n w + type_memory_size stv < dimword (:256)` by
    (qpat_assum `~is_word_type sty ==> _` mp_tac >>
     impl_tac >- simp[] >>
     disch_then drule >> strip_tac >> decide_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  qspecl_then [`cenv`, `op`, `dst_op`, `dty`, `sty`, `tr`, `sa`, `sb`, `stv`,
      `dtv`, `func`, `s`, `w`, `w2n root + delta`, `ctx`, `cx`, `env`, `ee`,
      `mid`, `var_name`, `keys`, `root`, `tv`, `path`, `delta`, `writes`, `v`]
    mp_tac place_store_slots_bytes_run >>
  (impl_tac >- (fs[] >> metis_tac[])) >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED
Resume place_store_value_storage_run[normalize]:
  `~is_bytestring_type dty` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  `~is_word_type sty` by
    (spose_not_then assume_tac >>
     qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     Cases_on `sty` >> Cases_on `dty` >>
     gvs[type_widens_to_def, is_word_type_def,
         arg_type_fits_def, is_bytestring_type_def] >>
     Cases_on `b` >> Cases_on `b'` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def] >>
     rename1 `arg_type_fits (BaseT (BytesT bd)) (BaseT (BytesT bd'))` >>
     Cases_on `bd` >> Cases_on `bd'` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def]) >>
  gvs[] >>
  drule_all place_store_destination_alloc_bound >> strip_tac >>
  fs[expr_val_rel_def] >>
  `?sw. eval_operand op s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory` by
    metis_tac[] >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (qpat_x_assum `!sw. eval_operand op s = SOME sw ==> _` (qspec_then `sw` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >> decide_tac) >>
  `cs_extends sa sm` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sm sc` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dty`, `op`, `sty`, `sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `cs_extends sc sb` by
    (mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dst_op`, `dty`, `tr`, `sc`]
       mp_tac) >> simp[ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next /\
   (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw)` by
    (qpat_assum `!sw. eval_operand op s = SOME sw ==> _` (qspec_then `sw` mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) place_store_normalize_path >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`cx`, `ctx`, `func`, `ee`, `stv`, `v`, `sw`, `s`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> metis_tac[])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `dw`
    (map_every assume_tac o CONJUNCTS))) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspec_then `type_memory_size dtv` (qspec_then `sa` mp_tac)
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `sm.cs_next_var <= sc.cs_next_var` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dty`, `op`, `sty`, `sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sc` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. a.buf_operand = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, comp_ignore_bind_def] >> strip_tac >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `!x. a.buf_operand = Var x \/ dst_op = Var x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand dst_op u = SOME (root+n2w delta)` by
    (Cases_on `dst_op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `~u.vs_call_ctx.cc_static` by
    (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`) place_store_storage_write_inv >>
     disch_then drule >> simp[]) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
        (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x u) /\
    t.vs_allocas = u.vs_allocas /\ t.vs_memory = u.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qspecl_then [`cenv`, `a.buf_operand`, `dst_op`, `dty`, `tr`, `sc`, `sb`, `dtv`, `func`, `u`,
      `dw`, `w2n root + delta`, `ctx`, `cx`, `env`, `ee`, `mid`, `var_name`, `keys`,
      `root`, `tv`, `path`, `delta`, `writes`, `v`] mp_tac
       place_store_slots_suffix_run >>
     (impl_tac >- (fs[] >> metis_tac[])) >> simp[]) >>
  qexists_tac `t` >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
       gas_marked_path_then)) >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> rpt strip_tac >>
  `not_fresh_at sc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `!x. not_fresh_at sc x ==> _` drule >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]
QED
Finalise place_store_value_storage_run
