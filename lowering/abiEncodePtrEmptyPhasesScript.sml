(*
 * lower_abi_encode with the pointer check for an empty encoder
 * (zero-byte source window): the twin of exprSimAbiEncodeEmptyFramed's
 * abi_encode_empty_framed_phases_open and exprSimAbiEncodeEmptyComplex's
 * abi_encode_empty_phases_open.
 * The setup (output alloca, data pointer, method id), the encoder body
 * (a zero-length copy or an empty tuple) and the length store run as one
 * pointer-checked path that ends where the framed phases end, with the
 * ghost kept and the output buffer covered and untainted.
 *
 * TOP-LEVEL:
 *   abi_encode_empty_phases_ptr
 *)
Theory abiEncodePtrEmptyPhases
Ancestors
  exprSimAbiEncodeEmptyFramed exprSimAbiEncodeEmptyComplex bodyPtrDefs fragGasPathPtr
  exprLoweringProps abiBuiltinEncodeCode abiEncoderWindowContract
  exprSimAbiEncodeExecFrame venomState list venomMemDefs
  abiEncodePtrEmptySetup abiEncodePtrEmptyBody abiEncodePtrEmptyGhost
  exprSimAbiEncodeEmptySource
  abiEncodePtrFinish abiEncodeWindowBuiltin abiBuiltinEncodeSetup
  abiDecoderContract abiEncoderWindow abiEncoderWindowLeaves
  abiBuiltinEncodeAllocate abiBuiltinAllocation abiEncoderExtendSim
  freshWrites loweringStateRelDefs localPtrsProps finite_map pred_set arithmetic words

val _ = Parse.hide "body";

Theorem abi_encode_empty_phases_ptr:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\
  (ei = AbiCopy 0 \/ ei = AbiComplex []) /\
  (!mem. mem_agree_outside tn.t_mem initial.vs_memory mem ==>
     abi_encoder_window_input ei at av sb 0 mem) /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) /\
  (* the pointer side *)
  LENGTH (enc at av) <= maxlen /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  op_taint tn src = {} /\
  local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  stmt_state_rel ctx func cenv cx es initial /\
  ghost_inv rb cenv cx es G tn initial ==>
  ?prepared body actual G' tn' x.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)+m) /\
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    window_strong_result ctx func ready body_end len at av d prepared body /\
    abi_decode_frame p 32 body actual /\
    actual.vs_allocas = body.vs_allocas /\ actual.vs_alloca_next = body.vs_alloca_next /\
    abi_encoder_registered_effect {} [(p,32)] body actual /\
    (!op v. abi_decoder_operand_live body_end.cs_next_var op /\ eval_operand op body = SOME v ==>
      eval_operand op actual = SOME v) /\
    abi_encode_exec_frame func initial actual /\
    LENGTH initial.vs_memory <= LENGTH actual.vs_memory /\
    prepared.vs_accounts = initial.vs_accounts /\ prepared.vs_transient = initial.vs_transient /\
    prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
    prepared.vs_pending_deletions = initial.vs_pending_deletions /\
    prepared.vs_labels = initial.vs_labels /\ actual.vs_labels = initial.vs_labels /\
    abi_encoder_extend_sim ctx func initial actual /\
    (* the pointer side *)
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn initial 0 G' tn' (OK actual) /\
    ghost_inv rb cenv cx es G' tn' actual /\
    ghost_kept cenv es st G tn initial G' tn' /\
    FST ops = Var x /\ ptr_covers G' tn' x actual outsz /\
    (!i. p <= i /\ i < p + 32 + m + LENGTH (enc at av) ==> i NOTIN tn'.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_encoder_window_input ei at av sb 0 initial.vs_memory` by
    (first_x_assum irule >> rewrite_tac[mem_agree_outside_def] >> simp_tac bool_ss []) >>
  `enc at av = []` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     qpat_assum `ei = AbiCopy 0 \/ ei = AbiComplex []` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     simp[abi_encoder_window_copy_iff, valueEncodingDefsTheory.mem_bytes_at_def,
       abi_encoder_window_complex_iff, abiEncoderInputTheory.abi_encoder_tuple_type_def] >>
     strip_tac >> gvs[contractABITheory.enc_def, LET_THM, listTheory.REV_DEF]) >>
  drule_all abi_encode_empty_setup_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `alloca_inv prepared /\ alloca_room ctx func prepared` by
    metis_tac[abi_window_setup_alloca_inv, abi_window_setup_room] >>
  `prepared.vs_allocas = (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas /\
   prepared.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next` by
    metis_tac[abi_window_setup_allocas, abi_window_setup_frontier] >>
  `d < dimword (:256)` by
    (qpat_assum `alloca_room ctx func (abi_builtin_allocate_state _ _ _)` mp_tac >>
     disch_then (mp_tac o MATCH_MP alloca_room_next_lt) >>
     qpat_assum `d + LENGTH (enc at av) <= _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `ei = AbiCopy 0 ==> abi_encode_empty_window_pre ctx func ready body_end
      (SND ops) src at av (n2w sb) d prepared` by
    (strip_tac >> pure_rewrite_tac[abi_encode_empty_window_pre_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- metis_tac[]
     >- (qpat_assum `abi_encoder_window_input ei at av sb 0 initial.vs_memory` mp_tac >>
         qpat_assum `ei = AbiCopy 0` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
         simp[abi_encoder_window_copy_iff, valueEncodingDefsTheory.mem_bytes_at_def])
     >- metis_tac[]
     >- metis_tac[]
     >> metis_tac[]) >>
  drule_all abiEncodePtrEmptyBodyCoreTheory.abi_encode_empty_body_observations_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "finish_inputs"
QED

Resume abi_encode_empty_phases_ptr[finish_inputs]:
  `32 <= outsz` by
    (qpat_assum `outsz = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `eval_operand (FST ops) t = SOME (n2w p)` by
    metis_tac[eval_operand_def] >>
  `eval_operand len t = SOME (n2w (LENGTH (enc at av))) /\
   ~t.vs_halted /\ t.vs_current_bb = body_end.cs_current_bb /\
   t.vs_inst_idx = LENGTH body_end.cs_current_insts` by
    (qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[window_strong_result_def, abi_encoder_window_result_def]) >>
  `abi_builtin_encode_finish (Var x) len m body_end = ((),final) /\
   abi_decoder_operand_live body_end.cs_next_var (Var x) /\
   eval_operand (Var x) t = SOME (n2w p)` by metis_tac[] >>
  `mem_bytes_at (p+32) (m+LENGTH (enc at av)) t.vs_memory =
   mem_bytes_at (p+32) (m+LENGTH (enc at av)) t.vs_memory` by simp_tac bool_ss [] >>
  drule_all abi_encode_finish_ptr_from_body_semantic >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `!i. i < p \/ p+32 <= i ==>
    mem_bytes_at i 1 actual.vs_memory = mem_bytes_at i 1 prepared.vs_memory` by
    (qpat_assum `abi_decode_frame p 32 t actual` mp_tac >>
     qpat_assum `!a n. mem_bytes_at a n t.vs_memory = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decode_frame_def] >>
     rpt strip_tac >> first_x_assum (qspecl_then [`i`, `1`] mp_tac) >> simp[]) >>
  `!z. not_fresh_at st z ==> not_fresh_at body_end z` by
    (qpat_assum `abi_builtin_encode_setup _ _ _ = _` mp_tac >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
     qpat_assum `ei = AbiCopy 0 \/ ei = AbiComplex []` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule abi_builtin_encode_setup_shape >> strip_tac >>
     `body_end.cs_next_var = ready.cs_next_var` by
       (Cases_on `ei = AbiCopy 0`
        >- (qpat_x_assum `ei = AbiCopy 0` SUBST_ALL_TAC >>
            drule abiEncoderLeavesTheory.abi_encode_copy_code >> strip_tac >>
            fs[emitHelperTheory.emit_void_def, compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
               compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >> gvs[]) >>
        `ei = AbiComplex []` by metis_tac[] >>
        gvs[abi_encode_empty_complex_body_probe]) >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists `st` >> simp[] >>
     Cases_on `method_id` >> fs[]) >>
  suspend "ghost_inputs"
QED

Resume abi_encode_empty_phases_ptr[ghost_inputs]:
  `local_ptrs_rel func cenv es.scopes prepared` by
    (qpat_assum `stmt_state_rel ctx func cenv cx es prepared` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def, state_rel_def]) >>
  `!n b sz. local_region cenv es.scopes prepared n b sz ==> regions_disjoint p 32 b sz` by
    (rpt strip_tac >>
     qpat_x_assum `!name b k. local_region _ _ _ _ _ _ ==> _` drule >>
     qpat_assum `32 <= outsz` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `actual.vs_accounts = prepared.vs_accounts /\ actual.vs_transient = prepared.vs_transient /\
   actual.vs_call_ctx = prepared.vs_call_ctx` by
    (qpat_assum `abi_encoder_registered_effect {} [(p,32)] t actual` mp_tac >>
     qpat_assum `abi_encode_exec_frame func prepared t` mp_tac >>
     qpat_assum `abi_encode_exec_frame func t actual` mp_tac >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ prepared t` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[window_strong_result_def, abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def,
       abi_encode_exec_frame_def] >> metis_tac[]) >>
  `!z v. not_fresh_at st z /\ lookup_var z prepared = SOME v ==>
      lookup_var z actual = SOME v` by
    (rpt strip_tac >>
     `abi_decoder_operand_live body_end.cs_next_var (Var z)` by
       (`not_fresh_at body_end z` by metis_tac[] >>
        pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[not_fresh_at_def, abiDecoderReentryTheory.abi_decoder_operand_live_def,
          abiDecoderReentryTheory.abi_decoder_older_vars_def]) >>
     metis_tac[eval_operand_def]) >>
  `ghost_inv rb cenv cx es H tf actual /\ ghost_kept cenv es st G tn initial H tf` by
    (irule abi_encode_empty_suffix_ghost >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`Gp`, `func`, `p`, `prepared`, `tnp`] >>
     simp_tac bool_ss [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  suspend "assemble"
QED

Resume abi_encode_empty_phases_ptr[assemble]:
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn initial 0 H tf (OK actual)` by
    metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
  `abi_encode_exec_frame func initial actual` by metis_tac[abi_encode_exec_frame_trans] >>
  `abi_decode_sim ctx func prepared t` by
    (qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[window_strong_result_def, abi_encoder_window_result_def]) >>
  `abi_decode_sim ctx func initial actual` by metis_tac[abiDecoderLoopTheory.abi_decode_sim_trans] >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists `prepared` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_encoder_extend_sim_trans >> qexists `t` >>
     conj_tac >- (qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp[window_strong_result_def]) >> first_assum ACCEPT_TAC) >>
  qexistsl [`prepared`, `t`, `actual`, `H`, `tf`, `x`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[]
  >- (qpat_assum `enc at av = []` (fn th => rewrite_tac[th]) >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[valueEncodingDefsTheory.mem_bytes_at_def])
  >- (qpat_assum `case method_id of NONE => T | SOME mid => _` mp_tac >>
      qpat_assum `abi_decode_frame p 32 t actual` mp_tac >>
      qpat_assum `!a n. mem_bytes_at a n t.vs_memory = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[abi_decode_frame_def] >> rpt strip_tac >>
      Cases_on `method_id` >> gvs[] >>
      first_x_assum (qspecl_then [`p+32`, `4`] mp_tac) >> simp[]) 
  >- (qpat_assum `abi_encode_exec_frame func initial actual` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_encode_exec_frame_def])
  >- metis_tac[]
  >> (qpat_assum `tf.t_mem = _` mp_tac >>
      qpat_assum `method_id <> NONE ==> !i. _` mp_tac >>
      qpat_assum `m = _` mp_tac >> qpat_assum `enc at av = []` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      Cases_on `method_id` >> simp[] >>
      rpt strip_tac >> gvs[IN_DIFF, GSPECIFICATION] >>
      Cases_on `i < p+32` >> simp[] >>
      `p+32 <= i /\ i < p+64` by decide_tac >> metis_tac[])
QED

Finalise abi_encode_empty_phases_ptr
