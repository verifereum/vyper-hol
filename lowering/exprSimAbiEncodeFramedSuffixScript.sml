(* Consumer checkpoint for the framed builtin suffix.  The body and finish
   must retain their singleton-context strong result; only the composed
   execution is transferred to the ambient context. *)
Theory exprSimAbiEncodeFramedSuffix
Ancestors
  exprSimAbiEncodeFramedBuiltin exprSimAbiEncodeFramedBody
  exprSimAbiEncodeOpenSetup exprSimAbiEncodeSetupOpen exprSimAbiEncodeWindowRoom abiEncoderWindowContract
  abiEncoderRegisteredEffect exprSimAbiEncodeFinish abiEncoderSequence
  instIdxIndep abiBuiltinEncodeCode venomState exprSimAbiEncodeExecution
  abiEncoderWindowLookup abiEncoderWindowSequence list venomMemDefs
  exprSimAbiEncodeConcreteResources abiDecoderLoop
  abiBuiltinEncodeSetup abiBuiltinAllocation abiDecoderContract abiBuiltinEncodeCorrect
  abiEncoderLeafGlobals
  exprSimAbiEncodeExecFrame exprSimAbiEncodeSemantic
  exprSimAbiEncodeOpenFinishExtension abiEncoderExtendSim
  exprLoweringProps compileEnv words finite_map arithmetic
  exprSimAbiEncodeSourceRoom exprSimAbiEncodeChargeTransfer venomInstIdsProps
  exprSimAbiEncodeNoBlockFrame exprSimAbiGasBridge emitHelperProps
  exprSimAbiEncodeConcreteBody exprSimAbiEncodeConcreteWrappers
  exprSimAbiEncodeObliviousFacts
  fragExec venomInst fragGasSeq fragGasMode

Theorem abi_encode_framed_setup_window:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\
  mid_size = (case method_id of NONE => 0 | SOME mid => 4) /\
  write_size = (case method_id of NONE => 0 | SOME mid => 32) /\
  outsz = 32+32*word_size (maxlen+mid_size) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  (sb+cap <= p+32 \/ p+32+write_size <= sb) ==>
  ?actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32+mid_size)) /\
    fresh_vars_wrt limit_st actual /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial actual /\
    abi_encoder_window_input ei at av sb cap actual.vs_memory /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    actual.vs_current_bb = ready.cs_current_bb /\
    actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    actual.vs_labels = initial.vs_labels
Proof
  Cases_on `method_id` >> simp[] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `mid_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `write_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  rule_assum_tac (SRULE [])
  >- (drule abi_encode_framed_setup_none_reach >> disch_then drule >>
      disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
         (32+32*word_size maxlen) p 0 initial actual` by
        gvs[abi_builtin_encode_setup_frame_def, abi_builtin_allocation_frame_def,
          abi_decode_frame_def] >>
      `FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,32+32*word_size maxlen)` by
        (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
      `abi_encoder_window_input ei at av sb cap actual.vs_memory` by
        (irule abi_encode_setup_frame_window_input >>
         goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
      qexists_tac `actual` >>
      pure_rewrite_tac[Q.SPECL [`32*word_size maxlen`, `32`] ADD_COMM] >> simp[]) >>
  drule abi_encode_framed_setup_some_reach >> disch_then drule >>
  disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,32+32*word_size (maxlen+4))` by
    (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_window_input ei at av sb cap actual.vs_memory` by
    (irule abi_encode_setup_frame_window_input >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qexists_tac `actual` >>
  pure_rewrite_tac[Q.SPECL [`32*word_size (maxlen+4)`, `32`] ADD_COMM] >> simp[]
QED

Theorem abi_encode_framed_body_singleton:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_encoder_window_pre (ctx with ctx_functions := [func]) func
    st st' dst src ei at av sb cap d s /\
  (!i. MEM i (fn_insts func) ==> i.inst_opcode <> INVOKE) ==>
  ?t. window_strong_result (ctx with ctx_functions := [func]) func
        st st' out at av d s t /\
      abi_encode_exec_frame func s t /\ abi_decode_sim ctx func s t
Proof
  strip_tac >> drule_all compile_abi_encode_to_buf_framed_run >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule abi_decode_sim_ctx_no_invoke >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `ctx with ctx_functions := [func]` >> simp[] >>
  drule window_strong_result_public >> simp[abi_encoder_window_result_def]
QED


(* Exact integration target for the next phase:
   abi_encode_window_phases_open in exprSimAbiEncodeExecution, with precisely
   the same premises except that room is over
     ctx with ctx_functions := [func]
   and with the additional premise
     !i. MEM i (fn_insts func) ==> i.inst_opcode <> INVOKE.
   Keep its prepared/body/actual witnesses and all its conclusions, keep the
   window_strong_result in that singleton context, and add
     abi_encode_exec_frame func initial actual.
   This target does NOT assume an expression frame.  The observer function
   func here is fn' of the counted bridge, not the real enclosing function.

   Premise inventory:
   - phase code/inclusion and distinct IDs: lower_abi_encode decomposition,
     fn_has_code subfragments, and the frozen bridge's fn' hypothesis;
   - allocation row, pure allocated-state alloca_inv, source/destination
     bounds, disjointness, 32-byte scratch rows: the existing producer
     boundaries and abi_encode_setup_window_pre (Execution imports);
   - singleton room: abi_encode_relabel_registered_room and setup_room;
     NO lookup_function func in the ambient ctx is required;
   - window input is the actual recursive read window, preserved by
     abi_encode_framed_setup_window for BOTH selector branches;
   - old/live source and buffer, phase variable limits: setup/finish shape
     lemmas and the producer metadata (unchanged from phases_open);
   - body execution: compile_abi_encode_to_buf_framed_run; no new outer
     function premise. Keep the same concrete body witness for finish;
   - finish: abi_encode_framed_builtin_finish at the singleton ctx; selector
     bytes use window_alloca_growth_frame, as in phases_open;
   - execution/frame transitivity, then abi_decode_sim_ctx_no_invoke ONCE.

   Expression consumer: abi_encode_nonword_counted_suffix currently returns
   bytes/control ONLY. Extend its Q with a real-function execution frame,
   registered effects and old-register preservation, not with strong_result
   (the latter contains execution and is not returndata insensitive).
   vv_post additionally requires stmt_state_rel, vv_holds, vv_at, old rows,
   protected old allocation bytes and locals_kept. The four-field exec_frame
   is not sufficient for those. Protected byte disjointness is supplied by
   actual allocation/local ownership; abi_encode_registered_protected_byte
   and abi_encode_charge_difference_lift are the checked transfer interfaces.
   Charge lifting additionally needs unchanged rows for real-function ALLOCAs
   absent from the observer: derive this from registered effect's ids, do NOT
   add a second instruction-inclusion premise to the bridge.

   No-block route: same phase composition target; count with the original
   abi_decode_sim_gas_path and the no-block observer, not a relabeled start.
   Its observer hypothesis has neither fn_name agreement nor no-INVOKE.
   Existing abi_encode_nonword_no_block_observer uses straight-line execution;
   a framed no-block consumer must retain that concrete sequence witness.
   Do not instantiate the singleton transfer theorem below at an arbitrary
   no-block observer without proving its no-INVOKE premise.
*)

Theorem abi_encode_registered_effect_bridge_updates:
  abi_encoder_registered_effect ids outs s t ==>
  abi_encoder_registered_effect ids outs s (t with vs_returndata := rd) /\
  abi_encoder_registered_effect ids outs s (t with vs_prev_bb := prev)
Proof
  simp[abi_encoder_registered_effect_def] >> metis_tac[]
QED

(* The window result preserves OLD registers but intentionally does not
   promise global fresh_vars_wrt at the final compile frontier.  Finish is
   straight-line and does not need that stronger premise. *)
Theorem abi_encode_framed_finish_open:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\
  fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\
  eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\ p < dimword (:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\
    mload p actual = n2w (len+mid_size) /\
    abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [(p,32)] initial actual /\
    abi_encode_exec_frame func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule_all abi_encode_finish_sequence_open >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule abi_builtin_encode_finish_global_code >> strip_tac >>
  drule_all abi_encoder_leaf_sequence_globals >> strip_tac >>
  `abi_encode_exec_frame func initial encoded` by
    (drule_all abi_encode_framed_finish_sequence >> simp[]) >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (first_x_assum irule >> simp[]) >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, eval_op_inst_idx, mload_def,
    abi_encoder_registered_effect_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem abi_encode_framed_phases_open_extend:
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
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
  (sb+cap <= p+32 \/ p+32+w <= sb) /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) ==>
  ?prepared body actual.
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
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_framed_setup_window_open_extend >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_builtin_encode_setup_frame _ _ _ _ _ initial prepared` >>
  `abi_encoder_window_pre ctx func ready body_end (SND ops) src ei at av sb cap d prepared` by
    (qpat_x_assum `d = _` SUBST_ALL_TAC >>
     qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
     qpat_x_assum `m = _` SUBST_ALL_TAC >>
     irule (SIMP_RULE bool_ss [LET_THM] abi_encode_setup_window_pre) >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     qexistsl [`initial`, `st.cs_next_var`, `32+32*word_size (maxlen+(case method_id of NONE => 0 | SOME mid => 4))`, `p`, `st.cs_next_id`, `w`] >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     rpt strip_tac >>
     qpat_x_assum `!inst b sz. _` (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  drule_all compile_abi_encode_to_buf_framed_run >> strip_tac >>
  rename1 `window_strong_result ctx func ready body_end len at av d prepared body_state` >>
  `eval_operand (FST ops) body_state = SOME (n2w p)` by
    (irule abi_encode_setup_buffer_eval >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [window_strong_result_def, abi_encoder_window_result_def]) >>
  drule_all abi_encode_framed_finish_open_extend >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "endpoint"
QED

Resume abi_encode_framed_phases_open_extend[endpoint]:
  `mem_bytes_at (p+32) m body_state.vs_memory = mem_bytes_at (p+32) m prepared.vs_memory` by
    (irule window_alloca_growth_frame >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
     conj_tac >- (qpat_x_assum `d + LENGTH _ <= _` mp_tac >>
       pure_asm_rewrite_tac[] >> decide_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`window_alloca_sites func (frag_ids ready body_end)`, `[(d,LENGTH (enc at av))]`] >>
     reverse conj_tac >-
       (conj_tac >- (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
     qpat_x_assum `d = _` SUBST_ALL_TAC >>
     qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
     qpat_x_assum `m = _` SUBST_ALL_TAC >>
     rpt strip_tac >>
     qpat_x_assum `_ IN window_alloca_sites _ _` mp_tac >>
     simp_tac (srw_ss()) [window_alloca_sites_def] >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
       (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     qpat_x_assum `FLOOKUP prepared.vs_allocas i = SOME (b,sz)` mp_tac >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  suspend "observations"
QED

Resume abi_encode_framed_phases_open_extend[observations]:
  `mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av` by
    (qpat_assum `abi_decode_frame p 32 body_state actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     qpat_x_assum `!p' k. _` (qspecl_then [`d`, `LENGTH (enc at av)`] mp_tac) >>
     (impl_tac >- (qpat_x_assum `d = _` mp_tac >> decide_tac)) >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `(case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid)` by
    (qpat_assum `abi_decode_frame p 32 body_state actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     `mem_bytes_at (p+32) m actual.vs_memory = mem_bytes_at (p+32) m body_state.vs_memory` by
       (qpat_x_assum `!p' k. _` (qspecl_then [`p+32`, `m`] mp_tac) >>
        simp_tac bool_ss [arithmeticTheory.LE_REFL]) >>
     qpat_x_assum `mem_bytes_at (p+32) m body_state.vs_memory = _` mp_tac >>
     qpat_x_assum `mem_bytes_at (p+32) m actual.vs_memory = _` mp_tac >>
     qpat_x_assum `case method_id of NONE => T | SOME mid => _` mp_tac >>
     qpat_x_assum `m = _` mp_tac >>
     Cases_on `method_id` >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists `prepared` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_decode_sim_trans >> qexists `body_state` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encode_exec_frame func initial actual` by
    (irule abi_encode_exec_frame_trans >> qexists `prepared` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_encode_exec_frame_trans >> qexists `body_state` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH initial.vs_memory <= LENGTH actual.vs_memory` by
    (drule abi_encode_exec_frame_memory_length >> simp[]) >>
  `actual.vs_labels = initial.vs_labels` by
    (drule window_strong_result_labels >> simp[]) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `prepared` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_encoder_extend_sim_trans >> qexists_tac `body_state` >> simp[]) >>
  qexistsl [`prepared`, `body_state`, `actual`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise abi_encode_framed_phases_open_extend

Theorem abi_encode_framed_phases_open:
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
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
  (sb+cap <= p+32 \/ p+32+w <= sb) /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) ==>
  ?prepared body actual.
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
    prepared.vs_labels = initial.vs_labels /\ actual.vs_labels = initial.vs_labels
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_framed_phases_open_extend >> strip_tac >>
  rename1 `window_strong_result _ _ _ _ _ _ _ _ prepared body_state` >>
  qexistsl [`prepared`, `body_state`, `actual`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Applies directly to the same actual endpoint exported by phases_open. *)
Theorem abi_encode_framed_semantic_fields:
  abi_encode_exec_frame func initial actual ==>
  actual.vs_tx_ctx = initial.vs_tx_ctx /\
  actual.vs_block_ctx = initial.vs_block_ctx /\
  actual.vs_outcomes = initial.vs_outcomes /\
  actual.vs_immutables = initial.vs_immutables /\
  actual.vs_code = initial.vs_code
Proof
  strip_tac >> drule abi_encode_exec_frame_semantic >>
  simp[abi_encode_semantic_obs_fields]
QED

Theorem abi_encode_raw_framed_observer:
  !dst src ei st out st' ctx func obs at av sb cap d s.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s /\
    fn_has_code st st' obs /\ fn_inst_ids_distinct obs /\
    obs.fn_name = func.fn_name /\
    (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
         i.inst_opcode <> NOP ==> MEM i (fn_insts func)) /\
    (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) ==>
    ?t. window_strong_result (ctx with ctx_functions := [obs]) obs
          st st' out at av d s t /\
        abi_encode_exec_frame func s t /\ abi_decode_sim ctx obs s t
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  `alloca_room (ctx with ctx_functions := [obs]) obs s` by
    (irule abi_encode_bridge_local_room >> metis_tac[]) >>
  `abi_encoder_window_pre (ctx with ctx_functions := [obs]) obs
     st st' dst src ei at av sb cap d s` by
    (pure_rewrite_tac[abi_encoder_window_pre_def] >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> _`
       irule >> qexists `inst` >> simp[] >>
       qpat_x_assum `!i. MEM i (fn_insts obs) /\ _ ==> _` irule >> simp[]) >>
  drule_all abi_encode_framed_body_singleton >> strip_tac >>
  `abi_encoder_registered_effect (window_alloca_sites obs (frag_ids st st'))
     [(d,LENGTH (enc at av))] s t` by
    (drule window_strong_result_effect >> simp[]) >>
  `!i. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
        ~MEM i (fn_insts obs) ==>
        FLOOKUP t.vs_allocas i.inst_id = FLOOKUP s.vs_allocas i.inst_id` by
    (rpt strip_tac >>
     `i.inst_id NOTIN window_alloca_sites obs (frag_ids st st')` by
       (simp[window_alloca_sites_def] >> disj2_tac >>
        rpt strip_tac >>
        `MEM inst (fn_insts func)` by
          (qpat_x_assum `!i. MEM i (fn_insts obs) /\ _ ==> _` irule >> simp[]) >>
        `inst = i` by metis_tac[venomInstIdsPropsTheory.fn_inst_ids_distinct_inj] >>
        metis_tac[]) >>
     fs[abi_encoder_registered_effect_def]) >>
  `abi_encode_exec_frame func s t` by
    (fs[abi_encode_exec_frame_def] >>
     irule abi_encode_charge_difference_lift >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists `obs` >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (fn_insts obs) /\ _ ==> _` irule >> simp[]) >>
  qexists `t` >> simp[]
QED

Theorem abi_encode_window_seq_counted:
  window_seq st en s raw /\ frag_gas_free st en /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~(raw with vs_inst_idx := LENGTH en.cs_current_insts).vs_halted /\
  Q (raw with vs_inst_idx := LENGTH en.cs_current_insts) /\
  (!t rd. Q t ==> Q (t with vs_returndata := rd)) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
      t.vs_current_bb = en.cs_current_bb /\
      t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  strip_tac >>
  irule abi_decode_sim_gas_path_named >> simp[] >> qexists `st` >> simp[] >>
  `en.cs_blocks = st.cs_blocks /\ en.cs_current_bb = st.cs_current_bb /\
   inst_extends st en` by fs[window_seq_def] >>
  `cs_extends st en` by
    (fs[cs_extends_def, inst_extends_def]) >>
  simp[] >> rpt strip_tac >>
  `?t. t = raw with vs_inst_idx := LENGTH en.cs_current_insts /\
       t.vs_current_bb = en.cs_current_bb /\
       t.vs_inst_idx = LENGTH en.cs_current_insts /\
       abi_decode_sim ctx fn' s t` by
    (irule abi_encoder_run_sequence_reach >> simp[] >> qexists `st` >>
     fs[window_seq_def]) >>
  qexists `t` >> gvs[]
QED

Theorem abi_encode_raw_sequence_counted_frame:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  window_seq st en s raw /\ frag_gas_free st en /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~(raw with vs_inst_idx := LENGTH en.cs_current_insts).vs_halted /\
  Q (raw with vs_inst_idx := LENGTH en.cs_current_insts) /\
  (!t rd. Q t ==> Q (t with vs_returndata := rd)) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\
      abi_encode_exec_frame func s t /\ ~t.vs_halted /\
      t.vs_current_bb = en.cs_current_bb /\
      t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  strip_tac >>
  `abi_encode_exec_frame func s
     (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule abi_encode_no_block_body_frame_normalized >>
     fs[window_seq_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`Q` |-> `\t. Q t /\ abi_encode_exec_frame func s t`]
    abi_encode_window_seq_counted) >>
  pure_rewrite_tac[BETA_THM, GSYM CONJ_ASSOC] >>
  impl_tac
  >- (simp[] >> metis_tac[abi_encode_exec_frame_bridge_updates]) >>
  simp[CONJ_ASSOC]
QED

Theorem abi_encode_raw_counted_no_blocks:
  !dst src ei st out en ctx func at av sb cap d s.
    compile_abi_encode_to_buf dst src ei st = (out,en) /\
    abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
    st.cs_blocks = en.cs_blocks ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = en.cs_current_bb /\
      t.vs_inst_idx = LENGTH en.cs_current_insts /\
      mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
      eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
      abi_encoder_registered_effect (frag_ids st en) [(d,LENGTH (enc at av))] s t /\
      alloca_inv t /\
      (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
      window_alloca_growth s t /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      t.vs_labels = s.vs_labels /\ abi_encode_exec_frame func s t
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (SPEC_ALL abi_encode_concrete_contract_all) >>
  rewrite_tac[abi_encode_concrete_contract_def] >>
  disch_then drule_all >> strip_tac >>
  fs[abi_encode_concrete_result_def] >>
  `cs_extends st en /\ frag_ops_free st en` by
    metis_tac[abi_encode_raw_relabel_structure] >>
  `en.cs_current_bb = st.cs_current_bb` by gvs[cs_extends_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st en) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts st en) = []` by
    (drule_all abi_encode_no_block_opcodes >>
     simp[EVERY_MEM, FILTER_EQ_NIL] >> strip_tac >>
     conj_tac >> rpt strip_tac >> first_x_assum drule >>
     strip_tac >> gvs[is_terminator_def]) >>
  `abi_encode_exec_frame func s (r with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule abi_encode_no_block_body_frame_normalized >>
     fs[abi_encoder_window_pre_def] >> metis_tac[]) >>
  `gas_path ctx func s 0 (OK (r with vs_inst_idx := LENGTH en.cs_current_insts))` by
    (fs[abi_encoder_window_pre_def, fn_has_code_def] >>
     `isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions)` by
       (fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
        qexists `l` >>
        pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >> REFL_TAC) >>
     `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     drule_all tuple_run_inst_seq_gas_path >>
     simp[] >>
     fs[inst_extends_def]) >>
  qexists `r with vs_inst_idx := LENGTH en.cs_current_insts` >>
  fs[gas_marked_path_def, window_strong_result_def, abi_encoder_window_result_def] >>
  metis_tac[]
QED

Theorem abi_encode_raw_relabel_window_pre:
  !dst src ei st out en ctx func at av sb cap d s L ids obs.
    compile_abi_encode_to_buf dst src ei st = (out,en) /\
    abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
    st.cs_blocks <> en.cs_blocks /\
    LENGTH ids = LENGTH st.cs_current_insts /\
    fn_has_code (start_relabel L ids st) (start_swap st L ids en) obs /\
    fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
    (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
         i.inst_opcode <> NOP ==> MEM i (fn_insts func)) ==>
    abi_encoder_window_pre (ctx with ctx_functions := [obs]) obs
      (start_relabel L ids st) (start_swap st L ids en)
      dst src ei at av sb cap d (s with vs_current_bb := L)
Proof
  rpt gen_tac >> strip_tac >>
  `alloca_room (ctx with ctx_functions := [obs]) obs s` by
    (irule abi_encode_bridge_local_room >>
     fs[abi_encoder_window_pre_def] >> metis_tac[]) >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  rewrite_tac[abi_encoder_window_pre_def] >>
  simp_tac (srw_ss()) [] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (Cases_on `src` >> fs[eval_operand_def, lookup_var_def])
  >- (Cases_on `dst` >> fs[eval_operand_def, lookup_var_def])
  >- (simp_tac (srw_ss()) [start_relabel_def,
        loweringStateRelDefsTheory.not_fresh_at_def] >>
      qpat_x_assum `!x. _ ==> not_fresh_at st x` mp_tac >>
      simp_tac (srw_ss()) [loweringStateRelDefsTheory.not_fresh_at_def])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_x_assum `alloca_inv s` mp_tac >>
      simp_tac (srw_ss()) [alloca_inv_def, allocas_non_overlapping_def,
        alloca_next_valid_def])
  >- (qpat_x_assum `alloca_room _ obs s` mp_tac >>
      simp_tac (srw_ss()) [alloca_room_def, pending_alloca_size_def])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (simp_tac (srw_ss()) [abiEncoderPropsTheory.frag_ids_def,
        start_relabel_def, start_swap_def, LET_THM] >>
      COND_CASES_TAC >> simp_tac (srw_ss()) [] >>
      rpt strip_tac >>
      `MEM inst (fn_insts func)` by
        (first_x_assum irule >> simp[]) >>
      qpat_x_assum `!inst b sz. _`
        (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
      simp[abiEncoderPropsTheory.frag_ids_def])
  >- first_assum ACCEPT_TAC
  >- simp_tac (srw_ss()) [start_relabel_def]
  >- simp[start_relabel_def]
QED
