(* Consumer checkpoint for the framed builtin suffix.  The body and finish
   must retain their singleton-context strong result; only the composed
   execution is transferred to the ambient context. *)
Theory exprSimAbiEncodeFramedSuffix
Ancestors
  exprSimAbiEncodeFramedBuiltin exprSimAbiEncodeFramedBody
  exprSimAbiEncodeOpenSetup exprSimAbiEncodeWindowRoom abiEncoderWindowContract
  abiEncoderRegisteredEffect
  abiBuiltinEncodeSetup abiBuiltinAllocation abiDecoderContract abiBuiltinEncodeCorrect
  exprSimAbiEncodeExecFrame exprLoweringProps compileEnv words finite_map arithmetic

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
    abi_encode_exec_frame func initial actual
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

Theorem abi_encode_exec_frame_bridge_updates:
  abi_encode_exec_frame func s t ==>
  abi_encode_exec_frame func s (t with vs_returndata := rd) /\
  abi_encode_exec_frame func s (t with vs_prev_bb := prev)
Proof
  simp[abi_encode_exec_frame_def, pending_alloca_size_def]
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
