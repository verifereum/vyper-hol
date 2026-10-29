(* Compatibility probe: a child call followed by actual straight-line code.
   The common spine neither constructs nor strengthens the child contract. *)
Theory abiEncoderCompositionCompat
Ancestors
  abiEncoderSharedContract abiEncoderCorrect abiEncoderSequence abiScratchEncoderContract
  abiEncoderAdmissible abiEncoderExtendSim
  abiDecoderLoop abiDecoderReentry compileEnv venomState venomExecSemantics list

Theorem abi_encoder_child_sequence_compose:
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s u. run_inst_seq (emitted_insts middle final) s = OK u /\
     ~s.vs_halted /\ s.vs_current_bb = middle.cs_current_bb /\
     s.vs_inst_idx = LENGTH middle.cs_current_insts ==>
     R s (u with vs_inst_idx := LENGTH final.cs_current_insts)) /\
  (?s. P s /\ R initial s) /\
  (!s. P s ==> ~s.vs_halted /\ s.vs_current_bb = middle.cs_current_bb /\
     s.vs_inst_idx = LENGTH middle.cs_current_insts /\
     ?u. run_inst_seq (emitted_insts middle final) s = OK u /\
       Q (u with vs_inst_idx := LENGTH final.cs_current_insts)) ==>
  ?actual. Q actual /\ R initial actual
Proof
  strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `u with vs_inst_idx := LENGTH final.cs_current_insts` >>
  conj_tac >- simp[] >>
  `R s (u with vs_inst_idx := LENGTH final.cs_current_insts)` by
    (first_x_assum irule >> simp[]) >>
  metis_tac[]
QED

(* These specializations check the concrete continuation adapter, not just
   transitivity.  P carries whichever observations the child really supplies. *)
Theorem abi_encoder_weak_child_sequence:
  final.cs_blocks = middle.cs_blocks /\
  final.cs_current_bb = middle.cs_current_bb /\ inst_extends middle final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts middle final) /\ fn_has_code middle final func /\
  (?s. P s /\ abi_decode_sim ctx func initial s) /\
  (!s. P s ==> ~s.vs_halted /\ s.vs_current_bb = middle.cs_current_bb /\
     s.vs_inst_idx = LENGTH middle.cs_current_insts /\
     ?u. run_inst_seq (emitted_insts middle final) s = OK u /\
       Q (u with vs_inst_idx := LENGTH final.cs_current_insts)) ==>
  ?actual. Q actual /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> irule abi_encoder_child_sequence_compose >>
  conj_tac >- metis_tac[abi_decode_sim_trans] >>
  qexistsl_tac [`P`, `final`, `middle`] >>
  conj_tac
  >- (rpt strip_tac >> drule_all abi_encoder_run_sequence_reach >> simp[]) >>
  conj_tac >- simp[] >> metis_tac[]
QED

Theorem abi_encoder_rich_child_sequence:
  final.cs_blocks = middle.cs_blocks /\
  final.cs_current_bb = middle.cs_current_bb /\ inst_extends middle final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts middle final) /\ fn_has_code middle final func /\
  (?s. P s /\ abi_encoder_extend_sim ctx func initial s) /\
  (!s. P s ==> ~s.vs_halted /\ s.vs_current_bb = middle.cs_current_bb /\
     s.vs_inst_idx = LENGTH middle.cs_current_insts /\
     ?u. run_inst_seq (emitted_insts middle final) s = OK u /\
       Q (u with vs_inst_idx := LENGTH final.cs_current_insts)) ==>
  ?actual. Q actual /\ abi_encoder_extend_sim ctx func initial actual
Proof
  strip_tac >> irule abi_encoder_child_sequence_compose >>
  conj_tac >- metis_tac[abi_encoder_extend_sim_trans] >>
  qexistsl_tac [`P`, `final`, `middle`] >>
  conj_tac
  >- (rpt strip_tac >> irule abi_encoder_run_sequence_extend_sim >> simp[] >> qexists_tac `middle` >> simp[]) >>
  conj_tac >- simp[] >> metis_tac[]
QED

(* Exact old child premises.  The continuation must work with these weak
   observations only; no registered effect or extension stability is assumed. *)
Theorem abi_encoder_scratch_call_sequence:
  abi_scratch_encoder ei /\
  compile_abi_encode_to_buf dst src ei start = (out,middle) /\ fn_has_code start middle func /\
  (start.cs_blocks = middle.cs_blocks \/
    !bb. lookup_block middle.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av start src dst sb source_cap d (LENGTH (enc at av))
    first last b cap initial /\
  abi_decoder_budget first last b cap initial /\
  first <= start.cs_next_id /\ middle.cs_next_id <= last /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  final.cs_blocks = middle.cs_blocks /\ final.cs_current_bb = middle.cs_current_bb /\
  inst_extends middle final /\ fn_has_code middle final func /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts middle final) /\
  (!s. mem_bytes_at d (LENGTH (enc at av)) s.vs_memory = enc at av /\
    eval_operand out s = SOME (n2w (LENGTH (enc at av))) /\
    abi_scratch_effect first last start.cs_next_id middle.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial s /\
    s.vs_current_bb = middle.cs_current_bb /\ s.vs_inst_idx = LENGTH middle.cs_current_insts /\
    ~s.vs_halted ==>
    ?u. run_inst_seq (emitted_insts middle final) s = OK u /\
      Q (u with vs_inst_idx := LENGTH final.cs_current_insts)) ==>
  ?actual. Q actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_scratch_encoder _`
    (mp_tac o PURE_REWRITE_RULE [abi_scratch_encoder_def]) >>
  disch_then drule_all >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule abi_encoder_weak_child_sequence >>
  qexistsl_tac [`\s. s = actual`, `final`, `middle`] >>
  simp[]
QED

Theorem abi_encoder_correct_call_sequence:
  abi_encoder_correct ei /\
  compile_abi_encode_to_buf dst src ei start = (out,middle) /\ fn_has_code start middle func /\
  (start.cs_blocks = middle.cs_blocks \/
    !bb. lookup_block middle.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_pre ei at av start src dst sb source_cap d b cap initial /\
  abi_decoder_budget first last b cap initial /\
  first <= start.cs_next_id /\ middle.cs_next_id <= last /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  final.cs_blocks = middle.cs_blocks /\ final.cs_current_bb = middle.cs_current_bb /\
  inst_extends middle final /\ fn_has_code middle final func /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts middle final) /\
  (!s. mem_bytes_at d (LENGTH (enc at av)) s.vs_memory = enc at av /\
    eval_operand out s = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last start.cs_next_id middle.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial s /\
    s.vs_current_bb = middle.cs_current_bb /\ s.vs_inst_idx = LENGTH middle.cs_current_insts /\
    ~s.vs_halted ==>
    ?u. run_inst_seq (emitted_insts middle final) s = OK u /\
      Q (u with vs_inst_idx := LENGTH final.cs_current_insts)) ==>
  ?actual. Q actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_correct_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule abi_encoder_weak_child_sequence >>
  qexistsl_tac [`\s. s = t`, `final`, `middle`] >> simp[]
QED

Theorem abi_encoder_shared_call_sequence:
  abi_encoder_shared ei /\
  compile_abi_encode_to_buf dst src ei start = (out,middle) /\ fn_has_code start middle func /\
  (start.cs_blocks = middle.cs_blocks \/
    !bb. lookup_block middle.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (ei,at,av) (start,src,dst) (sb,source_cap) (d,LENGTH (enc at av))
    (first,last,b,cap) initial /\
  abi_decoder_budget first last b cap initial /\
  first <= start.cs_next_id /\ middle.cs_next_id <= last /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  final.cs_blocks = middle.cs_blocks /\ final.cs_current_bb = middle.cs_current_bb /\
  inst_extends middle final /\ fn_has_code middle final func /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts middle final) /\
  (!s. abi_encoder_shared_endpoint (ctx,func) (start,middle,out,limit_st)
    (first,last,b,cap) (at,av,d) initial s ==>
    ?u. run_inst_seq (emitted_insts middle final) s = OK u /\
      Q (u with vs_inst_idx := LENGTH final.cs_current_insts)) ==>
  ?actual. Q actual /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule abi_encoder_shared_endpoint_extend_sim >> strip_tac >>
  drule abi_encoder_shared_endpoint_block >> strip_tac >>
  drule abi_encoder_shared_endpoint_index >> strip_tac >>
  drule abi_encoder_shared_endpoint_nonhalted >> strip_tac >>
  irule abi_encoder_rich_child_sequence >>
  qexistsl_tac [`\s. s = actual`, `final`, `middle`] >> simp[]
QED

(* Inactive arrays continue to require the old static-leaf interface. *)
Theorem abi_encoder_array_child_compat:
  (if active then abi_encoder_shared ei else abi_encoder_static_leaf ei) ==>
  (if active then abi_scratch_encoder ei else abi_encoder_static_leaf ei)
Proof
  Cases_on `active` >> simp[abi_encoder_shared_scratch]
QED
