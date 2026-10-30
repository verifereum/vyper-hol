(* Control-flow probes for extension-stable encoder simulation. *)
Theory abiEncoderExtendControl
Ancestors
  abiEncoderExtendSim abiEncoderVarTransport abiEncoderObserver
  abiEncoderArrayLoopEntry abiEncoderArrayLoopHeader abiDecoderPrimitiveLoopEntry
  abiDecoderLoop abiDecoderVarExtend execEquivParamDefs abiEncoderArrayHeader abiEncoderArrayLoopCode
  venomExecSemantics venomState venomInst words list arithmetic

Theorem abi_encoder_observer_step_extend_sim:
  abi_observer_step ctx fn cut s t ==> abi_encoder_extend_sim ctx fn s t
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_extend_sim_def] >> conj_tac
  >- (drule abi_observer_step_sim >> simp[]) >>
  rpt strip_tac >> drule_all abi_encoder_observer_step_extend >> strip_tac >>
  goal_assum (drule_at Any) >> drule abi_observer_step_sim >> simp[]
QED

(* Only successful selected PHI inputs are required.  Parallel assignment and
   predecessor preservation are supplied by abi_encoder_phis_extend. *)
Theorem abi_encoder_branch_phis_extend_sim:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ is_terminator inst.inst_opcode /\
  step_inst_base inst s = OK middle /\ ~s.vs_halted /\ ~middle.vs_halted /\
  lookup_block middle.vs_current_bb fn.fn_blocks = SOME target /\
  eval_phis middle target.bb_instructions = OK entered /\ ~entered.vs_halted ==>
  abi_encoder_extend_sim ctx fn s
    (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)
Proof
  strip_tac >> irule abi_encoder_observer_step_extend_sim >>
  qexists_tac `(s.vs_current_bb, SUC s.vs_inst_idx)` >>
  simp[abi_observer_step_def, step_inst_non_invoke] >>
  qexistsl_tac [`bb`, `inst`, `middle`] >> simp[step_inst_non_invoke] >>
  qexistsl_tac [`target`, `entered`] >> simp[]
QED

Theorem abi_encoder_vars_extend_jump:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras (jump_to lbl s) (jump_to lbl t)
Proof
  rw[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"] >>
  fs[jump_to_def, vsr_frame_def, venom_state_component_equality]
QED

Theorem abi_encoder_loop_entry_extend_sim:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted ==>
  abi_encoder_extend_sim ctx fn s (jump_to hdr s)
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_extend_sim_def] >> conj_tac
  >- (drule_all abi_decoder_loop_entry_sim >> simp[]) >>
  rpt strip_tac >> qexists_tac `jump_to hdr t` >> conj_tac
  >- (irule abi_encoder_vars_extend_jump >> simp[]) >>
  drule abi_encoder_vars_extend_control >> strip_tac >>
  irule abi_decoder_loop_entry_sim >> gvs[] >>
  qexists_tac `id` >> simp[]
QED

(* The actual encoder array entry has a zero PHI prefix. *)
Theorem abi_encoder_array_loop_entry_extend_sim:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  abi_encoder_extend_sim ctx func initial (jump_to (FST labels) initial)
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_extend_sim_def] >> conj_tac
  >- (drule_all abi_encoder_array_loop_entry_sim >> simp[]) >>
  rpt strip_tac >> qexists_tac `jump_to (FST labels) t` >> conj_tac
  >- (irule abi_encoder_vars_extend_jump >> simp[]) >>
  drule abi_encoder_vars_extend_control >> strip_tac >>
  irule abi_encoder_array_loop_entry_sim >> gvs[] >> metis_tac[]
QED

Theorem abi_encoder_extend_finite_iteration:
  !(bound:num) i loop_inv Q ctx fn s.
  i <= bound /\ loop_inv i s /\
  (!j u. loop_inv j u /\ j < bound ==>
    ?v. loop_inv (SUC j) v /\ abi_encoder_extend_sim ctx fn u v) /\
  (!u. loop_inv bound u ==> ?v. Q v /\ abi_encoder_extend_sim ctx fn u v) ==>
  ?t. Q t /\ abi_encoder_extend_sim ctx fn s t
Proof
  completeInduct_on `(bound:num) - i` >> rpt strip_tac >>
  Cases_on `i = bound`
  >- metis_tac[] >>
  `i < bound` by decide_tac >>
  `?v. loop_inv (SUC i) v /\ abi_encoder_extend_sim ctx fn s v` by metis_tac[] >>
  rename1 `loop_inv (SUC i) next` >>
  `?t. Q t /\ abi_encoder_extend_sim ctx fn next t` by
    (qpat_x_assum `!m. m < _ ==> _` (qspec_then `bound - SUC i` mp_tac) >>
     (impl_tac >- decide_tac) >>
     disch_then (qspecl_then [`bound`, `SUC i`] mp_tac) >>
     simp[] >> disch_then irule >> simp[] >>
     qexists_tac `loop_inv` >> simp[]) >>
  metis_tac[abi_encoder_extend_sim_trans]
QED

(* The emitted array header uses JNZ and enters blocks with zero PHI prefix.
   Both extended execution and ordinary simulation end at this same state. *)
Theorem abi_encoder_array_header_extend_sim:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ phi_prefix_length exit_bb.bb_instructions = 0 /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\ count_op <> Var iv /\
  eval_operand ip s = SOME p /\ eval_operand count_op s = SOME (n2w n) /\
  mload (w2n p) s = n2w i /\ i <= n /\ n < dimword (:256) ==>
  abi_encoder_extend_sim ctx func s (jump_to (if i<n then body_lbl else exit_lbl)
    (abi_encode_array_header_state iv cmp done i n s))
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_extend_sim_def] >> conj_tac
  >- (irule abi_encode_array_header_sim >> metis_tac[]) >>
  rpt strip_tac >>
  qexists_tac `jump_to (if i<n then body_lbl else exit_lbl)
    (abi_encode_array_header_state iv cmp done i n t)` >> conj_tac
  >- (irule abi_encoder_vars_extend_jump >>
      simp_tac bool_ss [abi_encode_array_header_state_def] >>
      rpt (irule abi_decoder_vars_extend_update) >> simp[]) >>
  `eval_operand ip t = SOME p` by
    (irule abi_decoder_vars_extend_eval >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand count_op t = SOME (n2w n)` by
    (irule abi_decoder_vars_extend_eval >> goal_assum (drule_at Any) >> simp[]) >>
  drule abi_encoder_vars_extend_control >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  irule abi_encode_array_header_sim >>
  gvs[mload_def] >> metis_tac[]
QED

Theorem abi_encoder_array_loop_header_extend_sim:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  s.vs_current_bb = FST labels /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  count_op <> Var (STRING #"%" (toString owner_st.cs_next_var)) /\
  eval_operand ip s = SOME p /\ eval_operand count_op s = SOME (n2w n) /\
  mload (w2n p) s = n2w i /\ i <= n /\ n < dimword (:256) ==>
  abi_encoder_extend_sim ctx func s
    (jump_to (if i<n then FST (SND labels) else SND (SND labels))
      (abi_encode_array_header_state
        (STRING #"%" (toString owner_st.cs_next_var))
        (STRING #"%" (toString (owner_st.cs_next_var+1)))
        (STRING #"%" (toString (owner_st.cs_next_var+2))) i n s))
Proof
  simp_tac bool_ss [abi_encoder_array_loop_code_def] >> strip_tac >>
  irule abi_encoder_array_header_extend_sim >> gvs[] >> metis_tac[]
QED
