(* Restore original variables at a shared encoder endpoint. *)
Theory abiEncoderVarRestore
Ancestors
  abiEncoderEntry abiEncoderSharedContract abiEncoderExtendSim abiScratchEffect
  abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend execEquivParamProps pair
  execEquivParamDefs stateEquiv venomExecSemantics venomState compileEnv finite_map

Theorem abi_encoder_vars_extend_fields:
  abi_decoder_vars_extend extras s t ==>
  (t.vs_memory, t.vs_allocas, t.vs_alloca_next,
   t.vs_accounts, t.vs_transient, t.vs_logs, t.vs_requests,
   t.vs_current_bb, t.vs_inst_idx, t.vs_halted) =
  (s.vs_memory, s.vs_allocas, s.vs_alloca_next,
   s.vs_accounts, s.vs_transient, s.vs_logs, s.vs_requests,
   s.vs_current_bb, s.vs_inst_idx, s.vs_halted)
Proof
  strip_tac >> drule abi_decoder_vars_extend_restore >>
  disch_then (mp_tac o AP_TERM ``\u:venom_state.
    (u.vs_memory,u.vs_allocas,u.vs_alloca_next,
     u.vs_accounts,u.vs_transient,u.vs_logs,u.vs_requests,
     u.vs_current_bb,u.vs_inst_idx,u.vs_halted)``) >> simp[]
QED

Theorem abi_encoder_shared_restore:
  abi_encoder_shared_endpoint (ctx,func) (st,st',out,limit_st)
    (first,last,b,cap) (at,av,d)
    (abi_decoder_prune_vars st.cs_next_var initial) actual ==>
  ?restored.
    abi_decoder_vars_extend initial.vs_vars actual restored /\
    restored.vs_memory = actual.vs_memory /\
    restored.vs_allocas = actual.vs_allocas /\
    restored.vs_alloca_next = actual.vs_alloca_next /\
    restored.vs_accounts = actual.vs_accounts /\
    restored.vs_transient = actual.vs_transient /\
    restored.vs_logs = actual.vs_logs /\
    restored.vs_requests = actual.vs_requests /\
    mem_bytes_at d (LENGTH (enc at av)) restored.vs_memory = enc at av /\
    eval_operand out restored = SOME (n2w (LENGTH (enc at av))) /\
    restored.vs_current_bb = st'.cs_current_bb /\
    restored.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~restored.vs_halted /\ abi_decode_sim ctx func initial restored
Proof
  strip_tac >> drule abi_encoder_shared_endpoint_extend_sim >>
  simp_tac bool_ss [abi_encoder_extend_sim_def] >> strip_tac >>
  `abi_decoder_vars_extend initial.vs_vars
    (abi_decoder_prune_vars st.cs_next_var initial) initial` by
    simp[abi_decoder_prune_extension] >>
  first_x_assum drule >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars actual restored` >>
  qexists_tac `restored` >>
  drule abi_encoder_vars_extend_fields >> simp_tac bool_ss [PAIR_EQ] >> strip_tac >>
  `eval_operand out restored = SOME (n2w (LENGTH (enc at av)))` by
    (irule abi_decoder_vars_extend_eval >>
     goal_assum (drule_at Any) >>
     drule abi_encoder_shared_endpoint_output >> simp[]) >>
  fs[abi_encoder_shared_endpoint_def]
QED

Theorem abi_encoder_restored_operand:
  abi_encoder_shared_endpoint (ctx,func) (st,st',out,limit_st)
    (first,last,b,cap) (at,av,d)
    (abi_decoder_prune_vars st.cs_next_var initial) actual /\
  abi_decoder_vars_extend initial.vs_vars actual restored /\
  abi_decoder_operand_live st.cs_next_var op /\
  eval_operand op initial = SOME w ==>
  eval_operand op restored = SOME w
Proof
  strip_tac >>
  `eval_operand op (abi_decoder_prune_vars st.cs_next_var initial) = SOME w` by
    (drule_all abi_decoder_prune_eval >> simp[]) >>
  `eval_operand op actual = SOME w` by
    (drule abi_encoder_shared_endpoint_scratch >>
     strip_tac >> drule_all abi_scratch_effect_operand >> simp[]) >>
  drule_all abi_decoder_vars_extend_eval >> simp[]
QED
