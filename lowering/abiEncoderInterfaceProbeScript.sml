(* Bounded probes for the execution/effect and variable-restoration interface.
   These do not claim a general producer of local executions. *)
Theory abiEncoderInterfaceProbe
Ancestors
  abiEncoderLeafSafety abiEncoderVarTransport abiEncoderExactWriteProbe
  valueEncodingProps execEquivParamDefs abiDecoderVarExtend
  venomExecSemantics venomState venomInst finite_map pred_set words

Theorem encoder_alloca_store_probe:
  FLOOKUP s.vs_allocas id = NONE /\ id IN ids /\
  exec_alloca (mk_inst id ALLOCA [Lit 32w] [tmp]) s (32w:bytes32) = OK allocated ==>
  encoder_exact_writes ids d n s
    (mstore s.vs_alloca_next w allocated) /\
  (mstore s.vs_alloca_next w allocated).vs_accounts = s.vs_accounts /\
  (mstore s.vs_alloca_next w allocated).vs_transient = s.vs_transient /\
  (mstore s.vs_alloca_next w allocated).vs_logs = s.vs_logs /\
  (mstore s.vs_alloca_next w allocated).vs_requests = s.vs_requests
Proof
  simp[exec_alloca_def, mk_inst_def, dimword_def] >> strip_tac >> gvs[] >>
  `!p w t. t.vs_memory = s.vs_memory ==>
     (mstore p w t).vs_memory = (mstore p w s).vs_memory` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  conj_tac
  >- (rw[encoder_exact_writes_def] >>
      `a < s.vs_alloca_next \/ s.vs_alloca_next+32 <= a` by
        (first_x_assum irule >> qexists_tac `id` >>
         simp[update_var_def, FLOOKUP_UPDATE]) >>
      simp[update_var_def] >>
      irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[mstore_def, write_memory_with_expansion_def, update_var_def]
QED

(* A supplied successful word-copy prefix transports as the SAME execution,
   with unchanged non-variable fields, not a second existential endpoint. *)
Theorem encoder_word_prefix_restore_probe:
  local_prefix ctx fn cut s t /\ abi_decoder_vars_extend extras s restored ==>
  ?final. local_prefix ctx fn cut restored final /\
    abi_decoder_vars_extend extras t final /\
    t.vs_memory = final.vs_memory /\
    t.vs_accounts = final.vs_accounts /\
    t.vs_transient = final.vs_transient /\
    t.vs_logs = final.vs_logs /\ t.vs_requests = final.vs_requests
Proof
  strip_tac >> drule_all abi_encoder_local_prefix_extend >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `abi_decoder_vars_extend extras t _` mp_tac >>
  simp[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"] >>
  simp[execEquivParamDefsTheory.vsr_frame_def,
       venom_state_component_equality] >> metis_tac[]
QED
