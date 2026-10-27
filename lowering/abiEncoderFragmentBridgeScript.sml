(* Public-frame boundary.  Exact write confinement is an explicit input;
   the reserved scratch frontier does not imply that input. *)
Theory abiEncoderFragmentBridge
Ancestors
  abiEncoderProps abiEncoderVarTransport abiEncoderObserver venomMemDefs venomState
  abiDecoderVarExtend execEquivParamDefs

Theorem enc_frame_assemble:
  (!x w. not_fresh_at st x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w) /\
  (!a. EVERY (\(b,n). a < b \/ b + n <= a) outs /\
       (!i b sz. i IN frag_ids st st' /\
                 FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
                 a < b \/ b + sz <= a) ==>
       mem_bytes_at a 1 s.vs_memory = mem_bytes_at a 1 s0.vs_memory) /\
  (!i. i NOTIN frag_ids st st' ==>
       FLOOKUP s.vs_allocas i = FLOOKUP s0.vs_allocas i) /\
  (!i r. FLOOKUP s0.vs_allocas i = SOME r ==>
         FLOOKUP s.vs_allocas i = SOME r) /\
  enc_scratch (frag_ids st st') lo top s /\
  s.vs_accounts = s0.vs_accounts /\ s.vs_transient = s0.vs_transient /\
  s.vs_logs = s0.vs_logs /\ s.vs_requests = s0.vs_requests ==>
  enc_frame st st' lo top outs s0 s
Proof
  rewrite_tac[enc_frame_def] >> strip_tac >> asm_rewrite_tac[]
QED

(* Frame clauses observe neither haltedness nor return data. *)
Theorem enc_scratch_stop_view:
  stop_view s = stop_view t ==>
  (enc_scratch ids lo top s <=> enc_scratch ids lo top t)
Proof
  strip_tac >> drule stop_view_fields >> strip_tac >>
  simp[enc_scratch_def, alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def]
QED

Theorem enc_frame_stop_view:
  stop_view s = stop_view t ==>
  (enc_frame st st' lo top outs s0 s <=>
   enc_frame st st' lo top outs s0 t)
Proof
  strip_tac >> drule enc_scratch_stop_view >> strip_tac >>
  drule stop_view_fields >> strip_tac >>
  simp[enc_frame_def, lookup_var_def]
QED

(* Extension changes only the variable map, and preserves every binding that
   was already defined at the observed endpoint. *)
Theorem enc_scratch_vars_extend:
  abi_decoder_vars_extend extras s t ==>
  (enc_scratch ids lo top s <=> enc_scratch ids lo top t)
Proof
  rw[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"] >>
  qpat_x_assum `vsr_frame s = vsr_frame t` mp_tac >>
  simp[vsr_frame_def, venom_state_component_equality] >> strip_tac >>
  simp[enc_scratch_def, alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def]
QED

