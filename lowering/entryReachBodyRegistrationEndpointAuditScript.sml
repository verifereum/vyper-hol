(* A previous argument's three witnesses survive at the same decoder endpoint. *)
Theory entryReachBodyRegistrationEndpointAudit
Ancestors
  valueEncodingDefs entryReachBodyRegistrationPrefixValues entryReachBodyRegistrationPrefixSupport
  entryReachBodyRegistrationCanonical
  entryReachBodyDecoderWindowCertificate abiDecoderReentry
  compileEnv finite_map words arithmetic

Theorem registration_next_slot_previous_witness:
  array_child_result ctx fn k root extent ambient
    (window_alloca_sites fn (abi_decoder_ids first.cs_next_id last.cs_next_id))
    b cap site limit first last cell tv value ready t /\
  old_id < k /\ k < first.cs_next_id /\
  st.cs_next_var <= first.cs_next_var /\
  FLOOKUP initial.vs_allocas old_id = SOME (p,type_memory_size old_tv) /\
  (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
    FLOOKUP ready.vs_allocas id = SOME entry) /\
  ready.vs_memory = initial.vs_memory /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op ready = eval_operand op initial) /\
  abi_decoder_operand_live st.cs_next_var dst /\
  eval_operand dst initial = SOME (n2w p) /\
  val_in_memory old_tv old_value p initial.vs_memory /\ val_wf old_tv old_value ==>
  FLOOKUP t.vs_allocas old_id = SOME (p,type_memory_size old_tv) /\
  eval_operand dst t = SOME (n2w p) /\
  val_in_memory old_tv old_value p t.vs_memory
Proof
  strip_tac >> conj_tac
  >- (drule_all registration_prefix_allocation >> simp[]) >>
  conj_tac
  >- (drule_all registration_prefix_operand >> simp[]) >>
  irule registration_prefix_value >>
  qpat_assum `array_child_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`p`, `old_id`, `type_memory_size old_tv`, `initial`] >> simp[]
QED
