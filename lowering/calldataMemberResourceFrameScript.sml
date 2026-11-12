(* Conservative resource packaging for source-valued member execution.
   Control location, decoded values and the two safety transfers are separate. *)
Theory calldataMemberResourceFrame
Ancestors
  calldataRecursiveResources calldataDynOwned abiDecoderFrame abiDecoderContract
  abiDecoderReentry calldataFiniteTransport
  compileEnv venomState venomExecSemantics finite_map words list arithmetic

Definition calldata_member_own_def:
  calldata_member_own fn lo hi s <=>
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]
End

Definition calldata_member_wit_def:
  calldata_member_wit lo hi s scratch <=>
    !q k. MEM (q,k) scratch ==> ?id.
      lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k)
End

Definition calldata_member_resource_frame_def:
  calldata_member_resource_frame ctx fn site limit_st lo hi live p len s t scratch <=>
    fresh_vars_wrt limit_st t /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    calldata_member_own fn lo hi t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < lo \/ hi <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live live op ==> eval_operand op t = eval_operand op s) /\
    abi_decode_footprint_frame ((p,len)::scratch) s t /\
    calldata_member_wit lo hi t scratch
End

Theorem calldata_member_resource_identity:
  fresh_vars_wrt limit_st s /\ alloca_inv s /\
  alloca_frontier_inv ctx fn site s /\ calldata_member_own fn lo hi s ==>
  calldata_member_resource_frame ctx fn site limit_st lo hi live p len s s []
Proof
  simp[calldata_member_resource_frame_def, calldata_member_wit_def,
    abi_decode_footprint_frame_refl]
QED

Theorem calldata_member_resource_endpoint:
  calldata_member_resource_frame ctx fn site limit_st lo hi live p len s t scratch ==>
  fresh_vars_wrt limit_st t /\ alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
  calldata_member_own fn lo hi t /\ calldata_member_wit lo hi t scratch /\
  abi_decode_footprint_frame ((p,len)::scratch) s t
Proof
  rewrite_tac[calldata_member_resource_frame_def] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem calldata_member_resource_observations:
  calldata_member_resource_frame ctx fn site limit_st lo hi live p len s t scratch ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!id q k. FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    FLOOKUP t.vs_allocas id = SOME (q,k)) /\
  (!id. id < lo \/ hi <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (!op. abi_decoder_operand_live live op ==> eval_operand op t = eval_operand op s)
Proof
  rewrite_tac[calldata_member_resource_frame_def] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem calldata_member_own_nested:
  calldata_member_own fn L H s /\ L <= l /\ h <= H ==>
  calldata_member_own fn l h s
Proof
  mp_tac calldata_scratch_own_restrict >>
  pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  rewrite_tac[GSYM calldata_member_own_def] >> simp[]
QED

Theorem calldata_member_wit_accumulate[local]:
  L <= l /\ h <= H /\
  calldata_member_wit L H u old /\ calldata_member_wit l h t new /\
  (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
    FLOOKUP t.vs_allocas id = SOME (q,k)) ==>
  calldata_member_wit L H t (old ++ new)
Proof
  simp_tac bool_ss [calldata_member_wit_def] >> strip_tac >>
  rpt gen_tac >> rewrite_tac[MEM_APPEND] >> strip_tac
  >- (first_x_assum drule >> strip_tac >> qexists_tac `id` >> simp[]) >>
  first_x_assum drule >> strip_tac >> qexists_tac `id` >> simp[]
QED

Theorem calldata_member_own_extend[local]:
  L <= l /\ l <= h /\ h <= H /\
  calldata_member_own fn L H s /\ calldata_member_own fn l h t /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!id. id < l \/ h <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) ==>
  calldata_member_own fn L H t
Proof
  mp_tac calldata_scratch_own_reassemble >>
  pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  rewrite_tac[GSYM calldata_member_own_def] >> simp[]
QED

Theorem calldata_member_resource_extend:
  calldata_member_resource_frame ctx fn site limit_st L H live p len s u old /\
  calldata_member_resource_frame ctx fn site limit_st l h next q sz u t new /\
  L <= l /\ l <= h /\ h <= H /\ live <= next /\ p <= q /\ q+sz <= p+len ==>
  calldata_member_resource_frame ctx fn site limit_st L H live p len s t (old ++ new)
Proof
  rewrite_tac[calldata_member_resource_frame_def] >> strip_tac >>
  `calldata_member_own fn L H t` by
    (drule_all calldata_member_own_extend >> disch_then ACCEPT_TAC) >>
  `!id. id < L \/ H <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id` by
    (rpt strip_tac >> `id < l \/ h <= id` by decide_tac >>
     asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame ((p,len)::(old ++ new)) s t` by
    (drule_all calldata_footprint_accumulate >> disch_then ACCEPT_TAC) >>
  `calldata_member_wit L H t (old ++ new)` by
    (drule_all calldata_member_wit_accumulate >> disch_then ACCEPT_TAC) >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- decide_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[abi_decoder_operand_live_mono]
QED

(* Navigation does not allocate or write memory.  This boundary attaches the
   invariant fields to its actual endpoint without selecting another state. *)
Theorem calldata_member_resource_unchanged:
  fresh_vars_wrt limit_st t /\ alloca_inv s /\
  alloca_frontier_inv ctx fn site s /\ calldata_member_own fn lo hi s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section /\
  (!op. abi_decoder_operand_live live op ==> eval_operand op t = eval_operand op s) ==>
  calldata_member_resource_frame ctx fn site limit_st lo hi live p len s t []
Proof
  strip_tac >>
  `alloca_inv t` by (irule calldata_alloca_inv_fields >> simp[] >> metis_tac[]) >>
  `alloca_frontier_inv ctx fn site t` by
    (irule calldata_alloca_frontier_inv_fields >> simp[] >> metis_tac[]) >>
  `calldata_member_own fn lo hi t` by
    (rewrite_tac[calldata_member_own_def] >> asm_rewrite_tac[] >>
     asm_rewrite_tac[GSYM calldata_member_own_def]) >>
  simp[calldata_member_resource_frame_def, calldata_member_wit_def,
    abi_decode_footprint_frame_def] >> asm_rewrite_tac[]
QED
