Theory calldataExactMemberFrame
Ancestors
  calldataDynOwned abiDecoderFrame abiDecoderContract abiDecoderReentry
  valueEncodingDefs words list arithmetic finite_map venomInst

Definition exact_member_owned_frame_def:
  exact_member_owned_frame ctx fn site lo hi live d sz s t sc <=>
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < lo \/ hi <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live live op ==>
      eval_operand op t = eval_operand op s) /\
    abi_decode_footprint_frame ((d,sz)::sc) s t /\
    (!q k. MEM (q,k) sc ==> ?id. lo <= id /\ id < hi /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
End

Theorem exact_member_owned_frame_init:
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  (!id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) ==>
  exact_member_owned_frame ctx fn site lo hi live d sz s s []
Proof
  strip_tac >> pure_rewrite_tac [exact_member_owned_frame_def] >>
  asm_rewrite_tac [abi_decode_footprint_frame_refl, MEM, LESS_EQ_REFL]
QED

Theorem exact_member_owned_frame_transport:
  exact_member_owned_frame ctx fn site lo hi live d sz s u sc /\
  v.vs_memory = u.vs_memory /\ v.vs_call_ctx = u.vs_call_ctx /\
  v.vs_data_section = u.vs_data_section /\ v.vs_allocas = u.vs_allocas /\
  v.vs_alloca_next = u.vs_alloca_next /\
  (!op. abi_decoder_operand_live live op ==> eval_operand op v = eval_operand op u) /\
  alloca_inv v /\ alloca_frontier_inv ctx fn site v ==>
  exact_member_owned_frame ctx fn site lo hi live d sz s v sc
Proof
  pure_rewrite_tac [exact_member_owned_frame_def, abi_decode_footprint_frame_def] >>
  rpt strip_tac >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem exact_member_owned_frame_compose:
  exact_member_owned_frame ctx fn site lo hi live d sz s u sc /\
  exact_member_owned_frame ctx fn site a b live' e len u v more /\
  lo <= a /\ a <= b /\ b <= hi /\ live <= live' /\
  d <= e /\ e+len <= d+sz ==>
  exact_member_owned_frame ctx fn site lo hi live d sz s v (sc ++ more)
Proof
  pure_rewrite_tac [exact_member_owned_frame_def] >> strip_tac >>
  `abi_decode_footprint_frame ((d,sz)::(sc ++ more)) s v` by
    (irule calldata_footprint_accumulate >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  `!id q k. lo <= id /\ id < hi /\ FLOOKUP v.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` by
    (mp_tac (Q.INST [`s` |-> `u`, `t` |-> `v`]
       (SPEC_ALL (PURE_REWRITE_RULE [LET_THM] calldata_owned_interval_replace))) >>
     (impl_tac >- asm_rewrite_tac[]) >> disch_then ACCEPT_TAC) >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- decide_tac
  >- metis_tac[]
  >- (rpt strip_tac >> `id < a \/ b <= id` by decide_tac >> metis_tac[])
  >- (rpt strip_tac >> drule_all abi_decoder_operand_live_mono >> metis_tac[]) >>
  simp_tac bool_ss [MEM_APPEND] >> rpt strip_tac >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED
