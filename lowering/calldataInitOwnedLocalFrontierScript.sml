Theory calldataInitOwnedLocalFrontier
Ancestors
  calldataInitLocalFrontier calldataInitEntry calldataDynOwned abiDecoderFrame
  abiDecoderIndexInit allocaFrontierBound venomState venomMemDefs exprLoweringProps

Theorem calldata_index_init_executed_ownership_local_frontier:
  let Own = \s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]
  in
  abi_decode_index_init header_st = (ip,loop_st) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
      p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (!id. id <> header_st.cs_next_id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
  FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32) /\
  (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
     t.vs_alloca_next = initial.vs_alloca_next+32
   else t.vs_alloca_next = initial.vs_alloca_next) /\
  lo <= header_st.cs_next_id /\ header_st.cs_next_id < hi /\ Own initial ==>
  alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
  initial.vs_alloca_next <= t.vs_alloca_next /\
  (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    FLOOKUP t.vs_allocas id = SOME (q,k)) /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\ Own t
Proof
  qmatch_goalsub_abbrev_tac `LET _ Own` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_index_init_local_frontier_fields >> strip_tac >>
  `p < dimword (:256) /\ p+32 <= t.vs_alloca_next` by
    (qpat_assum `FLOOKUP t.vs_allocas _ = SOME (p,32)` mp_tac >>
     qpat_assum `alloca_inv t` mp_tac >>
     qpat_assum `alloca_frontier_inv ctx fn site t` mp_tac >>
     qpat_assum `unit_alloca_budget ctx < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def, alloca_frontier_inv_def] >>
     rpt strip_tac >>
     `p+32 <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  `!id. id < lo \/ hi <= id ==>
     FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  asm_rewrite_tac[] >>
  drule_all calldata_index_init_literal_site >> strip_tac >>
  qpat_x_assum `Own initial` mp_tac >>
  simp_tac pure_ss [Abbr `Own`] >> BETA_TAC >> disch_tac >>
  ho_match_mp_tac (GEN_ALL (SIMP_RULE (pure_ss ++ boolSimps.BOOL_ss)
    [LET_THM] calldata_owned_counter_update)) >>
  qexistsl_tac [`initial`,`p`,`ins`,`header_st.cs_next_id`] >>
  asm_rewrite_tac[]
QED
