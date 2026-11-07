(* Scratch selection from actual allocations, including repeated loop visits. *)
Theory actualScratchSelection
Ancestors
  venomMemDefs venomInst finite_map words list arithmetic

Theorem actual_owned_scratch_selection:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]
  in
  alloca_inv s /\ Own lo hi s /\ lo <= iid /\ iid < hi /\
  (oid < lo \/ hi <= oid) /\ FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  base_addr <= d /\ d+sz <= base_addr+cap ==>
  ?p. ((FLOOKUP s.vs_allocas iid = NONE /\ p = s.vs_alloca_next) \/
       (FLOOKUP s.vs_allocas iid = SOME (p,32) /\
        p < dimword (:256) /\ p+32 <= s.vs_alloca_next)) /\
      (d+sz <= p \/ p+32 <= d) /\ d+sz <= s.vs_alloca_next
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `base_addr+cap <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `iid <> oid` by decide_tac >>
  Cases_on `FLOOKUP s.vs_allocas iid`
  >- (qexists_tac `s.vs_alloca_next` >> simp_tac std_ss [] >> decide_tac) >>
  PairCases_on `x` >> qexists_tac `x0` >>
  first_x_assum (qspecl_then [`iid`, `x0`, `x1`] mp_tac) >>
  simp[] >> strip_tac >>
  `x0+32 <= base_addr \/ base_addr+cap <= x0` by
    (fs[alloca_inv_def, allocas_non_overlapping_def] >> metis_tac[]) >>
  simp[] >> decide_tac
QED

Theorem actual_allocated_subbuffer_strict_bound:
  alloca_inv s /\ FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  d+sz <= base_addr+cap /\ s.vs_alloca_next < dimword (:256) ==>
  d+sz < dimword (:256)
Proof
  strip_tac >>
  `base_addr+cap <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  decide_tac
QED
