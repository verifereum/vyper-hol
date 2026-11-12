(* Actual scratch ownership algebra, independent of decoder execution. *)
Theory calldataRecursiveResources
Ancestors
  venomState venomExecSemantics venomInst finite_map words list arithmetic

Theorem calldata_scratch_own_restrict:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]
  in Own L H s /\ L <= l /\ h <= H ==> Own l h s
Proof
  simp_tac pure_ss [LET_THM] >> CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  rpt gen_tac >> strip_tac >>
  map_every qx_gen_tac [`id`, `q`, `k`] >> strip_tac >>
  `L <= id /\ id < H` by decide_tac >> metis_tac[]
QED

Theorem calldata_scratch_own_reassemble:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]
  in L <= l /\ l <= h /\ h <= H /\ Own L H s /\ Own l h t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!id. id < l \/ h <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) ==>
    Own L H t
Proof
  simp_tac pure_ss [LET_THM] >> CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  rpt gen_tac >> strip_tac >>
  map_every qx_gen_tac [`id`, `q`, `k`] >> strip_tac >>
  Cases_on `l <= id /\ id < h`
  >- (first_x_assum (qspec_then `id` mp_tac) >> metis_tac[]) >>
  `FLOOKUP s.vs_allocas id = SOME (q,k)` by
    (`id < l \/ h <= id` by decide_tac >> metis_tac[]) >>
  qpat_x_assum `!id q k. L <= id /\ _ ==> _`
    (qspecl_then [`id`, `q`, `k`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[] >>
  conj_tac >- decide_tac >> metis_tac[]
QED

Theorem calldata_outside_alloca_lookup:
  (!id. id < l \/ h <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (iid < l \/ h <= iid) /\ FLOOKUP s.vs_allocas iid = SOME (p,32) ==>
  FLOOKUP t.vs_allocas iid = SOME (p,32)
Proof
  metis_tac[]
QED

Theorem calldata_outside_allocas_nested:
  L <= l /\ h <= H /\
  (!id. id < L \/ H <= id ==> FLOOKUP mid.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (!id. id < l \/ h <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP mid.vs_allocas id) ==>
  !id. id < L \/ H <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id
Proof
  rpt strip_tac >> `id < l \/ h <= id` by decide_tac >> metis_tac[]
QED

Theorem calldata_outside_allocas_sequential:
  L <= m /\ m <= H /\
  (!id. id < L \/ m <= id ==> FLOOKUP mid.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (!id. id < m \/ H <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP mid.vs_allocas id) ==>
  !id. id < L \/ H <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id
Proof
  rpt strip_tac >> `id < L \/ m <= id` by decide_tac >>
  `id < m \/ H <= id` by decide_tac >> metis_tac[]
QED
