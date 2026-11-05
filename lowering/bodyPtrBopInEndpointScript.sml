(* Endpoint-only allocation separation; no initial allocation history assumed. *)
Theory bodyPtrBopInEndpoint
Ancestors abiCallerAllocation venomExecSemantics exprLoweringProps words

Theorem endpoint_allocation_words_distinct:
  alloca_inv t /\ t.vs_alloca_next < dimword (:256) /\
  FLOOKUP t.vs_allocas a = SOME (p,n) /\
  FLOOKUP t.vs_allocas b = SOME (q,m) /\
  a <> b /\ 0 < n /\ 0 < m ==>
  (n2w p : bytes32) <> n2w q
Proof
  strip_tac >>
  `p + n <= t.vs_alloca_next` by
    (gvs[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. _` (qspecl_then [`a`,`p`,`n`] mp_tac) >> simp[]) >>
  `q + m <= t.vs_alloca_next` by
    (gvs[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. _` drule >> simp[]) >>
  drule_all abi_caller_allocation_separate >> strip_tac >>
  `p < dimword (:256) /\ q < dimword (:256) /\ p <> q` by decide_tac >>
  simp[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]
QED

Theorem exec_alloca_recorded_output:
  inst.inst_outputs = [x] /\ exec_alloca inst s szw = OK t ==>
  ?p n. FLOOKUP t.vs_allocas inst.inst_id = SOME (p,n) /\
        lookup_var x t = SOME (n2w p)
Proof
  strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- gvs[exec_alloca_def, venomStateTheory.update_var_def,
         venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
  PairCases_on `entry` >>
  gvs[exec_alloca_def, venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

