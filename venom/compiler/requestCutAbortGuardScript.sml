Theory requestCutAbortGuard
Ancestors
  dftGasInvMemoryRanges dftGasInvCrossingProbe
  o1PassContract unitMemInv contextCodegenRel
  opcodeClass venomExecSemantics venomInst venomState words list pair

Theorem request_cut_paired_memory_guard:
  inst_shape_ok inst /\ inst.inst_opcode <> DRET /\ ~in_revert_forward fn9 t /\
  (!r. MEM r cpl.cp_regions ==> eom <= r.sr_spill_base /\
    r.sr_spill_end <= w2n t.vs_initial_fmp) /\
  mem_inv (\ctx fn i s. LENGTH s.vs_requests <= k ==> lowered_mem_fact eom ctx fn i s) C7 v7 /\
  (inv_memory_observation inst.inst_opcode ==>
    ?fn u. raw_reachable v7 C7 fn inst u /\ LENGTH u.vs_requests <= k /\
      ~in_revert_forward fn u /\ u.vs_initial_fmp = t.vs_initial_fmp /\
      (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op t)) ==>
  source_memory_reads_disjoint cpl inst t /\
  context_source_memory_writes_disjoint cpl inst t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\(off,len). len = 0 \/ off + len <= eom \/
      w2n t.vs_initial_fmp <= off) (inst_mem_ranges inst t)` by
    (Cases_on `inv_memory_observation inst.inst_opcode`
     >- (qpat_x_assum `inv_memory_observation _ ==> _` drule >> strip_tac >>
         `inst_mem_ranges inst u = inst_mem_ranges inst t` by
           metis_tac[inv_non_dret_ranges_cong] >>
         qpat_x_assum `mem_inv _ _ _`
           (strip_assume_tac o REWRITE_RULE [mem_inv_raw_reachable]) >>
         `lowered_mem_fact eom C7 fn inst u` by
           (qpat_assum `!f i s. raw_reachable _ _ f i s ==> _`
              (mp_tac o BETA_RULE o Q.SPECL [`fn`, `inst`, `u`]) >> asm_rewrite_tac[]) >>
         qpat_x_assum `lowered_mem_fact _ _ _ _ _`
           (mp_tac o REWRITE_RULE [lowered_mem_fact_def, lowered_mem_ok_def]) >>
         asm_rewrite_tac[]) >>
     `inst_mem_ranges inst t = []` by metis_tac[inv_memory_observation_covers_ranges] >>
     simp[]) >>
  `lowered_mem_ok eom (w2n t.vs_initial_fmp) C7 fn9 inst t` by
    simp[lowered_mem_ok_def] >>
  conj_tac
  >- (drule_all lowered_reads_disjoint >> simp[]) >>
  drule_all lowered_writes_disjoint >> simp[]
QED
