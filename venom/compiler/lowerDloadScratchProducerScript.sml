Theory lowerDloadScratchProducer
Ancestors
  lowerDloadAllocaProducer lowerDloadLiveScratch lowerDloadAllocation
  lowerDloadFrameCertificate lowerDloadOwnership lowerDloadLifetime
  venomExecSemantics venomState venomInst ptrDiscipline finite_map words pred_set

(* Allocation changes no old entry except the selected key, whether reused
   or fresh. This boundary is independent of ownership and scratch size. *)
Theorem ld_exec_alloca_other_entries:
  exec_alloca a t (n:bytes32) = OK z ==>
  !j. j <> a.inst_id ==> FLOOKUP z.vs_allocas j = FLOOKUP t.vs_allocas j
Proof
  strip_tac >> qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  strip_tac >> gvs[FLOOKUP_UPDATE] >> rpt strip_tac >> simp[]
QED

Theorem ld_scratch_frame_embedding:
  ld_frame_embedding E L H s t /\ ld_alloc_account keys d A s t /\
  a.inst_id IN keys /\ exec_alloca a t (n:bytes32) = OK z ==>
  ld_frame_embedding E L H s z
Proof
  strip_tac >>
  `a.inst_id NOTIN FDOM H` by
    (drule ld_frame_embedding_domains >>
     drule ld_alloc_account_disjoint >>
     simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  qpat_x_assum `ld_frame_embedding _ _ _ _ _` mp_tac >>
  simp[ld_frame_embedding_def] >> strip_tac >> simp[] >>
  rpt strip_tac >>
  `id <> a.inst_id` by metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  drule ld_exec_alloca_other_entries >> disch_then (qspec_then `id` mp_tac) >>
  simp[]
QED

Theorem ld_scratch_alloca_result[local]:
  a.inst_outputs = [av] /\ exec_alloca a t (32w:bytes32) = OK z /\
  ((FLOOKUP t.vs_allocas a.inst_id = NONE /\ p = t.vs_alloca_next) \/
   FLOOKUP t.vs_allocas a.inst_id = SOME(p,32)) ==>
  FLOOKUP z.vs_allocas a.inst_id = SOME(p,32) /\
  lookup_var av z = SOME(n2w p)
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  strip_tac >> qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, update_var_def, wordsTheory.dimword_def] >> strip_tac >>
  gvs[FLOOKUP_UPDATE, lookup_var_def] >> EVAL_TAC
QED

Theorem ld_scratch_certificate_structure:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\ a.inst_id IN keys /\
  step_inst fuel CT a t = OK t1 /\
  ld_alloc_account keys d A s t /\ ld_frame_embedding E L H s t /\
  lo <= f /\ allocas_non_overlapping t /\ alloca_next_valid t /\
  allocas_from f t /\ f <= t.vs_alloca_next /\
  t.vs_alloca_next < dimword (:256) /\
  (a.inst_id NOTIN A ==> t.vs_alloca_next + 32 < dimword (:256)) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\
    bt+sz <= t.vs_alloca_next) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz)) ==>
  ?p. f <= p /\ p+32 < dimword (:256) /\
    FLOOKUP t1.vs_allocas a.inst_id = SOME(p,32) /\
    lookup_var av t1 = SOME(n2w p) /\
    ((FLOOKUP t.vs_allocas a.inst_id = NONE /\ p = t.vs_alloca_next) \/
      FLOOKUP t.vs_allocas a.inst_id = SOME(p,32)) /\
    (!aa bb. ((aa=bb /\ aa<lo) \/ ld_site_bytes E live aa bb) ==>
      bb < p \/ p+32 <= bb) /\
    ld_alloc_account keys d (a.inst_id INSERT A) s t1 /\
    ld_frame_embedding E L H s t1 /\
    t.vs_alloca_next <= t1.vs_alloca_next /\
    ld_frame_bound t1.vs_alloca_next H BP BH /\
    ld_stack_bound t1.vs_alloca_next gstk /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\
      bt+sz <= t1.vs_alloca_next) /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t1.vs_allocas j = SOME(bt,sz)) /\
    (t1 with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
               vs_alloca_next := t.vs_alloca_next|>) = t
Proof
  strip_tac >>
  drule_all ld_alloca_step_effects >> strip_tac >>
  `n = 32w` by fs[eval_operand_def] >> gvs[] >>
  drule_all ld_live_scratch_separation_floor >>
  disch_then (qx_choose_then `p` (map_every assume_tac o CONJUNCTS)) >>
  drule_all ld_scratch_alloca_result >> strip_tac >>
  drule_all ld_alloc_account_scratch >> strip_tac >>
  drule_all ld_scratch_frame_embedding >> strip_tac >>
  qexists `p` >> asm_rewrite_tac[] >> rpt conj_tac
  >- (irule ld_frame_bound_mono >> goal_assum (drule_at Any) >> simp[])
  >- (irule ld_stack_bound_mono >> goal_assum (drule_at Any) >> simp[])
  >- suspend "endpoints"
  >> suspend "representation"
QED

Resume ld_scratch_certificate_structure[endpoints]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!owner bs bt sz. _ ==> _ /\ _ /\ _ /\ _`
    (qspecl_then [`owner`,`bs`,`bt`,`sz`] mp_tac) >>
  simp[] >> strip_tac >> simp[]
QED
Resume ld_scratch_certificate_structure[representation]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!owner bs bt sz. _ ==> _ \/ _`
    (qspecl_then [`owner`,`bs`,`bt`,`sz`] mp_tac) >>
  simp[] >> strip_tac >- simp[] >>
  disj2_tac >> qexists `j` >> simp[] >>
  `j <> a.inst_id` by metis_tac[] >>
  drule ld_exec_alloca_other_entries >> disch_then (qspec_then `j` mp_tac) >>
  simp[]
QED
Finalise ld_scratch_certificate_structure

(* Scratch-only structural audit: source s and E,L,H are unchanged; account
   charge uses key insertion and covers reuse as well as fresh allocation.
   No owner is added for scratch. The resulting interval is strictly below
   the word limit and disjoint from every target byte in the masked relation.
   Original embedding, live endpoints and floor-f representation are produced
   for t1, with target bounds moved only by frontier monotonicity. Saved table
   agreement and selection pairing are literally unchanged since E,L,H and
   all saved frames are unchanged. The restoration equation retains parameters
   and other nonallocation state fields. No intermediate memory/taint relation
   is claimed: the full DLOAD producer must still combine CODECOPY and MLOAD,
   prove original-output owned values/definedness and provenance, and establish
   the final masked byte/taint relation and source/target output agreement.
*)
