(* Precise scratch footprints across allocator growth.
   TOP-LEVEL: abi_scratch_evolution_alloca, abi_scratch_disjoint_advance and
   abi_scratch_frame_advance connect actual allocation to frame composition.
   Existing slots keep their locations; new slots occupy the old frontier tail. *)
Theory abiScratchFootprint
Ancestors
  abiDecoderFootprint abiDecoderFrame abiDecoderAllocation abiDecoderContract
  venomExecSemantics venomState finite_map pred_set list arithmetic words

Definition abi_scratch_evolution_def:
  abi_scratch_evolution ids b cap s t <=>
    s.vs_alloca_next <= t.vs_alloca_next /\ t.vs_alloca_next <= b + cap /\
    (!id slot. id IN ids /\ FLOOKUP s.vs_allocas id = SOME slot ==>
      FLOOKUP t.vs_allocas id = SOME slot) /\
    (!id p n. id IN ids /\ FLOOKUP s.vs_allocas id = NONE /\
      FLOOKUP t.vs_allocas id = SOME (p,n) ==>
      s.vs_alloca_next <= p /\ p + n <= t.vs_alloca_next)
End

Theorem abi_scratch_evolution_refl:
  s.vs_alloca_next <= b + cap ==> abi_scratch_evolution ids b cap s s
Proof
  simp[abi_scratch_evolution_def] >> rpt strip_tac >> gvs[]
QED

Theorem abi_scratch_evolution_transport:
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
  t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next ==>
  (abi_scratch_evolution ids b cap s' t' <=> abi_scratch_evolution ids b cap s t)
Proof
  simp[abi_scratch_evolution_def]
QED

Theorem abi_scratch_evolution_subset:
  abi_scratch_evolution ids b cap s t /\ child_ids SUBSET ids ==>
  abi_scratch_evolution child_ids b cap s t
Proof
  rw[abi_scratch_evolution_def] >> metis_tac[SUBSET_DEF]
QED

Theorem abi_scratch_evolution_trans:
  abi_scratch_evolution ids b cap s t /\
  abi_scratch_evolution ids b cap t u ==>
  abi_scratch_evolution ids b cap s u
Proof
  simp_tac bool_ss [abi_scratch_evolution_def] >> strip_tac >>
  conj_tac >- decide_tac >>
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP u.vs_allocas id = SOME (p,n)` >>
  Cases_on `FLOOKUP t.vs_allocas id`
  >- (qpat_x_assum `!id p n. _ ==> t.vs_alloca_next <= p /\ _`
        drule_all >> strip_tac >> decide_tac) >>
  rename1 `FLOOKUP t.vs_allocas id = SOME slot` >>
  `SOME slot = SOME (p,n)` by metis_tac[] >> gvs[] >>
  qpat_x_assum `!id p n. _ ==> s.vs_alloca_next <= p /\ _`
    drule_all >> strip_tac >> decide_tac
QED

Theorem abi_scratch_evolution_alloca:
  exec_alloca inst s asz = OK t /\ t.vs_alloca_next <= b + cap ==>
  abi_scratch_evolution ids b cap s t
Proof
  Cases_on `inst.inst_outputs` >- simp[exec_alloca_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >>
  simp[exec_alloca_def, LET_THM] >>
  TRY (rename1 `SOME slot` >> PairCases_on `slot`) >>
  rw[abi_scratch_evolution_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[] >> rw[FLOOKUP_UPDATE] >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
  FIRST [decide_tac, metis_tac[]]
QED

Theorem abi_scratch_registered_member:
  FINITE ids /\ id IN ids /\ FLOOKUP s.vs_allocas id = SOME (p,n) ==>
  MEM (p,n) (abi_decoder_child_scratch ids b cap s)
Proof
  strip_tac >> simp[abi_decoder_child_scratch_def, MEM_MAP] >>
  disj2_tac >> qexists_tac `id` >> simp[MEM_SET_TO_LIST]
QED

Theorem abi_scratch_frontier_disjoint:
  s.vs_alloca_next <= b + cap /\
  abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap s) ==>
  p + n <= s.vs_alloca_next \/ b + cap <= p
Proof
  simp_tac bool_ss [abi_footprint_disjoint_def] >> strip_tac >>
  qpat_x_assum `!d sz. _` (qspecl_then
    [`s.vs_alloca_next`, `b + cap - s.vs_alloca_next`] mp_tac) >>
  simp[abi_decoder_child_scratch_def] >> decide_tac
QED

Theorem abi_scratch_slot_origin:
  abi_scratch_evolution ids b cap s t /\ id IN ids /\
  FLOOKUP t.vs_allocas id = SOME (q,sz) ==>
  FLOOKUP s.vs_allocas id = SOME (q,sz) \/
  (s.vs_alloca_next <= q /\ q + sz <= t.vs_alloca_next)
Proof
  strip_tac >>
  qpat_x_assum `abi_scratch_evolution _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_scratch_evolution_def]) >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (disj2_tac >> qpat_x_assum `!id p n. _` drule_all >> simp[]) >>
  disj1_tac >> qpat_x_assum `!id slot. _` drule_all >> simp[]
QED

Theorem abi_scratch_slot_disjoint:
  abi_scratch_evolution ids b cap s t /\ FINITE ids /\
  abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap s) /\
  (p + n <= s.vs_alloca_next \/ b + cap <= p) /\
  t.vs_alloca_next <= b + cap /\ id IN ids /\
  FLOOKUP t.vs_allocas id = SOME (q,sz) ==>
  p + n <= q \/ q + sz <= p
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_slot_origin >> strip_tac
  >- (`MEM (q,sz) (abi_decoder_child_scratch ids b cap s)` by
        (irule abi_scratch_registered_member >> asm_simp_tac bool_ss [] >>
         qexists_tac `id` >> simp[]) >>
      qpat_x_assum `abi_footprint_disjoint _ _ _`
        (qspecl_then [`q`, `sz`] mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >> simp[]) >>
  decide_tac
QED

Theorem abi_scratch_disjoint_advance:
  abi_scratch_evolution ids b cap s t /\ FINITE ids /\
  abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap s) ==>
  abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap t)
Proof
  strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next /\ t.vs_alloca_next <= b + cap` by
    fs[abi_scratch_evolution_def] >>
  `s.vs_alloca_next <= b + cap` by decide_tac >>
  drule_all abi_scratch_frontier_disjoint >> disch_then assume_tac >>
  `!id q sz. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (q,sz) ==>
    p + n <= q \/ q + sz <= p` by
    (rpt gen_tac >> strip_tac >> drule_all abi_scratch_slot_disjoint >> simp[]) >>
  MATCH_MP_TAC abi_decoder_child_scratch_disjoint >> asm_simp_tac bool_ss [] >>
  conj_tac >- decide_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_scratch_disjoint_cons:
  abi_footprint_disjoint p n ((d,sz)::fp) <=>
  (p + n <= d \/ d + sz <= p) /\ abi_footprint_disjoint p n fp
Proof
  simp[abi_footprint_disjoint_def] >> metis_tac[]
QED

Theorem abi_scratch_frame_advance:
  abi_scratch_evolution ids b cap s t /\ FINITE ids /\
  abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch ids b cap t) t u ==>
  abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch ids b cap s) t u
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_footprint_frame_def] >> strip_tac >>
  asm_simp_tac (srw_ss()) [] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!p n. _` irule >>
  qpat_x_assum `abi_footprint_disjoint _ _ (_::_)`
    (strip_assume_tac o REWRITE_RULE [abi_scratch_disjoint_cons]) >>
  simp_tac bool_ss [abi_scratch_disjoint_cons] >> asm_rewrite_tac[] >>
  drule_all abi_scratch_disjoint_advance >> simp[]
QED

Theorem abi_scratch_allocation:
  abi_decoder_budget first last b cap s /\ FINITE ids /\
  ids SUBSET abi_decoder_ids first last /\ inst.inst_id IN ids /\
  inst.inst_outputs = [out] ==>
  ?t p loff len. exec_alloca inst s (32w:bytes32) = OK t /\
    abi_decoder_budget first last b cap t /\
    lookup_var out t = SOME (n2w p) /\ abi_scratch_evolution ids b cap s t /\
    MEM (loff,len) (abi_decoder_child_scratch ids b cap s) /\
    loff <= p /\ p + 32 <= loff + len /\
    abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap s) s t
Proof
  strip_tac >> drule_all abi_decoder_child_allocation >> strip_tac >>
  rename1 `lookup_var out t = SOME (n2w p)` >>
  rename1 `MEM (loff,len) (abi_decoder_child_scratch ids b cap s)` >>
  `t.vs_alloca_next <= b + cap` by
    (qpat_x_assum `abi_decoder_budget first last b cap t` mp_tac >>
     simp[abi_decoder_budget_def] >> decide_tac) >>
  `abi_scratch_evolution ids b cap s t` by
    (drule_all (Q.INST [`ids` |-> `ids`] abi_scratch_evolution_alloca) >> simp[]) >>
  `abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap s) s t` by
    (mp_tac (Q.INST [`id` |-> `SUC inst.inst_id`] abi_decoder_alloca_other_sites) >>
     impl_tac >- simp[] >> simp[abi_decode_footprint_frame_def]) >>
  qexistsl_tac [`t`, `p`, `loff`, `len`] >> simp[]
QED

Theorem abi_scratch_final_slot_frame:
  abi_scratch_evolution ids b cap s t /\ FINITE ids /\ site IN ids /\
  FLOOKUP t.vs_allocas site = SOME (slot,sz) /\ abi_decode_frame slot sz s t ==>
  abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap s) s t
Proof
  strip_tac >>
  `MEM (slot,sz) (abi_decoder_child_scratch ids b cap t)` by
    (irule abi_scratch_registered_member >> asm_simp_tac bool_ss [] >>
     qexists_tac `site` >> simp[]) >>
  simp_tac bool_ss [abi_decode_footprint_frame_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all abi_scratch_disjoint_advance >> strip_tac >>
      fs[abi_decode_frame_def, abi_footprint_disjoint_def] >> metis_tac[]) >>
  fs[abi_decode_frame_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_FOOTPRINT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch footprint not kernel closed: " ^ n)
  end) (DB.thms "abiScratchFootprint");
