Theory o1MakeSsaFrontierAncestry
Ancestors o1MakeSsaPhiGeneration makeSsaCurrentDefs relation list alist pair

Definition frontier_step_def:
  frontier_step df d q <=> ?fs. ALOOKUP df d = SOME fs /\ MEM q fs
End

Theorem generation_order_ancestry:
  !records roots.
    generation_order roots records /\
    EVERY (\(d,f,id). frontier_step df d f) records ==>
    !initial.
      (!d. MEM d roots ==> ?a. MEM a initial /\ RTC (frontier_step df) a d) ==>
      !d f id. MEM (d,f,id) records ==>
        ?a. MEM a initial /\ TC (frontier_step df) a f
Proof
  Induct >> simp[generation_order_def] >>
  gen_tac >> PairCases_on `h` >> simp[generation_order_def] >>
  rpt strip_tac >>
  `?a. MEM a initial /\ RTC (frontier_step df) a h0` by metis_tac[] >>
  `TC (frontier_step df) a h1` by metis_tac[EXTEND_RTC_TC_RIGHT1] >>
  gvs[] >- metis_tac[] >>
  first_x_assum (qspec_then `h1::roots` mp_tac) >> simp[] >>
  disch_then (qspec_then `initial` mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[TC_RTC]) >> metis_tac[]
QED

Theorem insertion_frontier_ancestry:
  insert_phis_for_var_supply s x df pm li bbs roots hp = (out,t) ==>
  ?records : (string # string # num) list.
    out = MAP (\bb. bb with bb_instructions :=
      generation_prefix x pm bb.bb_label records ++ bb.bb_instructions) bbs /\
    (!d q id. MEM (d,q,id) records ==>
      ?a. MEM a roots /\ TC (frontier_step df) a q)
Proof
  strip_tac >> drule insertion_generation_certificate >> strip_tac >>
  qexists_tac `records` >> simp[] >>
  `EVERY (\(d,f,id). frontier_step df d f) records` by
    (gvs[EVERY_MEM, FORALL_PROD, frontier_step_def] >> metis_tac[]) >>
  `!d. MEM d roots ==> ?a. MEM a roots /\ RTC (frontier_step df) a d` by
    (rpt strip_tac >> qexists_tac `d` >> simp[]) >>
  metis_tac[generation_order_ancestry]
QED

Theorem insertion_frontier_preserves:
  insert_phis_for_var_supply s x df pm li bbs roots hp = (out,t) /\
  EVERY (\bb. EVERY (P bb.bb_label) bb.bb_instructions) bbs /\
  (!a q id. MEM a roots /\ TC (frontier_step df) a q ==>
    P q (build_phi_inst_supply id x
      (case ALOOKUP pm q of NONE => [] | SOME ps => ps))) ==>
  EVERY (\bb. EVERY (P bb.bb_label) bb.bb_instructions) out
Proof
  strip_tac >> drule insertion_frontier_ancestry >> strip_tac >>
  gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac
  >- (drule generation_prefix_member >> strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem add_phi_frontier_preserves:
  !defs s bbs out t.
  add_phi_nodes_supply s df pm li bbs defs = (out,t) /\
  EVERY (\bb. EVERY (P bb.bb_label) bb.bb_instructions) bbs /\
  (!x roots a q id. MEM (x,roots) defs /\ MEM a roots /\ TC (frontier_step df) a q ==>
    P q (build_phi_inst_supply id x
      (case ALOOKUP pm q of NONE => [] | SOME ps => ps))) ==>
  EVERY (\bb. EVERY (P bb.bb_label) bb.bb_instructions) out
Proof
  Induct >> simp[add_phi_nodes_supply_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[add_phi_nodes_supply_def] >> pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum irule >> conj_tac >- metis_tac[] >>
  qexistsl_tac [`bbs'`,`s''`,`t`] >> simp[] >>
  irule insertion_frontier_preserves >> metis_tac[]
QED

Theorem add_phi_frontier_ancestry:
  add_phi_nodes_supply s df pm li bbs defs = (out,t) ==>
  EVERY (\bb. EVERY (\i.
    (?old. MEM old bbs /\ old.bb_label = bb.bb_label /\ MEM i old.bb_instructions) \/
    (?x roots a id. MEM (x,roots) defs /\ MEM a roots /\
      TC (frontier_step df) a bb.bb_label /\
      i = build_phi_inst_supply id x
        (case ALOOKUP pm bb.bb_label of NONE => [] | SOME ps => ps)))
    bb.bb_instructions) out
Proof
  strip_tac >> ho_match_mp_tac add_phi_frontier_preserves >>
  qexistsl_tac [`defs`,`s`,`bbs`,`t`] >> simp[] >> conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >> disj1_tac >> metis_tac[]) >>
  rpt strip_tac >> disj2_tac >> metis_tac[]
QED

(* Ancestry is in the frontier-generation relation only. It is not a final
   PHI dependency path, and implies neither seed connectivity nor dominance.
   Existing original PHIs fall under the first disjunct. The second disjunct
   retains the per-variable initial def_blocks witness from defs. *)
