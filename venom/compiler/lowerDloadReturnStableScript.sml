(* Allocation-map framing for the shared successful-return package. *)
Theory lowerDloadReturnStable
Ancestors
  lowerDloadReturnOrdinary lowerDloadExpansionEndpoint finite_map pred_set list
Libs
  lowerDloadReturnPackageLib

Theorem ld_slots_map_extend:
  (!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a) ==>
  ld_slots A fs SUBSET ld_slots Ar fs
Proof
  simp[SUBSET_DEF, ld_slots_def] >> rpt strip_tac >>
  `FLOOKUP Ar (f.lf_serial,aid) = SOME (b,c,n)` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  metis_tac[]
QED

Theorem ld_stable_head_extend:
  ^ld_probe_stable lo P Sigma names fs f0 A0 A (f::fs) /\
  g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
  g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q /\
  (!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a) /\
  ld_global lo Ar (g::fs) ==>
  ^ld_probe_stable lo P Sigma names fs f0 A0 Ar (g::fs)
Proof
  simp[] >> strip_tac >>
  `ld_slots A fs SUBSET ld_slots Ar fs` by
    (irule ld_slots_map_extend >> simp[]) >>
  gvs[] >>
  rpt conj_tac >> rpt strip_tac
  >- (qpat_x_assum `!j k. _` (qspecl_then [`j`,`k`] mp_tac) >>
      Cases_on `j` >> Cases_on `k` >> gvs[])
  >- metis_tac[SUBSET_TRANS]
  >- metis_tac[SUBSET_DEF]
  >> `a IN FDOM A` by metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  metis_tac[]
QED

val _ = if null (hyp ld_stable_head_extend) then ()
        else raise Fail "stable head extension has hypotheses";
