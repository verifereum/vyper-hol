(* Concrete return-package preservation for nonallocating ordinary steps. *)
Theory lowerDloadReturnOrdinary
Ancestors
  lowerDloadReturnAlignment lowerDloadOrdinaryEndpoint list
Libs
  lowerDloadReturnPackageLib

Theorem ld_stable_head_replace:
  ^ld_probe_stable lo P Sigma names fs f0 A0 A (f::fs) /\
  g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
  g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q /\
  ld_global lo A (g::fs) ==>
  ^ld_probe_stable lo P Sigma names fs f0 A0 A (g::fs)
Proof
  simp[] >> strip_tac >> gvs[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!j k. _` (qspecl_then [`j`,`k`] mp_tac) >>
  Cases_on `j` >> Cases_on `k` >> gvs[]
QED

val _ = if null (hyp ld_stable_head_replace) then ()
        else raise Fail "stable head replacement has hypotheses";
