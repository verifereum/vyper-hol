Theory lowerDloadStoreProducer
Ancestors
  lowerDloadLifetime arithmetic finite_map pred_set

(* Length-parametric footprint: the store consumer instantiates n = 32.
   Separation is required only among currently live owners. *)
Theorem ld_fixed_live_write_footprint:
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\
    (bt+sz <= ct \/ ct+cz <= bt)) /\
  ((p = q /\ p+n <= lo) \/
   (?owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz /\
     bs <= p /\ p+n <= bs+sz /\ q = bt+(p-bs))) ==>
  (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
    ((p<=a /\ a<p+n) <=> (q<=b /\ b<q+n))) /\
  (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
    p<=a /\ a<p+n ==> a-p=b-q)
Proof
  strip_tac >> rpt conj_tac >> rpt gen_tac >>
  simp[ld_site_bytes_def] >> strip_tac >>
  gvs[] >>
  qpat_assum `!owner bs bt sz. _ ==> lo <= bs /\ lo <= bt`
    (fn th => imp_res_tac th)
  >- decide_tac
  >- decide_tac
  >- decide_tac
  >- (Cases_on `owner = owner'`
      >- (gvs[ld_site_entry_def] >> decide_tac) >>
      qpat_x_assum `!owner other bs bt sz cs ct cz. _` drule_all >>
      decide_tac)
  >- decide_tac >>
  Cases_on `owner = owner'`
  >- (gvs[ld_site_entry_def] >> decide_tac) >>
  qpat_x_assum `!owner other bs bt sz cs ct cz. _` drule_all >> decide_tac
QED
