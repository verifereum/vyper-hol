(* Shared package supply boundaries; activity/control boundaries follow here. *)
Theory lowerDloadReturnAlignment
Ancestors
  lowerDloadReturnInterfaceProbe lowerDloadConfiguredOrigins list
Libs
  lowerDloadReturnPackageLib

Theorem ld_sync_supply_covered:
  (!f. MEM f C.ctx_functions ==> ir_supply_covers_fn (Sigma f.fn_name) f) /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames ==>
  ir_supply_covers_fn (HD frames).lf_supply fn
Proof
  strip_tac >> drule ld_sync_active >> strip_tac >>
  `MEM (HD frames) frames` by (Cases_on `frames` >> gvs[]) >>
  `MEM fn C.ctx_functions` by
    (qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ld_sync_def, EVERY_MEM] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

(* The production specialization changes only Ambient, not Point/Terminal. *)
Theorem ld_covered_package_induction:
  ^ld_package_induction ^ld_covered_ambient ^ld_probe_point ^ld_probe_terminal
Proof
  MATCH_ACCEPT_TAC ld_return_package_induction
QED

val _ = List.app (fn th => if null (hyp th) then ()
            else raise Fail "return package supply boundary has hypotheses")
  [ld_sync_supply_covered, ld_covered_package_induction];
