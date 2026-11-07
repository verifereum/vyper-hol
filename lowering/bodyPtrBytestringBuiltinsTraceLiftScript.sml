Theory bodyPtrBytestringBuiltinsTraceLift
Ancestors
  fragGasPathPtr fragGasPath fragExec

(* This lifts one supplied ordinary path, not an independently selected run.
   The caller must establish safe edges and endpoint invariants separately. *)
Theorem gas_path_invariant_ptr_lift:
  !ctx fn s n r. gas_path ctx fn s n r ==>
  !Inv J D lo PG G tn.
  (!s k r G tn.
    Inv s G tn /\ gas_path_edge ctx fn s k r ==>
    ?G' tn'. gas_path_ptr_edge D lo ctx fn PG G tn s k G' tn' r /\
      ((?t. r = OK t /\ Inv t G' tn') \/
       (exit_result r /\ J r G' tn'))) /\ Inv s G tn ==>
    ?G' tn'. gas_path_ptr D lo ctx fn PG G tn s n G' tn' r /\
      ((?t. r = OK t /\ Inv t G' tn') \/
       (exit_result r /\ J r G' tn'))
Proof
  ho_match_mp_tac gas_path_ind >> rpt strip_tac
  >- (qexistsl_tac [`G`, `tn`] >>
      simp[] >> irule (cj 1 gas_path_ptr_rules) >> simp[])
  >- (qpat_assum `!s k r G tn. Inv s G tn /\ gas_path_edge _ _ s k r ==> _` drule_all >>
      disch_then (strip_assume_tac o
        SIMP_RULE (srw_ss()) [exit_result_def]) >>
      qpat_x_assum `!Inv J D lo PG G tn. _`
        (qspecl_then [`Inv`, `J`, `D`, `lo`, `PG`] mp_tac) >>
      disch_then drule_all >> strip_tac >>
      metis_tac[gas_path_ptr_rules])
  >> qpat_assum `!s k r G tn. Inv s G tn /\ gas_path_edge _ _ s k r ==> _` drule_all >>
  strip_tac >> metis_tac[gas_path_ptr_rules]
QED

Theorem gas_path_invariant_ptr_lift_normal:
  gas_path ctx fn s n (OK t) /\ Inv s G tn /\
  (!s k r G tn.
    Inv s G tn /\ gas_path_edge ctx fn s k r ==>
    ?G' tn'. gas_path_ptr_edge D lo ctx fn PG G tn s k G' tn' r /\
      ((?t. r = OK t /\ Inv t G' tn') \/
       (exit_result r /\ J r G' tn'))) ==>
  ?G' tn'. gas_path_ptr D lo ctx fn PG G tn s n G' tn' (OK t) /\
    Inv t G' tn'
Proof
  strip_tac >> drule_all gas_path_invariant_ptr_lift >>
  simp[exit_result_def]
QED

Theorem gas_path_invariant_ptr_lift_exit:
  gas_path ctx fn s n r /\ exit_result r /\ Inv s G tn /\
  (!s k r G tn.
    Inv s G tn /\ gas_path_edge ctx fn s k r ==>
    ?G' tn'. gas_path_ptr_edge D lo ctx fn PG G tn s k G' tn' r /\
      ((?t. r = OK t /\ Inv t G' tn') \/
       (exit_result r /\ J r G' tn'))) ==>
  ?G' tn'. gas_path_ptr D lo ctx fn PG G tn s n G' tn' r /\ J r G' tn'
Proof
  strip_tac >> drule_all gas_path_invariant_ptr_lift >>
  metis_tac[exit_result_def]
QED
