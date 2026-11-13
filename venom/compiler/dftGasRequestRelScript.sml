(* Request-sensitive result boundary for the gas-oracle DFT simulation.
 * Successful results stay exact; only aborts acquire a directional prefix.
 * Error deliberately retains the permissive behavior of dft_res_rel.
 *)
Theory dftGasRequestRel
Ancestors
  dftRunRel dftGasOracleDefs o1RequestContract o1PassContract

Definition dft_rq_res_rel_def:
  dft_rq_res_rel D r r' <=>
    dft_res_rel r r' /\
    (!a t a' t'. r = Abort a t /\ r' = Abort a' t' ==>
       request_prefix_rel D t.vs_requests t'.vs_requests)
End

Theorem dft_rq_res_rel_imp:
  dft_rq_res_rel D r r' ==> dft_res_rel r r'
Proof
  simp[dft_rq_res_rel_def]
QED

Theorem dft_rq_res_rel_refl:
  dft_rq_res_rel D r r
Proof
  Cases_on `r` >> simp[dft_rq_res_rel_def, dft_res_rel_def,
                        request_prefix_rel_refl]
QED

Theorem dft_rq_res_rel_abort:
  dft_rq_res_rel D (Abort a t) r' <=>
    ?a' t'. r' = Abort a' t' /\
      (a = Revert_abort ==> a' = Revert_abort) /\
      request_prefix_rel D t.vs_requests t'.vs_requests
Proof
  Cases_on `r'` >> simp[dft_rq_res_rel_def, dft_res_rel_def]
QED

Theorem dft_rq_res_rel_trans:
  dead_wf D /\ dft_rq_res_rel D r r' /\ dft_rq_res_rel D r' r'' ==>
  dft_rq_res_rel D r r''
Proof
  Cases_on `r` >> Cases_on `r'` >> Cases_on `r''` >>
  simp[dft_rq_res_rel_def, dft_res_rel_def] >>
  metis_tac[request_prefix_rel_trans]
QED

Theorem dft_rq_res_rel_ok_continuation:
  dft_rq_res_rel D r r' /\
  (!s. r = OK s ==> dft_rq_res_rel D (k s) (k' s)) ==>
  dft_rq_res_rel D
    (case r of OK s => k s | other => other)
    (case r' of OK s => k' s | other => other)
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[dft_rq_res_rel_def, dft_res_rel_def]
QED

Theorem gas_variant_requests:
  gas_variant s s' ==> s.vs_requests = s'.vs_requests
Proof
  strip_tac >> fs[gas_variant_def] >>
  qpat_x_assum `s' = _` SUBST1_TAC >> simp[]
QED

(* One constructor characterization covers both replay orientations. *)
Theorem gas_res_rel_abort:
  (gas_res_rel (Abort a t) r <=>
     ?u. r = Abort a u /\ gas_variant t u) /\
  (gas_res_rel r (Abort a t) <=>
     ?u. r = Abort a u /\ gas_variant u t)
Proof
  Cases_on `r` >> simp[gas_res_rel_def] >> metis_tac[]
QED

Theorem gas_res_rel_abort_requests:
  (gas_res_rel (Abort a t) r ==>
     ?u. r = Abort a u /\ t.vs_requests = u.vs_requests) /\
  (gas_res_rel r (Abort a t) ==>
     ?u. r = Abort a u /\ u.vs_requests = t.vs_requests)
Proof
  simp[gas_res_rel_abort] >> metis_tac[gas_variant_requests]
QED
