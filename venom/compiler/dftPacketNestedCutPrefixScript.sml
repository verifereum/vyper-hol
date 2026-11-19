Theory dftPacketNestedCutPrefix
Ancestors
  list arithmetic

(* Compose the prefixes along the selected cut chain, retaining its suffixes. *)
Theorem dft_packet_nested_cut_prefix:
  !n (A:num -> 'a list) P.
    0 < n /\
    (!i. i < n ==> ?suf.
      A i = P i ++ (if SUC i < n then A (SUC i) else []) ++ suf)
    ==> ?rest. A 0 = FLAT (GENLIST P n) ++ rest
Proof
  Induct_on `n` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `n = 0`
  >- (gvs[] >>
      first_x_assum (qspec_then `0` mp_tac) >>
      simp[GENLIST_CONS]) >>
  `?rest. A 1 = FLAT (GENLIST (P o SUC) n) ++ rest` by
    (qpat_x_assum `!A P. _`
       (qspecl_then [`A o SUC`, `P o SUC`] mp_tac) >>
     simp[] >>
     (impl_tac
      >- (qx_gen_tac `i` >> strip_tac >>
          first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])) >>
     simp[]) >>
  qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `rest ++ suf` >>
  simp[GENLIST_CONS, APPEND_ASSOC]
QED
