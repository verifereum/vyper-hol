(* The counted physical traversal also carries a transitive relation on
   the very states chosen by its header and body callbacks. *)
Theory fragGasCopyIterSide
Ancestors
  fragGasOriginPtrLoop arithmetic

Theorem copy_loop_iterate_origin_ptr_side:
  !P Inv cx (n:num) hdr loop_body exit remaining k G tn s.
  (!p q r. P p q /\ P q r ==> P p r) /\
  (!j G tn q. j <= n /\ Inv j G tn q /\ ~q.vs_halted /\
          q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r G1 tn1. gas_origin_ptr_path cx (q,G,tn) [] (OK r,G1,tn1) /\
         Inv j G1 tn1 r /\ ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = n then exit else loop_body) /\ P q r) /\
  (!j G tn q. j < n /\ Inv j G tn q /\ ~q.vs_halted /\
          q.vs_current_bb = loop_body /\ q.vs_inst_idx = 0 ==>
     ?r G1 tn1. gas_origin_ptr_path cx (q,G,tn) [] (OK r,G1,tn1) /\
         Inv (j+1) G1 tn1 r /\ ~r.vs_halted /\
         r.vs_current_bb = hdr /\ r.vs_inst_idx = 0 /\ P q r) /\
  k + remaining = n /\ Inv k G tn s /\ ~s.vs_halted /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t Gf tnf. gas_origin_ptr_path cx (s,G,tn) [] (OK t,Gf,tnf) /\
      Inv n Gf tnf t /\ ~t.vs_halted /\
      t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ P s t
Proof
  ntac 7 gen_tac >> Induct
  >- (rpt gen_tac >> strip_tac >>
      `k = n` by decide_tac >>
      qpat_x_assum `!j G tn q. j <= n /\ _ ==> _`
        (qspecl_then [`k`, `G`, `tn`, `s`] mp_tac) >>
      simp[] >> strip_tac >> qexistsl_tac [`r`, `G1`, `tn1`] >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `k < n /\ k <= n /\ (k+1)+remaining = n` by decide_tac >>
  qpat_assum `!j G tn q. j <= n /\ _ ==> _`
    (qspecl_then [`k`, `G`, `tn`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`r`, `G1`, `tn1`] strip_assume_tac) >>
  qpat_assum `!j G tn q. j < n /\ _ ==> _`
    (qspecl_then [`k`, `G1`, `tn1`, `r`] mp_tac) >>
  (impl_tac >- gvs[]) >>
  disch_then (qx_choosel_then [`u`, `G2`, `tn2`] strip_assume_tac) >>
  qpat_x_assum `!k G tn s. (_ /\ _ /\ _ /\ k + remaining = n /\ _) ==> _`
    (qspecl_then [`k+1`, `G2`, `tn2`, `u`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t`, `Gf`, `tnf`] strip_assume_tac) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >> simp[] >> conj_tac
  >- metis_tac[gas_origin_ptr_path_trans] >>
  metis_tac[]
QED
