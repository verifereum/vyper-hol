(* Finite loops whose transition endpoints are uniform in the joint parameters. *)
Theory fullStoreSlotsUniformLoop
Ancestors fragGasCopyLoop fragGasOriginPtr venomState arithmetic

Theorem store_slots_uniform_loop_iterate:
  !Inv lo ctx func (n:num) hdr body exit remaining k G tn s.
  (!j G tn q. j <= n /\ Inv j G tn q /\ ~q.vs_halted /\
       q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
    ?r G1 tn1.
      (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (q,G,tn) [] (OK r,G1,tn1)) /\
      Inv j G1 tn1 r /\ ~r.vs_halted /\ r.vs_inst_idx = 0 /\
      r.vs_current_bb = (if j=n then exit else body)) /\
  (!j G tn q. j < n /\ Inv j G tn q /\ ~q.vs_halted /\
       q.vs_current_bb = body /\ q.vs_inst_idx = 0 ==>
    ?r G1 tn1.
      (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (q,G,tn) [] (OK r,G1,tn1)) /\
      Inv (j+1) G1 tn1 r /\ ~r.vs_halted /\
      r.vs_current_bb = hdr /\ r.vs_inst_idx = 0) /\
  k + remaining = n /\ Inv k G tn s /\ ~s.vs_halted /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    Inv n Gf tnf t /\ ~t.vs_halted /\
    t.vs_current_bb = exit /\ t.vs_inst_idx = 0
Proof
  ntac 8 gen_tac >> Induct
  >- (rpt gen_tac >> strip_tac >>
      `k=n` by decide_tac >>
      qpat_x_assum `!j G tn q. j <= n /\ _ ==> _`
        (qspecl_then [`k`, `G`, `tn`, `s`] mp_tac) >>
      simp[] >> strip_tac >> qexistsl_tac [`r`, `G1`, `tn1`] >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `k<n /\ k<=n /\ (k+1)+remaining=n` by decide_tac >>
  qpat_assum `!j G tn q. j <= n /\ _ ==> _`
    (qspecl_then [`k`, `G`, `tn`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`r`, `G1`, `tn1`] strip_assume_tac) >>
  qpat_assum `!j G tn q. j < n /\ _ ==> _`
    (qspecl_then [`k`, `G1`, `tn1`, `r`] mp_tac) >>
  (impl_tac >- gvs[]) >>
  disch_then (qx_choosel_then [`u`, `G2`, `tn2`] strip_assume_tac) >>
  qpat_x_assum `!k G tn s. (_ /\ _ /\ k + remaining = n /\ _) ==> _`
    (qspecl_then [`k+1`, `G2`, `tn2`, `u`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >> simp[] >>
  metis_tac[origin_ptr_path_then]
QED
