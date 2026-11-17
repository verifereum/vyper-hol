Theory dftPacketBlockAppendTransport
Ancestors
  venomExecSemantics venomState list

Theorem dft_packet_block_append_transport:
  !(A : bytes32 list -> (string # num) list # exec_result) B H D
    gB g1 E0 Eb E1 be post.
  (!t. D t =
    (case A (gB ++ g1 ++ t) of
       (ea,OK ua) =>
         (case B (g1 ++ t) of
            (eb,OK ub) => (ea ++ eb ++ FST (H t),SND (H t))
          | (eb,rb) => (ea ++ eb,rb))
     | (ea,ra) => (ea,ra))) /\
  (!t. ?extra. E0 = FST (A t) ++ extra) /\
  (!t. ?extra. Eb = FST (B t) ++ extra) /\
  (!t. ?extra. E1 = FST (H t) ++ extra) /\
  (!t e u. A t = (e,OK u) ==>
    e = E0 /\ u = be with vs_gas_readings := t /\
    (!t'. A t' = (E0,OK (be with vs_gas_readings := t')))) /\
  (!t e u. B t = (e,OK u) ==>
    e = Eb /\ u = post with vs_gas_readings := t /\
    (!t'. B t' = (Eb,OK (post with vs_gas_readings := t')))) /\
  (!t e u. H t = (e,OK u) ==>
    e = E1 /\ u.vs_gas_readings = t /\
    (!t'. H t' = (E1,OK (u with vs_gas_readings := t')))) ==>
  !t.
    (?extra. E0 ++ Eb ++ E1 = FST (D t) ++ extra) /\
    (!e u. D t = (e,OK u) ==>
      e = E0 ++ Eb ++ E1 /\ u.vs_gas_readings = t /\
      (!t'. D t' = (E0 ++ Eb ++ E1,OK (u with vs_gas_readings := t'))) /\
      A (gB ++ g1 ++ t) =
        (E0,OK (be with vs_gas_readings := gB ++ g1 ++ t)) /\
      B (g1 ++ t) = (Eb,OK (post with vs_gas_readings := g1 ++ t)) /\
      H t = (E1,OK u))
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "compose")
    (CONJUNCTS_THEN2 (mk_asm "coverA")
      (CONJUNCTS_THEN2 (mk_asm "coverB")
        (CONJUNCTS_THEN2 (mk_asm "coverH")
          (CONJUNCTS_THEN2 (mk_asm "successA")
            (CONJUNCTS_THEN2 (mk_asm "successB") (mk_asm "successH"))))))) >>
  gen_tac >> conj_tac
  >- (Cases_on `A (gB ++ g1 ++ t)` >>
      rename1 `A (gB ++ g1 ++ t) = (ea,ra)` >>
      Cases_on `ra`
      >- (asm "successA" (qspecl_then [`gB ++ g1 ++ t`,`ea`,`v`] mp_tac) >>
          simp[] >> strip_tac >>
          Cases_on `B (g1 ++ t)` >> rename1 `B (g1 ++ t) = (eb,rb)` >>
          Cases_on `rb`
          >- (asm "successB" (qspecl_then [`g1 ++ t`,`eb`,`v'`] mp_tac) >>
              simp[] >> strip_tac >>
              asm "coverH" (qspec_then `t` mp_tac) >>
              simp[markerLib.L "compose"] >> metis_tac[APPEND_ASSOC]) >>
          asm "coverB" (qspec_then `g1 ++ t` mp_tac) >>
          simp[markerLib.L "compose"] >> metis_tac[APPEND_ASSOC]) >>
      asm "coverA" (qspec_then `gB ++ g1 ++ t` mp_tac) >>
      simp[markerLib.L "compose"] >> metis_tac[APPEND_ASSOC]) >>
  rpt gen_tac >> strip_tac >>
  asm "compose" (qspec_then `t` mp_tac) >>
  Cases_on `A (gB ++ g1 ++ t)` >> rename1 `A (gB ++ g1 ++ t) = (ea,ra)` >>
  Cases_on `ra` >> simp[] >> strip_tac >>
  rename1 `A (gB ++ g1 ++ t) = (ea,OK ua)` >>
  Cases_on `B (g1 ++ t)` >> rename1 `B (g1 ++ t) = (eb,rb)` >>
  Cases_on `rb` >> fs[] >>
  rename1 `B (g1 ++ t) = (eb,OK ub)` >>
  Cases_on `H t` >> rename1 `H t = (eh,rh)` >>
  Cases_on `rh` >> fs[] >>
  asm "successA" drule >> strip_tac >>
  asm "successB" drule >> strip_tac >>
  asm "successH" drule >> strip_tac >>
  simp[markerLib.L "compose"]
QED
