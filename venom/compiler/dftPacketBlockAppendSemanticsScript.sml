Theory dftPacketBlockAppendSemantics
Ancestors
  dftPacketSameLevelCompose dftPacketRootedOperational
  venomExecSemantics venomInst venomState list rich_list

Theorem dft_packet_block_rooted_eval_append:
  !R (P : string -> (basic_block # num # instruction list) list ->
       venom_state -> (string # num) list # exec_result)
    (S : instruction -> venom_state -> exec_result)
    (row_eval : string -> (basic_block # num # instruction list) ->
       venom_state -> (string # num) list # exec_result)
    B H pre sf rows bb d z0 Z bb1 z1 entry.
  P = (\owner plan ent.
    FOLDL (\(ev,r) row. case r of
      OK u => (ev ++ FST (row_eval owner row u), SND (row_eval owner row u))
    | other => (ev,other)) ([],OK ent) plan) /\
  R = (\levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
          (prior ++ FST (P sf.fn_name plan ent),
           case SND (P sf.fn_name plan ent) of
             OK caller => (case call of NONE => OK caller | SOME c => S c caller)
           | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  (!ent. row_eval sf.fn_name (bb,d,Z) ent =
    (case SND (row_eval sf.fn_name (bb,d,z0) ent) of
       OK u => (FST (row_eval sf.fn_name (bb,d,z0) ent) ++ FST (B u), SND (B u))
     | r => (FST (row_eval sf.fn_name (bb,d,z0) ent),r))) /\
  H = (\u. case B u of
    (eb,OK v) => (eb ++ FST (row_eval sf.fn_name (bb1,SUC d,z1) v),
                  SND (row_eval sf.fn_name (bb1,SUC d,z1) v))
  | (eb,r) => (eb,r)) ==>
  R (pre ++ [(sf,rows ++ [(bb,d,Z);(bb1,SUC d,z1)],NONE)]) entry =
    (case SND (R (pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)]) entry) of
       OK u => (FST (R (pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)]) entry) ++
                  FST (H u), SND (H u))
     | r => (FST (R (pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)]) entry),r))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `FOLDL fstep` >>
  simp[FOLDL_APPEND,FOLDL] >>
  Cases_on `FOLDL fstep ([],OK entry) pre` >>
  rename1 `FOLDL fstep ([],OK entry) pre = (prior,result)` >>
  Cases_on `result` >> simp[Abbr `fstep`,FOLDL_APPEND,FOLDL] >>
  qmatch_goalsub_abbrev_tac `FOLDL rstep` >>
  Cases_on `FOLDL rstep ([],OK v) rows` >>
  rename1 `FOLDL rstep ([],OK v) rows = (events,row_result)` >>
  Cases_on `row_result` >> simp[Abbr `rstep`] >>
  Cases_on `row_eval sf.fn_name (bb,d,z0) v'` >>
  rename1 `row_eval sf.fn_name (bb,d,z0) v' = (local_events,local_result)` >>
  first_x_assum (qspec_then `v'` mp_tac) >>
  Cases_on `local_result` >> simp[APPEND_ASSOC] >> strip_tac >> simp[] >>
  Cases_on `B v''` >> rename1 `B v'' = (eb,rb)` >>
  Cases_on `rb` >> simp[APPEND_ASSOC] >>
  rename1 `B v'' = (eb,OK next)` >>
  Cases_on `SND (row_eval sf.fn_name (bb1,SUC d,z1) next)` >> simp[]
QED

Theorem dft_packet_block_append_event_tail:
  !(A : bytes32 list -> (string # num) list # exec_result) D
    (H : venom_state -> (string # num) list # exec_result) gs1 E0 E1.
  (!t. D t = (case SND (A t) of
       OK u => (FST (A t) ++ FST (H u), SND (H u))
     | other => (FST (A t),other))) /\
  (!t. (?extra. E0 = FST (A t) ++ extra) /\
    (!ev u. A t = (ev,OK u) ==> ev = E0 /\ u.vs_gas_readings = t /\
      (!t'. A t' = (E0,OK (u with vs_gas_readings := t'))))) /\
  (!t u. A (gs1 ++ t) = (E0,OK u) ==>
    (?extra. E1 = FST (H u) ++ extra) /\
    (!ev v. H u = (ev,OK v) ==> ev = E1 /\ v.vs_gas_readings = t /\
      (!t'. H (u with vs_gas_readings := gs1 ++ t') =
        (E1,OK (v with vs_gas_readings := t'))))) ==>
  !tail.
    (?extra. E0 ++ E1 = FST (D (gs1 ++ tail)) ++ extra) /\
    (!ev v. D (gs1 ++ tail) = (ev,OK v) ==>
      ev = E0 ++ E1 /\ v.vs_gas_readings = tail /\
      (!tail'. D (gs1 ++ tail') = (E0 ++ E1,OK (v with vs_gas_readings := tail'))))
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "compose")
    (CONJUNCTS_THEN2 (mk_asm "old") (mk_asm "local"))) >>
  gen_tac >> Cases_on `A (gs1 ++ tail)` >>
  rename1 `A (gs1 ++ tail) = (old_events,old_result)` >>
  Cases_on `?u. old_result = OK u`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      asm "old" (qspec_then `gs1 ++ tail` mp_tac) >>
      disch_then (CONJUNCTS_THEN2 kall_tac
        (qspecl_then [`old_events`,`u`] mp_tac)) >> simp[] >>
      disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (CONJUNCTS_THEN2 (mk_asm "gas") (mk_asm "old_tail"))) >>
      asm "local" (qspecl_then [`tail`,`u`] mp_tac) >> simp[] >>
      disch_then (CONJUNCTS_THEN2 (mk_asm "coverage") (mk_asm "local_success")) >>
      Cases_on `H u` >> rename1 `H u = (events,result)` >>
      Cases_on `result`
      >- (asm "local_success" (qspecl_then [`events`,`v`] mp_tac) >> simp[] >>
          disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
            (CONJUNCTS_THEN2 (mk_asm "new_gas") (mk_asm "local_tail"))) >>
          simp[markerLib.L "compose",markerLib.L "old_tail",markerLib.L "local_tail",markerLib.L "new_gas"]) >>
      simp[markerLib.L "compose"] >>
      asm "coverage" mp_tac >> simp[] >> metis_tac[APPEND_ASSOC]) >>
  `D (gs1 ++ tail) = (old_events,old_result)` by
    (Cases_on `old_result` >> simp[markerLib.L "compose"] >> gvs[]) >>
  asm "old" (qspec_then `gs1 ++ tail` mp_tac) >> simp[] >> strip_tac >>
  simp[] >> metis_tac[APPEND_ASSOC]
QED
