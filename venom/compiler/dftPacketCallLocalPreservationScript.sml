Theory dftPacketCallLocalPreservation
Ancestors
  dftPacketCallEdgeClauses dftPacketFreshRow dftPacketCallNative
  frameJointTransition list rich_list finite_map arithmetic pred_set

(* A current call cannot already have a retained record: a returned call is
   in the scheduled prefix, while an unreturned child is on the old live path. *)
Theorem dft_packet_call_record_fresh:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (calls:(gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p d inst xs rho count q.
    q < LENGTH xs /\ EL q xs = inst /\ ~MEM q (TAKE count rho) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
    (!r h b0 done child ret.
      FLOOKUP calls (p,d,inst.inst_id) = SOME (r,h,b0,done,child,ret) ==>
      r < LENGTH xs /\ (EL r xs).inst_id = inst.inst_id /\
      (case ret of
        NONE => MEM ((d,inst.inst_id)::p)
          (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
      | SOME returned => MEM r (TAKE count rho))) /\
    (!sf tf inc entry order res rest.
      FLOOKUP acts ((d,inst.inst_id)::p) =
        SOME (sf,tf,inc,entry,order,res,rest) ==>
      ?r h b0 done ret.
        FLOOKUP calls (p,d,inst.inst_id) = SOME (r,h,b0,done,entry,ret)) ==>
    FLOOKUP calls (p,d,inst.inst_id) = NONE /\
    FLOOKUP acts ((d,inst.inst_id)::p) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `!k. k <= LENGTH p ==> (d,inst.inst_id)::p <> DROP k p` by
    (rpt strip_tac >>
     qpat_x_assum `_::_ = DROP _ _` (mp_tac o AP_TERM ``LENGTH:(num # num) list -> num``) >>
     simp[]) >>
  `FLOOKUP calls (p,d,inst.inst_id) = NONE` by
    (Cases_on `FLOOKUP calls (p,d,inst.inst_id)` >- simp[] >>
     PairCases_on `x` >>
     gvs[] >>
     `x0 = q` by
       (drule ALL_DISTINCT_EL_IMP >>
        disch_then (qspecl_then [`x0`,`q`] mp_tac) >> simp[EL_MAP]) >>
     Cases_on `x5` >> gvs[MEM_GENLIST] >> metis_tac[LESS_EQ_IFF_LESS_SUC]) >>
  simp[] >>
  Cases_on `FLOOKUP acts ((d,inst.inst_id)::p)` >- simp[] >>
  PairCases_on `x` >> metis_tac[optionTheory.NOT_SOME_NONE]
QED
