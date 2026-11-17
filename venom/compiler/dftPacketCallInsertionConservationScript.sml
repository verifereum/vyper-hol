Theory dftPacketCallInsertionConservation
Ancestors
  list rich_list

(* Synchronized insertion of unobserved slots preserves both ordered
   observation projections.  The statement is polymorphic in slots, sites,
   and keys so that it applies directly to each concrete packet list. *)
Theorem dft_packet_call_insertion_conservation:
  !(lm:'v option list) rm (le:'s list) re (lk:'k list) rk cm ce ck.
    LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
    LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk /\
    LENGTH cm = LENGTH ce /\ LENGTH cm = LENGTH ck /\
    EVERY (\x. x = NONE) cm ==>
    LENGTH (lm ++ cm ++ rm) = LENGTH (le ++ ce ++ re) /\
    LENGTH (lm ++ cm ++ rm) = LENGTH (lk ++ ck ++ rk) /\
    MAP THE (FILTER IS_SOME (lm ++ cm ++ rm)) =
      MAP THE (FILTER IS_SOME (lm ++ rm)) /\
    MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot)
        (ZIP (lk ++ ck ++ rk,lm ++ cm ++ rm))) =
    MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot) (ZIP (lk ++ rk,lm ++ rm))) /\
    (ALL_DISTINCT (lk ++ rk) /\ ALL_DISTINCT ck /\
      (!x. MEM x ck ==> ~MEM x (lk ++ rk)) ==>
      ALL_DISTINCT (lk ++ ck ++ rk))
Proof
  rpt gen_tac >> strip_tac >>
  `FILTER IS_SOME cm = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >>
     gvs[EVERY_MEM] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  `FILTER (\(key,slot). IS_SOME slot) (ZIP (ck,cm)) = []` by
    (simp[FILTER_EQ_NIL] >>
     `EVERY (\x. SND x = NONE) (ZIP (ck,cm))` by
       simp[every_zip_snd] >>
     fs[pairTheory.LAMBDA_PROD]) >>
  simp[LENGTH_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND] >>
  gvs[ALL_DISTINCT_APPEND, MEM_APPEND] >> metis_tac[]
QED
