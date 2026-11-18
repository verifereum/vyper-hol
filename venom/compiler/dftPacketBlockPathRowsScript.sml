Theory dftPacketBlockPathRows
Ancestors
  dftPacketExistingPathRows list rich_list finite_map arithmetic pred_set

(* The three tables share their path and update indices, but not their values. *)
Theorem dft_packet_block_path_rows:
  !p:((num # num) list). !inds orders d cm ce ck
    (m:(((num # num) list # num),'m list list) fmap)
    (es:(((num # num) list # num),'e list list) fmap)
    (ks:(((num # num) list # num),'k list list) fmap).
    LENGTH inds = LENGTH p /\ LENGTH orders = SUC (LENGTH p) /\
    (!i. i < LENGTH p ==> ?rows.
      FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
      EL i inds < LENGTH rows) /\
    (!i. i < LENGTH p ==> ?rows.
      FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
      EL i inds < LENGTH rows) /\
    (!i. i < LENGTH p ==> ?rows.
      FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
      EL i inds < LENGTH rows) ==>
    ?mts ets kts m' es' ks'.
      (LENGTH mts = SUC (LENGTH p) /\
       EL 0 mts = m |+ ((p,SUC d),cm) /\ m' = EL (LENGTH p) mts /\
       (!i. i < LENGTH p ==>
         EL (SUC i) mts = EL i mts |+
           ((DROP (SUC i) p,FST (EL i p)),
            LUPDATE
              (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i mts) (DROP i p,f))))
                (EL i orders))) (EL i inds)
              (THE (FLOOKUP (EL i mts) (DROP (SUC i) p,FST (EL i p)))))) /\
       (!i. i < LENGTH p ==>
         FLOOKUP (EL i mts) (DROP (SUC i) p,FST (EL i p)) =
         FLOOKUP m (DROP (SUC i) p,FST (EL i p))) /\
       (!i a e. i <= LENGTH p /\ (a,e) <> (p,SUC d) /\
         (!r. r < i ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
         FLOOKUP (EL i mts) (a,e) = FLOOKUP m (a,e)) /\
       FLOOKUP m' (p,SUC d) = SOME cm /\
       (!i rows. i < LENGTH p /\
         FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
         FLOOKUP m' (DROP (SUC i) p,FST (EL i p)) =
           SOME (LUPDATE
             (FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (DROP i p,f))))
               (EL i orders))) (EL i inds) rows) /\
         (!k. k <= EL i inds ==>
           TAKE k (THE (FLOOKUP m' (DROP (SUC i) p,FST (EL i p)))) = TAKE k rows) /\
         (!r. r < LENGTH rows /\ r <> EL i inds ==>
           EL r (THE (FLOOKUP m' (DROP (SUC i) p,FST (EL i p)))) = EL r rows) /\
         LENGTH (THE (FLOOKUP m' (DROP (SUC i) p,FST (EL i p)))) = LENGTH rows) /\
       FDOM m' = FDOM m UNION {(p,SUC d)}) /\
      (LENGTH ets = SUC (LENGTH p) /\
       EL 0 ets = es |+ ((p,SUC d),ce) /\ es' = EL (LENGTH p) ets /\
       (!i. i < LENGTH p ==>
         EL (SUC i) ets = EL i ets |+
           ((DROP (SUC i) p,FST (EL i p)),
            LUPDATE
              (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i ets) (DROP i p,f))))
                (EL i orders))) (EL i inds)
              (THE (FLOOKUP (EL i ets) (DROP (SUC i) p,FST (EL i p)))))) /\
       (!i. i < LENGTH p ==>
         FLOOKUP (EL i ets) (DROP (SUC i) p,FST (EL i p)) =
         FLOOKUP es (DROP (SUC i) p,FST (EL i p))) /\
       (!i a e. i <= LENGTH p /\ (a,e) <> (p,SUC d) /\
         (!r. r < i ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
         FLOOKUP (EL i ets) (a,e) = FLOOKUP es (a,e)) /\
       FLOOKUP es' (p,SUC d) = SOME ce /\
       (!i rows. i < LENGTH p /\
         FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
         FLOOKUP es' (DROP (SUC i) p,FST (EL i p)) =
           SOME (LUPDATE
             (FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (DROP i p,f))))
               (EL i orders))) (EL i inds) rows) /\
         (!k. k <= EL i inds ==>
           TAKE k (THE (FLOOKUP es' (DROP (SUC i) p,FST (EL i p)))) = TAKE k rows) /\
         (!r. r < LENGTH rows /\ r <> EL i inds ==>
           EL r (THE (FLOOKUP es' (DROP (SUC i) p,FST (EL i p)))) = EL r rows) /\
         LENGTH (THE (FLOOKUP es' (DROP (SUC i) p,FST (EL i p)))) = LENGTH rows) /\
       FDOM es' = FDOM es UNION {(p,SUC d)}) /\
      (LENGTH kts = SUC (LENGTH p) /\
       EL 0 kts = ks |+ ((p,SUC d),ck) /\ ks' = EL (LENGTH p) kts /\
       (!i. i < LENGTH p ==>
         EL (SUC i) kts = EL i kts |+
           ((DROP (SUC i) p,FST (EL i p)),
            LUPDATE
              (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i kts) (DROP i p,f))))
                (EL i orders))) (EL i inds)
              (THE (FLOOKUP (EL i kts) (DROP (SUC i) p,FST (EL i p)))))) /\
       (!i. i < LENGTH p ==>
         FLOOKUP (EL i kts) (DROP (SUC i) p,FST (EL i p)) =
         FLOOKUP ks (DROP (SUC i) p,FST (EL i p))) /\
       (!i a e. i <= LENGTH p /\ (a,e) <> (p,SUC d) /\
         (!r. r < i ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
         FLOOKUP (EL i kts) (a,e) = FLOOKUP ks (a,e)) /\
       FLOOKUP ks' (p,SUC d) = SOME ck /\
       (!i rows. i < LENGTH p /\
         FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
         FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)) =
           SOME (LUPDATE
             (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (DROP i p,f))))
               (EL i orders))) (EL i inds) rows) /\
         (!k. k <= EL i inds ==>
           TAKE k (THE (FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)))) = TAKE k rows) /\
         (!r. r < LENGTH rows /\ r <> EL i inds ==>
           EL r (THE (FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)))) = EL r rows) /\
         LENGTH (THE (FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)))) = LENGTH rows) /\
       FDOM ks' = FDOM ks UNION {(p,SUC d)})
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`p`,`LENGTH p`,`inds`,`orders`]
    (qspecl_then [`SUC d`,`cm`,`m`] mp_tac)
    (INST_TYPE [``:'v`` |-> ``:'m``] dft_packet_existing_path_rows) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `mts` (qx_choose_then `m'` strip_assume_tac)) >>
  qspecl_then [`p`,`LENGTH p`,`inds`,`orders`]
    (qspecl_then [`SUC d`,`ce`,`es`] mp_tac)
    (INST_TYPE [``:'v`` |-> ``:'e``] dft_packet_existing_path_rows) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `ets` (qx_choose_then `es'` strip_assume_tac)) >>
  qspecl_then [`p`,`LENGTH p`,`inds`,`orders`]
    (qspecl_then [`SUC d`,`ck`,`ks`] mp_tac)
    (INST_TYPE [``:'v`` |-> ``:'k``] dft_packet_existing_path_rows) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `kts` (qx_choose_then `ks'` strip_assume_tac)) >>
  qexistsl [`mts`,`ets`,`kts`,`m'`,`es'`,`ks'`] >> simp[]
QED
