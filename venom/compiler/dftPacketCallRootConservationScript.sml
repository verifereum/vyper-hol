Theory dftPacketCallRootConservation
Ancestors
  dftPacketCallPathInsertion dftPacketCallInsertionConservation

(* The final synchronized table recurrence inserts the fresh, unobserved
   child exactly once.  No root aggregate equality is assumed. *)
Theorem dft_packet_call_root_conservation:
  !b:((num # num) list). !inds orders seed
    (m:(((num # num) list # num),bytes32 option list list) fmap) m'
    (s:(((num # num) list # num),(string # num) list list) fmap) s'
    (k:(((num # num) list # num),gas_event list list) fmap) k' cm ce ck.
    b <> [] /\ LENGTH inds = LENGTH b /\ LENGTH orders = SUC (LENGTH b) /\
    EL 0 orders = [seed] /\
    FLOOKUP m' (b,seed) = SOME cm /\ FLOOKUP s' (b,seed) = SOME ce /\
    FLOOKUP k' (b,seed) = SOME ck /\
    LENGTH (FLAT cm) = LENGTH (FLAT ce) /\ LENGTH (FLAT cm) = LENGTH (FLAT ck) /\
    (!a e. (a,e) <> (b,seed) /\
      (!r. r < LENGTH b ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
      FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\
      FLOOKUP s' (a,e) = FLOOKUP s (a,e) /\
      FLOOKUP k' (a,e) = FLOOKUP k (a,e)) /\
    (!i. i < LENGTH b ==>
      ALL_DISTINCT (EL (SUC i) orders) /\
      MEM (FST (EL i b)) (EL (SUC i) orders) /\
      ?ms ss ks.
        FLOOKUP m (DROP (SUC i) b,FST (EL i b)) = SOME ms /\
        FLOOKUP s (DROP (SUC i) b,FST (EL i b)) = SOME ss /\
        FLOOKUP k (DROP (SUC i) b,FST (EL i b)) = SOME ks /\
        EL i inds < LENGTH ms /\ EL i inds < LENGTH ss /\ EL i inds < LENGTH ks /\
        EL (EL i inds) ms = (if i = 0 then [] else
          FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP i b,f)))) (EL i orders))) /\
        EL (EL i inds) ss = (if i = 0 then [] else
          FLAT (MAP (\f. FLAT (THE (FLOOKUP s (DROP i b,f)))) (EL i orders))) /\
        EL (EL i inds) ks = (if i = 0 then [] else
          FLAT (MAP (\f. FLAT (THE (FLOOKUP k (DROP i b,f)))) (EL i orders))) /\
        FLOOKUP m' (DROP (SUC i) b,FST (EL i b)) =
          SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (DROP i b,f))))
            (EL i orders))) (EL i inds) ms) /\
        FLOOKUP s' (DROP (SUC i) b,FST (EL i b)) =
          SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP s' (DROP i b,f))))
            (EL i orders))) (EL i inds) ss) /\
        FLOOKUP k' (DROP (SUC i) b,FST (EL i b)) =
          SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP k' (DROP i b,f))))
            (EL i orders))) (EL i inds) ks)) /\
    (!i f. i < LENGTH b /\ MEM f (EL (SUC i) orders) ==>
      ?ms ss ks. FLOOKUP m (DROP (SUC i) b,f) = SOME ms /\
        FLOOKUP s (DROP (SUC i) b,f) = SOME ss /\
        FLOOKUP k (DROP (SUC i) b,f) = SOME ks /\
        LENGTH ms = LENGTH ss /\ LENGTH ms = LENGTH ks /\
        LIST_REL (\x y. LENGTH x = LENGTH y) ms ss /\
        LIST_REL (\x y. LENGTH x = LENGTH y) ms ks) /\
    EVERY (\x. x = NONE) (FLAT cm) ==>
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m' ([],f)))) (EL (LENGTH b) orders))) =
      LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP s' ([],f)))) (EL (LENGTH b) orders))) /\
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m' ([],f)))) (EL (LENGTH b) orders))) =
      LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP k' ([],f)))) (EL (LENGTH b) orders))) /\
    MAP THE (FILTER IS_SOME
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP m' ([],f)))) (EL (LENGTH b) orders)))) =
    MAP THE (FILTER IS_SOME
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP m ([],f)))) (EL (LENGTH b) orders)))) /\
    MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot)
        (ZIP (FLAT (MAP (\f. FLAT (THE (FLOOKUP k' ([],f)))) (EL (LENGTH b) orders)),
              FLAT (MAP (\f. FLAT (THE (FLOOKUP m' ([],f)))) (EL (LENGTH b) orders))))) =
    MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot)
        (ZIP (FLAT (MAP (\f. FLAT (THE (FLOOKUP k ([],f)))) (EL (LENGTH b) orders)),
              FLAT (MAP (\f. FLAT (THE (FLOOKUP m ([],f)))) (EL (LENGTH b) orders))))) /\
    (ALL_DISTINCT (FLAT (MAP (\f. FLAT (THE (FLOOKUP k ([],f)))) (EL (LENGTH b) orders))) /\
      ALL_DISTINCT (FLAT ck) /\
      (!x. MEM x (FLAT ck) ==>
        ~MEM x (FLAT (MAP (\f. FLAT (THE (FLOOKUP k ([],f)))) (EL (LENGTH b) orders)))) ==>
      ALL_DISTINCT (FLAT (MAP (\f. FLAT (THE (FLOOKUP k' ([],f)))) (EL (LENGTH b) orders))))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_call_path_insertion >> strip_tac >>
  asm_rewrite_tac[] >>
  irule dft_packet_call_insertion_conservation >> simp[]
QED
