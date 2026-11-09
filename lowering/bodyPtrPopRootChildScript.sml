Theory bodyPtrPopRootChild
Ancestors
  bodyPtrPopBoundary accountsRelProps compileEnv ptrDiscipline vyperStorage
  words pred_set

(* This uses the child's ORIGINAL runtime liveness. Global deadness after
   shortening is deliberately not a premise: it includes the whole child. *)
Theorem pop_child_taint_header:
  storage_read_live cx tr st elem tv /\
  X SUBSET {(k,b) | storage_dead cx tr st (w2n k) b} /\
  w2n (hdr:bytes32) < w2n elem /\
  w2n elem + type_slot_size tv <= dimword (:256) ==>
  !k b. (k,b) IN key_update X hdr {} /\
        w2n elem <= w2n k /\ w2n k < w2n elem + type_slot_size tv ==>
    dead_bytes (update_storage hdr u st) (w2n elem) tv (w2n k) b
Proof
  strip_tac >> rpt gen_tac >> simp[key_update_def] >> strip_tac >>
  `storage_dead cx tr st (w2n k) b` by
    (qpat_x_assum `_ SUBSET _` mp_tac >> simp[SUBSET_DEF] >>
     disch_then (qspec_then `(k,b)` mp_tac) >> simp[]) >>
  `dead_bytes st (w2n elem) tv (w2n k) b` by
    (gvs[storage_read_live_def] >> first_x_assum drule >> simp[]) >>
  drule_all pop_child_dead_bytes_header >> simp[]
QED
