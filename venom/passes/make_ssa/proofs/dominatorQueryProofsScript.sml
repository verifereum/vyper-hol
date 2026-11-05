(* Full-domain query boundaries for the concrete dominator child lists. *)
Theory dominatorQueryProofs
Ancestors
  dominatorDefs cfgDefs finite_map list

Theorem fmap_insert_list_mem:
  MEM c (fmap_lookup_list
    (m |+ (k,set_insert v (fmap_lookup_list m k))) n) <=>
  MEM c (fmap_lookup_list m n) \/ (n = k /\ c = v)
Proof
  Cases_on `n = k` >>
  simp[fmap_lookup_list_def, FLOOKUP_UPDATE, set_insert_def] >>
  Cases_on `FLOOKUP m k` >> simp[] >>
  Cases_on `MEM v x` >> simp[] >> metis_tac[]
QED

Theorem compute_dominated_fold_mem:
  !labels (idom:'a |-> 'b) (m:'b |-> 'a list) n c.
    MEM c (fmap_lookup_list
      (FOLDL (\m lbl. case FLOOKUP idom lbl of
          NONE => m
        | SOME parent => m |+ (parent,
             set_insert lbl (fmap_lookup_list m parent))) m labels) n) <=>
    MEM c (fmap_lookup_list m n) \/
    (MEM c labels /\ FLOOKUP idom c = SOME n)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP idom h` >> simp[fmap_insert_list_mem] >>
  Cases_on `c = h` >> gvs[] >> metis_tac[]
QED

Theorem compute_dominated_membership:
  MEM c (fmap_lookup_list (compute_dominated idom labels) n) <=>
  MEM c labels /\ FLOOKUP idom c = SOME n
Proof
  simp[compute_dominated_def] >>
  once_rewrite_tac[compute_dominated_fold_mem] >>
  simp[fmap_lookup_list_def]
QED

Theorem compute_dominated_fold_distinct:
  !labels (idom:'a |-> 'b) (m:'b |-> 'a list).
    (!n. ALL_DISTINCT (fmap_lookup_list m n)) ==>
    !n. ALL_DISTINCT (fmap_lookup_list
      (FOLDL (\m lbl. case FLOOKUP idom lbl of
          NONE => m
        | SOME parent => m |+ (parent,
             set_insert lbl (fmap_lookup_list m parent))) m labels) n)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP idom h` >> simp[] >>
  first_x_assum irule >>
  gen_tac >> simp[fmap_lookup_list_def, FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[fmap_lookup_list_def, set_insert_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem compute_dominated_distinct:
  ALL_DISTINCT (fmap_lookup_list (compute_dominated idom labels) n)
Proof
  simp[compute_dominated_def] >>
  irule compute_dominated_fold_distinct >> simp[fmap_lookup_list_def]
QED

Theorem dominated_query_membership:
  MEM c (dominated_of (dom_analyze cfg fn) n) <=>
  MEM c (fn_labels fn) /\ idom_of (dom_analyze cfg fn) c = SOME n
Proof
  simp[dominated_of_def, idom_of_def, dom_analyze_def,
       compute_dominated_membership]
QED

Theorem dominated_query_distinct:
  ALL_DISTINCT (dominated_of (dom_analyze cfg fn) n)
Proof
  simp[dominated_of_def, dom_analyze_def, compute_dominated_distinct]
QED
