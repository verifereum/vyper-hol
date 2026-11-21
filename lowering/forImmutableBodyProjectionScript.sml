Theory forImmutableBodyProjection
Ancestors
  bodyLoopImmutableFrame immutableIteratorPrefixWrite whitelistForIterMem
  vyperAST vyperState vyperInterpreter vyperBareGlobalName vyperCallOutcomeFrame
  vyperTypeContract vyperTypeSystem list alist

(* A successful current read need not see the capture-time prefix array.
   Its shape, however, is still forced by the first subscript of the suffix. *)
Theorem immutable_iterator_prefix_shape[local]:
  !attrs tail cap_ty cap_root pav av tv old.
    evaluate_subscripts cap_ty cap_root (MAP AttrSubscript attrs) = INL (ArrayV pav) /\
    evaluate_subscripts cap_ty cap_root (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av) /\
    evaluate_subscripts tv old (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av) ==>
    ?cur. evaluate_subscripts tv old (MAP AttrSubscript attrs) = INL (ArrayV cur)
Proof
  Induct >- (
    simp[evaluate_subscripts_def] >> rpt gen_tac >> strip_tac >>
    Cases_on `tail`
    >- gvs[evaluate_subscripts_def] >>
    Cases_on `h` >> gvs[Once evaluate_subscripts_def] >>
    Cases_on `v` >> Cases_on `old` >> gvs[evaluate_subscripts_def]) >>
  rpt gen_tac >> Cases_on `cap_root` >> Cases_on `old` >>
  simp[] >>
  ntac 4 (simp[Once evaluate_subscripts_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem for_selected_immutable_array_body_observation:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  loop_iterator_place e = SOME p /\
  place_access p [] = (TopLevelNameTarget (src,name),attrs) /\
  iterator_unmodified (Array e) ss /\
  stmt_loop_calls_ok [(NONE,tops)] (For id et (Array e) bound ss) /\
  path = MAP AttrSubscript attrs ++ tail /\
  evaluate_subscripts cap_ty cap_root (MAP AttrSubscript attrs) = INL (ArrayV pav) /\
  evaluate_subscripts cap_ty cap_root path = INL (ArrayV av) /\
  lookup_immutable cx st src name = SOME (tv,old) /\
  evaluate_subscripts tv old path = INL (ArrayV av) /\
  eval_stmts cx ss st = (res,st') ==>
  ?v. lookup_immutable cx st' src name = SOME (tv,v) /\
      evaluate_subscripts tv v path = INL (ArrayV av)
Proof
  strip_tac >> gvs[] >>
  `?cur. evaluate_subscripts tv old (MAP AttrSubscript attrs) = INL (ArrayV cur)` by
    metis_tac[immutable_iterator_prefix_shape] >>
  `?v. lookup_immutable cx st' src name = SOME (tv,v) /\
       evaluate_subscripts tv v (MAP AttrSubscript attrs) = INL (ArrayV cur)` by
    (irule for_selected_immutable_body_frame_from_guard >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `stmt_loop_calls_ok _ _`)) >>
     goal_assum (drule_at (Pat `loop_iterator_place _ = _`)) >>
     simp[] >> rpt gen_tac >> strip_tac >>
     `!s. lookup_immutable cx' s src name = lookup_immutable cx s src name` by
       simp[lookup_immutable_def] >>
     drule_all immutable_guarded_prefix_mutation >> simp[]) >>
  qexists `v` >> simp[] >> metis_tac[evaluate_subscripts_prefix_agree]
QED
