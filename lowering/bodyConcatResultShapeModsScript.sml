(* The successful typed Concat result has the same payload as the linked fold. *)
Theory bodyConcatResultShapeMods
Ancestors
  bodyConcatCutsMods exprSimConcatSource vyperTypeConversions vyperTyping vyperValue list

Theorem concat_result_shape_mods:
  !cx a n args vs tv.
    2 <= LENGTH args /\ SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
    evaluate_type (get_tenv cx) a = SOME tv /\
    ((a = BaseT (BytesT (Dynamic n)) /\
      EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
     (a = BaseT (StringT n) /\
      EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))) /\
    LIST_REL (\e v. ?te. evaluate_type (get_tenv cx) (expr_type e) = SOME te /\
                         value_has_type te v) args vs ==>
    ?v. evaluate_concat n vs = INL v /\ value_has_type tv v /\
        concat_payload_mods v = FLAT (MAP concat_payload_mods vs)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\t v. ?te. evaluate_type (get_tenv cx) t = SOME te /\
                        value_has_type te v) (MAP expr_type args) vs` by
    simp[LIST_REL_MAP1, combinTheory.o_DEF] >>
  qpat_x_assum `(_ /\ _) \/ (_ /\ _)` strip_assume_tac >> gvs[]
  >- (drule_then assume_tac evaluate_type_BaseT_SOME >>
      qpat_assum `LIST_REL _ (MAP expr_type args) vs`
        (mp_then Any (qspec_then `n` mp_tac) evaluate_concat_typed_bytes) >>
      (impl_tac >- simp[]) >> strip_tac >>
      rename1 `vs = MAP BytesV bs` >> qexists_tac `BytesV (FLAT bs)` >>
      gvs[value_has_type_def, concat_payload_mods_def, MAP_MAP_o, combinTheory.o_DEF]) >>
  drule_then assume_tac evaluate_type_BaseT_SOME >>
  qpat_assum `LIST_REL _ (MAP expr_type args) vs`
    (mp_then Any (qspec_then `n` mp_tac) evaluate_concat_typed_string) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `vs = MAP StringV ss` >> qexists_tac `StringV (FLAT ss)` >>
  gvs[value_has_type_def, concat_payload_mods_def, MAP_MAP_o, combinTheory.o_DEF, MAP_FLAT] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED
