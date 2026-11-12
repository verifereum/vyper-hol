(* Fixed source paths remain readable in any typed replacement root. *)
Theory popNestedFixedPathMemory
Ancestors
  vyperPlaceResultTyping vyperPlaceStatePreservation vyperTyping
  vyperState vyperValue vyperValueOperation integer list rich_list option alist

Theorem pop_nested_fixed_path_ready:
  !path tv replacement ptv.
    well_formed_type_value tv /\ value_has_type tv replacement /\
    subscripts_type tv path = SOME ptv /\
    (!prefix i suffix et n.
      path = prefix ++ ValueSubscript (IntV i)::suffix ==>
      subscripts_type tv prefix <> SOME (ArrayTV et (Dynamic n))) ==>
    ?v. evaluate_subscripts tv replacement path = INL v
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs()] >>
  rename1 `subscript_type tv h = SOME etv` >>
  `?w. evaluate_subscripts tv replacement [h] = INL w` by
    (Cases_on `h`
     >- (Cases_on `v` >> gvs[subscript_type_def] >>
         rename1 `ValueSubscript (IntV i)` >>
         `!et n. tv <> ArrayTV et (Dynamic n)` by
           (rpt strip_tac >>
            first_x_assum (qspecl_then [`[]`, `i`, `path`, `et`, `n`] mp_tac) >>
            simp[subscripts_type_def]) >>
         Cases_on `tv` >> gvs[subscript_type_def] >>
         Cases_on `replacement` >> gvs[value_has_type_def] >>
         Cases_on `a` >> gvs[value_has_type_def]
         >~ [`values_have_types ts vs`]
         >- (drule values_have_types_length >> strip_tac >>
            simp[evaluate_subscripts_def, array_index_def,
                 subscript_type_def, listTheory.oEL_THM]) >>
         Cases_on `b` >> gvs[value_has_type_def] >>
         simp[evaluate_subscripts_def, array_index_def] >>
         Cases_on `ALOOKUP l (Num i)` >> simp[evaluate_subscripts_def])
     >> metis_tac[evaluate_subscripts_attribute_ready]) >>
  `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
  `value_has_type etv w` by
    (irule evaluate_subscripts_type >>
     qexistsl_tac [`replacement`, `[h]`, `tv`] >>
     simp[subscripts_type_def]) >>
  `!prefix i suffix et n.
     path = prefix ++ ValueSubscript (IntV i)::suffix ==>
     subscripts_type etv prefix <> SOME (ArrayTV et (Dynamic n))` by
    (rpt strip_tac >>
     first_x_assum (qspecl_then [`h::prefix`, `i`, `suffix`, `et`, `n`] mp_tac) >>
     simp[subscripts_type_def]) >>
  first_x_assum (qspecl_then [`etv`, `w`, `ptv`] mp_tac) >>
  simp[] >> strip_tac >>
  drule evaluate_subscripts_cons_typed >> simp[] >> metis_tac[]
QED
