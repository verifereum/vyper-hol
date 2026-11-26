(* The shortened local and the removed element share one physical pop store. *)
Theory bodyPopLocalRepresentationMods
Ancestors
  exprSimPopNestedLocalProps exprSimPopNestedLocalMemory
  bodyFullSubscriptPopLayout representationCleanPtr
  exprSimProps valueEncoding valueEncodingDefs valueEncodingProps
  venomState vyperTyping vyperPlaceStatePreservation
  arithmetic words list rich_list

Theorem pop_local_representation_mods:
  !cx es id path pre sc entry rest s locbase k etv n vs.
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    entry.assignable /\
    mutable_place_path entry.type path /\
    value_has_type entry.type entry.value /\
    well_formed_type_value entry.type /\
    val_wf entry.type entry.value /\
    subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n)) /\
    mem_path_offset entry.type path = SOME (k,ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts entry.type entry.value path =
      INL (ArrayV (DynArrayV vs)) /\
    vs <> [] /\
    val_in_memory entry.type entry.value locbase s.vs_memory ==>
  ?updated.
    assign_subscripts entry.type entry.value path
      (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
    evaluate_subscripts entry.type updated path =
      INL (ArrayV (DynArrayV (FRONT vs))) /\
    evaluate_subscripts entry.type updated
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) =
        INR (RuntimeError "evaluate_subscripts array_index") /\
    subscripts_type entry.type
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) = SOME etv /\
    (let t = es with scopes := pre ++ sc |+ (id,entry with
           <|value := updated;
             popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs)
               entry.popped|>) :: rest
     in
       val_in_memory entry.type updated locbase
         (mstore (locbase + k) (n2w (LENGTH vs - 1)) s).vs_memory /\
       val_in_memory etv (LAST vs)
         (locbase + k + 32 + (LENGTH vs - 1) * type_memory_size etv)
         (mstore (locbase + k) (n2w (LENGTH vs - 1)) s).vs_memory /\
       (!b i. subscript_layout_byte entry.type updated b i ==>
          subscript_layout_byte entry.type entry.value b i) /\
       pop_place cx (MemoryPlace id path) es =
         (INL (PlaceR (MemoryPlace id
           (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))),t) /\
       read_result cx (PlaceR (MemoryPlace id
           (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))) t =
         (INL (LAST vs),t))
Proof
  rpt strip_tac >>
  drule_all exprSimPopNestedLocalPropsTheory.pop_memory_live_transition >>
  disch_then (qspec_then `cx`
    (qx_choose_then `updated` strip_assume_tac)) >>
  qpat_x_assum `let t = _ in _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [LET_THM]) >>
  qexists_tac `updated` >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [LET_THM] >>
  (conj_tac >-
    (drule_all val_in_memory_pop_path >> disch_then assume_tac >>
     `locbase + k = k + locbase` by decide_tac >>
     qpat_assum `locbase + k = k + locbase`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC)) >>
  (conj_tac >-
    (drule_all pop_path_elem_in_memory >> disch_then assume_tac >>
     `locbase + k = k + locbase` by decide_tac >>
     qpat_assum `locbase + k = k + locbase`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC)) >>
  (conj_tac >-
    (rpt gen_tac >> strip_tac >>
     drule_all subscript_pop_layout_shorten >>
     disch_then assume_tac >> first_assum ACCEPT_TAC)) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
