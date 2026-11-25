(* Select an immutable element at the reached no-copy array cut. *)
Theory bodyArrayReachedImmutableMods
Ancestors
  bodyArrayReachedImmutableBaseMods bodyArrayReachedImmutableKeyMods
  bodyFullSubscriptLiveImmSelect bodyArraySelectImmutableMods
  bodyArrayNoCopySourceMods bodyArrayNoCopyCutsMods
  bodySubscriptArrayRouteDefsMods exprSimTopLevelProps context
Libs
  monadsyntax

Theorem array_reached_immutable_select_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  subscript_array_unframed_case_mods cenv cx obj idx et bd /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0 (es,s0,G0,tn0)
    (sa,sm,st2,sb,bvv,iop,dst,loc) (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = PlaceR (ImmutablePlace owner id path) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx ann obj idx et bd st0 (es,s0,G0,tn0) (sa,sb,dst,loc)
    (raw,key) (fin,it,Gi,tni)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac array_reached_immutable_base_mods >>
  drule_all_then strip_assume_tac array_reached_immutable_key_mods >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  qhdtm_x_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  `~array_slot_base cenv obj` by
    (strip_tac >> drule array_slot_base_compile_location >>
     disch_then (qspecl_then [`ty`,`sa`] mp_tac) >> simp[vv_location_def]) >>
  `expr_body_pre_mods mods cenv cx env obj (es with gas_obs := gs1)` by simp[] >>
  `expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2)` by simp[] >>
  qpat_assum `!p w. bvv = _ /\ eval_operand _ _ = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!etv. evaluate_type _ et = SOME etv ==> _` (drule_then assume_tac) >>
  qpat_x_assum `raw = PlaceR _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac immutable_expr_current_parent_mods >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `bvv = LocatedValue _ _` SUBST_ALL_TAC >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV _` SUBST_ALL_TAC >>
  qpat_x_assum `i = (if _ then _ else _)` SUBST_ALL_TAC >>
  qpat_x_assum `LocCode = (case vv_location _ of NONE => _ | SOME l => l)` kall_tac >>
  irule array_select_immutable_mods >>
  simp[] >> conj_tac
  >- (qexistsl [`env`,`exps`,`mods`] >> simp[]) >>
  qhdtm_assum `array_nocopy_cut_mods`
    (part_match_exists_tac (last o strip_conj) o concl) >>
  qexists `iw` >> simp[arithmeticTheory.ADD_COMM]
QED
