(* Restore the saved storage place or owned bytes on the continuing loop edge. *)
Theory bodyForArraySlotOwnedRestoreMods
Ancestors
  bodyForArrayEntryMods bodyForArraySavedFrameMods
  vyperStorageTrace vyperStorageFootprint vyperStoragePlaceObserved
  vyperState vyperInterpreter valueEncodingTyping valueEncodingProofs
  bodyForArrayHeaderMods bodyPtrDefs bodyFullForArrayRound gasOutcomeFull
  loweringPosts ptrDiscipline valueEncoding
  exprSimProps arithmetic finite_map list words

val _ = Parse.hide "body";

Theorem restore_capture_frame[local]:
  for_array_header_mods mods DF lo d ctx func c cx env id st0
    (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) item
    vs (op,bw,len_op,idx) cond Route H rs ee G tn f ==>
  for_array_capture_frame_mods c (em,sbExpr,saL,u,tu) ee tn f
Proof
  simp[for_array_header_mods_def]
QED

Theorem restore_saved_frame[local]:
  push_scope_with_var id tyv v (es with gas_obs := []) = (INL (),ep) /\
  eval_stmts cx body (ep with gas_obs := gs) = (raw,fin) /\
  for_array_capture_frame_mods c (em,sbExpr,saL,u,tu)
    (fin with scopes := TL fin.scopes) tn1 f /\
  copy_old_operand saL op /\ (!lbl. op <> Label lbl) /\
  eval_operand op u = SOME bw /\
  (!q. not_fresh_at saL q ==>
    FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q)) ==>
  eval_operand op f = SOME bw /\ op_prov G1 op = op_prov G op /\
  (!aid b sz rt av.
    FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ aid < sbExpr.cs_next_id /\
    (!nm lb lsz. local_region c em.scopes u nm lb lsz ==> b+sz <= lb \/ lb+lsz <= b) /\
    b <= w2n bw /\ w2n bw + val_footprint rt (ArrayV av) <= b+sz /\ val_wf rt (ArrayV av) /\
    (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
           val_in_memory rt (ArrayV av) (w2n bw) mem) ==>
    FLOOKUP f.vs_allocas aid = SOME (b,sz) /\
    (!nm lb lsz. local_region c (TL fin.scopes) f nm lb lsz ==> b+sz <= lb \/ lb+lsz <= b) /\
    !mem. mem_agree_outside tn1.t_mem f.vs_memory mem ==>
          val_in_memory rt (ArrayV av) (w2n bw) mem)
Proof
  strip_tac >>
  drule_all (SIMP_RULE std_ss [] (Q.INST
    [`st` |-> `eb with gas_obs := obs`, `ep` |-> `fin with scopes := TL fin.scopes`]
    for_array_saved_after_body_mods)) >>
  disch_then (qspec_then `ARB:type_value` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem restore_trace_append[local]:
  push_scope_with_var id tyv v (es with gas_obs := []) = (INL (),ep) /\
  eval_stmts cx body (ep with gas_obs := gs) = (raw,fin) ==>
  ?suffix. fin.storage_trace = es.storage_trace ++ suffix
Proof
  strip_tac >>
  `ep.storage_trace = es.storage_trace` by
    (qpat_x_assum `push_scope_with_var _ _ _ _ = _` mp_tac >>
     simp[push_scope_with_var_def,return_def] >> disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  drule_at (Pos last) storage_trace_frame_prefix >>
  simp[cj 2 evaluate_storage_trace_frame]
QED

Theorem for_array_slot_restore_mods:
  (!K. valid_horizon cx st0 K es.storage_trace ==>
    for_array_entry_route_mods c cx lo (sty,bd,slot_loc tr)
      (em,sbExpr,u,Gu,tu) (op,bw) vs (ForArraySlot tr off root path delta)
      K (a::rs) es G tn s) /\
  copy_old_operand saL op /\ (!lbl. op <> Label lbl) /\
  push_scope_with_var id tyv v (es with gas_obs := []) = (INL (),ep) /\
  eval_stmts cx body (ep with gas_obs := gs) = (raw,fin) /\
  valid_horizon cx st0 H fin.storage_trace /\
  for_array_header_mods mods DF lo d ctx func c cx env id st0
    (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) item
    vs (op,bw,len_op,idx) cond (\_ _ _ _ _ _. T)
    H rs (fin with scopes := TL fin.scopes) G1 tn1 f /\
  (!q. not_fresh_at saL q ==>
    FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q)) ==>
  for_array_entry_route_mods c cx lo (sty,bd,slot_loc tr)
    (em,sbExpr,u,Gu,tu) (op,bw) vs (ForArraySlot tr off root path delta)
    H rs (fin with scopes := TL fin.scopes) G1 tn1 f
Proof
  strip_tac >> drule_all_then (qx_choose_then `suffix` assume_tac) restore_trace_append >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule valid_horizon_append >> qexists_tac `suffix` >>
     qpat_assum `fin.storage_trace = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!K. valid_horizon _ _ K _ ==> for_array_entry_route_mods _ _ _ _ _ _ _ _ K _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [for_array_entry_route_mods_def])) >>
  drule_then assume_tac restore_capture_frame >>
  drule_all_then strip_assume_tac restore_saved_frame >>
  qpat_x_assum `bw = _` SUBST_ALL_TAC >>
  simp[for_array_entry_route_mods_def]
QED

Theorem for_array_owned_restore_mods:
  (!K. valid_horizon cx st0 K es.storage_trace ==>
    for_array_entry_route_mods c cx lo (sty,bd,LocMemory)
      (em,sbExpr,u,Gu,tu) (op,bw) vs (ForArrayOwned av) K (a::rs) es G tn s) /\
  (!tv. evaluate_type (get_tenv cx) sty = SOME tv ==>
    !mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) mem) /\
  copy_old_operand saL op /\ (!lbl. op <> Label lbl) /\
  push_scope_with_var id tyv v (es with gas_obs := []) = (INL (),ep) /\
  eval_stmts cx body (ep with gas_obs := gs) = (raw,fin) /\
  valid_horizon cx st0 H fin.storage_trace /\
  for_array_header_mods mods DF lo d ctx func c cx env id st0
    (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) item
    vs (op,bw,len_op,idx) cond (\_ _ _ _ _ _. T)
    H rs (fin with scopes := TL fin.scopes) G1 tn1 f /\
  (!q. not_fresh_at saL q ==>
    FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q)) ==>
  for_array_entry_route_mods c cx lo (sty,bd,LocMemory)
    (em,sbExpr,u,Gu,tu) (op,bw) vs (ForArrayOwned av)
    H rs (fin with scopes := TL fin.scopes) G1 tn1 f
Proof
  strip_tac >> drule_all_then (qx_choose_then `suffix` assume_tac) restore_trace_append >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule valid_horizon_append >> qexists_tac `suffix` >>
     qpat_assum `fin.storage_trace = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!K. valid_horizon _ _ K _ ==> for_array_entry_route_mods _ _ _ _ _ _ _ _ K _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [for_array_entry_route_mods_def])) >>
  drule_then assume_tac restore_capture_frame >>
  drule_all_then strip_assume_tac restore_saved_frame >>
  drule_then assume_tac (cj 1 value_has_type_val_wf) >>
  qpat_x_assum `for_array_memory_backing_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [for_array_memory_backing_mods_def]) >>
  simp[for_array_entry_route_mods_def,for_array_memory_backing_mods_def] >>
  Cases_on `0 < type_memory_size (ArrayTV tv bd)` >-
    (qpat_x_assum `0 < _ ==> ?aid b sz. _`
       (drule_then (qx_choosel_then [`aid`,`b`,`sz`] strip_assume_tac)) >>
     `val_footprint (ArrayTV tv bd) (ArrayV av) <= type_memory_size (ArrayTV tv bd)` by
       (irule val_footprint_le >> first_assum ACCEPT_TAC) >>
     `w2n bw + val_footprint (ArrayTV tv bd) (ArrayV av) <= b+sz` by decide_tac >>
     qpat_assum `!tv. evaluate_type _ _ = SOME tv ==> _` (drule_then assume_tac) >>
     qpat_x_assum `!aid b sz rt av. _ ==> _` (drule_all_then strip_assume_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     disch_tac >> qexistsl_tac [`aid`,`b`,`sz`] >>
     ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (CONV_TAC (LAND_CONV (REWR_CONV ADD_COMM)) >> first_assum ACCEPT_TAC) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >> irule (cj 1 return_zero_wf_memory_mutual) >> simp[]
QED
