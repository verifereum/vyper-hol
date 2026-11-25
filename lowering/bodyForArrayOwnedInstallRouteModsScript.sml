(* The owned Array capture uses the separated expression-age row certified
   by ownership, at both the length cursor and the installed header. *)
Theory bodyForArrayOwnedInstallRouteMods
Ancestors
  bodyForArrayEntryMods bodyForArrayHeaderInstallMods bodyFullTargetArrayLoad
  loweringPosts loweringStateRelDefs exprSimCopy vyperValue valueEncoding
  venomState finite_map words context ptrDiscipline

Theorem owned_region_reserved_frame[local]:
  local_ptrs_reserved c cut /\
  (!x. not_fresh_at cut x ==> lookup_var x t = lookup_var x r) ==>
  (local_region c scopes t nm b sz <=> local_region c scopes r nm b sz)
Proof
  strip_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
  first_x_assum irule >> fs[local_ptrs_reserved_def] >>
  first_x_assum (drule_then (qspecl_then [`name`,`sz`] mp_tac)) >> simp[]
QED

Theorem owned_raw_row[local]:
  vv_own c cx aty sa sb em (Value (ArrayV av)) vv r /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  read_result cx (Value (ArrayV av)) em = (INL (ArrayV av),em) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\ ~is_word_type aty /\
  eval_operand (vv_operand vv) r = SOME bw /\
  0 < type_memory_size (ArrayTV tv bd) ==>
  ?aid b sz. FLOOKUP r.vs_allocas aid = SOME (b,sz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    b <= w2n bw /\ w2n bw + type_memory_size (ArrayTV tv bd) <= b+sz /\
    (!nm lb lsz. local_region c em.scopes r nm lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  Cases_on `vv` >>
  gvs[vv_location_def,vv_operand_def,vv_own_def,expr_val_own_def,val_footprint_def] >>
  qexistsl [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem owned_length_operand_frame[local]:
  array_length_frame sb r Gr traw u Gu tu /\ copy_old_operand sb op ==>
  eval_operand op u = eval_operand op r
Proof
  Cases_on `op` >>
  simp[array_length_frame_def,copy_old_operand_def,eval_operand_def] >>
  strip_tac >>
  `r.vs_labels = u.vs_labels` by
    (qpat_assum `(_ with vs_vars := _) = r` (once_rewrite_tac o single o SYM) >> simp[]) >>
  simp[]
QED

Theorem owned_install_operand_frame[local]:
  for_array_install_frame_mods saL u Gu tu G tn t /\ copy_old_operand saL op ==>
  eval_operand op t = eval_operand op u /\ op_prov G op = op_prov Gu op
Proof
  Cases_on `op` >>
  simp[for_array_install_frame_mods_def,copy_old_operand_def,eval_operand_def,op_prov_def]
QED

Theorem for_array_owned_install_route_mods:
  evaluate_type (get_tenv cx) sty = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\ ~is_word_type aty /\
  vv_own c cx aty sa0 sbExpr em (Value (ArrayV av)) vv r /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  read_result cx (Value (ArrayV av)) em = (INL (ArrayV av),em) /\
  array_length_frame sbExpr r Gr traw u Gu tu /\
  local_ptrs_reserved c sbExpr /\ local_ptrs_reserved c saL /\
  copy_old_operand sbExpr (vv_operand vv) /\ copy_old_operand saL (vv_operand vv) /\
  eval_operand (vv_operand vv) u = SOME bw /\
  for_array_memory_backing_mods cx sty bd tv av (vv_operand vv) bw (u,Gu,tu) (t,tn) /\
  for_array_install_frame_mods saL u Gu tu G tn t ==>
  for_array_entry_route_mods c cx lo (sty,bd,LocMemory) (em,sbExpr,u,Gu,tu)
    (vv_operand vv,bw) vs (ForArrayOwned av) H vs em G tn t
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac owned_install_operand_frame >>
  simp[for_array_entry_route_mods_def] >> strip_tac >>
  drule_all_then assume_tac owned_length_operand_frame >>
  `eval_operand (vv_operand vv) r = SOME bw` by fs[] >>
  drule_all_then (qx_choosel_then [`aid`,`b`,`sz`] strip_assume_tac) owned_raw_row >>
  qpat_assum `array_length_frame _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [array_length_frame_def]) >>
  `u.vs_allocas = r.vs_allocas` by
    (qpat_assum `(_ with vs_vars := _) = r` (once_rewrite_tac o single o SYM) >> simp[]) >>
  qpat_assum `for_array_install_frame_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [for_array_install_frame_mods_def]) >>
  `FLOOKUP u.vs_allocas aid = SOME (b,sz)` by simp[] >>
  qexistsl [`aid`,`b`,`sz`] >> simp[] >>
  `!nm lb lsz. local_region c em.scopes u nm lb lsz <=>
               local_region c em.scopes r nm lb lsz` by
    (rpt gen_tac >> irule owned_region_reserved_frame >> qexists `sbExpr` >> simp[]) >>
  `!nm lb lsz. local_region c em.scopes t nm lb lsz <=>
               local_region c em.scopes u nm lb lsz` by
    (rpt gen_tac >> irule owned_region_reserved_frame >> qexists `saL` >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED
