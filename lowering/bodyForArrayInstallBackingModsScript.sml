(* Header allocation leaves the captured array's byte footprint intact. *)
Theory bodyForArrayInstallBackingMods
Ancestors
  bodyForArrayEntryMods bodyForArrayHeaderInstallMods bodyPtrDefs
  logValueFramePtr valueEncodingTyping loweringPosts words pred_set

Theorem for_array_install_backing_mods:
  evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV tv bd) /\
  eval_operand op u = SOME bw /\
  ptr_mem_ok cx (ArrayT sty bd) (ArrayV av) op Gu tu u /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  (0 < type_memory_size (ArrayTV tv bd) ==>
    w2n bw + type_memory_size (ArrayTV tv bd) <= u.vs_alloca_next) /\
  for_array_install_frame_mods saL u Gu tu G tn t ==>
  for_array_memory_backing_mods cx sty bd tv av op bw (u,Gu,tu) (t,tn)
Proof
  strip_tac >> simp[for_array_memory_backing_mods_def] >>
  `!m. mem_agree_outside tu.t_mem u.vs_memory m ==>
      val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) m` by
    (qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
      (qspecl_then [`ArrayTV tv bd`,`bw`] mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
     simp[]) >>
  qpat_x_assum `for_array_install_frame_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [for_array_install_frame_mods_def]) >>
  `val_wf (ArrayTV tv bd) (ArrayV av)` by
    metis_tac[value_has_type_val_wf] >>
  ho_match_mp_tac robust_val_in_memory_footprint_frame >>
  qexistsl [`tu.t_mem`,`u.vs_memory`] >> simp[val_footprint_def] >>
  rpt strip_tac >>
  `i < u.vs_alloca_next` by decide_tac >>
  qpat_assum `!j. j < u.vs_alloca_next ==> _`
    (drule_then (fn th => fs[th]))
QED
