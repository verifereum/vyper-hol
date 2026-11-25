Theory createSizeImmutableModuleTransportMods
Ancestors
  bodyFullPostsMods bodyInvSplit loweringStateRelDefs loweringPosts
  compileEnv valueEncodingDefs words arithmetic

Theorem immutable_holds_data_mods:
  immutable_frame_mods func ce cx es s /\ ~ce.ce_is_ctor /\
  immutable_holds_mods ce cx ty raw w es s' ==>
  ?rt v. evaluate_type (get_tenv cx) ty = SOME rt /\
         read_result cx raw es = (INL v,es) /\
         val_in_memory rt v (w2n w) s.vs_data_section
Proof
  rw[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_holds_mods_def, immutable_holds_def] >>
  qpat_x_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _` drule >>
  simp[immutables_rel_def] >> disch_then drule_all >> strip_tac >>
  gvs[sub_layout_def] >> first_x_assum drule >> strip_tac >>
  `off + k < dimword (:256)` by decide_tac >>
  gvs[arithmeticTheory.ADD_COMM]
QED
