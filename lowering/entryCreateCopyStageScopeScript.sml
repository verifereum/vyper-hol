Theory entryCreateCopyStageScope
Ancestors
  dallocaCreateGeometry createSizeStraightPrefix createSizePreparationCode
  externalEntryShape builtinCreate compileEnv fragExec createSizeCutCode pair

(* The compiler's straight-line preparation ends at the actual dispatch cut. *)
Theorem copy_prepare_scope_layout[local]:
  compile_create_copy target amount salt rof sm = (result,sb) /\
  fn_has_code sm sb func ==>
  ?sc buf len.
    compile_create_dispatch buf len amount salt rof sc = (result,sb) /\
    fn_has_code sm sc func /\ fn_has_code sc sb func /\
    create_cut_code {} sm sc /\
    sc.cs_current_bb = sm.cs_current_bb /\
    sc.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sc /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sc)
Proof
  strip_tac >> drule_then strip_assume_tac create_copy_create_prefix >>
  `compile_create_dispatch buf len amount salt rof sc = (result,sb)` by
    (Cases_on `salt` >> fs[compile_create_dispatch_def, comp_bind_def]) >>
  drule_all_then strip_assume_tac create_copy_preparation_code >>
  `cs_extends sc sb` by metis_tac[compile_create_dispatch_labels,SND] >>
  `create_cut_code {} sm sc` by
    (irule (cj 5 create_preparation_cut_code) >> rpt (goal_assum (drule_at Any))) >>
  `fn_has_code sm sc func /\ fn_has_code sc sb func` by
    metis_tac[fn_has_code_split] >>
  qexistsl_tac [`sc`,`buf`,`len`] >> simp[]
QED
