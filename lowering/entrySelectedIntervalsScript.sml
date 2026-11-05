(* Unrestricted selected stmts intervals before internal compilation. *)
Theory entrySelectedIntervals
Ancestors
  entryRuntimePrefix entryCompileIntervals entryBodyBoundLabels
  loweringShapeDefs fragExec entryRuntimeSlice compileEnv moduleLowering

Theorem external_member_append_interval[local]:
  MEM (lbl,ce,args,cds,pay,nr,key,tr,view,stmts,rt) packages /\
  compile_external_fn_bodies packages start = ((),st_final) ==>
  ?sd cenv sa se.
    compile_register_positional_args ce args 4 sd = (cenv,sa) /\
    compile_guarded_body cenv nr key tr view stmts rt sa = ((),se) /\
    cs_extends start sa /\ cs_extends sa se /\ cs_extends se st_final
Proof
  strip_tac >> drule_all compile_external_fn_bodies_member >> strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_external_fn_bodies) >> strip_tac >>
  drule (SRULE [cs_appends_def] (cj 2 cs_appends_prims)) >> strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_entry_checks) >> strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_register_positional_args) >> strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_guarded_body) >> strip_tac >>
  qexistsl [`sd`, `cenv`, `sa`, `se`] >> simp[] >>
  metis_tac[cs_appends_def, cs_appends_external_fn_bodies, cs_extends_trans]
QED

Theorem runtime_pre_internal_endpoint:
  compile_generate_runtime sels exts ints fb Linear bc mb db ei start =
    ((),st_final) ==>
  ?entry_st ir.
    compile_generate_runtime sels exts [] fb Linear bc mb db ei start =
      ((),entry_st) /\
    compile_internal_fn_bodies ints entry_st = (ir,st_final)
Proof
  strip_tac >> drule compile_generate_runtime_linear_split >> strip_tac >>
  qexistsl [`entry_st`, `ir`] >> simp[] >>
  simp[compile_generate_runtime_def, compile_internal_fn_bodies_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem runtime_selected_append_interval:
  compile_generate_runtime sels exts ints fb Linear bc mb db ei start =
    ((),st_final) /\
  MEM (lbl,ce,args,cds,pay,nr,key,tr,view,stmts,rt) exts ==>
  ?sd cenv sa se entry_st ir.
    compile_register_positional_args ce args 4 sd = (cenv,sa) /\
    compile_guarded_body cenv nr key tr view stmts rt sa = ((),se) /\
    cs_extends sa se /\ cs_extends se entry_st /\
    compile_generate_runtime sels exts [] fb Linear bc mb db ei start =
      ((),entry_st) /\
    compile_internal_fn_bodies ints entry_st = (ir,st_final)
Proof
  strip_tac >> drule runtime_pre_internal_endpoint >> strip_tac >>
  drule compile_generate_runtime_linear_split >> strip_tac >>
  gvs[compile_internal_fn_bodies_def, comp_return_def] >>
  drule_all external_member_append_interval >> strip_tac >>
  `cs_extends s3 entry_st` by
    (qspec_then `fallback_lbl` mp_tac
       (GEN_ALL cs_appends_runtime_fallback_suffix) >>
     simp[cs_appends_def, comp_ignore_bind_def, comp_bind_def] >>
     disch_then (qspecl_then [`fb`, `s3`, `entry_st`] mp_tac) >> simp[]) >>
  qexistsl [`sd`, `cenv`, `sa`, `se`] >> simp[] >>
  metis_tac[cs_extends_trans]
QED

Theorem runtime_pre_internal_jump_labels:
  compile_generate_runtime sels exts [] fb Linear bc mb db ei start =
    ((),entry_st) /\
  EVERY (\(lbl,ce,args,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl) exts /\
  EVERY jump_label_ok (MAP (\bb. bb.bb_label) (all_blocks start)) ==>
  EVERY jump_label_ok (MAP (\bb. bb.bb_label) (all_blocks entry_st))
Proof
  strip_tac >>
  mp_tac (Q.INST [`P` |-> `jump_label_ok`] bound_labels_runtime_linear_no_internals) >>
  (impl_tac >- simp[jump_label_ok_def]) >>
  disch_then drule_all >> metis_tac[pairTheory.SND]
QED
