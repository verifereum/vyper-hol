Theory entryReachBodyCanonicalOccurrence
Ancestors
  externalEntryChecks actualDecoderPackaging actualRegistrationCode
  externalEntryShape compileEnv compileVyper moduleLowering fragExec list pair

(* A single occurrence supplies both the check boundary and registration. *)
Theorem entry_canonical_occurrence:
  MEM (lbl,ce,args,mincd,pay,nr,key,ut,iv,fbody,rt) packages /\
  compile_external_fn_bodies packages sd = ((),sx) ==>
  ?pre post opened checks start cenv registered body_end.
    packages = pre ++ (lbl,ce,args,mincd,pay,nr,key,ut,iv,fbody,rt)::post /\
    compile_external_fn_bodies pre sd = ((),opened) /\
    new_block lbl opened = (opened.cs_current_bb,checks) /\
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce args 4 start = (cenv,registered) /\
    compile_guarded_body cenv nr key ut iv fbody rt registered = ((),body_end) /\
    compile_external_fn_bodies post body_end = ((),sx) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    sd.cs_next_var <= checks.cs_next_var /\
    cs_extends start registered /\ cs_extends registered body_end /\
    cs_extends body_end sx
Proof
  strip_tac >> drule_all external_checks_occurrence >> strip_tac >>
  qpat_x_assum `compile_external_function_body _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_external_function_body_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `cs_extends st' cs'` by
    metis_tac[compile_register_positional_args_labels, pairTheory.SND] >>
  `cs_extends cs' sb` by
    metis_tac[compile_guarded_body_labels, pairTheory.SND] >>
  `cs_extends sb sx` by
    (qspecl_then [`post`,`sb`] mp_tac
      compile_external_fn_bodies_label_partition >> simp[]) >>
  qexistsl_tac [`pre`,`post`,`sa`,`st`,`st'`,`cenv'`,`cs'`,`sb`] >> simp[]
QED

Theorem entry_canonical_occurrence_code:
  MEM (lbl,ce,args,mincd,pay,nr,key,ut,iv,fbody,rt) packages /\
  ALL_DISTINCT (MAP FST packages) /\ ~isPREFIX "@" lbl /\
  ~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks sd)) /\
  compile_external_fn_bodies packages sd = ((),sx) /\
  cs_extends sx se /\ func.fn_blocks = all_blocks se /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se)) ==>
  ?checks start cenv registered body_end.
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce args 4 start = (cenv,registered) /\
    compile_guarded_body cenv nr key ut iv fbody rt registered = ((),body_end) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    sd.cs_next_var <= checks.cs_next_var /\
    cs_extends start registered /\ cs_extends registered body_end /\
    cs_extends body_end se /\
    fn_has_code checks start func /\ fn_has_code start body_end func /\
    fn_has_code registered body_end func /\
    (!inst. MEM inst (state_insts registered) ==> MEM inst (fn_insts func))
Proof
  strip_tac >> drule_all entry_canonical_occurrence >> strip_tac >>
  `cs_extends body_end se` by metis_tac[cs_extends_trans] >>
  `cs_extends start se` by metis_tac[cs_extends_trans] >>
  `~MEM lbl (MAP FST pre)` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `fn_has_code checks start func` by
    (drule_all external_checks_labels_unshadowed >> simp[]) >>
  `fn_has_code start body_end func` by
    (`cs_extends start start` by simp[cs_extends_refl] >>
     `cs_extends start body_end` by metis_tac[cs_extends_trans] >>
     mp_tac (Q.INST [`first` |-> `start`, `decoder_start` |-> `start`,
       `decoder_end` |-> `body_end`, `entry_end` |-> `se`]
       external_decoder_fn_has_code) >>
     simp[fn_has_code_def, venomInstTheory.mk_raw_function_def]) >>
  `fn_has_code registered body_end func` by
    metis_tac[fn_has_code_split] >>
  qexistsl_tac [`checks`,`start`,`cenv`,`registered`,`body_end`] >> simp[] >>
  gen_tac >> strip_tac >>
  `cs_extends registered se` by metis_tac[cs_extends_trans] >>
  `abi_decoder_code_member inst registered` by
    simp[decoder_code_member_state_insts] >>
  drule_all external_phase_decoder_owned >>
  simp[venomInstTheory.fn_insts_def, venomInstTheory.mk_raw_function_def]
QED
