(* Indexed decomposition keeps compiler endpoints from the whole registration. *)
Theory entryReachBodyRegistrationIndexedShell
Ancestors
  entryReachBodyCallerResources actualRegistrationCode entryReachBodyPackageAlignment
  abiCanonicalHeadSize compileVyper compileEnv list rich_list arithmetic fragExec emitHelperProps

Theorem entry_indexed_registration_boundaries:
  compile_register_positional_args ce pos 4 st = (cef,last) /\
  i < LENGTH pos ==>
  ?cei sti cei1 sti1.
    compile_register_positional_args ce (TAKE i pos) 4 st = (cei,sti) /\
    compile_register_positional_args cei [EL i pos]
      (4 + SUM (MAP (\(name,prim,dyn,sz,info). sz) (TAKE i pos))) sti = (cei1,sti1) /\
    compile_register_positional_args cei1 (DROP (SUC i) pos)
      (4 + SUM (MAP (\(name,prim,dyn,sz,info). sz) (TAKE i pos)) +
       (\(name,prim,dyn,sz,info). sz) (EL i pos)) sti1 = (cef,last) /\
    cs_extends st sti /\ cs_extends sti sti1 /\ cs_extends sti1 last
Proof
  strip_tac >>
  `pos = TAKE i pos ++ EL i pos :: DROP (SUC i) pos` by
    metis_tac[TAKE_DROP_SUC, APPEND_ASSOC, APPEND] >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  metis_tac[register_selected_arg_boundaries]
QED

Theorem entry_descriptor_prefix_offset:
  LENGTH pos = LENGTH tys /\ i <= LENGTH tys /\
  (!j. j < LENGTH tys ==>
    (\(name,prim,dyn,sz,info). sz) (EL j pos) = abi_member_head_size (EL j tys)) ==>
  SUM (MAP (\(name,prim,dyn,sz,info). sz) (TAKE i pos)) =
    SUM (MAP abi_member_head_size (TAKE i tys))
Proof
  strip_tac >> AP_TERM_TAC >> irule LIST_EQ >>
  simp[LENGTH_MAP, LENGTH_TAKE] >> rpt strip_tac >>
  simp[EL_MAP, EL_TAKE]
QED

Theorem entry_selected_prefix_offset:
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME scope /\
  set_external_package_target target
    (package_external_fn tops F keys
      (mut,F,raw,tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pos,cds,pay,F,key,ut,view,fbody,rt) /\
  compile_register_positional_args ce pos 4 st = (cef,last) /\
  i <= LENGTH args ==>
  SUM (MAP (\(name,prim,dyn,sz,info). sz) (TAKE i pos)) =
    SUM (MAP abi_member_head_size
      (TAKE i (MAP (vyper_to_abi_type (type_env tops)) (MAP SND args))))
Proof
  strip_tac >> drule entry_runtime_package_layout >> strip_tac >>
  `LENGTH pos = LENGTH args` by simp[build_positional_args_def] >>
  qpat_x_assum `pos = _` kall_tac >>
  irule entry_descriptor_prefix_offset >> simp[] >>
  qx_gen_tac `j` >> strip_tac >>
  `j < LENGTH pos` by simp[] >>
  drule_all entry_indexed_registration_boundaries >> strip_tac >>
  drule_all entry_selected_indexed_metadata >> strip_tac >>
  simp[EL_MAP]
QED

Theorem entry_indexed_registration_code:
  compile_register_positional_args ce pos 4 st = (cef,last) /\
  cs_extends last final /\ last.cs_next_var <= final.cs_next_var /\
  fn_has_code st final fn /\
  i < LENGTH pos ==>
  ?cei sti cei1 sti1.
    compile_register_positional_args ce (TAKE i pos) 4 st = (cei,sti) /\
    compile_register_positional_args cei [EL i pos]
      (4 + SUM (MAP (\(name,prim,dyn,sz,info). sz) (TAKE i pos))) sti = (cei1,sti1) /\
    compile_register_positional_args cei1 (DROP (SUC i) pos)
      (4 + SUM (MAP (\(name,prim,dyn,sz,info). sz) (TAKE i pos)) +
       (\(name,prim,dyn,sz,info). sz) (EL i pos)) sti1 = (cef,last) /\
    fn_has_code st sti fn /\ fn_has_code sti sti1 fn /\
    fn_has_code sti1 last fn /\ fn_has_code last final fn /\
    sti.cs_next_var <= final.cs_next_var /\
    sti1.cs_next_var <= final.cs_next_var
Proof
  strip_tac >> drule_all entry_indexed_registration_boundaries >> strip_tac >>
  `cs_extends st last` by metis_tac[cs_extends_trans] >>
  `cs_extends sti last /\ cs_extends sti final /\ cs_extends sti1 final` by
    metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code st sti fn /\ fn_has_code sti last fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code sti sti1 fn /\ fn_has_code sti1 last fn` by metis_tac[fn_has_code_split] >>
  qexistsl_tac [`cei`, `sti`, `cei1`, `sti1`] >> simp[] >>
  imp_res_tac externalEntryChecksTheory.compile_register_positional_args_next_var >>
  decide_tac
QED

Theorem entry_selected_indexed_shell:
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME scope /\
  set_external_package_target target
    (package_external_fn tops F keys
      (mut,F,raw,tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pos,cds,pay,F,key,ut,view,fbody,rt) /\
  compile_register_positional_args ce pos 4 st = (cef,last) /\
  compile_guarded_body cef F key ut view fbody rt last = ((),final) /\
  fn_has_code st final fn /\ i < LENGTH args ==>
  ?cei sti cei1 sti1.
    compile_register_positional_args ce (TAKE i pos) 4 st = (cei,sti) /\
    compile_register_positional_args cei [EL i pos]
      (4 + SUM (MAP abi_member_head_size
        (TAKE i (MAP (vyper_to_abi_type (type_env tops)) (MAP SND args))))) sti = (cei1,sti1) /\
    compile_register_positional_args cei1 (DROP (SUC i) pos)
      (4 + SUM (MAP abi_member_head_size
        (TAKE i (MAP (vyper_to_abi_type (type_env tops)) (MAP SND args)))) +
       (\(name,prim,dyn,sz,info). sz) (EL i pos)) sti1 = (cef,last) /\
    fn_has_code st sti fn /\ fn_has_code sti sti1 fn /\
    fn_has_code sti1 last fn /\ fn_has_code last final fn /\
    sti.cs_next_var <= final.cs_next_var /\
    sti1.cs_next_var <= final.cs_next_var
Proof
  strip_tac >>
  `cs_extends last final` by
    (mp_tac externalEntryShapeTheory.compile_guarded_body_labels >>
     disch_then (qspecl_then [`cef`, `F`, `key`, `ut`, `view`, `fbody`, `rt`, `last`] mp_tac) >>
     simp[]) >>
  `last.cs_next_var <= final.cs_next_var` by
    (mp_tac (GEN_ALL (SRULE [abiDecoderCountersTheory.abi_decoder_vars_mono_def]
       externalEntryChecksTheory.compile_guarded_body_vars_mono)) >>
     metis_tac[pairTheory.SND]) >>
  `LENGTH pos = LENGTH args` by
    (drule entry_runtime_package_layout >> simp[build_positional_args_def]) >>
  `i <= LENGTH args` by decide_tac >>
  drule_all entry_selected_prefix_offset >> disch_tac >>
  `i < LENGTH pos` by simp[] >>
  drule_all entry_indexed_registration_code >> simp[]
QED
