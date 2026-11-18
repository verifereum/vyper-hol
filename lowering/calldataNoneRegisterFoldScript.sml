(* A rejecting suffix may run any number of successful registrations first. *)
Theory calldataNoneRegisterFold
Ancestors calldataRegistrationExec calldataSourceSize actualRegistrationCode
  fragGasOriginPtrLoop vyperCalldata compileVyper list rich_list arithmetic

Theorem none_registration_decode_tail[local]:
  IS_SOME (calldata_decode_args cd [tv] ofs) /\
  calldata_decode_args cd (tv::tvs) ofs = NONE ==>
  calldata_decode_args cd tvs (ofs + tv_abi_size tv) = NONE
Proof
  simp[calldata_decode_args_def] >>
  qmatch_goalsub_abbrev_tac `cd_decode F cd tv p` >>
  Cases_on `p < 4` >> Cases_on `cd_decode F cd tv p` >>
  simp[AllCaseEqs()]
QED

Theorem none_registration_tail_metadata[local]:
  LIST_REL (\(n,ty) tv.
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars n = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  compile_register_positional_args ce [build_positional_arg ce (name,ty)] off st =
    (ce1,st1) /\ ~MEM name (MAP FST args) ==>
  LIST_REL (\(n,ty) tv.
    abi_decoder_coherent ce1 env ce1.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce1.ce_vars n = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs
Proof
  strip_tac >> drule registration_env_fields >> strip_tac >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  Cases_on `EL n args` >> rename1 `EL n args = (nm,t)` >> simp[] >>
  `name <> nm` by
    (strip_tac >> `MEM (nm,t) args` by metis_tac[EL_MEM] >>
     qpat_x_assum `~MEM _ _` mp_tac >>
     simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
  `FLOOKUP ce1.ce_vars nm = FLOOKUP ce.ce_vars nm` by
    (irule registration_unmentioned_binding >> goal_assum $ drule_at Any >>
     simp[build_positional_arg_def] >> metis_tac[]) >>
  qpat_x_assum `!n. n < LENGTH tvs ==> _` (qspec_then `n` mp_tac) >>
  simp[] >> strip_tac >>
  drule calldataRegistrationTheory.registration_coherent_env_cong >> simp[]
QED

(* R is the singleton's state/ghost resource interface. Compiler placement,
   unchanged calldata and the source cursor are managed by this fold. *)
Theorem none_registration_suffix_reject:
  (!ce st ce1 st1 name ty tv ofs s G tn.
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256) /\
    compile_register_positional_args ce [build_positional_arg ce (name,ty)]
      (4+ofs) st = (ce1,st1) /\ fn_has_code st st1 fn /\
    4+ofs+tv_abi_size tv <= LENGTH cd /\ 4+ofs+tv_abi_size tv < dimword (:256) /\
    s.vs_call_ctx.cc_calldata = cd /\ R st s G tn ==>
      (?z H u. z.vs_returndata = [] /\
        !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
          (s,G,tn) [] (Abort Revert_abort z,H,u)) \/
      (?v H u. IS_SOME (calldata_decode_args cd [tv] ofs) /\
        v.vs_call_ctx.cc_calldata = cd /\ R st1 v H u /\
        !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
          (s,G,tn) [] (OK v,H,u))) ==>
  !args tvs ce st cef last ofs s G tn.
    ALL_DISTINCT (MAP FST args) /\
    LIST_REL (\(n,ty) tv.
      abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
      (?loc. FLOOKUP ce.ce_vars n = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args tvs /\
    compile_register_positional_args ce (build_positional_args ce args)
      (4+ofs) st = (cef,last) /\ fn_has_code st last fn /\
    4+ofs+SUM (MAP tv_abi_size tvs) <= LENGTH cd /\
    4+ofs+SUM (MAP tv_abi_size tvs) < dimword (:256) /\
    calldata_decode_args cd tvs ofs = NONE /\
    s.vs_call_ctx.cc_calldata = cd /\ R st s G tn ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
      (s,G,tn) [] (Abort Revert_abort z,H,u)
Proof
  disch_then (mk_asm "step") >> Induct
  >- (Cases >> simp[calldata_decode_args_def]) >>
  qpat_x_assum `!tvs ce st cef last ofs s G tn. _` (mk_asm "ih") >>
  gen_tac >> PairCases_on `h` >> Cases >> simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `abi_decoder_coherent ce env _ ty tv` >>
  rename1 `~MEM name (MAP FST args)` >>
  `abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv` by
    metis_tac[calldata_coherent_embedded_size] >>
  qpat_x_assum `compile_register_positional_args ce _ _ st = _` mp_tac >>
  simp_tac std_ss [build_positional_args_def, MAP] >>
  once_rewrite_tac[SRULE [] (Q.SPEC `[build_positional_arg ce (name,ty)]`
    register_positional_args_append)] >>
  simp[GSYM build_positional_args_def, build_positional_arg_def, PULL_EXISTS] >>
  qx_gen_tac `ce1` >> qx_gen_tac `st1` >> strip_tac >>
  `compile_register_positional_args ce [build_positional_arg ce (name,ty)]
     (4+ofs) st = (ce1,st1)` by simp[build_positional_arg_def] >>
  `ce1.ce_struct_fields = ce.ce_struct_fields /\
   ce1.ce_flag_n_members = ce.ce_flag_n_members` by
    (drule registration_env_fields >> simp[]) >>
  `compile_register_positional_args ce1 (build_positional_args ce1 args)
     (4+(ofs+tv_abi_size tv)) st1 = (cef,last)` by
    (`build_positional_args ce1 args = build_positional_args ce args` by
       (irule build_positional_args_layout_cong >> simp[]) >> simp[]) >>
  `cs_extends st st1 /\ cs_extends st1 last` by
    metis_tac[register_positional_args_suffix_extends] >>
  `fn_has_code st st1 fn /\ fn_has_code st1 last fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  asm_x "step" (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `R _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  impl_tac >- (simp[] >> decide_tac) >>
  disch_then DISJ_CASES_TAC >- first_assum ACCEPT_TAC >>
  pop_assum (qx_choose_then `v` (qx_choose_then `H1` (qx_choose_then `u1` strip_assume_tac))) >>
  drule_all none_registration_decode_tail >> strip_tac >>
  drule_all none_registration_tail_metadata >> strip_tac >>
  asm_x "ih" (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `R _ v H1 u1`)) >>
  disch_then (drule_at (Pat `LIST_REL _ _ _`)) >>
  impl_tac >- (simp[] >> decide_tac) >>
  strip_tac >> qexistsl [`z`,`H`,`u`] >> simp[] >>
  metis_tac[gas_origin_ptr_path_trans]
QED
