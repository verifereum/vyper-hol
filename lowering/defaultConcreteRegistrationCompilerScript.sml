(* Static boundaries for one concrete registration slot. *)
Theory defaultConcreteRegistrationCompiler
Ancestors defaultConcreteRegistrationDefs defaultConcreteRegistrationInit
  actualRegistrationCode entryStateRel ctorRegisterArgs compileEnv entryArgPtrs moduleLowering
  finite_map list words

Theorem default_registration_singleton_suffix:
  compile_register_positional_args ce ((name,prim,dyn,sz,info)::rest) off st = (cef,sa) /\
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (ce1,st1) ==>
  compile_register_positional_args ce1 rest (off+sz) st1 = (cef,sa) /\
  cs_extends st st1 /\ cs_extends st1 sa
Proof
  strip_tac >>
  qspecl_then [`[(name,prim,dyn,sz,info)]`,`rest`]
    (fn th =>
      qpat_x_assum `compile_register_positional_args ce ((name,prim,dyn,sz,info)::rest) off st = (cef,sa)` mp_tac >>
      once_rewrite_tac [SRULE [] th]) register_positional_args_append >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[register_positional_args_suffix_extends]
QED

Theorem default_registration_slot_vars:
  ~ (name = other) ==>
  (default_registration_slot tops
     (ce with ce_vars := ce.ce_vars |+ (name,loc)) ((other,ty),tv) spec <=>
   default_registration_slot tops ce ((other,ty),tv) spec)
Proof
  PairCases_on `spec` >>
  simp[default_registration_slot_def, FLOOKUP_UPDATE,
       ctor_decoder_coherent_vars] 
QED

Theorem default_registration_slots_vars:
  !args tvs specs.
  LENGTH args = LENGTH tvs /\ ~MEM name (MAP FST args) /\
  LIST_REL (default_registration_slot tops ce) (ZIP (args,tvs)) specs ==>
  LIST_REL (default_registration_slot tops
    (ce with ce_vars := ce.ce_vars |+ (name,loc))) (ZIP (args,tvs)) specs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `specs` >> simp[] >>
  gen_tac >> rename1 `FST arg` >> PairCases_on `arg` >>
  simp[] >> strip_tac >>
  simp[default_registration_slot_vars] >> metis_tac[]
QED

Theorem default_registration_reservation_update:
  default_registration_ptr_reservation ce st /\
  (!v. not_fresh_at st v ==> not_fresh_at st1 v /\ v <> p) /\
  not_fresh_at st1 p ==>
  default_registration_ptr_reservation
    (ce with ce_vars := ce.ce_vars |+ (name,PtrVar (Var p) sz)) st1
Proof
  simp[default_registration_ptr_reservation_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem default_registration_prefix_advance:
  DROP n specs = head::rest /\
  off = 4 + SUM (MAP (\(name,prim,dyn,sz,info). sz) (TAKE n specs)) /\
  compile_register_positional_args ce0 (TAKE n specs) 4 start = (ce,st) /\
  compile_register_positional_args ce [head] off st = (ce1,st1) ==>
  compile_register_positional_args ce0 (TAKE (SUC n) specs) 4 start = (ce1,st1)
Proof
  strip_tac >>
  simp[rich_listTheory.TAKE_SUC, register_positional_args_append] >> gvs[]
QED

Theorem default_registration_slot_sizes:
  !args tvs specs.
  LENGTH args = LENGTH tvs /\
  LIST_REL (default_registration_slot tops ce) (ZIP (args,tvs)) specs ==>
  MAP (\(name,prim,dyn,sz,info). sz) specs = MAP tv_abi_size tvs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `specs` >> simp[] >>
  gen_tac >> rename1 `default_registration_slot _ _ (arg,tv) spec` >>
  PairCases_on `arg` >> PairCases_on `spec` >>
  simp[default_registration_slot_def] >> metis_tac[]
QED


Theorem default_registration_singleton_update:
  FLOOKUP ce.ce_vars name = SOME (MemLoc old msz) /\
  default_registration_ptr_reservation ce st /\
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (ce1,st1) ==>
  ?p.
    ce1 = ce with ce_vars updated_by (\m. m |+ (name,PtrVar (Var p) msz)) /\
    ~not_fresh_at st p /\ not_fresh_at st1 p /\
    cs_extends st st1 /\
    default_registration_ptr_reservation ce1 st1
Proof
  strip_tac >> drule register_positional_args_step >>
  simp[var_location_memory_size_def, register_positional_args_nil] >>
  disch_then (fn th => fs[th, register_positional_args_nil]) >> gvs[] >>
  drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >> gvs[] >>
  drule decode_args_suffix_extends >> strip_tac >>
  qexists `p` >> simp[] >>
  `cs_extends st st1` by metis_tac[cs_extends_trans] >>
  `sa.cs_next_var <= st1.cs_next_var` by
    (qmatch_asmsub_abbrev_tac `compile_decode_args updated _ _ _ _ _ _` >>
     qspecl_then [`[(name,prim,dyn,sz,info)]`,`updated`,`off`,
       `CALLDATALOAD`,`Lit 0w`,`4`,`sa`] mp_tac
       calldataRegistrationExecTheory.registration_decode_ci_mono >>
     simp[exprLoweringPropsTheory.ci_mono_def] >> gvs[]) >>
  `st.cs_next_var <= st1.cs_next_var` by decide_tac >>
  `not_fresh_at st1 p` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  simp[] >>
  qpat_x_assum `default_registration_ptr_reservation ce st` mp_tac >>
  qpat_x_assum `~not_fresh_at st p` mp_tac >>
  qpat_x_assum `not_fresh_at st1 p` mp_tac >>
  `st.cs_next_var <= st1.cs_next_var` by decide_tac >>
  pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  simp[default_registration_ptr_reservation_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem default_registration_vars_update:
  (ce with ce_vars updated_by (\m. m |+ (name,loc))) =
  (ce with ce_vars := ce.ce_vars |+ (name,loc))
Proof
  Cases_on `ce` >> simp[recordtype_compile_env_seldef_ce_vars_fupd_def]
QED

Theorem default_registration_slots_advance:
  LENGTH args = LENGTH tvs /\ ALL_DISTINCT (MAP FST args) /\
  LIST_REL (default_registration_slot tops ce) (ZIP (args,tvs))
    ((name,prim,dyn,sz,info)::rest) ==>
  LIST_REL (default_registration_slot tops
    (ce with ce_vars updated_by (\m. m |+ (name,loc))))
    (ZIP (TL args,TL tvs)) rest
Proof
  Cases_on `args` >> Cases_on `tvs` >> simp[] >>
  PairCases_on `h` >>
  simp[default_registration_slot_def] >> strip_tac >> gvs[] >>
  simp[default_registration_vars_update] >>
  irule default_registration_slots_vars >> simp[]
QED

