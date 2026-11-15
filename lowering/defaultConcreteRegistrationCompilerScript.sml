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


Theorem default_registration_compiler_advance:
  default_registration_invariant tops cx ctx fn site k initial ce0 start
    args all_tvs specs cef sa ce st off
    ((name,prim,dyn,sz,info)::rest) (tv::tvs) s G tn owners /\
  DROP (LENGTH owners) args = (name,ty)::tail /\
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (ce1,st1) ==>
  ?p.
    ce1 = ce with ce_vars updated_by
      (\m. m |+ (name,PtrVar (Var p) (type_memory_size tv))) /\
    ~not_fresh_at st p /\ not_fresh_at st1 p /\
    cs_extends st st1 /\ cs_extends st1 sa /\
    default_registration_ptr_reservation ce1 st1 /\
    compile_register_positional_args ce0 (TAKE (SUC (LENGTH owners)) specs)
      4 start = (ce1,st1) /\
    compile_register_positional_args ce1 rest (off+sz) st1 = (cef,sa) /\
    LIST_REL (default_registration_slot tops ce1) (ZIP (tail,tvs)) rest /\
    FDOM ce1.ce_vars = set (MAP FST args) /\
    (!n. n <> name ==> FLOOKUP ce1.ce_vars n = FLOOKUP ce.ce_vars n) /\
    FLOOKUP ce1.ce_vars name = SOME (PtrVar (Var p) (type_memory_size tv)) /\
    (!n. MEM n (MAP FST (TAKE (LENGTH owners) args)) ==>
      FLOOKUP ce1.ce_vars n = FLOOKUP ce.ce_vars n) /\
    ce1.ce_module = ce.ce_module /\ ce1.ce_is_ctor = ce.ce_is_ctor /\
    ce1.ce_imm_alloca = ce.ce_imm_alloca /\
    ce1.ce_return_pc = ce.ce_return_pc /\ ce1.ce_return_buf = ce.ce_return_buf /\
    ce1.ce_struct_fields = ce.ce_struct_fields
Proof
  strip_tac >>
  `off = 4 + SUM (MAP (\(name,prim,dyn,sz,info). sz)
    (TAKE (LENGTH owners) specs))` by
      (irule default_registration_invariant_prefix_size >> goal_assum drule) >>
  `compile_register_positional_args ce0 (TAKE (SUC (LENGTH owners)) specs)
    4 start = (ce1,st1)` by
    (irule default_registration_prefix_advance >>
     fs[default_registration_invariant_def] >> metis_tac[]) >>
  `compile_register_positional_args ce1 rest (off+sz) st1 = (cef,sa) /\
   cs_extends st st1 /\ cs_extends st1 sa` by
    (fs[default_registration_invariant_def] >>
     qpat_assum `compile_register_positional_args ce (_::rest) _ st = (cef,sa)`
       (mp_then Any mp_tac default_registration_singleton_suffix) >>
     disch_then (qspecl_then [`st1`,`ce1`] mp_tac) >> simp[]) >>
  fs[default_registration_invariant_def] >>
  `?old. FLOOKUP ce.ce_vars name = SOME (MemLoc old (type_memory_size tv))` by
    fs[default_registration_slot_def] >>
  `LENGTH tail = LENGTH tvs` by
    (qpat_assum `DROP (LENGTH owners) args = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     qpat_assum `tv::tvs = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `ALL_DISTINCT (name::MAP FST tail)` by
    (qpat_assum `ALL_DISTINCT (MAP FST args)`
       (mp_then Any mp_tac ALL_DISTINCT_DROP) >>
     disch_then (qspec_then `LENGTH owners` mp_tac) >>
     simp[GSYM MAP_DROP]) >>
  `~MEM name (MAP FST (TAKE (LENGTH owners) args))` by
    (qspec_then `MAP FST args` mp_tac rich_listTheory.ALL_DISTINCT_TAKE_DROP >>
     simp[] >> disch_then (qspecl_then [`LENGTH owners`,`name`] mp_tac) >>
     simp[GSYM MAP_TAKE, GSYM MAP_DROP]) >>
  drule_all default_registration_singleton_update >> strip_tac >>
  qexists `p` >> simp[] >>
  gvs[default_registration_vars_update] >>
  simp[FLOOKUP_UPDATE] >>
  conj_tac >- (irule default_registration_slots_vars >> simp[]) >>
  conj_tac
  >- gvs[pred_setTheory.ABSORPTION, FLOOKUP_DEF] >>
  metis_tac[]
QED
