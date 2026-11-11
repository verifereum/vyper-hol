(* Exact parameter-slot metadata at the internal-call entry boundary. *)
Theory bodyIntCallFamCallIntEntryPackage
Ancestors
  compileVyper compileEnv list entryStateRel intCallCallee
  entryArgPtrs vyperCall stmtSimReturn exprSimProps exprLoweringProps
  bodyIntCallJointContract loweringSlice abiCallerAllocation

Theorem intcall_build_env_parameter_slots:
  ALL_DISTINCT (MAP FST args) /\
  ce = build_compile_env tops vis mut name args ret code_stmts tr ==>
  EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) args
Proof
  strip_tac >>
  `ce.ce_vars = FST (allocate_args
      (get_struct_fields (make_struct_fields_map tops)) args 0 FEMPTY) /\
   ce.ce_struct_fields = make_struct_fields_map tops` by
    (gvs[] >> simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
  drule allocate_args_lookup >>
  disch_then (qspecl_then
    [`get_struct_fields (make_struct_fields_map tops)`, `0`, `FEMPTY`]
    strip_assume_tac) >>
  gvs[GSYM type_mem_bytes_type_memory_bytes]
QED

Theorem intcall_package_parameter_metadata:
  package_internal_fn tops tr keys ctor imm
    (mut,nr,rr,name,args,dflts,ret,code_stmts) =
    (lbl,ce,params,rb,is_nr,nkey,use_tr,is_view,is_ctor,imm_len,code_stmts',ret_type) /\
  ALL_DISTINCT (MAP FST args) ==>
  params = ZIP (MAP FST args,
    compute_pass_via_stack (MAP SND args)
      (returns_stack_count
        (\n. MAP (FST o SND)
          (get_struct_fields (make_struct_fields_map tops) n)) ret)) /\
  MAP FST params = MAP FST args /\
  EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) args
Proof
  strip_tac >>
  gvs[package_internal_fn_def, update_cenv_nonreentrant_def] >>
  simp[MAP_ZIP, LENGTH_compute_pass_via_stack] >>
  simp[GSYM type_mem_bytes_type_memory_bytes] >>
  irule (SRULE [GSYM type_mem_bytes_type_memory_bytes]
    intcall_build_env_parameter_slots) >> simp[]
QED

(* Bind source values to slots without exposing scope entries to consumers. *)
Theorem intcall_bound_arguments_rel:
  !tenv args values penv flags base argv ce frontier mem.
  bind_arguments tenv args values = SOME penv /\
  ALL_DISTINCT (MAP FST args) /\ LENGTH flags = LENGTH args /\
  (base:num) + LENGTH args <= LENGTH (argv:bytes32 list) /\ LENGTH argv < dimword (:256) /\
  (!i. i < LENGTH args ==>
    ?tv off. evaluate_type tenv (SND (EL i args)) = SOME tv /\
      FLOOKUP ce.ce_vars (FST (EL i args)) =
        SOME (MemLoc off (type_memory_size tv)) /\
      (if EL i flags then
         is_word_type (SND (EL i args)) /\
         value_has_type tv (EL i values) /\
         EL (base+i) argv = typed_val_to_w256 tv (EL i values)
       else w2n (EL (base+i) argv) + type_memory_size tv <= frontier /\
         val_in_memory tv (EL i values) (w2n (EL (base+i) argv)) mem)) /\
  (!i j ti tj. i < LENGTH args /\ j < LENGTH args /\ i <> j /\
    ~EL i flags /\ ~EL j flags /\
    evaluate_type tenv (SND (EL i args)) = SOME ti /\
    evaluate_type tenv (SND (EL j args)) = SOME tj ==>
    regions_disjoint (w2n (EL (base+i) argv)) (type_memory_size ti)
      (w2n (EL (base+j) argv)) (type_memory_size tj)) ==>
  internal_args_rel ce (ZIP (MAP FST args,flags)) penv base argv frontier mem
Proof
  rpt gen_tac >> strip_tac >>
  simp[internal_args_rel_def, MAP_ZIP, EL_ZIP, EL_MAP] >>
  conj_tac >- metis_tac[bind_arguments_fdom] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!i. i < LENGTH args ==> _` (drule_then strip_assume_tac) >>
      drule_all bind_arguments_lookup_index >> strip_tac >> gvs[] >>
      drule_all bind_arguments_memory_wf >> strip_tac >>
      goal_assum (drule_at Any) >> simp[] >>
      Cases_on `EL i flags` >> gvs[] >>
      conj_tac
      >- (drule_all stmtSimReturnTheory.word_type_sizes >> simp[]) >>
      rpt strip_tac >> irule (iffRL exprSimPropsTheory.val_in_memory_word) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[EL_ZIP, EL_MAP] >>
  qpat_assum `!i. i < LENGTH args ==> ?tv off. _`
    (qspec_then `i` (strip_assume_tac o UNDISCH)) >>
  qpat_assum `!i. i < LENGTH args ==> ?tv off. _`
    (qspec_then `j` (strip_assume_tac o UNDISCH)) >>
  gvs[] >> metis_tac[]
QED

Theorem intcall_package_module_agreement:
  !tops tr keys imm mut nr rr name args dflts ret code_stmts
   lbl ce params rb is_nr nkey use_tr is_view is_ctor imm_len code_stmts' rt caller.
  package_internal_fn tops tr keys caller.ce_is_ctor imm
    (mut,nr,rr,name,args,dflts,ret,code_stmts) =
    (lbl,ce,params,rb,is_nr,nkey,use_tr,is_view,is_ctor,imm_len,code_stmts',rt) /\
  cenv_module_pins tops caller ==>
  ce.ce_module_vars = caller.ce_module_vars /\
  ce.ce_module = caller.ce_module /\ ce.ce_is_ctor = caller.ce_is_ctor
Proof
  rpt gen_tac >>
  simp[package_internal_fn_def, update_cenv_nonreentrant_def,
       cenv_module_pins_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem intcall_package_empty_state:
  !tops tr keys imm mut nr rr name args dflts ret code_stmts
   lbl ce params rb is_nr nkey use_tr is_view is_ctor imm_len code_stmts' rt
   caller func cx es s.
  package_internal_fn tops tr keys caller.ce_is_ctor imm
    (mut,nr,rr,name,args,dflts,ret,code_stmts) =
    (lbl,ce,params,rb,is_nr,nkey,use_tr,is_view,is_ctor,imm_len,code_stmts',rt) /\
  cenv_module_pins tops caller /\ state_rel func caller cx es s ==>
  state_rel func ce cx (es with scopes := []) s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_package_module_agreement >> strip_tac >>
  drule state_rel_scopes_nil >> strip_tac >>
  irule state_rel_cenv_cong >> qexists_tac `caller` >>
  simp[vyperStateTheory.lookup_scopes_def]
QED

Theorem intcall_state_immutable_regions:
  !ctx func ce cx es s.
  stmt_state_rel ctx func ce cx es s ==>
  internal_immutable_regions ce cx es s.vs_alloca_next
Proof
  simp[stmt_state_rel_def, state_rel_def, internal_immutable_regions_def,
       immutable_alloca_sep_def, immutables_rel_def] >>
  metis_tac[cj 1 immutable_admissible_val_wf]
QED

Theorem intcall_alloca_subregion_immutable_sep:
  !func ce cx es s inst b len p k.
  immutable_alloca_sep func ce cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,len) /\
  b <= p /\ p+k <= b+len ==>
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint io (type_memory_size tv) p k)
Proof
  rpt gen_tac >> simp[immutable_alloca_sep_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[regions_disjoint_def] >> strip_tac >>
  qpat_x_assum `!inst' b' sz. _` (qspec_then `inst` mp_tac) >>
  simp[] >> decide_tac
QED

Theorem intcall_package_immutable_regions:
  !tops tr keys imm mut nr rr name args dflts ret code_stmts
   lbl ce params rb is_nr nkey use_tr is_view is_ctor imm_len code_stmts' rt
   caller ctx func cx es s.
  package_internal_fn tops tr keys caller.ce_is_ctor imm
    (mut,nr,rr,name,args,dflts,ret,code_stmts) =
    (lbl,ce,params,rb,is_nr,nkey,use_tr,is_view,is_ctor,imm_len,code_stmts',rt) /\
  cenv_module_pins tops caller /\ stmt_state_rel ctx func caller cx es s ==>
  internal_immutable_regions ce cx es s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_package_module_agreement >> strip_tac >>
  drule intcall_state_immutable_regions >>
  simp[internal_immutable_regions_def]
QED

Theorem intcall_parameter_slot_provenance:
  !ce args flags params base argv s func lo hi.
  params = ZIP (MAP FST args,flags) /\ LENGTH flags = LENGTH args /\
  EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) args /\
  (!i. i < LENGTH args /\ ~EL i flags ==>
    ?aid off len inst.
      FLOOKUP s.vs_allocas aid = SOME (off,len) /\
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
      lo <= aid /\ aid < hi /\ off <= w2n (EL (base+i) argv) /\
      w2n (EL (base+i) argv) + type_memory_bytes ce (SND (EL i args)) <= off+len) ==>
  !i po psz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
    ?aid off len.
      FLOOKUP s.vs_allocas aid = SOME (off,len) /\
      (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid) /\
      lo <= aid /\ aid < hi /\ off <= w2n (EL (base+i) argv) /\
      w2n (EL (base+i) argv) + psz <= off+len
Proof
  rpt gen_tac >> strip_tac >> gvs[EVERY_EL] >>
  rpt strip_tac >> gvs[EL_ZIP, EL_MAP] >>
  qpat_x_assum `!n. n < LENGTH args ==> _`
    (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> metis_tac[]
QED

Theorem intcall_alloca_subregions_disjoint:
  !s id other b sz q len p n r k.
  alloca_inv s /\ id <> other /\
  FLOOKUP s.vs_allocas id = SOME (b,sz) /\
  FLOOKUP s.vs_allocas other = SOME (q,len) /\
  b <= p /\ p+n <= b+sz /\ q <= r /\ r+k <= q+len ==>
  compileEnv$regions_disjoint p n r k
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_caller_allocation_separate >>
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED
