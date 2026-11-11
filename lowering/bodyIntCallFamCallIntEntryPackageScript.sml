(* Exact parameter-slot metadata at the internal-call entry boundary. *)
Theory bodyIntCallFamCallIntEntryPackage
Ancestors
  compileVyper compileEnv list entryStateRel intCallCallee
  entryArgPtrs vyperCall stmtSimReturn exprSimProps

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
