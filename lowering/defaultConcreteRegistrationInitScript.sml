(* Source/compiler initialization and singleton staging for exact registration. *)
Theory defaultConcreteRegistrationInit
Ancestors defaultConcreteRegistrationDefs calldataRegistrationExec entryArgPtrs
  calldataSourceSize calldataRegistration compileVyper compileEnv moduleLowering
  abiDecoderCoherence entryStateRel entryExternalPackageCoherence
  list finite_map words pred_set option

Theorem default_registration_initial_slots:
  !args tvs.
  LIST_REL (\(name,ty) tv.
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
    (is_word_type ty \/ is_bytestring_type ty) /\
    ?p. FLOOKUP ce.ce_vars name = SOME (MemLoc p (type_memory_size tv))) args tvs ==>
  LIST_REL (default_registration_slot tops ce) (ZIP (args,tvs))
    (build_positional_args ce args)
Proof
  Induct >> Cases_on `tvs` >> simp[build_positional_args_def] >>
  gen_tac >> PairCases_on `h'` >> simp[build_positional_arg_def] >>
  rpt strip_tac >> simp[default_registration_slot_def] >>
  metis_tac[calldata_coherent_embedded_size, build_positional_args_def]
QED

Theorem default_registration_initial_domain:
  (!n. MEM n (MAP FST args) ==>
     ?p sz. FLOOKUP ce.ce_vars n = SOME (MemLoc p sz)) /\
  (!n loc. FLOOKUP ce.ce_vars n = SOME loc ==> MEM n (MAP FST args)) ==>
  FDOM ce.ce_vars = set (MAP FST args) /\
  default_registration_ptr_reservation ce st
Proof
  simp[default_registration_ptr_reservation_def] >> strip_tac >>
  conj_tac >- (simp[EXTENSION, cj 1 TO_FLOOKUP] >>
    gen_tac >> Cases_on `FLOOKUP ce.ce_vars x` >> gvs[] >>
    strip_tac >> first_x_assum drule >> simp[]) >>
  rpt strip_tac >>
  `MEM n1 (MAP FST args)` by metis_tac[] >>
  metis_tac[var_location_distinct, optionTheory.SOME_11]
QED

Theorem default_registration_singleton_stages:
  FLOOKUP ce.ce_vars name = SOME (MemLoc p msz) /\
  (prim ==> ?c. info = DecPrimWord c) /\
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (cef,decoded) ==>
  ?buf allocated head after_head src first.
    compile_alloc_buffer msz st = (buf,allocated) /\
    cef = ce with ce_vars updated_by (\m. m |+ (name,PtrVar buf.buf_operand msz)) /\
    emit_op ADD [Lit 4w; Lit (n2w (off-4))] allocated = (head,after_head) /\
    (if dyn /\ ~prim then
       ?offset after_load after_src.
         emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
         emit_op ADD [Lit 4w; offset] after_load = (src,after_src) /\
         compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) after_src = ((),first)
     else src = head /\ first = after_head) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w) (Lit 0w)
      info first = ((),decoded)
Proof
  strip_tac >> drule register_positional_args_step >>
  simp[var_location_memory_size_def, register_positional_args_nil] >>
  disch_then (fn th => fs[th, register_positional_args_nil]) >> gvs[] >>
  drule registration_decoder_prelude >>
  simp[FLOOKUP_UPDATE, var_location_decode_operand_def] >>
  strip_tac >> rpt (goal_assum $ drule_at Any) >> simp[combinTheory.APPLY_UPDATE_THM]
QED

Theorem default_registration_package_locations:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,fname,args,ds,ret,fbody)) =
    (lbl,ce,specs,mc,pay,nr',nk,ut,iv,stmts,rt) /\
  ALL_DISTINCT (MAP FST args) ==>
  EVERY (\a. ?p. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc p (type_memory_bytes ce (SND a)))) args /\
  FDOM ce.ce_vars = set (MAP FST args) /\
  default_registration_ptr_reservation ce st
Proof
  Cases_on `package_external_fn tops use_trans keys
    (mut,nr,rr,fname,args,ds,ret,fbody)` >> PairCases_on `r` >>
  simp[set_external_package_target_def] >> strip_tac >> gvs[] >>
  drule_all package_external_fn_vars >> strip_tac >>
  `type_memory_bytes (r0 with ce_target := target) = type_memory_bytes r0` by
    (irule type_memory_bytes_frame >> simp[]) >>
  simp[] >>
  `FDOM r0.ce_vars = set (MAP FST args) /\
   default_registration_ptr_reservation r0 st` suffices_by
    (simp[default_registration_ptr_reservation_def] >> metis_tac[]) >>
  irule default_registration_initial_domain >>
  gvs[EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD,
      pairTheory.EXISTS_PROD] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem default_registration_package_slots:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,fname,args,ds,ret,fbody)) =
    (lbl,ce,specs,mc,pay,nr',nk,ut,iv,stmts,rt) /\
  ALL_DISTINCT (MAP FST args) /\
  contract_namespaces_ok in_deploy [(NONE,tops)] /\
  LIST_REL (\(name,ty) tv.
    assignable_type (type_env tops) ty /\
    evaluate_type (type_env tops) ty = SOME tv /\
    (is_word_type ty \/ is_bytestring_type ty)) args tvs ==>
  LIST_REL (default_registration_slot tops ce) (ZIP (args,tvs)) specs
Proof
  strip_tac >>
  `!ty tv. assignable_type (type_env tops) ty /\
     evaluate_type (type_env tops) ty = SOME tv ==>
     abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv` by
    (rpt strip_tac >> drule_all external_package_decoder_coherent >> simp[]) >>
  drule external_package_layout >> strip_tac >>
  drule_all default_registration_package_locations >>
  disch_then (qspec_then `st` strip_assume_tac) >> gvs[] >>
  irule default_registration_initial_slots >>
  qpat_x_assum `LIST_REL _ args tvs` mp_tac >>
  qpat_x_assum `EVERY _ args` mp_tac >>
  map_every qid_spec_tac [`tvs`,`args`] >>
  Induct >> Cases_on `tvs` >> simp[] >> gen_tac >> PairCases_on `h'` >>
  simp[] >> strip_tac >> strip_tac >>
  `abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields h'1 h` by
    metis_tac[] >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >> simp[]
QED

(* Specialize empty-prefix initialization to a source package. Runtime resources
   are inputs: their independent construction is defaultEntryResourceInit. *)
Theorem default_registration_package_initial:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,fname,args,ds,ret,fbody)) =
    (lbl,ce,specs,mc,pay,nr',nk,ut,iv,stmts,rt) /\
  ALL_DISTINCT (MAP FST args) /\
  contract_namespaces_ok in_deploy [(NONE,tops)] /\
  LIST_REL (\(name,ty) tv.
    assignable_type (type_env tops) ty /\
    evaluate_type (type_env tops) ty = SOME tv /\
    (is_word_type ty \/ is_bytestring_type ty)) args tvs /\
  SUM (MAP tv_abi_size tvs) <= LENGTH (DROP 4 initial.vs_call_ctx.cc_calldata) /\
  LENGTH initial.vs_call_ctx.cc_calldata < dimword (:256) /\
  compile_register_positional_args ce specs 4 st = (cef,sa) /\
  fn_has_code st sa fn /\ cs_extends st sa /\
  default_registration_resources ctx fn site k st s tn /\
  default_registration_entry_frame initial s /\
  ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  immutable_section_layout ce tops ==>
  default_registration_invariant tops cx ctx fn site k initial ce st
    args tvs specs cef sa ce st 4 specs tvs s G tn []
Proof
  strip_tac >>
  drule_all default_registration_package_slots >> strip_tac >>
  drule_all default_registration_package_locations >>
  disch_then (qspec_then `st` strip_assume_tac) >>
  irule default_registration_invariant_initial >> simp[] >>
  `LENGTH args = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH specs = LENGTH args` by
    (drule LIST_REL_LENGTH >> simp[LENGTH_ZIP]) >>
  simp[] >>
  qpat_x_assum `LIST_REL _ args tvs` mp_tac >>
  match_mp_tac LIST_REL_mono >> simp[pairTheory.FORALL_PROD]
QED
