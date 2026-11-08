(* Selected-frame resources, derived rather than assumed at return sites. *)
Theory externalReturnSelectedResources
Ancestors externalReturnPackage e2eDefs externalReturnPlan externalReturnConsumerProbe externalReturnBufferlessAlloc
  typedCopyProducer externalReturnCopyRecursive exprSimHypsDefs bodySim compileVyper compileEnv words

Theorem return_selected_consumer_resources:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv ce ==>
  ce.ce_raw_return = rr /\ ce.ce_type_env = type_env tops /\
  ce.ce_struct_fields = make_struct_fields_map tops /\
  ce.ce_nonreentrant = (F,nkey,F,mut = View) /\
  ce.ce_is_external /\ ~ce.ce_is_ctor /\ ce.ce_return_pc = NONE /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  type_memory_bytes ce ret < dimword (:256) /\
  (?tv. evaluate_type (type_env tops) ret = SOME tv) /\
  (ret <> NoneT ==>
    abi_enc_plan (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) ce.ce_ret_enc_info /\
    vyper_abi_size_bound (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) <= ce.ce_max_return_size)
Proof
  strip_tac >> drule_all return_selected_same_frame_mode >> strip_tac >>
  `type_memory_bytes ce ret < 2 ** 64` by
    (irule return_selected_lookup_size >> metis_tac[]) >>
  `acyclic_struct_metadata ce.ce_struct_fields` by
    (gvs[source_typing_ok_def] >>
     drule_all supported_checked_struct_metadata_acyclic >> simp[]) >>
  `?tv. evaluate_type (type_env tops) ret = SOME tv` by
    (drule_all return_selected_type_evaluates >> simp[]) >>
  simp[] >> conj_tac
  >- (fs[dimword_def] >> decide_tac) >>
  strip_tac >> drule_all return_selected_plan >> strip_tac >>
  drule_all return_consumer_frame_metadata >> simp[]
QED

Theorem return_site_output_buffer_bound:
  stmt_exprs_ok ce (Return (SOME e)) /\ ce.ce_is_external /\
  ~ce.ce_raw_return ==>
  ce.ce_max_return_size < dimword (:256)
Proof
  simp[stmt_exprs_ok_def, stmt_valued_return_def, return_buffer_ok_def,
    dimword_def] >> rpt strip_tac >> gvs[]
QED

Theorem return_site_copy_metadata:
  expr_sim_inv ce cx env es ==>
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields)
Proof
  simp[expr_sim_inv_def] >> rpt strip_tac >> simp[]
QED

(* Relate the compiler allocation size to the semantic destination layout.
   Together with return_selected_consumer_resources this discharges the two
   size premises of return_consumer_located_normalize. *)
Theorem return_site_memory_size:
  expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_bytes ce ty = type_memory_size tv
Proof
  strip_tac >> drule return_site_copy_metadata >> strip_tac >>
  irule return_copy_memory_size >> goal_assum (drule_at Any) >>
  rpt strip_tac >> metis_tac[]
QED
