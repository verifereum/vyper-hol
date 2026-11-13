Theory bodyCustomErrorWindowBounds
Ancestors
  abiEncoderSourceAggregate abiEncoderOpenInput abiEncoderWindow vyperABIValid
  abiTypeBoundProps exprSimHypsDefs loweringStateRelDefs typedMemoryCopy
  structFieldsProps bodySim vyperContext finite_map alist list
  externalReturnSelectedResources

Theorem custom_error_source_rep_window_bound:
  source_rep env ty ei ct /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_in_memory tv v p mem /\
  vyper_abi_size_bound env ty = abi_size_bound sf ty ==>
  ?rv. abi_encoder_window_input ei ct rv p (type_memory_size tv) mem /\
    enc ct rv = enc (vyper_to_abi_type env ty) av /\
    LENGTH (enc ct rv) <= abi_size_bound sf ty
Proof
  strip_tac >> drule_all source_rep_transport >> strip_tac >>
  drule_all abi_encoder_open_input_window >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_enc_le_size_bound) >> strip_tac >>
  qexists_tac `rv` >> simp[]
QED

Theorem custom_error_expr_inv_abi_bound:
  expr_sim_inv ce cx env es /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
  abi_size_bound ce.ce_struct_fields ty = vyper_abi_size_bound (get_tenv cx) ty
Proof
  strip_tac >> irule (cj 2 abi_props_vyper_typed) >>
  gvs[expr_sim_inv_def] >> metis_tac[]
QED

Theorem custom_error_main_modules_struct_keys:
  !mods k a. EVERY (\m. FST m = NONE) mods /\
    FLOOKUP (type_env_all_modules mods) k = SOME (StructArgs a) ==>
    FST k = NONE
Proof
  Induct_on `mods` >- simp[type_env_all_modules_def] >>
  Cases_on `h` >> simp[type_env_all_modules_def, FLOOKUP_FUNION] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule type_env_for_module_struct_mem >> strip_tac >> gvs[]
QED

Theorem custom_error_body_inv_struct_keys:
  body_inv tops ctx ce cx /\
    FLOOKUP (get_tenv cx) k = SOME (StructArgs a) ==> FST k = NONE
Proof
  strip_tac >>
  `!src ts. get_module_code cx src = SOME ts ==> src = NONE` by
    gvs[bodySimTheory.body_inv_def] >>
  qpat_x_assum `body_inv _ _ _ _` kall_tac >>
  Cases_on `ALOOKUP cx.sources cx.txn.target` >>
  gvs[get_tenv_def, get_module_code_def] >>
  irule custom_error_main_modules_struct_keys >>
  goal_assum (drule_at Any) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM (FST m) (MAP FST x)` by (simp[MEM_MAP] >> metis_tac[]) >>
  `ALOOKUP x (FST m) <> NONE` by simp[ALOOKUP_NONE] >>
  Cases_on `ALOOKUP x (FST m)` >> gvs[]
QED

Theorem custom_error_invariant_layout:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es ==>
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!k a. FLOOKUP (get_tenv cx) k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     abi_size_bound ce.ce_struct_fields ty = vyper_abi_size_bound (get_tenv cx) ty)
Proof
  strip_tac >> rpt conj_tac
  >- gvs[expr_sim_inv_def]
  >- metis_tac[custom_error_body_inv_struct_keys]
  >- metis_tac[return_site_memory_size] >>
  metis_tac[custom_error_expr_inv_abi_bound]
QED
