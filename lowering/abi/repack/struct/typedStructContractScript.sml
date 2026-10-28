(* TOP-LEVEL: complete checked struct copies close their parent contract
   from the contracts of their actual metadata field types. The verified
   tuple-field copier supplies execution, layout and allocation frames. *)
Theory typedStructContract
Ancestors
  typedStructCode typedStructMemory typedStructMetadata typedCopyCompatibility
  typedCopyTypeContract typedCopyContract typedFieldsList typedFieldsContract checkedCopyAcyclic
  context compileEnv compileVyper vyperContext vyperTypeContract vyperTypeSystem vyperValue
  list pair combin

Theorem typed_copy_same_field_list:
  !tenv ctx func cenv tys.
    (!ty tv. MEM ty tys /\ evaluate_type tenv ty = SOME tv ==>
      typed_copy_type_contract ctx func cenv ty ty tv tv) ==>
    LIST_REL (\fty aty. !ftv atv.
      evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv ==>
      typed_copy_type_contract ctx func cenv fty aty ftv atv) tys tys
Proof
  MAP_EVERY qx_gen_tac [`tenv`, `ctx`, `func`, `cenv`] >> Induct_on `tys`
  >- simp[] >> qx_gen_tac `ty` >> DISCH_TAC >> simp_tac bool_ss [LIST_REL_def] >> conj_tac
  >- (MAP_EVERY qx_gen_tac [`ftv`, `atv`] >> strip_tac >>
      `ftv = atv` by fs[] >> pop_assum SUBST_ALL_TAC >>
      qpat_x_assum `!ty tv. _` (qspecl_then [`ty`, `atv`] mp_tac) >> simp[]) >>
  first_x_assum irule >> MAP_EVERY qx_gen_tac [`field_ty`, `field_tv`] >> strip_tac >>
  qpat_x_assum `!ty tv. _` (qspecl_then [`field_ty`, `field_tv`] mp_tac) >> simp[]
QED

Theorem typed_copy_type_contract_struct:
  !tops in_deploy layouts addr art ctx func cenv nsid tv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) (StructT nsid) = SOME tv /\
    (!field_ty field_tv.
      MEM field_ty (MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))) /\
      evaluate_type (type_env tops) field_ty = SOME field_tv ==>
      typed_copy_type_contract ctx func cenv field_ty field_ty field_tv field_tv) ==>
    typed_copy_type_contract ctx func cenv (StructT nsid) (StructT nsid) tv tv
Proof
  rpt gen_tac >> strip_tac >> drule_all evaluated_struct_copy_metadata >>
  disch_then (qx_choose_then `fields` (qx_choose_then `tvs` strip_assume_tac)) >>
  qpat_x_assum `tv = StructTV tvs` SUBST_ALL_TAC >>
  qpat_assum `get_struct_fields _ _ = fields`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq]) >> ASSUME_TAC eq) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    (asm_rewrite_tac [] >> drule_all checked_struct_metadata_acyclic >> simp[]) >>
  `event_arg_compatible_list (MAP (FST o SND) fields) (MAP (FST o SND) fields)` by
    simp[CONJUNCT2 event_arg_compatible_reflexive] >>
  mp_tac (Q.SPECL [`type_env tops`, `ctx`, `func`, `cenv`,
    `MAP (FST o SND) (fields : (string # type # num) list)`]
    typed_copy_same_field_list) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  simp_tac bool_ss [typed_copy_type_contract_def] >>
  MAP_EVERY qx_gen_tac [`dst`, `src`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  `compile_typed_copy_fields cenv dst src (MAP (FST o SND) fields) (MAP (FST o SND) fields) 0 0 cs = (ret,cs')` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [compile_typed_struct_dispatch, compile_struct_typed_copy_identical]) >>
  irule typed_fields_copy_contract_struct >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`]
    checked_compile_typed_fields_contract) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qspecl_then [`MAP (FST o SND) fields`, `MAP (FST o SND) fields`, `MAP SND tvs`, `MAP SND tvs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qspecl_then [`dst`, `src`, `0`, `0`, `cs`, `ret`, `cs'`] mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked recursive struct copy contract: " ^ name)
  end) (DB.thms "typedStructContract")
