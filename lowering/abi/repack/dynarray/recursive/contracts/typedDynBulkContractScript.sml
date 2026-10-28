(* TOP-LEVEL: the checked bulk-copy case supplies the same typed contract
   as recursive array repacking, for arbitrary identical element types. *)
Theory typedDynBulkContract
Ancestors
  typedCopyContract typedDynLoopPrefix typedDynStoreProps typedSArrayDynSafety
  typedSArrayDynInvariant dynCopyCode checkedCopyAcyclic memoryValueDefs valueLoadProps valueEncoding
  context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem
  vyperValue fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem dynarray_copy_bulk_separated:
  !elem_tv src_capacity dst_capacity copy_count src_off dst_off.
    copy_count <= src_capacity /\
    (src_off + type_memory_size (ArrayTV elem_tv (Dynamic src_capacity)) <= dst_off \/
      dst_off + type_memory_size (ArrayTV elem_tv (Dynamic dst_capacity)) <= src_off) ==>
    (copy_count * type_memory_size elem_tv = 0 \/
      src_off + 32 + copy_count * type_memory_size elem_tv <= dst_off \/ dst_off <= src_off)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `copy_count * type_memory_size elem_tv <= src_capacity * type_memory_size elem_tv` by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `_ \/ _` mp_tac >> simp_tac bool_ss [type_memory_size_def] >> decide_tac
QED

Theorem checked_compile_typed_dynarray_bulk_contract:
  !tops in_deploy layouts addr art ctx func cenv dst elem_ty elem_tv dst_capacity src src_capacity cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) elem_ty = SOME elem_tv /\
    src_capacity <= dst_capacity /\ dst_capacity < dimword(:256) /\
    compile_store_memory_typed cenv dst (ArrayT elem_ty (Dynamic dst_capacity))
      src (ArrayT elem_ty (Dynamic src_capacity)) cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src (ArrayTV elem_tv (Dynamic dst_capacity))
      (ArrayTV elem_tv (Dynamic src_capacity)) cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    (asm_rewrite_tac [] >> drule_all checked_struct_metadata_acyclic >> simp[]) >>
  `compile_copy_dynarray_typed cenv dst elem_ty dst_capacity src elem_ty cs = (ret,cs')` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [compile_typed_dynarray_dispatch]) >>
  drule compile_copy_dynarray_code >> strip_tac >>
  asm_simp_tac (srw_ss()) [typed_copy_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `v`, `dst_addr`, `src_addr`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule value_has_type_dynarray_cases >> disch_then (qx_choose_then `vs` SUBST_ALL_TAC) >>
  drule array_copy_dynamic_values >> strip_tac >>
  `w2n dst_addr + 32 < dimword(:256) /\ w2n src_addr + 32 < dimword(:256)` by
    (qpat_x_assum `w2n dst_addr + type_memory_size _ < _` mp_tac >>
     qpat_x_assum `w2n src_addr + type_memory_size _ < _` mp_tac >>
     simp_tac bool_ss [type_memory_size_def] >> decide_tac) >>
  `type_memory_size (ArrayTV elem_tv (Dynamic src_capacity)) < dimword(:256)` by decide_tac >>
  mp_tac (Q.SPECL [`elem_tv`, `src_capacity`, `dst_capacity`, `LENGTH (vs:value list)`,
    `w2n (src_addr:bytes32)`, `w2n (dst_addr:bytes32)`] dynarray_copy_bulk_separated) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `lowered_value_rel (ArrayT elem_ty (Dynamic src_capacity)) (ArrayTV elem_tv (Dynamic src_capacity))
    (ArrayV (DynArrayV vs)) src ss` by simp[lowered_value_rel_def, is_word_type_def] >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `elem_ty`, `elem_tv`,
    `src_capacity`, `dst_capacity`, `vs`, `dst`, `src`, `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `src_addr`]
    checked_compile_typed_dynarray_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexists_tac `out` >>
  qpat_x_assum `!other_tv other_v offset. _` mp_tac >>
  asm_simp_tac (srw_ss()) [array_copy_frame_def, type_memory_size_def, ADD_ASSOC] >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked bulk dynamic-array contract: " ^ name)
  end) (DB.thms "typedDynBulkContract")
