(* TOP-LEVEL: complete field evaluations identify every actual checked
   struct metadata stride with the compiler's physical type size. *)
Theory typedStructSizes
Ancestors
  structLayoutProps typeLayoutProps typedCopyProducer
  context compileEnv compileVyper vyperContext vyperValue vyperTypeContract
  list pair option combin finite_map

Theorem evaluated_struct_fields_is_some:
  !fields tvs tenv.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP (FST o SND) fields) tvs ==>
    EVERY (\entry. IS_SOME (evaluate_type tenv (FST (SND entry)))) fields
Proof
  Induct_on `fields` >- (Cases_on `tvs` >> simp[]) >>
  rpt gen_tac >> qmatch_goalsub_rename_tac `MAP (FST o SND) (entry::rest)` >>
  PairCases_on `entry` >> Cases_on `tvs` >> simp[o_DEF] >> rpt strip_tac >>
  rename1 `LIST_REL _ (MAP _ rest) rest_tvs` >>
  qpat_x_assum `!tvs tenv. _` (qspecl_then [`rest_tvs`, `tenv`] mp_tac) >> simp[o_DEF]
QED

Theorem checked_struct_metadata_sizes:
  !tops in_deploy layouts addr art cenv name fields tvs.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    FLOOKUP (make_struct_fields_map tops) name = SOME fields /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP (FST o SND) fields) tvs ==>
    EVERY (\entry. SND (SND entry) = type_memory_bytes cenv (FST (SND entry))) fields
Proof
  rpt gen_tac >> strip_tac >> drule checked_contract_struct_args_unique >> DISCH_TAC >>
  drule evaluated_struct_fields_is_some >> DISCH_TAC >>
  rewrite_tac[EVERY_MEM] >> qx_gen_tac `entry` >> DISCH_TAC >>
  PairCases_on `entry` >> rename1 `MEM (field_name,ty,byte_count) fields` >>
  qpat_x_assum `EVERY (\entry. IS_SOME _) fields` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `(field_name,ty,byte_count)` mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  simp_tac (srw_ss()) [IS_SOME_EXISTS] >> disch_then (qx_choose_then `tv` ASSUME_TAC) >>
  mp_tac (Q.SPECL [`tops`, `name`, `fields`, `field_name`, `ty`, `byte_count`, `tv`]
    make_struct_fields_map_field_size) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `cenv`, `ty`, `tv`] type_memory_bytes_evaluated) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked struct metadata field sizes: " ^ name)
  end) (DB.thms "typedStructSizes")
