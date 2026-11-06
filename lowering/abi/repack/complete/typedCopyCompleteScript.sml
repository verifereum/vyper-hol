(* TOP-LEVEL: every compatible, fully evaluated type pair satisfies the
   actual typed-copy contract in a checked main-module environment.
   Well-founded metadata recursion discharges every child callback. *)
Theory typedCopyComplete
Ancestors
  vyperEventArgCompat
  typedCopyCompleteDefs typedCopyCompleteArray typedCopyCompleteAggregate
  checkedCopyAcyclic typedCopyDomain typedCopyTypeContract
  context compileEnv compileVyper vyperTypeContract vyperContext vyperValue
  list relation

Theorem typed_copy_complete_step:
  !tops in_deploy layouts addr art ctx func cenv fty.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    (!child. type_copy_child cenv.ce_struct_fields child fty ==>
      typed_copy_complete (type_env tops) ctx func cenv child) ==>
    typed_copy_complete (type_env tops) ctx func cenv fty
Proof
  rpt gen_tac >> strip_tac >> Cases_on `fty`
  >- simp[typed_copy_complete_base]
  >- (rename1 `TupleT tys` >>
      `EVERY (typed_copy_complete (type_env tops) ctx func cenv) tys` by
        (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
         first_x_assum irule >> simp[type_copy_child_def]) >>
      mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `tys`]
        typed_copy_complete_tuple) >> simp[])
  >- (rename1 `ArrayT elem bd` >>
      `typed_copy_complete (type_env tops) ctx func cenv elem` by
        (first_x_assum irule >> simp[type_copy_child_def]) >>
      Cases_on `bd` >> FIRST
        [drule_all typed_copy_complete_fixed >> simp[] >> NO_TAC,
         drule_all typed_copy_complete_dynamic >> simp[]])
  >- (rename1 `StructT nsid` >>
      `EVERY (typed_copy_complete (type_env tops) ctx func cenv)
        (MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid)))` by
        (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
         first_x_assum irule >> simp[type_copy_child_def]) >>
      mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `nsid`]
        typed_copy_complete_struct) >> simp[])
  >- simp[typed_copy_complete_flag]
  >> irule typed_copy_complete_none >> asm_rewrite_tac [] >>
  drule_all checked_struct_metadata_acyclic >> simp[]
QED

Theorem checked_typed_copy_complete:
  !tops in_deploy layouts addr art ctx func cenv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops ==>
    !fty. typed_copy_complete (type_env tops) ctx func cenv fty
Proof
  rpt gen_tac >> strip_tac >>
  `WF (type_copy_child cenv.ce_struct_fields)` by
    (asm_rewrite_tac [] >> drule_all checked_struct_metadata_well_founded >> simp[]) >>
  pop_assum (fn th => ho_match_mp_tac (MATCH_MP WF_INDUCTION_THM th)) >>
  qx_gen_tac `fty` >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `fty`]
    typed_copy_complete_step) >> simp[]
QED

Theorem checked_typed_copy_type_contract:
  !tops in_deploy layouts addr art ctx func cenv fty aty ftv atv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\
    evaluate_type (type_env tops) aty = SOME atv ==>
    typed_copy_type_contract ctx func cenv fty aty ftv atv
Proof
  rpt gen_tac >> strip_tac >> drule_all checked_typed_copy_complete >>
  disch_then (qspecl_then [`ctx`, `func`, `fty`] ASSUME_TAC) >>
  drule_all typed_copy_complete_instance >> simp[]
QED
