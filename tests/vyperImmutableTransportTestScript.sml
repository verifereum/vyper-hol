(* Regression for the Function static transport prefix, checked independently
   of its dynamic soundness suffix. The proofs mirror that production prefix. *)
Theory vyperImmutableTransportTest
Ancestors
  list rich_list arithmetic finite_map alist option pair
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues
  vyperTypeContractStaticMaps vyperTypeContractContext
Libs
  wordsLib

val _ = Parse.hide "body";

Definition static_maps_transfer_env_def:
  static_maps_transfer_env env1 env2 <=>
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==>
       FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==>
       FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==>
       FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\
            FLOOKUP env1.bare_global_assignable k = NONE ==>
       FLOOKUP env2.bare_global_assignable k = NONE) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==>
       FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==>
       FLOOKUP env1.toplevel_vtypes k = SOME (Type ty)) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==>
       FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\
            FLOOKUP env1.bare_globals k = NONE ==>
       FLOOKUP env2.bare_globals k = NONE)
End
Theorem well_typed_defaults_static_maps_transfer[local]:
  well_typed_exprs (defaults_env env1) dflts /\
  env2.current_src = env1.current_src /\
  env2.type_defs = env1.type_defs /\
  (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
  (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
  (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
  (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_global_assignable k = NONE ==> FLOOKUP env2.bare_global_assignable k = NONE) /\
  (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
  (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
  (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
  well_typed_exprs (defaults_env env2) dflts
Proof
  rw[defaults_env_def] >>
  irule (cj 4 well_typed_static_maps_transfer) >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem static_maps_transfer_env_extend_local[local]:
  static_maps_transfer_env env1 env2 ==>
  static_maps_transfer_env (extend_local env1 n ty a) (extend_local env2 n ty a)
Proof
  rw[static_maps_transfer_env_def, extend_local_def]
QED

Theorem well_typed_expr_static_maps_transfer_env[local]:
  well_typed_expr env1 e /\ static_maps_transfer_env env1 env2 ==> well_typed_expr env2 e
Proof
  rw[static_maps_transfer_env_def] >>
  irule (cj 1 well_typed_static_maps_transfer) >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem well_typed_exprs_static_maps_transfer_env[local]:
  well_typed_exprs env1 es /\ static_maps_transfer_env env1 env2 ==> well_typed_exprs env2 es
Proof
  rw[static_maps_transfer_env_def] >>
  irule (cj 4 well_typed_static_maps_transfer) >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem type_place_expr_static_maps_transfer_env[local]:
  type_place_expr env1 e = SOME vt /\ static_maps_transfer_env env1 env2 ==>
  type_place_expr env2 e = SOME vt
Proof
  rw[static_maps_transfer_env_def] >>
  drule (cj 2 well_typed_static_maps_transfer) >>
  disch_then (qspec_then `env2` mp_tac) >>
  simp[]
QED

Theorem type_place_target_static_maps_transfer_env[local]:
  type_place_target env1 tgt = SOME vt /\ static_maps_transfer_env env1 env2 ==>
  type_place_target env2 tgt = SOME vt
Proof
  rw[static_maps_transfer_env_def] >>
  drule (cj 3 well_typed_static_maps_transfer) >>
  disch_then (qspec_then `env2` mp_tac) >>
  simp[]
QED

Theorem target_mutable_static_maps_transfer_env[local]:
  target_mutable env1 tgt /\ static_maps_transfer_env env1 env2 ==>
  target_mutable env2 tgt
Proof
  rw[static_maps_transfer_env_def] >>
  drule_all target_mutable_static_maps_transfer >> simp[]
QED

Theorem type_place_expr_static_maps_transfer_env_reverse_SOME[local]:
  !e env1 env2 vt.
    well_typed_expr env1 e /\
    static_maps_transfer_env env1 env2 /\
    type_place_expr env2 e = SOME vt ==>
    type_place_expr env1 e = SOME vt
Proof
  Induct >>
  rw[well_typed_expr_def, static_maps_transfer_env_def, AllCaseEqs()] >>
  gvs[] >>
  TRY (PairCases_on `p` >> gvs[well_typed_expr_def, vtype_annotation_ok_def]) >>
  gvs[well_typed_expr_def, vtype_annotation_ok_def] >>
  TRY (rename1 `FLOOKUP env1.toplevel_vtypes (src,id) = SOME (Type ty)` >>
       `FLOOKUP env2.toplevel_vtypes (src,id) = SOME (Type ty)` by metis_tac[] >>
       gvs[]) >>
  TRY (`static_maps_transfer_env env1 env2` by rw[static_maps_transfer_env_def]) >>
  TRY (rename1 `subscript_vtype base_vt (expr_type idx) = SOME result_vt` >>
       qpat_x_assum `!env1 env2 vt. well_typed_expr env1 e /\ static_maps_transfer_env env1 env2 /\ type_place_expr env2 e = SOME vt ==> type_place_expr env1 e = SOME vt`
         (qspecl_then [`env1`,`env2`,`base_vt`] mp_tac) >>
       simp[] >> strip_tac >>
       qexists `base_vt` >> simp[]) >>
  TRY (rename1 `type_place_expr env2 e = SOME env2_vt` >>
       qpat_x_assum `!env1 env2 vt. well_typed_expr env1 e /\ static_maps_transfer_env env1 env2 /\ type_place_expr env2 e = SOME vt ==> type_place_expr env1 e = SOME vt`
         (qspecl_then [`env1`,`env2`,`env2_vt`] mp_tac) >>
       simp[] >> strip_tac >> gvs[]) >>
  TRY (rename1 `type_place_expr env1 e = SOME base_vt` >>
       `type_place_expr env2 e = SOME base_vt` by metis_tac[type_place_expr_static_maps_transfer_env] >>
       gvs[]) >>
  TRY (rename1 `FLOOKUP env1.bare_globals (src,id) = SOME ty` >>
       qpat_x_assum `!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env1.toplevel_vtypes k = SOME (Type ty)` drule >>
       simp[vtype_annotation_ok_def] >> NO_TAC) >>
  metis_tac[]
QED

Theorem type_place_expr_no_hash_static_maps_transfer_env[local]:
  well_typed_expr env1 e /\
  static_maps_transfer_env env1 env2 /\
  (!kt vt. type_place_expr env1 e <> SOME (HashMapT kt vt)) ==>
  (!kt vt. type_place_expr env2 e <> SOME (HashMapT kt vt))
Proof
  rw[] >>
  strip_tac >>
  drule_all type_place_expr_static_maps_transfer_env_reverse_SOME >>
  metis_tac[]
QED

Theorem well_typed_atarget_static_maps_transfer_env[local]:
  !env1 tgt ty.
    well_typed_atarget env1 tgt ty ==>
    !env2. static_maps_transfer_env env1 env2 ==>
      well_typed_atarget env2 tgt ty
Proof
  recInduct well_typed_atarget_ind >>
  rw[well_typed_atarget_def, well_typed_target_def]
  >- metis_tac[type_place_target_static_maps_transfer_env]
  >> gvs[LIST_REL_EL_EQN] >>
  rw[] >>
  first_x_assum irule >>
  simp[MEM_EL] >>
  conj_tac >- (qexists `n` >> simp[]) >>
  qexists `tys` >> qexists `n` >> simp[] >>
  first_x_assum irule >>
  simp[]
QED

Theorem well_typed_iterator_static_maps_transfer_env[local]:
  well_typed_iterator env1 typ it /\ static_maps_transfer_env env1 env2 ==>
  well_typed_iterator env2 typ it
Proof
  Cases_on `it` >>
  rw[well_typed_iterator_def] >>
  metis_tac[well_typed_expr_static_maps_transfer_env]
QED

Theorem type_stmt_static_maps_transfer_mutual[local]:
  (!env1 ret s env1'.
     type_stmt env1 ret s = SOME env1' ==>
     !env2.
       static_maps_transfer_env env1 env2 ==>
       ?env2'. type_stmt env2 ret s = SOME env2' /\ static_maps_transfer_env env1' env2') /\
  (!env1 ret ss env1'.
     type_stmts env1 ret ss = SOME env1' ==>
     !env2.
       static_maps_transfer_env env1 env2 ==>
       ?env2'. type_stmts env2 ret ss = SOME env2' /\ static_maps_transfer_env env1' env2')
Proof
  ho_match_mp_tac type_stmt_ind >>
  rw[type_stmt_def, AllCaseEqs()] >>
  gvs[] >>
  TRY (rename1 `well_typed_expr env1 e` >> qexists `env2` >> simp[] >>
       conj_tac >- metis_tac[type_place_expr_no_hash_static_maps_transfer_env] >>
       irule well_typed_expr_static_maps_transfer_env >> simp[]) >>
  rpt (first_x_assum (drule_then strip_assume_tac)) >>
  gvs[] >>
  rpt (first_x_assum (drule_then strip_assume_tac)) >>
  gvs[] >>
  TRY (irule_at Any static_maps_transfer_env_extend_local >> simp[]) >>
  TRY (irule_at Any well_typed_expr_static_maps_transfer_env >> simp[]) >>
  TRY (irule_at Any well_typed_exprs_static_maps_transfer_env >> simp[]) >>
  TRY (irule_at Any type_place_target_static_maps_transfer_env >> simp[]) >>
  TRY (irule_at Any target_mutable_static_maps_transfer_env >> simp[]) >>
  TRY (irule_at Any type_place_expr_no_hash_static_maps_transfer_env >> simp[]) >>
  TRY (rename1 `?env. static_maps_transfer_env env env2 /\ well_typed_expr env expr` >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `?env. (!kt vt. type_place_expr env expr <> SOME (HashMapT kt vt)) /\ static_maps_transfer_env env env2 /\ well_typed_expr env expr` >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `?env. static_maps_transfer_env env env2 /\ well_typed_exprs env es` >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `assignable_type env2.type_defs ty` >>
       gvs[static_maps_transfer_env_def]) >>
  TRY (rename1 `assignable_type env2.type_defs (expr_type e)` >>
       gvs[static_maps_transfer_env_def]) >>
  TRY (rename1 `id NOTIN FDOM env2.var_types` >>
       gvs[static_maps_transfer_env_def]) >>
  TRY (rename1 `type_place_target env1 bt = SOME (Type (ArrayT ty (Dynamic n)))` >>
       qexistsl [`n`,`env1`,`env1`] >> simp[static_maps_transfer_env_def]) >>
  TRY (rename1 `well_typed_atarget env1 tgt (expr_type e)` >>
       irule well_typed_atarget_static_maps_transfer_env >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `well_typed_target env1 bt ty` >>
       gvs[well_typed_target_def] >>
       irule type_place_target_static_maps_transfer_env >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `IS_SOME (type_stmts env2 ret ss)` >>
       metis_tac[IS_SOME_EXISTS]) >>
  TRY (rename1 `IS_SOME (type_stmts env2 ret ss')` >>
       metis_tac[IS_SOME_EXISTS]) >>
  TRY (rename1 `IS_SOME (type_stmts (extend_local env2 id typ F) ret ss)` >>
       metis_tac[IS_SOME_EXISTS, static_maps_transfer_env_extend_local]) >>
  TRY (rename1 `well_typed_iterator env2 typ it` >>
       irule well_typed_iterator_static_maps_transfer_env >>
       qexists `env1` >> simp[]) >>
  gvs[static_maps_transfer_env_def] >>
  TRY (qexists `env1` >> simp[]) >>
  metis_tac[static_maps_transfer_env_extend_local,
            well_typed_expr_static_maps_transfer_env,
            well_typed_exprs_static_maps_transfer_env,
            well_typed_atarget_static_maps_transfer_env,
            well_typed_iterator_static_maps_transfer_env,
            type_place_target_static_maps_transfer_env,
            target_mutable_static_maps_transfer_env,
            type_place_expr_no_hash_static_maps_transfer_env]
QED

Theorem type_stmts_static_maps_transfer[local]:
  type_stmts env1 ret body = SOME env_after /\
  static_maps_transfer_env env1 env2 ==>
  ?env_after2. type_stmts env2 ret body = SOME env_after2
Proof
  rw[] >>
  drule (cj 2 type_stmt_static_maps_transfer_mutual) >>
  disch_then (qspec_then `env2` mp_tac) >>
  simp[] >>
  metis_tac[]
QED

val () = let
  val th = type_stmts_static_maps_transfer
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print "IMMUTABLE_STATIC_TRANSPORT_KERNEL_CLOSED\n"
    else raise Fail "static transport not kernel closed"
  end;
