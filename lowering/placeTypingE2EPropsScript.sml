Theory placeTypingE2EProps
Ancestors
  e2eDefs placeTypingBuildProps placeTypingProps exprLowering
  compileVyper vyperTypeSystem

(* This boundary retains the checker environment at the relevant place.
   check_contract_runtime_function_body_MEM supplies a checked function body,
   not well_typed_expr for arbitrary subterms in an arbitrary local context.
   Successful place typing is therefore an explicit premise here. Struct
   layout and runtime pointer locations are separate obligations: these
   theorems establish only agreement of structural type descriptors. *)
Theorem checked_contract_place_type:
  check_contract d layouts addr [(NONE,tops)] = SOME art /\
  env.toplevel_vtypes = art.cta_toplevel_vtypes /\
  type_place_expr env e = SOME vt ==>
  place_type (build_compile_env tops vis mut fname args ret fbody use_trans) e =
    value_type_place vt
Proof
  strip_tac >> irule place_type_checked_place_on_defined >>
  qexists `env` >> simp[] >>
  irule build_compile_env_defined_map_agreement >> metis_tac[]
QED

(* Local allocation and declaration typing cannot change the map table. *)
Theorem checked_contract_place_type_local_updates:
  check_contract d layouts addr [(NONE,tops)] = SOME art /\
  env.toplevel_vtypes = art.cta_toplevel_vtypes /\
  type_place_expr (extend_local env id ty assignable) e = SOME vt ==>
  place_type
    ((build_compile_env tops vis mut fname args ret fbody use_trans)
       with <| ce_vars := vars; ce_var_type := tys |>) e = value_type_place vt
Proof
  simp[place_type_local_updates] >> strip_tac >>
  irule checked_contract_place_type >>
  qexistsl [`addr`, `art`, `d`, `extend_local env id ty assignable`, `layouts`] >>
  simp[extend_local_def]
QED

Theorem source_typing_ok_place_type:
  source_typing_ok tops am tx ==>
  ?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
    (!env. env.toplevel_vtypes = art.cta_toplevel_vtypes ==>
      place_map_tables_agree_on_defined
        (build_compile_env tops vis mut fname args ret fbody use_trans) env) /\
    (!env e vt. env.toplevel_vtypes = art.cta_toplevel_vtypes /\
       type_place_expr env e = SOME vt ==>
       place_type (build_compile_env tops vis mut fname args ret fbody use_trans) e =
         value_type_place vt)
Proof
  rw[source_typing_ok_def] >> qexists `art` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      irule (INST_TYPE [``:'a`` |-> ``:160 word``, ``:'b`` |-> ``:num``]
        build_compile_env_defined_map_agreement) >>
      qexistsl [`tx.target`, `art`, `F`, `am.layouts`] >> simp[]) >>
  rpt strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:160 word``, ``:'b`` |-> ``:num``] checked_contract_place_type) >>
  qexistsl [`tx.target`, `art`, `F`, `env`, `am.layouts`] >> simp[]
QED

val _ = List.app (fn (name,th) =>
  if List.all (fn tag => tag = "DISK_THM")
       (fst (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("oracle in contextual place typing bridge: " ^ name))
  (DB.thms "placeTypingE2EProps");
