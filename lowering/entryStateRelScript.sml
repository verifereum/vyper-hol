(*
 * External entry: the state relation at the start of the body (#639)
 *
 * The selected external function's body starts, on the source side, in
 * the state call_external_function builds: initial_state with the
 * arguments bound, after send_call_value; on the Venom side after
 * compile_register_positional_args has allocated and decoded the
 * parameters.  This file relates the two by state_rel.
 *
 * TOP-LEVEL:
 *   entry_storage_vars_rel -- storage_vars_rel and transient_vars_rel for
 *                             the compiler's env, from the declarations'
 *                             slots and layouts_agree
 *   body_entry_state_rel   -- state_rel at body start, given the
 *                             parameters' local_ptrs_rel
 *   external_body_entry_state_rel -- state_rel at body start from the S1
 *                             premises
 *)
Theory entryStateRel
Ancestors
  list rich_list finite_map alist
  e2eDefs vyperLoweringCorrect entryDecodePlanProps entryArgPtrs fragExec
  compileEnv compileVyper moduleLowering supportedProgram supportedNames
  supportedDecls immutableLocationProps immutableSectionRel immutableRelation
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeContractContext
  vyperInterpreter vyperState vyperContext vyperAST vyperValue vyperTypeDefaults
  venomState
Libs
  dep_rewrite

(* ===== Module variables in the compiler's env ===== *)

(* Where a module variable's entry in add_module_var_locations comes
   from: the starting map, or a declaration with a slot. *)
Theorem add_module_var_locations_cases:
  !tops vars k loc.
    FLOOKUP (add_module_var_locations tops vars) k = SOME loc ==>
    FLOOKUP vars k = SOME loc \/
    (?vis mut name ty n.
       MEM (VariableDecl vis mut name ty (SOME n)) tops /\
       k = (NONE, name) /\
       ((mut = Storage /\ loc = StorageLoc (n2w n)) \/
        (mut = Transient /\ loc = TransientLoc (n2w n)))) \/
    (?vis tr name kt vt n.
       MEM (HashMapDecl vis tr name kt vt (SOME n)) tops /\
       k = (NONE, name) /\
       loc = if tr then TransientLoc (n2w n) else StorageLoc (n2w n))
Proof
  Induct >- simp[add_module_var_locations_def] >>
  rpt gen_tac >> simp[add_module_var_locations_def] >> strip_tac >>
  first_x_assum drule >> reverse strip_tac >- metis_tac[] >- metis_tac[] >>
  pop_assum mp_tac >> BasicProvers.every_case_tac >> simp[FLOOKUP_UPDATE] >>
  rw[] >> metis_tac[]
QED

(* A declaration's own name is untouched by the other declarations. *)
Theorem add_module_var_locations_other:
  !tops vars name.
    ~MEM (NONE, name) (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) ==>
    FLOOKUP (add_module_var_locations tops vars) ((NONE, name)) =
    FLOOKUP vars ((NONE, name))
Proof
  Induct >- simp[add_module_var_locations_def] >>
  rpt gen_tac >> simp[add_module_var_locations_def] >> strip_tac >>
  BasicProvers.every_case_tac >>
  gvs[toplevel_vtype_keys_toplevel_def, FLOOKUP_UPDATE]
QED

(* With distinct names, a declared module variable's entry is the one its
   own declaration gives. *)
Theorem add_module_var_locations_mem:
  !tops vars top name.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    MEM top tops /\ toplevel_vtype_keys_toplevel (NONE:num option) top = [(NONE, name)] /\
    FLOOKUP vars ((NONE, name)) = NONE ==>
    FLOOKUP (add_module_var_locations tops vars) ((NONE, name)) =
    FLOOKUP (add_module_var_locations [top] FEMPTY) ((NONE, name))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> gvs[ALL_DISTINCT_APPEND]
  >- (Cases_on `h` >> gvs[toplevel_vtype_keys_toplevel_def] >>
      simp[add_module_var_locations_def] >> BasicProvers.every_case_tac >>
      asm_simp_tac (srw_ss()) [add_module_var_locations_other, FLOOKUP_UPDATE]) >>
  simp[Once add_module_var_locations_def] >>
  first_x_assum irule >> simp[] >>
  Cases_on `h` >> gvs[toplevel_vtype_keys_toplevel_def] >>
  BasicProvers.every_case_tac >>
  gvs[FLOOKUP_UPDATE, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!l. _` mp_tac >> simp[] >>
  qexists_tac `toplevel_vtype_keys_toplevel (NONE:num option) top` >>
  asm_simp_tac (srw_ss()) [] >>
  qexists_tac `top` >> asm_simp_tac (srw_ss()) []
QED

(* The declaration find_var_decl_by_name finds. *)
Theorem find_var_decl_by_name_mem:
  !ts name d id.
    find_var_decl_by_name name ts = SOME (d, id) ==>
    id = name /\
    ((?vis mut ty a.
        MEM (VariableDecl vis mut name ty a) ts /\
        (mut = Storage \/ mut = Transient) /\
        d = StorageVarDecl (mut = Transient) ty) \/
     (?vis tr kt vt a.
        MEM (HashMapDecl vis tr name kt vt a) ts /\
        d = HashMapVarDecl tr kt vt))
Proof
  Induct >- simp[find_var_decl_by_name_def] >>
  Cases >> rw[find_var_decl_by_name_def] >>
  simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> metis_tac[]
QED

(* Supported storage/transient variables and hashmaps carry their slots. *)
Theorem supported_storage_decl_slot:
  !tops vis mut name ty a.
    supported_declaration_headers tops /\
    MEM (VariableDecl vis mut name ty a) tops /\
    (mut = Storage \/ mut = Transient) ==>
    ?n. a = SOME n
Proof
  rw[supported_declaration_headers_def, EVERY_MEM] >>
  first_x_assum drule >>
  Cases_on `vis` >> Cases_on `a` >> simp[supported_declaration_header_def]
QED

Theorem supported_hashmap_decl_slot:
  !tops vis tr name kt vt a.
    supported_declaration_headers tops /\
    MEM (HashMapDecl vis tr name kt vt a) tops ==>
    ?n. a = SOME n
Proof
  rpt gen_tac >> simp[supported_declaration_headers_def, EVERY_MEM] >>
  strip_tac >> first_x_assum drule >>
  Cases_on `vis` >> Cases_on `tr` >> Cases_on `a` >> Cases_on `vt` >>
  simp[supported_declaration_header_def]
QED

Theorem source_typing_ok_vtype_keys_distinct:
  !tops am tx.
    source_typing_ok tops am tx ==>
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))
Proof
  rw[source_typing_ok_def, check_contract_def] >>
  drule contract_namespaces_ok_module_toplevel_vtype_keys >> simp[]
QED

(* The layout's slots as lookup_var_slot_from_layout reads them. *)
Theorem layouts_agree_lookup:
  !tops am tx cx.
    layouts_agree tops am tx /\
    cx.layouts = am.layouts /\ cx.txn.target = tx.target ==>
    (!vis id ty n. MEM (VariableDecl vis Storage id ty (SOME n)) tops ==>
                   lookup_var_slot_from_layout cx F NONE id = SOME n) /\
    (!vis id ty n. MEM (VariableDecl vis Transient id ty (SOME n)) tops ==>
                   lookup_var_slot_from_layout cx T NONE id = SOME n) /\
    (!vis tr id kt vt n. MEM (HashMapDecl vis tr id kt vt (SOME n)) tops ==>
                         lookup_var_slot_from_layout cx tr NONE id = SOME n)
Proof
  rpt gen_tac >> strip_tac >>
  fs[layouts_agree_def, lookup_var_slot_from_layout_def] >>
  Cases_on `ALOOKUP am.layouts tx.target` >> gvs[] >>
  rename1 `SOME p` >> PairCases_on `p` >> gvs[] >>
  rpt conj_tac >> rpt gen_tac >> TRY (Cases_on `tr`) >> simp[] >> metis_tac[]
QED

(* ===== storage_vars_rel and transient_vars_rel ===== *)

(* The compiler's env for a function of tops holds the module variables
   add_module_var_locations gives (build_compile_env's ce_module_vars).
   For a deployment of tops alone, with its slots as the layout's, both
   directions of the storage and transient relations hold. *)
Theorem entry_storage_vars_rel:
  !tops am tx cenv cx.
    supported_declaration_headers tops /\
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    source_deployment_rel tops am tx /\
    cx.sources = am.sources /\ cx.layouts = am.layouts /\
    cx.txn.target = tx.target /\
    cenv.ce_module = NONE /\
    (!name. FLOOKUP cenv.ce_module_vars (NONE, name) =
            FLOOKUP (add_module_var_locations tops FEMPTY)
              ((NONE, name))) ==>
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx
Proof
  rpt gen_tac >> strip_tac >> fs[source_deployment_rel_def] >>
  drule_all layouts_agree_lookup >> strip_tac >>
  `!src ts. get_module_code cx src = SOME ts ==> src = NONE /\ ts = tops` by
    (simp[get_module_code_def] >> Cases >> simp[]) >>
  simp[storage_vars_rel_def, transient_vars_rel_def] >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >~ [`FLOOKUP _ _ = SOME (StorageLoc slot)`]
  >- (drule add_module_var_locations_cases >> rw[] >>
      gvs[] >> res_tac >> simp[] >>
      Cases_on `tr` >> gvs[] >> res_tac >> simp[])
  >~ [`FLOOKUP _ _ = SOME (TransientLoc slot)`]
  >- (drule add_module_var_locations_cases >> rw[] >>
      gvs[] >> res_tac >> simp[] >>
      Cases_on `tr` >> gvs[] >> res_tac >> simp[]) >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule find_var_decl_by_name_mem >> strip_tac >>
  gvs[var_decl_transient_def]
  >- (`?n. a = SOME n` by metis_tac[supported_storage_decl_slot] >> gvs[] >>
      res_tac >> gvs[] >>
      drule_then (qspecl_then [`FEMPTY`, `VariableDecl vis Storage id ty (SOME n)`, `id`] mp_tac)
        add_module_var_locations_mem >>
      asm_simp_tac (srw_ss())
        [toplevel_vtype_keys_toplevel_def, add_module_var_locations_def,
         LET_THM, FLOOKUP_UPDATE])
  >- (drule_all supported_hashmap_decl_slot >> strip_tac >> gvs[] >>
      res_tac >> gvs[] >>
      drule_then (qspecl_then [`FEMPTY`, `HashMapDecl vis F id kt vt (SOME n)`, `id`] mp_tac)
        add_module_var_locations_mem >>
      asm_simp_tac (srw_ss())
        [toplevel_vtype_keys_toplevel_def, add_module_var_locations_def,
         LET_THM, FLOOKUP_UPDATE])
  >- (`?n. a = SOME n` by metis_tac[supported_storage_decl_slot] >> gvs[] >>
      res_tac >> gvs[] >>
      drule_then (qspecl_then [`FEMPTY`, `VariableDecl vis Transient id ty (SOME n)`, `id`] mp_tac)
        add_module_var_locations_mem >>
      asm_simp_tac (srw_ss())
        [toplevel_vtype_keys_toplevel_def, add_module_var_locations_def,
         LET_THM, FLOOKUP_UPDATE]) >>
  drule_all supported_hashmap_decl_slot >> strip_tac >> gvs[] >>
  res_tac >> gvs[] >>
  drule_then (qspecl_then [`FEMPTY`, `HashMapDecl vis T id kt vt (SOME n)`, `id`] mp_tac)
    add_module_var_locations_mem >>
  asm_simp_tac (srw_ss())
    [toplevel_vtype_keys_toplevel_def, add_module_var_locations_def,
     LET_THM, FLOOKUP_UPDATE]
QED

(* Immutable declarations cannot overwrite a populated storage/transient key. *)
Theorem entry_module_lookup_immutable_frame[local]:
  !tops sft off key loc.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME loc ==>
    FLOOKUP (add_immutable_locations sft tops off
      (add_module_var_locations tops FEMPTY)) key = SOME loc
Proof
  rpt gen_tac >> strip_tac >>
  `!vis name ty slot.
     MEM (VariableDecl vis Immutable name ty slot) tops ==>
     (NONE, name) <> key` by
    (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     drule_then (qspecl_then
       [`FEMPTY`, `VariableDecl vis Immutable name ty slot`, `name`] mp_tac)
       add_module_var_locations_mem >>
     simp[toplevel_vtype_keys_toplevel_def] >>
     Cases_on `slot` >> simp[add_module_var_locations_def]) >>
  drule add_immutable_locations_lookup_unchanged >> simp[]
QED

Theorem entry_storage_vars_rel_immutable[local]:
  !tops am tx cenv cx.
    supported_declaration_headers tops /\
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    source_deployment_rel tops am tx /\
    cx.sources = am.sources /\ cx.layouts = am.layouts /\
    cx.txn.target = tx.target /\ cenv.ce_module = NONE /\
    (!name. FLOOKUP cenv.ce_module_vars (NONE, name) =
      FLOOKUP (add_immutable_locations
        (get_struct_fields (make_struct_fields_map tops)) tops 0
        (add_module_var_locations tops FEMPTY)) ((NONE, name))) ==>
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx
Proof
  rpt gen_tac >> strip_tac >>
  `storage_vars_rel (cenv with ce_module_vars := add_module_var_locations tops FEMPTY) cx /\
   transient_vars_rel (cenv with ce_module_vars := add_module_var_locations tops FEMPTY) cx` by
    (irule entry_storage_vars_rel >> simp[] >>
     qexistsl_tac [`am`, `tops`, `tx`] >> simp[]) >>
  `!key slot.
    (FLOOKUP (add_immutable_locations
      (get_struct_fields (make_struct_fields_map tops)) tops 0
      (add_module_var_locations tops FEMPTY)) key = SOME (StorageLoc slot) <=>
     FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (StorageLoc slot)) /\
    (FLOOKUP (add_immutable_locations
      (get_struct_fields (make_struct_fields_map tops)) tops 0
      (add_module_var_locations tops FEMPTY)) key = SOME (TransientLoc slot) <=>
     FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (TransientLoc slot))` by
    (rpt gen_tac >> conj_tac >> eq_tac >> strip_tac
     >- (drule add_immutable_locations_FLOOKUP >> simp[])
     >- (irule entry_module_lookup_immutable_frame >> simp[])
     >- (drule add_immutable_locations_FLOOKUP >> simp[])
     >- (irule entry_module_lookup_immutable_frame >> simp[])) >>
  `!src ts. get_module_code cx src = SOME ts ==> src = NONE /\ ts = tops` by
    (gvs[source_deployment_rel_def, get_module_code_def] >> Cases >> simp[]) >>
  gvs[storage_vars_rel_def, transient_vars_rel_def] >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  first_assum drule_all >> simp[]
QED

(* ===== The source's body-start state ===== *)

(* send_call_value moves the value as accounts_after_transfer does. *)
Theorem send_call_value_accounts:
  !mut cx st st'.
    send_call_value mut cx st = (INL (), st') ==>
    st' = st with accounts := accounts_after_transfer cx.txn st.accounts
Proof
  rw[send_call_value_def, accounts_after_transfer_def, return_def,
     bind_def, ignore_bind_def, check_def, assert_def, transfer_value_def,
     get_accounts_def, update_accounts_def, LET_THM, AllCaseEqs()] >>
  gvs[evaluation_state_component_equality]
QED

(* ===== state_rel at body start ===== *)

(* The body starts in the source in es, which call_external_function
   builds from am with the arguments bound in env (for a function
   without a lock), and in Venom in ss.  ss differs from the state vs at
   the entry only in variables, memory and allocations, and its
   parameters' pointers hold the arguments (local_ptrs_rel).  Then the
   two are related, given the storage and transient relations
   (entry_storage_vars_rel) and an env with no immutables (as
   required explicitly by this special-case theorem). *)
Theorem body_entry_state_rel:
  !tops func cenv cx am tx vs ss mut env es.
    initial_venom_state_rel tops am tx vs /\ cx.txn = tx /\
    send_call_value mut cx
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INL (), es) /\
    ss.vs_accounts = vs.vs_accounts /\ ss.vs_transient = vs.vs_transient /\
    ss.vs_logs = vs.vs_logs /\ ss.vs_call_ctx = vs.vs_call_ctx /\
    ss.vs_tx_ctx = vs.vs_tx_ctx /\ ss.vs_block_ctx = vs.vs_block_ctx /\
    ss.vs_outcomes = vs.vs_outcomes /\ ss.vs_requests = vs.vs_requests /\
    local_ptrs_rel func cenv [env] ss /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    (!n off. FLOOKUP cenv.ce_module_vars n <> SOME (ImmutableLoc off)) ==>
    state_rel func cenv cx es ss
Proof
  rpt gen_tac >> strip_tac >>
  drule send_call_value_accounts >> strip_tac >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def, state_rel_def,
      initial_state_def] >>
  `ss.vs_call_ctx.cc_address = cx.txn.target` by fs[call_ctx_rel_def] >>
  simp[storage_rel_def, transient_rel_def, contract_storage_def,
       contract_transient_def, logs_rel_def, immutables_rel_def,
       accounts_rel_def]
QED

Theorem body_entry_state_rel_runtime[local]:
  !tops func cenv cx am tx vs ss mut env es.
    initial_venom_state_rel tops am tx vs /\ cx.txn = tx /\
    send_call_value mut cx
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INL (), es) /\
    ss.vs_accounts = vs.vs_accounts /\ ss.vs_transient = vs.vs_transient /\
    ss.vs_logs = vs.vs_logs /\ ss.vs_call_ctx = vs.vs_call_ctx /\
    ss.vs_tx_ctx = vs.vs_tx_ctx /\ ss.vs_block_ctx = vs.vs_block_ctx /\
    ss.vs_outcomes = vs.vs_outcomes /\ ss.vs_requests = vs.vs_requests /\
    local_ptrs_rel func cenv [env] ss /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    cenv.ce_module = NONE /\ ~cenv.ce_is_ctor /\
    immutable_section_layout cenv tops /\ ss.vs_data_section = vs.vs_data_section ==>
    state_rel func cenv cx es ss
Proof
  rpt gen_tac >> strip_tac >>
  drule send_call_value_accounts >> strip_tac >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es ss` by
    (gvs[] >> irule immutables_section_rel_runtime_fallback >>
     gvs[initial_venom_state_rel_def, initial_state_def, account_immutables_def] >>
     qexists_tac `tops` >> simp[]) >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def, state_rel_def,
      initial_state_def] >>
  `ss.vs_call_ctx.cc_address = cx.txn.target` by fs[call_ctx_rel_def] >>
  simp[storage_rel_def, transient_rel_def, contract_storage_def,
       contract_transient_def, logs_rel_def, accounts_rel_def]
QED

(* ===== The compiler's env for an external function ===== *)

Theorem type_mem_bytes_type_memory_bytes:
  !cenv ty.
    type_mem_bytes (get_struct_fields cenv.ce_struct_fields) ty =
    type_memory_bytes cenv ty
Proof
  ho_match_mp_tac type_memory_bytes_ind >>
  rw[type_mem_bytes_def, type_memory_bytes_def] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[]
QED

Theorem allocate_args_lookup:
  !args sft off vars.
    ALL_DISTINCT (MAP FST args) ==>
    (!k. ~MEM k (MAP FST args) ==>
         FLOOKUP (FST (allocate_args sft args off vars)) k = FLOOKUP vars k) /\
    EVERY (\a. ?p. FLOOKUP (FST (allocate_args sft args off vars)) (FST a) =
                   SOME (MemLoc p (type_mem_bytes sft (SND a)))) args
Proof
  Induct >- simp[allocate_args_def] >>
  PairCases >> rw[allocate_args_def] >> gvs[FLOOKUP_UPDATE] >>
  first_x_assum (qspecl_then [`sft`, `off + type_mem_bytes sft h1`,
    `vars |+ (h0, MemLoc off (type_mem_bytes sft h1))`] strip_assume_tac) >>
  gvs[FLOOKUP_UPDATE, EVERY_MEM] >> metis_tac[]
QED

(* The env package_external_fn builds holds each parameter in an abstract
   memory slot of its type's size, and the module variables as
   the immutable-aware module environment gives them. *)
Theorem package_external_fn_vars:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   lbl cenv pos_args rest.
    package_external_fn tops use_trans nkey_map
      (mut, nr, rr, fname, fargs, dflts, ret, fbody) =
      (lbl, cenv, pos_args, rest) /\
    ALL_DISTINCT (MAP FST fargs) ==>
    cenv.ce_module = NONE /\
    EVERY (\a. ?off. FLOOKUP cenv.ce_vars (FST a) =
                     SOME (MemLoc off (type_memory_bytes cenv (SND a)))) fargs /\
    (!k. ~MEM k (MAP FST fargs) ==> FLOOKUP cenv.ce_vars k = NONE) /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv.ce_vars =
   FST (allocate_args (get_struct_fields (make_struct_fields_map tops)) fargs 0
          FEMPTY) /\
   cenv.ce_module_vars =
     add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
       tops 0 (add_module_var_locations tops FEMPTY) /\
   cenv.ce_module = NONE /\
   cenv.ce_struct_fields = make_struct_fields_map tops` by (
    `cenv.ce_vars = (build_compile_env tops External mut fname fargs ret fbody
                       use_trans).ce_vars /\
     cenv.ce_module_vars = (build_compile_env tops External mut fname fargs ret
                              fbody use_trans).ce_module_vars /\
     cenv.ce_module = (build_compile_env tops External mut fname fargs ret fbody
                         use_trans).ce_module /\
     cenv.ce_struct_fields = (build_compile_env tops External mut fname fargs
                                ret fbody use_trans).ce_struct_fields` by
      (gvs[package_external_fn_def, update_cenv_nonreentrant_def] >>
       rw[update_cenv_ret_abi_def]) >>
    simp[build_compile_env_ce_struct_fields] >>
    simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
  drule_then (qspecl_then [`get_struct_fields (make_struct_fields_map tops)`,
    `0`, `FEMPTY`] strip_assume_tac)
    allocate_args_lookup >>
  gvs[] >> rpt strip_tac >>
  gvs[EVERY_MEM, GSYM type_mem_bytes_type_memory_bytes] >> metis_tac[]
QED

Theorem package_external_fn_immutable_layout[local]:
  package_external_fn tops use_trans nkey_map
    (mut,nr,rr,fname,fargs,dflts,ret,fbody) = (lbl,cenv,pos_args,rest) ==>
  ~cenv.ce_is_ctor /\ immutable_section_layout cenv tops
Proof
  strip_tac >>
  qspecl_then [`tops`, `External`, `mut`, `fname`, `fargs`, `ret`,
    `fbody`, `use_trans`] mp_tac immutable_build_compile_env_layout >>
  gvs[package_external_fn_def, update_cenv_nonreentrant_def] >>
  rw[update_cenv_ret_abi_def] >>
  gvs[immutable_section_layout_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* compile_register_positional_args rebinds only the parameters, each to a
   pointer. *)
Theorem compile_register_positional_args_cenv:
  !args cenv off st cenv' st'.
    compile_register_positional_args cenv args off st = (cenv', st') ==>
    cenv' = cenv with ce_vars := cenv'.ce_vars /\
    (!n. ~MEM n (MAP FST args) ==>
         FLOOKUP cenv'.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    (!n l. FLOOKUP cenv'.ce_vars n = SOME l ==>
           FLOOKUP cenv.ce_vars n = SOME l \/ ?p sz. l = PtrVar p sz)
Proof
  Induct
  >- simp[compile_register_positional_args_def, comp_return_def,
          compileEnvTheory.compile_env_component_equality] >>
  PairCases >> rpt gen_tac >> simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[]
  >- (strip_tac >> first_x_assum drule >> rw[] >> metis_tac[]) >>
  rename1 `var_location_memory_size loc` >>
  Cases_on `var_location_memory_size loc` >> simp[]
  >- (strip_tac >> first_x_assum drule >> rw[] >> metis_tac[]) >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >> rpt conj_tac
  >- (pop_assum kall_tac >> pop_assum kall_tac >> pop_assum SUBST1_TAC >>
      simp[compileEnvTheory.compile_env_component_equality])
  >- (rpt strip_tac >> gvs[FLOOKUP_UPDATE]) >>
  rpt strip_tac >> first_x_assum drule >> rw[FLOOKUP_UPDATE] >> gvs[]
QED

Theorem register_positional_args_immutable_layout[local]:
  compile_register_positional_args cenv args off st = (cenv',st') /\
  ~cenv.ce_is_ctor /\ immutable_section_layout cenv tops ==>
  ~cenv'.ce_is_ctor /\ immutable_section_layout cenv' tops
Proof
  strip_tac >> drule compile_register_positional_args_cenv >>
  strip_tac >>
  `cenv'.ce_is_ctor = cenv.ce_is_ctor /\
   cenv'.ce_module_vars = cenv.ce_module_vars` by
    (qpat_x_assum `cenv' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[immutable_section_layout_def]
QED

(* ===== The selected function's parameters ===== *)

Theorem source_typing_ok_type_def_keys_distinct[local]:
  !tops am tx.
    source_typing_ok tops am tx ==>
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))
Proof
  rw[source_typing_ok_def, check_contract_def] >>
  drule contract_namespaces_ok_module_type_def_keys >> simp[]
QED

Theorem type_env_all_modules_one[local]:
  type_env_all_modules [(NONE, tops)] = type_env tops
Proof
  simp[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED

(* With no public variables, an external function lookup_function selects
   is a declared function, not a getter. *)
Theorem lookup_function_external_decl[local]:
  !tops tops0 name mut nr args dflts ret fbody.
    EVERY (supported_declaration_header tops0) tops /\
    lookup_function NONE name External tops =
      SOME (mut, nr, args, dflts, ret, fbody) ==>
    ?raw. MEM (FunctionDecl External mut nr raw name args dflts ret fbody) tops
Proof
  Induct >- simp[lookup_function_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h` >> gvs[supported_declaration_header_def, lookup_function_def] >>
  BasicProvers.every_case_tac >> gvs[lookup_function_def, AllCaseEqs()] >>
  metis_tac[]
QED

(* The source typing check gives the parameters distinct names and
   assignable types. *)
Theorem source_typing_ok_params_ok[local]:
  !tops am tx mut nr fargs ret fbody.
    supported_declaration_headers tops /\ source_typing_ok tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, fargs, [], ret, fbody) ==>
    params_ok (type_env tops) fargs
Proof
  rpt strip_tac >>
  drule_at (Pos last) lookup_function_external_decl >>
  disch_then (qspec_then `tops` mp_tac) >>
  impl_tac >- fs[supported_declaration_headers_def] >> strip_tac >>
  fs[source_typing_ok_def] >>
  drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
  drule check_contract_runtime_function_body_MEM >>
  disch_then (qspecl_then [`External`, `tops`, `NONE`, `ret`, `raw`, `nr`,
    `mut`, `tx.function_name`, `[]`, `fbody`, `fargs`] mp_tac) >>
  simp[check_function_body_def, type_env_all_modules_one]
QED

Theorem build_positional_args_names[local]:
  !cenv fargs. MAP FST (build_positional_args cenv fargs) = MAP FST fargs
Proof
  Induct_on `fargs` >> fs[build_positional_args_def] >>
  PairCases >> fs[build_positional_arg_def]
QED

(* Each parameter that had a memory binding is now a pointer variable to
   an ALLOCA of that size. *)
Theorem compile_register_positional_args_ptrs:
  !args cenv off st cenv' st' n l sz.
    compile_register_positional_args cenv args off st = (cenv', st') /\
    MEM n (MAP FST args) /\ FLOOKUP cenv.ce_vars n = SOME l /\
    var_location_memory_size l = SOME sz ==>
    ?p. FLOOKUP cenv'.ce_vars n = SOME (PtrVar (Var p) sz)
Proof
  Induct >- simp[] >>
  PairCases >> rpt gen_tac >> simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[]
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rename1 `var_location_memory_size loc` >>
  Cases_on `var_location_memory_size loc` >> simp[]
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  Cases_on `MEM n (MAP FST args)`
  >- (rpt strip_tac >> last_x_assum drule >> disch_then irule >>
      simp[FLOOKUP_UPDATE] >> rw[] >> gvs[var_location_memory_size_def]) >>
  rpt strip_tac >> gvs[] >>
  drule (cj 2 compile_register_positional_args_cenv) >>
  disch_then (qspec_then `h0` mp_tac) >> gvs[FLOOKUP_UPDATE]
QED

(* Since #733, evaluate_type only accepts whole-byte integer widths. *)
Theorem evaluate_type_int_byte_widths:
  (!tenv ty tv. evaluate_type tenv ty = SOME tv ==> int_byte_widths tv) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     EVERY int_byte_widths acc ==> EVERY int_byte_widths tvs)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >- (Cases_on `bt` >> simp[evaluate_type_def, AllCaseEqs()] >>
      rw[] >> simp[int_byte_widths_def])
  >- (strip_tac >> simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      rw[] >> gvs[int_byte_widths_def, ETA_AX])
  >- (strip_tac >> simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      rw[] >> gvs[int_byte_widths_def])
  >- (strip_tac >> simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      rw[] >> gvs[int_byte_widths_def] >>
      imp_res_tac evaluate_types_length >>
      gvs[EVERY_MEM, MEM_ZIP, PULL_EXISTS, EL_MEM])
  >- (simp[evaluate_type_def, AllCaseEqs()] >> rw[] >>
      simp[int_byte_widths_def])
  >- simp[evaluate_type_def, int_byte_widths_def]
  >- (simp[evaluate_type_def] >> rw[] >> simp[EVERY_REVERSE])
  >- (strip_tac >> simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      rw[] >> gvs[])
QED

(* ===== state_rel at the external body's start ===== *)

(* From the S1 premises, the selected external function's parameter
   decoding (compile_register_positional_args, in the package
   package_external_fn builds for it) runs from s0, the state its entry
   checks leave, to a state related by state_rel to es, where the source
   body starts: call_external_function's initial_state with the arguments
   bound, after send_call_value.  Each parameter is then a pointer
   variable to its own ALLOCA, holding the argument (local_ptrs_rel).

   Beyond the S1 premises it assumes that
   each argument is a word or has a static ABI encoding (dynamic
   decoding is #762). *)
Theorem external_body_entry_state_rel:
  !tops use_trans nkey_map mut rr fargs ret fbody lbl cenv0 pos_args rest
   am tx vs env es st cenv st' ctx func s0.
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, fargs, [], ret, fbody) /\
    package_external_fn tops use_trans nkey_map
      (mut, F, rr, tx.function_name, fargs, [], ret, fbody) =
      (lbl, cenv0, pos_args, rest) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, st') /\
    bind_arguments (type_env tops) fargs tx.args = SOME env /\
    send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INL (), es) /\
    EVERY (\a. is_word_type (SND a) \/
               ~is_dynamic (vyper_to_abi_type (type_env tops) (SND a))) fargs /\
    s0.vs_accounts = vs.vs_accounts /\ s0.vs_transient = vs.vs_transient /\
    s0.vs_logs = vs.vs_logs /\ s0.vs_call_ctx = vs.vs_call_ctx /\
    s0.vs_tx_ctx = vs.vs_tx_ctx /\ s0.vs_block_ctx = vs.vs_block_ctx /\
    s0.vs_outcomes = vs.vs_outcomes /\ s0.vs_requests = vs.vs_requests /\
    s0.vs_allocas = vs.vs_allocas /\ s0.vs_alloca_next = vs.vs_alloca_next /\
    s0.vs_data_section = vs.vs_data_section /\
    fresh_vars_wrt st s0 /\ fn_has_code st st' func /\ ~s0.vs_halted /\
    s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts ==>
    EVERY (\a. ?p. FLOOKUP cenv.ce_vars (FST a) =
                   SOME (PtrVar (Var p) (type_memory_bytes cenv0 (SND a)))) fargs /\
    ?t. state_rel func cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es t /\
        fresh_vars_wrt st' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> strip_tac >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  `params_ok (type_env tops) fargs` by metis_tac[source_typing_ok_params_ok] >>
  `ALL_DISTINCT (MAP FST fargs)` by fs[params_ok_def] >>
  drule_at (Pos last) package_external_fn_dec_cenv_agrees >>
  impl_tac >- metis_tac[source_typing_ok_type_def_keys_distinct] >>
  strip_tac >> gvs[] >>
  drule_all package_external_fn_vars >> strip_tac >>
  conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      `?off. FLOOKUP cenv0.ce_vars (FST a) =
             SOME (MemLoc off (type_memory_bytes cenv0 (SND a)))` by
        fs[EVERY_MEM] >>
      irule compile_register_positional_args_ptrs >>
      qpat_assum `compile_register_positional_args _ _ _ _ = _`
        (irule_at Any) >>
      simp[build_positional_args_names] >>
      simp[var_location_memory_size_def, MEM_MAP] >> metis_tac[]) >>
  `EVERY (\a. !tv. evaluate_type (type_env tops) (SND a) = SOME tv ==>
                   int_byte_widths tv) fargs` by
    (rw[EVERY_MEM] >> metis_tac[evaluate_type_int_byte_widths]) >>
  drule compile_register_positional_args_cenv >>
  simp[build_positional_args_names] >> strip_tac >>
  `calldata_encodes (type_env tops) tx.function_name (MAP SND fargs) tx.args
     vs.vs_call_ctx.cc_calldata` by gvs[valid_vyper_call_def] >>
  `LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256)` by
    metis_tac[initial_venom_state_calldata_length] >>
  `vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = 0` by
    fs[initial_venom_state_rel_def] >>
  `EVERY (\a. is_word_type (SND a) \/
              (assignable_type (type_env tops) (SND a) /\
               ~is_dynamic (vyper_to_abi_type (type_env tops) (SND a)))) fargs` by
    (gvs[params_ok_def, EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     res_tac >> gvs[]) >>
  qspecl_then [`cenv0`, `type_env tops`, `tx.function_name`, `fargs`,
    `tx.args`, `env`, `st`, `cenv`, `st'`, `ctx`, `func`, `s0`] mp_tac
    register_positional_args_local_ptrs >>
  impl_tac >- gvs[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!fuel r. _`
        (qspecl_then [`fuel`, `run_from fuel ctx func t`] mp_tac) >>
      simp[]) >>
  `cenv.ce_module = NONE /\ cenv.ce_module_vars = cenv0.ce_module_vars` by
    (qpat_x_assum `cenv = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `storage_vars_rel cenv
     (initial_evaluation_context am.sources am.layouts tx NONE) /\
   transient_vars_rel cenv
     (initial_evaluation_context am.sources am.layouts tx NONE)` by
    (irule entry_storage_vars_rel_immutable >>
     simp[initial_evaluation_context_def] >>
     metis_tac[source_typing_ok_vtype_keys_distinct]) >>
  `~cenv0.ce_is_ctor /\ immutable_section_layout cenv0 tops` by
    (drule package_external_fn_immutable_layout >> simp[]) >>
  `~cenv.ce_is_ctor /\ immutable_section_layout cenv tops` by
    (drule_all register_positional_args_immutable_layout >> simp[]) >>
  irule body_entry_state_rel_runtime >> simp[] >>
  qexistsl_tac [`am`, `env`, `mut`, `tops`, `vs`] >>
  qpat_x_assum `_ with <| vs_vars := _; vs_memory := _; vs_allocas := _;
                          vs_alloca_next := _; vs_inst_idx := _ |> = s0`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  gvs[initial_evaluation_context_def]
QED
