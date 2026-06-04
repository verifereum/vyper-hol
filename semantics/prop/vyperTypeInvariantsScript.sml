(*
 * Type-soundness invariants and global consistency predicates for Vyper.
 *
 * This theory contains runtime well-typedness invariants and proof-facing
 * consistency predicates used by the type-soundness theorems.  The executable
 * static type system itself is defined in vyperTypeSystem.
 *)

Theory vyperTypeInvariants
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage
  vyperTyping vyperEncodeDecode vyperArith vyperTypeSystem
Libs
  wordsLib

(* ===== Runtime invariants ===== *)

Definition scope_well_typed_def:
  scope_well_typed (sc : scope) <=>
    !id entry. FLOOKUP sc id = SOME entry ==>
      value_has_type entry.type entry.value /\ well_formed_type_value entry.type
End

Definition imms_well_typed_def:
  imms_well_typed (imms : module_immutables) <=>
    !src_id_opt m id tv v.
      ALOOKUP imms src_id_opt = SOME m /\ FLOOKUP m id = SOME (tv, v) ==>
      value_has_type tv v /\ well_formed_type_value tv
End

Definition state_well_typed_def:
  state_well_typed st <=>
    EVERY scope_well_typed st.scopes /\
    EVERY (\(addr, mods). imms_well_typed mods) st.immutables
End

(* ===== Global consistency predicates ===== *)

Definition fn_sigs_consistent_def:
  fn_sigs_consistent fn_sigs cx <=>
    !src_id_opt fn sig.
      FLOOKUP fn_sigs (src_id_opt, fn) = SOME sig ==>
      ?ts fm nr params dflts body.
        get_module_code cx src_id_opt = SOME ts /\
        lookup_callable_function cx.in_deploy fn ts =
          SOME (fm, nr, params, dflts, sig.ret_ty, body) /\
        sig.param_types = MAP SND params /\
        sig.num_defaults = LENGTH dflts
End

Definition fn_sigs_complete_def:
  fn_sigs_complete fn_sigs cx <=>
    !src_id_opt fn ts fm nr params dflts ret body.
      get_module_code cx src_id_opt = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts =
        SOME (fm, nr, params, dflts, ret, body) ==>
      FLOOKUP fn_sigs (src_id_opt, fn) =
        SOME <| param_types := MAP SND params;
                num_defaults := LENGTH dflts;
                ret_ty := ret |>
End

Definition toplevel_vtypes_complete_def:
  toplevel_vtypes_complete toplevel_vtypes cx <=>
    (!src ts vis mut id ty init.
       get_module_code cx src = SOME ts /\
       MEM (VariableDecl vis mut id ty init) ts ==>
       FLOOKUP toplevel_vtypes (src,string_to_num id) = SOME (Type ty)) /\
    (!src ts vis is_transient id kt vt init.
       get_module_code cx src = SOME ts /\
       MEM (HashMapDecl vis is_transient id kt vt init) ts ==>
       FLOOKUP toplevel_vtypes (src,string_to_num id) = SOME (HashMapT kt vt))
End

Definition is_bare_global_decl_def:
  is_bare_global_decl n [] = F /\
  is_bare_global_decl n (VariableDecl _ Immutable vid _ _ :: ts) =
    (if string_to_num vid = n then T else is_bare_global_decl n ts) /\
  is_bare_global_decl n (VariableDecl _ (Constant e) vid _ _ :: ts) =
    (if string_to_num vid = n then T else is_bare_global_decl n ts) /\
  is_bare_global_decl n (_ :: ts) = is_bare_global_decl n ts
End

Theorem is_immutable_decl_imp_is_bare_global_decl:
  is_immutable_decl id ts ==> is_bare_global_decl id ts
Proof
  Induct_on `ts` >>
  rw[is_immutable_decl_def, is_bare_global_decl_def] >>
  Cases_on `h` >>
  gvs[is_immutable_decl_def, is_bare_global_decl_def] >>
  TRY (Cases_on `v0` >> gvs[is_immutable_decl_def, is_bare_global_decl_def])
QED

Definition bare_globals_complete_def:
  bare_globals_complete bare_globals cx <=>
    !src ts vis mut id ty init.
      get_module_code cx src = SOME ts /\
      MEM (VariableDecl vis mut id ty init) ts /\
      (mut = Immutable \/ ?e. mut = Constant e) ==>
      FLOOKUP bare_globals (src,string_to_num id) = SOME ty
End

Definition flag_members_complete_def:
  flag_members_complete flag_members cx <=>
    !src ts fid members.
      get_module_code cx src = SOME ts /\
      lookup_flag fid ts = SOME members ==>
      FLOOKUP flag_members (src,fid) = SOME members
End

Definition env_context_consistent_def:
  env_context_consistent env cx <=>
    env.type_defs = get_tenv cx /\
    env.current_src = current_module cx /\
    fn_sigs_consistent env.fn_sigs cx /\
    fn_sigs_complete env.fn_sigs cx /\
    toplevel_vtypes_complete env.toplevel_vtypes cx /\
    bare_globals_complete env.bare_globals cx /\
    flag_members_complete env.flag_members cx /\
    (!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==>
       ?ts. get_module_code cx src = SOME ts /\
            FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
            is_bare_global_decl id ts /\
            find_var_decl_by_num id ts = NONE /\
            ty <> NoneT) /\
    (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
       well_formed_vtype env.type_defs vt) /\
    (!src id ty.
       FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
       FLOOKUP env.bare_globals (src,id) = NONE ==>
       ?ts is_transient typ id_str.
         get_module_code cx src = SOME ts /\
         find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) /\
         typ = ty /\
         IS_SOME (evaluate_type (get_tenv cx) typ) /\
         IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)) /\
    (!src id kt vt.
       FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==>
       ?ts is_transient id_str.
         get_module_code cx src = SOME ts /\
         find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
         IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)) /\
    (!src fid ls.
       FLOOKUP env.flag_members (src, fid) = SOME ls ==>
       ?ts. get_module_code cx src = SOME ts /\ lookup_flag fid ts = SOME ls /\
            FLOOKUP (get_tenv cx) (string_to_num fid) = SOME (FlagArgs (LENGTH ls)))
End

Theorem env_context_consistent_static_completeness:
  env_context_consistent env cx ==>
    toplevel_vtypes_complete env.toplevel_vtypes cx /\
    bare_globals_complete env.bare_globals cx /\
    flag_members_complete env.flag_members cx
Proof
  rw[env_context_consistent_def]
QED

Theorem env_context_consistent_bare_global_old:
  env_context_consistent env cx /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  get_module_code cx src = SOME ts ==>
    FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
    is_bare_global_decl id ts /\ ty <> NoneT
Proof
  rw[env_context_consistent_def] >>
  first_x_assum drule >> rw[] >> gvs[]
QED

Theorem env_context_consistent_bare_global_find_NONE:
  env_context_consistent env cx /\
  FLOOKUP env.bare_globals (src,id) = SOME ty ==>
    ?ts. get_module_code cx src = SOME ts /\
         FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
         is_bare_global_decl id ts /\
         find_var_decl_by_num id ts = NONE /\
         ty <> NoneT
Proof
  rw[env_context_consistent_def] >>
  first_x_assum drule >> rw[] >> gvs[]
QED


Definition env_scopes_consistent_def:
  env_scopes_consistent env cx (st:evaluation_state) <=>
    st.scopes <> [] /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==> IS_SOME (lookup_scopes id st.scopes)) /\
    (!id entry. lookup_scopes id st.scopes = SOME entry ==>
       IS_SOME (FLOOKUP env.var_types id)) /\
    (!id ty entry.
       FLOOKUP env.var_types id = SOME ty /\ lookup_scopes id st.scopes = SOME entry ==>
       evaluate_type (get_tenv cx) ty = SOME entry.type) /\
    (!id. FLOOKUP env.var_assignable id = SOME T ==> IS_SOME (FLOOKUP env.var_types id)) /\
    (!id. FLOOKUP env.var_assignable id = SOME T ==>
       ?entry. lookup_scopes id st.scopes = SOME entry /\ entry.assignable)
End

Definition env_immutables_consistent_def:
  env_immutables_consistent env cx (st:evaluation_state) <=>
    (!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==>
       IS_SOME (FLOOKUP (get_source_immutables src
         (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id)) /\
    (!src id ty tv v.
       FLOOKUP env.bare_globals (src,id) = SOME ty /\
       FLOOKUP (get_source_immutables src
         (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv) /\
    (!src id ty ts.
       FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ get_module_code cx src = SOME ts ==>
       (!is_transient typ id_str.
          find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) ==> typ = ty) /\
       (!is_transient kt vt id_str.
          find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) ==> F) /\
       (find_var_decl_by_num id ts = NONE ==>
         !tv v. FLOOKUP (get_source_immutables src
           (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
         evaluate_type (get_tenv cx) ty = SOME tv))
End

Definition env_consistent_def:
  env_consistent env cx (st:evaluation_state) <=>
    env_context_consistent env cx /\
    env_scopes_consistent env cx st /\
    env_immutables_consistent env cx st
End

Theorem env_consistent_bare_global_find_NONE:
  env_consistent env cx st /\
  FLOOKUP env.bare_globals (src,id) = SOME ty ==>
    ?ts. get_module_code cx src = SOME ts /\
         FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
         is_bare_global_decl id ts /\
         find_var_decl_by_num id ts = NONE /\
         ty <> NoneT
Proof
  rw[env_consistent_def] >>
  drule_all env_context_consistent_bare_global_find_NONE >>
  simp[]
QED

Definition functions_well_typed_def:
  functions_well_typed cx <=>
    !fn_sigs bare_globals toplevel_vtypes flag_members.
      fn_sigs_consistent fn_sigs cx /\
      fn_sigs_complete fn_sigs cx /\
      toplevel_vtypes_complete toplevel_vtypes cx /\
      bare_globals_complete bare_globals cx /\
      flag_members_complete flag_members cx /\
      (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
         ?ts. get_module_code cx src = SOME ts /\
              FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
              is_bare_global_decl id ts /\
              find_var_decl_by_num id ts = NONE /\
              ty <> NoneT) /\
      (!src id vt ts.
         FLOOKUP toplevel_vtypes (src,id) = SOME vt /\ get_module_code cx src = SOME ts ==>
         ((?ty. vt = Type ty /\
             ((!is_transient typ id_str.
                 find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) ==> typ = ty) /\
              (!is_transient kt hv id_str.
                 find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt hv,id_str) ==> F) /\
              (find_var_decl_by_num id ts = NONE ==> IS_SOME (evaluate_type (get_tenv cx) ty)))) \/
          (?kt hv. vt = HashMapT kt hv /\
             ?is_transient id_str.
               find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt hv,id_str)))) /\
      (!src fid ls.
         FLOOKUP flag_members (src,fid) = SOME ls ==>
         ?ts. get_module_code cx src = SOME ts /\ lookup_flag fid ts = SOME ls /\
              FLOOKUP (get_tenv cx) (string_to_num fid) = SOME (FlagArgs (LENGTH ls))) ==>
      !src_id_opt fn ts fm nr args dflts ret body.
        get_module_code cx src_id_opt = SOME ts /\
        lookup_callable_function cx.in_deploy fn ts = SOME (fm,nr,args,dflts,ret,body) ==>
        (nr ==> cx.nonreentrant_slot <> NONE) /\
        ?env_body ret_tv env_after.
          env_body.current_src = src_id_opt /\
          env_body.type_defs = get_tenv cx /\
          env_body.fn_sigs = fn_sigs /\
          env_body.bare_globals = bare_globals /\
          env_body.toplevel_vtypes = toplevel_vtypes /\
          env_body.flag_members = flag_members /\
          evaluate_type (get_tenv cx) ret = SOME ret_tv /\
          type_stmts env_body ret body = SOME env_after /\
          (ret = NoneT \/ stmts_no_fallthrough body) /\
          stmts_no_control_escape body /\
          well_typed_exprs (defaults_env env_body) dflts /\
          (!id typ. MEM (id,typ) args ==>
             FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
             FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
          (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
             ?id. MEM (id,ty) args /\ n = string_to_num id) /\
          (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
             ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T) /\
          MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args)
End

Definition context_well_typed_def:
  context_well_typed cx <=>
    cx.txn.value < 2 ** 256 /\
    cx.txn.time_stamp < 2 ** 256 /\
    cx.txn.block_number < 2 ** 256 /\
    cx.txn.blob_base_fee < 2 ** 256 /\
    cx.txn.gas_price < 2 ** 256 /\
    cx.txn.chain_id < 2 ** 256 /\
    cx.txn.gas_limit < 2 ** 256 /\
    cx.txn.base_fee < 2 ** 256 /\
    cx.txn.prev_randao < 2 ** 256
End

Definition account_well_typed_def:
  account_well_typed (a : account_state) <=>
    a.balance < 2 ** 256 /\ LENGTH a.code <= 24576
End

Definition accounts_well_typed_def:
  accounts_well_typed acc <=>
    !addr. account_well_typed (lookup_account addr acc)
End

Definition toplevel_value_typed_def:
  (toplevel_value_typed (Value v) tyv <=> value_has_type tyv v) /\
  (toplevel_value_typed (ArrayRef _ _ elem_tv bd) tyv <=> tyv = ArrayTV elem_tv bd) /\
  (toplevel_value_typed (HashMapRef _ _ _ _) tyv <=> tyv = NoneTV)
End

