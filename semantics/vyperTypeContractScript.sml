(*
 * Whole-contract static type checking for Vyper.
 *
 * This theory packages the expression/statement type checker from
 * vyperTypeSystem into a contract-level checker.  The checker constructs the
 * global static maps used by typing environments and checks callable bodies and
 * top-level declarations against the current static rules.
 *
 * Soundness theorems connecting this checker to the proof-facing invariants in
 * prop/vyperTypeInvariants are proved separately.
 *)

Theory vyperTypeContract
Ancestors
  list rich_list arithmetic finite_map option pair
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeSystem
Libs
  wordsLib

(* ===== Contract typing artifacts ===== *)

Datatype:
  contract_type_artifact = <|
    cta_fn_sigs         : ((num option # string) |-> fn_sig);
    cta_bare_globals    : ((num option # num) |-> type);
    cta_toplevel_vtypes : ((num option # num) |-> value_type);
    cta_flag_members    : ((num option # string) |-> string list)
  |>
End

Definition empty_contract_type_artifact_def:
  empty_contract_type_artifact =
    <| cta_fn_sigs := FEMPTY;
       cta_bare_globals := FEMPTY;
       cta_toplevel_vtypes := FEMPTY;
       cta_flag_members := FEMPTY |>
End

Definition artifact_env_def:
  artifact_env art mods src =
    <| current_src := src;
       var_types := FEMPTY;
       var_assignable := FEMPTY;
       bare_globals := art.cta_bare_globals;
       toplevel_vtypes := art.cta_toplevel_vtypes;
       type_defs := type_env_all_modules mods;
       fn_sigs := art.cta_fn_sigs;
       flag_members := art.cta_flag_members |>
End

Definition function_entry_env_def:
  function_entry_env art mods src args =
    FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (artifact_env art mods src) args
End

(* ===== Static map construction ===== *)

Definition fn_sig_of_def:
  fn_sig_of args dflts ret =
    <| param_types := MAP SND args;
       num_defaults := LENGTH dflts;
       ret_ty := ret |>
End

Definition include_fn_sig_def:
  include_fn_sig in_deploy Internal = T /\
  include_fn_sig in_deploy Deploy = in_deploy /\
  include_fn_sig in_deploy External = F
End

Definition add_toplevel_static_maps_def:
  add_toplevel_static_maps in_deploy src tl art =
    case tl of
    | FunctionDecl vis _ _ _ id args dflts ret _ =>
        if include_fn_sig in_deploy vis then
          art with cta_fn_sigs updated_by
            (flip FUPDATE ((src,id), fn_sig_of args dflts ret))
        else art
    | VariableDecl _ Immutable id typ _ =>
        art with <| cta_bare_globals updated_by
                    (flip FUPDATE ((src,string_to_num id), typ));
                    cta_toplevel_vtypes updated_by
                    (flip FUPDATE ((src,string_to_num id), Type typ)) |>
    | VariableDecl _ (Constant e) id typ _ =>
        art with <| cta_bare_globals updated_by
                    (flip FUPDATE ((src,string_to_num id), typ));
                    cta_toplevel_vtypes updated_by
                    (flip FUPDATE ((src,string_to_num id), Type typ)) |>
    | VariableDecl _ Storage id typ _ =>
        art with cta_toplevel_vtypes updated_by
          (flip FUPDATE ((src,string_to_num id), Type typ))
    | VariableDecl _ Transient id typ _ =>
        art with cta_toplevel_vtypes updated_by
          (flip FUPDATE ((src,string_to_num id), Type typ))
    | HashMapDecl _ _ id kt vt _ =>
        art with cta_toplevel_vtypes updated_by
          (flip FUPDATE ((src,string_to_num id), HashMapT kt vt))
    | FlagDecl fid members =>
        art with cta_flag_members updated_by
          (flip FUPDATE ((src,fid), members))
    | _ => art
End

Definition add_module_static_maps_def:
  add_module_static_maps in_deploy src tls art =
    FOLDL (\art tl. add_toplevel_static_maps in_deploy src tl art) art tls
End

Definition build_contract_type_artifact_def:
  build_contract_type_artifact in_deploy mods =
    FOLDL (\art (src,tls). add_module_static_maps in_deploy src tls art)
      empty_contract_type_artifact mods
End

(* ===== Namespace/duplicate checks ===== *)

Definition fn_sig_keys_toplevel_def:
  fn_sig_keys_toplevel in_deploy src (FunctionDecl vis _ _ _ id _ _ _ _) =
    (if include_fn_sig in_deploy vis then [(src,id)] else []) /\
  fn_sig_keys_toplevel _ _ _ = []
End

Definition toplevel_vtype_keys_toplevel_def:
  toplevel_vtype_keys_toplevel src (VariableDecl _ _ id _ _) = [(src,string_to_num id)] /\
  toplevel_vtype_keys_toplevel src (HashMapDecl _ _ id _ _ _) = [(src,string_to_num id)] /\
  toplevel_vtype_keys_toplevel _ _ = []
End

Definition flag_member_keys_toplevel_def:
  flag_member_keys_toplevel src (FlagDecl fid _) = [(src,fid)] /\
  flag_member_keys_toplevel _ _ = []
End

Definition contract_keys_def:
  contract_keys f mods = FLAT (MAP (\(src,tls). FLAT (MAP (f src) tls)) mods)
End

Definition contract_namespaces_ok_def:
  contract_namespaces_ok in_deploy mods <=>
    ALL_DISTINCT (MAP FST mods) /\
    ALL_DISTINCT (contract_keys (fn_sig_keys_toplevel in_deploy) mods) /\
    ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) /\
    ALL_DISTINCT (contract_keys flag_member_keys_toplevel mods)
End

Definition params_ok_def:
  params_ok tenv args <=>
    ALL_DISTINCT (MAP (string_to_num o FST) args) /\
    EVERY (\(_,ty). assignable_type tenv ty) args
End

(* ===== Declaration checks ===== *)

Definition lookup_var_slot_in_layouts_def:
  lookup_var_slot_in_layouts layouts addr is_transient src var_name =
    case ALOOKUP layouts addr of
    | NONE => NONE
    | SOME (storage_lay, transient_lay) =>
        ALOOKUP (if is_transient then transient_lay else storage_lay) (src,var_name)
End

Definition check_value_type_def:
  check_value_type tenv (Type ty) = assignable_type tenv ty /\
  check_value_type tenv (HashMapT kt vt) =
    (well_formed_type tenv kt /\ hashmap_key_type kt /\ check_value_type tenv vt)
Termination
  WF_REL_TAC `measure (\(_,vt). value_type_size vt)` >>
  simp[value_type_size_def]
End

Definition check_toplevel_decl_def:
  check_toplevel_decl layouts addr mods art src tl =
    let tenv = type_env_all_modules mods in
    let env = artifact_env art mods src in
    case tl of
    | VariableDecl _ Storage id typ _ =>
        assignable_type tenv typ /\
        IS_SOME (lookup_var_slot_in_layouts layouts addr F src id)
    | VariableDecl _ Transient id typ _ =>
        assignable_type tenv typ /\
        IS_SOME (lookup_var_slot_in_layouts layouts addr T src id)
    | VariableDecl _ Immutable id typ _ =>
        assignable_type tenv typ
    | VariableDecl _ (Constant e) id typ _ =>
        assignable_type tenv typ /\ well_typed_expr env e /\ expr_type e = typ
    | HashMapDecl _ is_transient id kt vt _ =>
        well_formed_type tenv kt /\ hashmap_key_type kt /\ check_value_type tenv vt /\
        IS_SOME (lookup_var_slot_in_layouts layouts addr is_transient src id)
    | StructDecl id fields =>
        EVERY (\(_,ty). assignable_type tenv ty) fields
    | FlagDecl id members => T
    | InterfaceDecl id funcs =>
        EVERY (\(fn,args,ret,mut).
          params_ok tenv args /\ well_formed_type tenv ret) funcs
    | EventDecl id fields =>
        EVERY (\((_,ty),indexed). assignable_type tenv ty) fields
    | FunctionDecl _ _ _ _ _ args dflts ret _ =>
        params_ok tenv args /\ well_formed_type tenv ret
End

(* ===== Callable-body checks ===== *)

Definition check_function_body_def:
  check_function_body layouts addr mods art src mut nr args dflts ret body =
    let tenv = type_env_all_modules mods in
    let env = function_entry_env art mods src args in
      params_ok tenv args /\
      (nr ==> IS_SOME (lookup_nonreentrant_slot layouts addr)) /\
      IS_SOME (evaluate_type tenv ret) /\
      IS_SOME (type_stmts env ret body) /\
      (ret = NoneT \/ stmts_no_fallthrough body) /\
      stmts_no_control_escape body /\
      well_typed_exprs (defaults_env env) dflts /\
      MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args)
End

Definition check_toplevel_body_def:
  check_toplevel_body layouts addr mods art src tl =
    case tl of
    | FunctionDecl _ mut nr _ _ args dflts ret body =>
        check_function_body layouts addr mods art src mut nr args dflts ret body
    | _ => T
End

Definition check_module_def:
  check_module layouts addr mods art (src,tls) =
    (EVERY (check_toplevel_decl layouts addr mods art src) tls /\
     EVERY (check_toplevel_body layouts addr mods art src) tls)
End

Definition check_contract_def:
  check_contract in_deploy layouts addr mods =
    let art = build_contract_type_artifact in_deploy mods in
      if contract_namespaces_ok in_deploy mods /\
         EVERY (check_module layouts addr mods art) mods
      then SOME art else NONE
End
