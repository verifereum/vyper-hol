(*
 * The target/place judgment (#636, Places)
 *
 * compile_get_target_ptr lowers an assignment target (and the array of a
 * pop) to a pointer, its location and its place type; the source evaluates
 * the target to a place (eval_base_place, then get_place for
 * eval_target_place).  target_sim relates the two: the target's fragment,
 * run from stmt_state_rel at the source state where the target is
 * evaluated, either reaches its end with stmt_state_rel at the state after
 * it and the pointer at the place the source returns (target_post), or,
 * where the source raises an error other than a type error, exits as
 * expr_exit allows.
 *
 * Where the pointer sits (place_ptr_rel), by the kind of place:
 *   - a local's place MemoryPlace x path: x's pointer plus the byte offset
 *     of path in x's type (mem_path_offset), in memory.  The offset is the
 *     type's, not the value's: a DynArray local reserves its capacity, so
 *     a place keeps its address while x's value changes (x[x.pop()]);
 *   - a storage or transient place: its slot, in storage or transient
 *     storage;
 *   - a mapping (HashMapRef): its slot, at the mapping's key and value
 *     types.
 * Immutables are left out (immutable_root): the lowering keeps them in
 * code (LocCode), which nothing relates to the source's immutables yet
 * (exprSimLeaves' compile_toplevel_immutable_sim).
 *
 * The offsets (mem_path_offset and its steps) are exprSim's, which the
 * live-locals frame locals_kept uses too.
 *
 * TOP-LEVEL:
 *   place_ptr_rel, place_readable, target_post, target_res_ok,
 *   target_sim             — the judgment
 *   target_env_ok, target_root, immutable_root, target_indices_pre,
 *   target_pre, target_case, target_idx_case — its premises and the shared
 *                          case form (as expr_vv_case: nocalls = T for
 *                          compile_expr_sim, F for the body simulation)
 *   target_name_case       — a local: its pointer, no code
 *   toplevel_target_env    — a module variable's compile env entries
 *   target_toplevel_case   — a storage or transient variable or a mapping:
 *                          its slot, no code
 * The steps (fields, subscripts) and the induction over targets are in
 * targetPlaceSimCases.
 *
 * Helpers: target_pre_sub,
 *   expr_sim_inv_local, target_post_refl, toplevel_decl_ce_vars, toplevel_target_decl
 *)

Theory targetPlaceSim
Ancestors
  exprSimFieldLayout
  targetPlaceSimDefs
  exprSimHypsDefs placeTypingProps
  loweringPosts
  list rich_list finite_map pair
  fragExec  exprSimHyps exprSimAttributeFields
  exprLowering exprLoweringProps compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperValue
  vyperTypeSystem vyperTypeEnv vyperTypeInvariants vyperPlaceResultTyping
  venomState venomInst
Libs
  pairLib

(* ===== The judgment ===== *)

(* The source results the judgment speaks of: a place or a mapping, an
   error other than a type error, or an assertion. *)

(* The judgment: the target's fragment of bt, typed vt, run from a state
   related at es, reaches its end in target_post on a place, and exits as
   expr_exit allows on an error. *)

(* ===== Premises ===== *)

(* The compile environment's module tables agree with the declarations:
   a storage or transient variable is not a mapping and has its declared
   type, a mapping its declared key and value types.  The body
   simulation's body_inv gives this for the main module (build_hashmap_info,
   build_var_type_map). *)
Definition target_env_ok_def:
  target_env_ok cenv cx <=>
    !src id ts d id_str.
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (d, id_str) ==>
      (!tr typ. d = StorageVarDecl tr typ ==>
                cenv.ce_hashmap_info (src,id) = NONE /\
                cenv.ce_module_var_type (src,id) = SOME typ) /\
      (!tr kt vt. d = HashMapVarDecl tr kt vt ==>
                  ?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt))
End

Definition target_root_def:
  target_root (NameTarget id) = NameTarget id /\
  target_root (TopLevelNameTarget nsid) = TopLevelNameTarget nsid /\
  target_root (AttributeTarget t fld) = target_root t /\
  target_root (SubscriptTarget t e) = target_root t
End

(* The target is inside an immutable or a constant: a module name with no
   storage declaration. *)
Definition immutable_root_def:
  immutable_root cx bt <=>
    ?src id ts. target_root bt = TopLevelNameTarget (src,id) /\
                get_module_code cx src = SOME ts /\
                find_var_decl_by_name id ts = NONE
End

(* Every index of the target meets expr_body_pre wherever expr_sim_inv
   holds: the static part of expr_body_pre. *)
Definition target_indices_pre_def:
  target_indices_pre cenv cx env (NameTarget id) = T /\
  target_indices_pre cenv cx env (TopLevelNameTarget nsid) = T /\
  target_indices_pre cenv cx env (AttributeTarget t fld) =
    target_indices_pre cenv cx env t /\
  target_indices_pre cenv cx env (SubscriptTarget t e) =
    (target_indices_pre cenv cx env t /\
     !es. expr_sim_inv cenv cx env es ==> expr_body_pre cenv cx env e es)
End

Definition target_pre_def:
  target_pre cenv cx env bt es <=>
    expr_sim_inv cenv cx env es /\ ~immutable_root cx bt /\
    target_indices_pre cenv cx env bt
End

(* The shared case form, as expr_vv_case: target_sim at every state meeting
   target_pre, with no internal call in the target if nocalls. *)
Definition target_case_def:
  target_case nocalls ctx func cenv cx bt <=>
    !env es.
      target_pre cenv cx env bt es /\ (nocalls ==> int_calls_target bt = []) ==>
      target_sim ctx func cenv cx env bt es
End

(* The indices' judgments, each if its base can evaluate, as the body
   simulation's body_base_target_ok has them. *)
Definition target_idx_case_def:
  target_idx_case nocalls ctx func cenv cx (NameTarget id) = T /\
  target_idx_case nocalls ctx func cenv cx (TopLevelNameTarget nsid) = T /\
  target_idx_case nocalls ctx func cenv cx (AttributeTarget t fld) =
    target_idx_case nocalls ctx func cenv cx t /\
  target_idx_case nocalls ctx func cenv cx (SubscriptTarget t e) =
    (target_idx_case nocalls ctx func cenv cx t /\
     ((?s pv s1. eval_base_place cx t s = (INL pv, s1)) ==>
      expr_sim_case nocalls ctx func cenv cx e /\
      expr_vv_case nocalls ctx func cenv cx e))
End

Theorem target_pre_sub:
  (!cenv cx env t fld es.
     target_pre cenv cx env (AttributeTarget t fld) es ==>
     target_pre cenv cx env t es) /\
  (!cenv cx env t e es.
     target_pre cenv cx env (SubscriptTarget t e) es ==>
     target_pre cenv cx env t es)
Proof
  cheat
QED

(* ===== Locals ===== *)

(* A local the typing knows: its pointer variable, its scope entry, and its
   declared type evaluating to the entry's type.  As stmtSimAugAssign's
   expr_sim_inv_local, restated here so the judgment does not depend on the
   statement simulation. *)
Theorem expr_sim_inv_local[local]:
  !cenv cx env es id ty.
    expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty ==>
    (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    (?entry. lookup_scopes id es.scopes = SOME entry) /\
    !entry. lookup_scopes id es.scopes = SOME entry ==>
            evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  cheat
QED

(* ===== Leaves ===== *)

(* No code, and the post at the start state. *)
Theorem target_post_refl[local]:
  !ctx func cenv cx es sa s pv vt r.
    stmt_state_rel ctx func cenv cx es s /\
    (?w. eval_operand (FST r) s = SOME w /\
         place_ptr_rel cenv cx s pv w (FST (SND r)) vt) /\
    SND (SND r) = SOME (value_type_place vt) /\
    (!x. FST r = Var x ==> not_fresh_at sa x) /\
    place_readable cx es pv ==>
    target_post ctx func cenv cx es sa sa s es pv vt r s
Proof
  cheat
QED

(* A local: its place MemoryPlace x [] at its pointer, no code. *)
Theorem target_name_case:
  !nocalls ctx func cenv cx id.
    target_case nocalls ctx func cenv cx (NameTarget id)
Proof
  cheat
QED

(* The compile environment holds a storage, transient or mapping variable
   at the layout's slot (storage_vars_rel, transient_vars_rel). *)
Theorem toplevel_decl_ce_vars[local]:
  !cenv cx src id ts d id_str tr slot.
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (d, id_str) /\
    var_decl_transient d = tr /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot ==>
    FLOOKUP cenv.ce_module_vars (src, id) =
      SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))
Proof
  cheat
QED

(* A module variable target, typed: a storage or transient variable of its
   declared type, or a mapping of its declared key and value types.
   bare_global_assignable and bare_globals name immutables, which have no
   storage declaration. *)
Theorem toplevel_target_decl[local]:
  !env cx st src id vt.
    type_place_target env (TopLevelNameTarget (src,id)) = SOME vt /\
    env_consistent env cx st /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts <> NONE) ==>
    ?ts tr id_str slot.
      get_module_code cx src = SOME ts /\
      ((?ty tv. vt = Type ty /\
                find_var_decl_by_name id ts =
                  SOME (StorageVarDecl tr ty, id_str) /\
                evaluate_type (get_tenv cx) ty = SOME tv /\
                lookup_var_slot_from_layout cx tr src id_str = SOME slot) \/
       (?kt vt'. vt = HashMapT kt vt' /\
                 find_var_decl_by_name id ts =
                   SOME (HashMapVarDecl tr kt vt', id_str) /\
                 lookup_var_slot_from_layout cx tr src id_str = SOME slot))
Proof
  cheat
QED

(* A typed module variable target has its compile environment entries: a
   storage or transient variable is not a mapping and has its declared
   type, a mapping its declared key and value types (expr_sim_inv's
   storage clause and place_map_tables_agree_on_defined). *)
Theorem toplevel_target_env:
  !cenv cx env es src id vt ts d id_str.
    expr_sim_inv cenv cx env es /\
    type_place_target env (TopLevelNameTarget (src,id)) = SOME vt /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (d, id_str) ==>
    (!tr typ. d = StorageVarDecl tr typ ==>
              cenv.ce_hashmap_info (src,id) = NONE /\
              cenv.ce_module_var_type (src,id) = SOME typ) /\
    (!tr kt vt'. d = HashMapVarDecl tr kt vt' ==>
                 ?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt'))
Proof
  cheat
QED

(* A storage, transient or mapping variable: its slot, no code. *)
Theorem target_toplevel_case:
  !nocalls ctx func cenv cx nsid.
    target_case nocalls ctx func cenv cx (TopLevelNameTarget nsid)
Proof
  cheat
QED



