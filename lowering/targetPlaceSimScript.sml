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
 * TOP-LEVEL:
 *   mem_field_offset, mem_step_offset, mem_path_offset — the byte offset of
 *                          a field, an element and a path in a type's
 *                          memory layout
 *   mem_path_offset_sound — a path's offset is where subscripts_type puts
 *                          it, inside the type's bytes
 *   place_ptr_rel, place_readable, target_post, target_res_ok,
 *   target_sim             — the judgment
 *   target_env_ok, target_root, immutable_root, target_indices_pre,
 *   target_pre, target_case, target_idx_case — its premises and the shared
 *                          case form (as expr_vv_case: nocalls = T for
 *                          compile_expr_sim, F for the body simulation)
 *   target_name_case       — a local: its pointer, no code
 *   target_toplevel_case   — a storage or transient variable or a mapping:
 *                          its slot, no code
 * The steps (fields, subscripts) and the induction over targets are in
 * targetPlaceSimCases.
 *
 * Helpers: mem_field_offset_layout, mem_path_offset_snoc, target_pre_sub,
 *   expr_sim_inv_local, target_post_refl, toplevel_decl_ce_vars, toplevel_target_decl
 *)

Theory targetPlaceSim
Ancestors
  list rich_list finite_map pair
  fragExec exprSim exprSimHyps exprSimAttributeFields
  exprLowering exprLoweringProps compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperValue
  vyperTypeSystem vyperTypeEnv vyperTypeInvariants vyperPlaceResultTyping
  venomState venomInst
Libs
  pairLib

(* ===== Offsets in memory ===== *)

(* The byte offset of a field in a struct's memory layout, and its type:
   the preceding fields' sizes, as struct_field_slot sums slots. *)
Definition mem_field_offset_def:
  mem_field_offset [] id = NONE /\
  mem_field_offset ((name,tv)::fields) id =
    if name = id then SOME (0n,tv)
    else OPTION_MAP (\(off,ftv). (type_memory_size tv + off,ftv))
           (mem_field_offset fields id)
End

(* One step of a path: a field, or an element of an array (past the length
   word of a DynArray) or a tuple, where subscript_type has it. *)
Definition mem_step_offset_def:
  mem_step_offset (StructTV fields) (AttrSubscript id) =
    mem_field_offset fields id /\
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < n then SOME (Num i * type_memory_size etv, etv)
     else NONE) /\
  mem_step_offset (ArrayTV etv (Dynamic n)) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < n then SOME (32 + Num i * type_memory_size etv, etv)
     else NONE) /\
  mem_step_offset (TupleTV tvs) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < LENGTH tvs then
       SOME (type_memory_size_list (TAKE (Num i) tvs), EL (Num i) tvs)
     else NONE) /\
  mem_step_offset _ _ = NONE
End

Definition mem_path_offset_def:
  mem_path_offset tv [] = SOME (0n,tv) /\
  mem_path_offset tv (sb::path) =
    case mem_step_offset tv sb of
    | NONE => NONE
    | SOME (k,etv) =>
        OPTION_MAP (\(k',ptv). (k + k',ptv)) (mem_path_offset etv path)
End

Theorem mem_path_offset_snoc:
  !path tv k ptv sb k2 etv.
    mem_path_offset tv path = SOME (k,ptv) /\
    mem_step_offset ptv sb = SOME (k2,etv) ==>
    mem_path_offset tv (path ++ [sb]) = SOME (k + k2,etv)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  first_x_assum drule_all >> simp[]
QED

(* A field of a struct ce_struct_fields lays out as its type value: its
   offset is struct_field_offset's. *)
Theorem mem_field_offset_layout:
  !flds fs fld ftv.
    fields_layout flds fs /\ ALOOKUP fs fld = SOME ftv ==>
    mem_field_offset fs fld = SOME (struct_field_offset flds fld, ftv)
Proof
  simp[fields_layout_def] >>
  Induct >> simp[] >> PairCases >> Cases >> simp[] >>
  PairCases_on `h` >>
  simp[struct_field_offset_def, mem_field_offset_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >> IF_CASES_TAC >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem mem_field_offset_sound[local]:
  !fs fld k ftv.
    mem_field_offset fs fld = SOME (k,ftv) ==>
    ALOOKUP fs fld = SOME ftv /\
    k + type_memory_size ftv <= type_memory_size_fields fs
Proof
  Induct >> simp[mem_field_offset_def] >> PairCases >>
  simp[mem_field_offset_def, type_memory_size_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[PULL_EXISTS, FORALL_PROD] >>
  rpt strip_tac >> res_tac >> simp[]
QED

Theorem type_memory_size_list_take_el[local]:
  !tvs n. n < LENGTH tvs ==>
    type_memory_size_list (TAKE n tvs) + type_memory_size (EL n tvs) <=
    type_memory_size_list tvs
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `n` >>
  simp[type_memory_size_def] >> strip_tac >> res_tac >> simp[]
QED

Theorem mul_succ_le[local]:
  !i n. i < n ==> !s. i * s + s <= n * s
Proof
  rpt strip_tac >> REWRITE_TAC [GSYM arithmeticTheory.MULT] >>
  irule arithmeticTheory.LESS_MONO_MULT >> simp[]
QED

Theorem mem_step_offset_sound[local]:
  !tv sb k etv.
    mem_step_offset tv sb = SOME (k,etv) ==>
    subscript_type tv sb = SOME etv /\
    k + type_memory_size etv <= type_memory_size tv
Proof
  rpt gen_tac >> Cases_on `tv` >> Cases_on `sb` >>
  TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  TRY (rename1 `ArrayTV _ bd` >> Cases_on `bd`) >>
  simp[mem_step_offset_def, subscript_type_def, type_memory_size_def] >>
  rw[] >> gvs[] >>
  TRY (drule mem_field_offset_sound >> simp[] >> NO_TAC) >>
  TRY (drule type_memory_size_list_take_el >> simp[] >> NO_TAC) >>
  qpat_x_assum `Num _ < _` (mp_tac o MATCH_MP mul_succ_le) >>
  disch_then (qspec_then `type_memory_size etv` mp_tac) >> simp[]
QED

(* A path's offset is where the source's subscripts_type puts the path, and
   the place's bytes lie inside the type's. *)
Theorem mem_path_offset_sound:
  !path tv k ptv.
    mem_path_offset tv path = SOME (k,ptv) ==>
    subscripts_type tv path = SOME ptv /\
    k + type_memory_size ptv <= type_memory_size tv
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def, subscripts_type_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  drule mem_step_offset_sound >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[subscripts_type_def]
QED

(* ===== The judgment ===== *)

(* The location of a storage or transient place. *)
Definition slot_loc_def:
  slot_loc tr = if tr then LocTransient else LocStorage
End

(* w is where the lowering finds the source place pv of type vt, at
   location loc, in s (see the header).  A local's place is at its pointer
   plus the path's offset in its declared type. *)
Definition place_ptr_rel_def:
  (place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc vt <=>
     ?p sz b t0 tv0 k tv t.
       FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
       lookup_var p s = SOME b /\
       cenv.ce_var_type id = SOME t0 /\
       evaluate_type (get_tenv cx) t0 = SOME tv0 /\
       mem_path_offset tv0 path = SOME (k,tv) /\
       w = b + n2w k /\ loc = SOME LocMemory /\
       vt = Type t /\ evaluate_type (get_tenv cx) t = SOME tv) /\
  (place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot tv)) w loc vt <=>
     w = slot /\ loc = SOME (slot_loc tr) /\
     ?t. vt = Type t /\ evaluate_type (get_tenv cx) t = SOME tv) /\
  (place_ptr_rel cenv cx s (HashMapRef tr slot kt vt') w loc vt <=>
     w = slot /\ loc = SOME (slot_loc tr) /\ vt = HashMapT kt vt') /\
  (place_ptr_rel cenv cx s (PlaceR (ImmutablePlace src id path)) w loc vt <=>
     F) /\
  (place_ptr_rel cenv cx s (Value v) w loc vt <=> F)
End

(* A local's place reads at es: extending it can fail only by a type
   error.  A place is formed where it reads, but an index evaluated after
   the base can pop the base's array (x[i][x[i].pop()]). *)
Definition place_readable_def:
  (place_readable cx es (PlaceR (MemoryPlace id path)) <=>
     ?v. read_place cx (MemoryPlace id path) es = (INL v,es)) /\
  (place_readable cx es pv <=> T)
End

(* After the target's fragment, run from s0 related at es, in s related at
   es', with the source's place pv of type vt: the pointer r's operand is
   at pv, and r's place type is vt's.  The operand is not fresh at the
   fragment's end, so code lowered after it keeps it.  The frame is
   vv_post's: the variables and allocations from before, the memory of the
   allocations made before the fragment's start but those holding a local,
   and the live locals' memory but their root DynArray length words.
   Nested length words are not exempt: indices that pop nested arrays
   require a repair of the shared expression/target frame (see
   target_subscript_case). *)
Definition target_post_def:
  target_post ctx func cenv cx es sa sb s0 es' pv vt
    (r : operand # data_location option # place_ty option) s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    (?w. eval_operand (FST r) s = SOME w /\
         place_ptr_rel cenv cx s pv w (FST (SND r)) vt) /\
    SND (SND r) = SOME (value_type_place vt) /\
    (!x. FST r = Var x ==> not_fresh_at sb x) /\
    place_readable cx es' pv /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s
End

(* The source results the judgment speaks of: a place or a mapping, an
   error other than a type error, or an assertion. *)
Definition target_res_ok_def:
  target_res_ok (res : eval_result + exception) <=>
    (?pv. res = INL pv) \/ (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str))
End

(* The judgment: the target's fragment of bt, typed vt, run from a state
   related at es, reaches its end in target_post on a place, and exits as
   expr_exit allows on an error. *)
Definition target_sim_def:
  target_sim ctx func cenv cx env bt es <=>
    !vt sa sb r res es' s0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      eval_base_place cx bt es = (res, es') /\ target_res_ok res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?pv. res = INL pv /\
                  target_post ctx func cenv cx es sa sb s0 es' pv vt r s)
        (expr_exit res)
End

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
    expr_sim_inv cenv cx env es /\ target_env_ok cenv cx /\
    ~immutable_root cx bt /\ target_indices_pre cenv cx env bt
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
  rw[target_pre_def, immutable_root_def, target_root_def,
     target_indices_pre_def]
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
  rpt gen_tac >> strip_tac >>
  fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
  qpat_x_assum `!id ty. _ ==> IS_SOME _` drule >>
  qpat_x_assum `!id ty. _ ==> ?p sz. _` drule >>
  simp[optionTheory.IS_SOME_EXISTS] >> rpt strip_tac >>
  qpat_x_assum `!id ty entry. _ /\ _ ==> _` drule_all >> simp[]
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
  rw[target_post_def] >> metis_tac[]
QED

(* A local: its place MemoryPlace x [] at its pointer, no code. *)
Theorem target_name_case:
  !nocalls ctx func cenv cx id.
    target_case nocalls ctx func cenv cx (NameTarget id)
Proof
  rw[target_case_def, target_sim_def, target_pre_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  irule target_post_refl >> simp[value_type_place_def] >>
  `?b. lookup_var p s = SOME b` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  simp[eval_operand_def, place_ptr_rel_def, mem_path_offset_def,
       place_readable_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, return_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, wordsTheory.WORD_ADD_0]
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
  rpt strip_tac >> Cases_on `tr` >>
  gvs[storage_vars_rel_def, transient_vars_rel_def] >> metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  drule_all type_place_target_global_lookup >> strip_tac >>
  Cases_on `vt`
  >- (Cases_on `FLOOKUP env.bare_globals (src,id)`
      >- (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
          gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
      drule_all env_consistent_bare_global_find_NONE >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

(* A storage, transient or mapping variable: its slot, no code. *)
Theorem target_toplevel_case:
  !nocalls ctx func cenv cx nsid.
    target_case nocalls ctx func cenv cx (TopLevelNameTarget nsid)
Proof
  rw[target_case_def, target_sim_def, target_pre_def] >>
  PairCases_on `nsid` >> rename1 `TopLevelNameTarget (src,id)` >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts <> NONE` by
    (fs[immutable_root_def, target_root_def] >> metis_tac[]) >>
  drule_all toplevel_target_decl >> strip_tac >> gvs[]
  >- suspend "storage" >>
  suspend "mapping"
QED

Resume target_toplevel_case[storage]:
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, ignore_bind_def,
       record_storage_event_def, lift_option_type_def, return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  `cenv.ce_hashmap_info (src,id) = NONE /\
   cenv.ce_module_var_type (src,id) = SOME ty` by
    (fs[target_env_ok_def] >> metis_tac[]) >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- (simp[frag_exec_def] >> rpt strip_tac >>
      gvs[stmt_state_rel_def, state_rel_def]) >>
  qspecl_then [`cenv`, `cx`, `src`, `id`, `ts`, `StorageVarDecl tr ty`,
               `id_str`, `tr`, `slot`] mp_tac toplevel_decl_ce_vars >>
  simp[var_decl_transient_def] >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  simp[target_post_def, eval_operand_def, place_ptr_rel_def, slot_loc_def,
       value_type_place_def, place_readable_def, locals_kept_def]
QED

Resume target_toplevel_case[mapping]:
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  `?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt')` by
    (fs[target_env_ok_def] >> metis_tac[]) >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- (simp[frag_exec_def] >> rpt strip_tac >>
      gvs[stmt_state_rel_def, state_rel_def]) >>
  qspecl_then [`cenv`, `cx`, `src`, `id`, `ts`, `HashMapVarDecl tr kt vt'`,
               `id_str`, `tr`, `slot`] mp_tac toplevel_decl_ce_vars >>
  simp[var_decl_transient_def] >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  irule target_post_refl >>
  simp[eval_operand_def, place_ptr_rel_def, slot_loc_def,
       value_type_place_def, place_readable_def]
QED

Finalise target_toplevel_case
