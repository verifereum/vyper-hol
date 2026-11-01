(*
 * Top-Level Vyper Compiler: toplevel list → byte list option
 *
 * Packages the full compilation pipeline:
 *   1. Extract metadata from toplevel list
 *   2. Build per-function compile_env
 *   3. Lower: Vyper AST → Venom IR (via compile_generate_runtime)
 *   4. Optimize: pipeline of Venom passes
 *   5. Codegen: Venom IR → EVM bytecode
 *
 * TOP-LEVEL:
 *   compile_vyper          -- toplevel list → byte list option
 *   compile_vyper_eval     -- bounded-dataflow evaluator variant
 *
 * The storage/transient layout (variable name → slot) comes from the
 * Python compiler's annotated AST, NOT recomputed here.
 * fn_eom is internal to the Venom pipeline and codegen.
 *)

Theory compileVyper
Ancestors
  exprLowering
  vyperCompiler
  venomPipeline
  codegen
  selectorDispatch
  jumptableUtils
  vyperContext
  vyperEvent
  valueEncoding
  compileEnv
  vyperAST
  byte


(* ===== Struct Fields Map ===== *)

(* Compute memory bytes for a type given a struct field map.
   Same as type_memory_bytes but takes sft directly (no cenv). *)
Definition type_mem_bytes_def:
  type_mem_bytes (sft : string -> (string # type # num) list)
    (BaseT (BytesT (Dynamic n))) = 32 + ((n + 31) DIV 32) * 32 ∧
  type_mem_bytes sft (BaseT (StringT n)) = 32 + ((n + 31) DIV 32) * 32 ∧
  type_mem_bytes sft (BaseT _) = 32 ∧
  type_mem_bytes sft (FlagT _) = 32 ∧
  type_mem_bytes sft (ArrayT elem_ty (Fixed n)) =
    n * type_mem_bytes sft elem_ty ∧
  type_mem_bytes sft (ArrayT elem_ty (Dynamic n)) =
    32 + n * type_mem_bytes sft elem_ty ∧
  type_mem_bytes sft (StructT nsid) =
    SUM (MAP (SND o SND) (sft (nsid_to_string nsid))) ∧
  type_mem_bytes sft (TupleT tys) =
    SUM (MAP (type_mem_bytes sft) tys) ∧
  type_mem_bytes sft NoneT = 0
Termination
  WF_REL_TAC `measure (type_size o SND)`
End

(* Memory size of a struct field, resolved against the whole program's type
   environment.  Vyper resolves type declarations in any order
   (ModuleAnalyzer._visit_nodes_looping), so a field may name a struct
   declared later; sizing it against only the earlier declarations would
   give that field size 0.  Like the rest of the compiler (ce_module = NONE),
   this covers the main module only: a field whose type doesn't evaluate in
   its type_env, such as an imported flag, gets size 0. *)
Definition field_mem_bytes_def:
  field_mem_bytes tenv ty =
    case evaluate_type tenv ty of
      SOME tv => type_memory_size tv
    | NONE => 0
End

Definition build_struct_fields_one_def:
  build_struct_fields_one tenv (args : (string # type) list) =
    MAP (λ(name, ty). (name, ty, field_mem_bytes tenv ty)) args
End

(* Field sizes use the complete semantic environment, so a reference to a
   later struct declaration has the same layout as an earlier reference.
   Invalid field types are rejected by check_contract before compilation. *)
Definition build_struct_fields_map_def:
  build_struct_fields_map tenv []
    (sft : (string, (string # type # num) list) fmap) = sft ∧
  build_struct_fields_map tenv (top :: rest) sft =
    case top of
      StructDecl sname args =>
        build_struct_fields_map tenv rest
          (sft |+ (sname, build_struct_fields_one tenv args))
    | _ => build_struct_fields_map tenv rest sft
End

Definition make_struct_fields_map_def:
  make_struct_fields_map tops =
    build_struct_fields_map (type_env tops) tops FEMPTY
End

(* ===== Simple AST Extractors ===== *)

Definition build_flag_member_id_one_def:
  build_flag_member_id_one [] (idx : num) = (K 0n) ∧
  build_flag_member_id_one (m :: ms) idx =
    let rest = build_flag_member_id_one ms (idx + 1) in
    (λname. if name = m then idx else rest name)
End

Definition build_flag_info_def:
  build_flag_info [] fmid fnm = (fmid, fnm) ∧
  build_flag_info (top :: rest) fmid fnm =
    case top of
      FlagDecl fname members =>
        build_flag_info rest
          (λfn. if fn = fname then build_flag_member_id_one members 0
                else fmid fn)
          (λfn. if fn = fname then LENGTH members else fnm fn)
    | _ => build_flag_info rest fmid fnm
End

Definition build_var_type_map_def:
  build_var_type_map ([] : toplevel list) = (K NONE : nsid -> type option) ∧
  build_var_type_map (top :: rest) =
    case top of
      VariableDecl _ _ vname ty _ =>
        (λn. if n = (NONE, vname) then SOME ty
             else build_var_type_map rest n)
    | _ => build_var_type_map rest
End

(* Sum of memory_bytes_required for all immutable variables.
   Mirrors Python: module_t.immutable_section_bytes. *)
Definition compute_immutables_len_def:
  compute_immutables_len sft ([] : toplevel list) = (0 : num) ∧
  compute_immutables_len sft (top :: rest) =
    (case top of
       VariableDecl _ Immutable _ ty _ =>
         type_mem_bytes sft ty + compute_immutables_len sft rest
     | _ => compute_immutables_len sft rest)
End

Definition build_hashmap_info_def:
  build_hashmap_info ([] : toplevel list) =
    (K NONE : nsid -> (bool # type # value_type) option) ∧
  build_hashmap_info (top :: rest) =
    case top of
      HashMapDecl _ tr hname kt vt _ =>
        (λn. if n = (NONE, hname) then SOME (tr, kt, vt)
             else build_hashmap_info rest n)
    | _ => build_hashmap_info rest
End

Theorem build_hashmap_info_head[simp]:
  build_hashmap_info (HashMapDecl vis tr name kt vt slot :: rest)
    ((NONE, name)) = SOME (tr, kt, vt)
Proof
  simp[build_hashmap_info_def]
QED

Theorem build_hashmap_info_other:
  n ≠ (NONE, name) ⇒
  build_hashmap_info (HashMapDecl vis tr name kt vt slot :: rest) n =
    build_hashmap_info rest n
Proof
  simp[build_hashmap_info_def]
QED

Theorem build_hashmap_info_transient:
  build_hashmap_info [HashMapDecl vis T name kt vt slot]
    ((NONE, name)) = SOME (T, kt, vt)
Proof
  simp[build_hashmap_info_def]
QED

(* The leftmost declaration wins, including when declarations are appended. *)
Theorem build_hashmap_info_append:
  !xs ys n. build_hashmap_info (xs ++ ys) n =
    case build_hashmap_info xs n of
      NONE => build_hashmap_info ys n
    | SOME info => SOME info
Proof
  Induct >> simp[build_hashmap_info_def] >>
  Cases_on `h` >> simp[build_hashmap_info_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem build_hashmap_info_some:
  !tops n tr kt vt.
    build_hashmap_info tops n = SOME (tr, kt, vt) ==>
    ?pre post vis name slot.
      tops = pre ++ HashMapDecl vis tr name kt vt slot :: post /\
      n = (NONE, name) /\
      build_hashmap_info pre n = NONE
Proof
  Induct >> simp[build_hashmap_info_def] >>
  Cases_on `h` >> simp[build_hashmap_info_def] >> rpt gen_tac
  >> TRY (IF_CASES_TAC >> gvs[])
  >> rpt strip_tac
  >> TRY (qexists `[]` >> simp[build_hashmap_info_def] >> NO_TAC)
  >> first_x_assum drule >> strip_tac
  >> qmatch_goalsub_abbrev_tac `head::tops`
  >> qexists `head::pre` >> simp[Abbr `head`, build_hashmap_info_def]
  >> metis_tac[]
QED

(* ===== Event Info ===== *)

(* event_hash is shared with the source semantics in vyperEventTheory.
   is_bytestring_type is in compileEnvTheory. *)

Definition build_event_info_def:
  build_event_info tenv ([] : toplevel list) eim = eim ∧
  build_event_info tenv (top :: rest) eim =
    case top of
      EventDecl ename args_indexed =>
        let arg_types = MAP (SND o FST) args_indexed in
        let ehash = event_hash tenv ename arg_types in
        let indexed_flags = MAP SND args_indexed in
        build_event_info tenv rest
          (λn. if n = ename then SOME (ehash, arg_types, indexed_flags) else eim n)
    | _ => build_event_info tenv rest eim
End

Theorem build_event_info_lookup_event_metadata_in:
  ∀tops.
    event_decl_unique ename tops ⇒
    ∀eim.
      build_event_info tenv tops eim ename =
      case lookup_event_metadata_in tenv ename tops of
      | NONE => eim ename
      | SOME metadata => SOME metadata
Proof
  Induct_on `tops` >>
  simp[build_event_info_def, lookup_event_metadata_in_def] >>
  Cases_on `h` >>
  gvs[build_event_info_def, lookup_event_metadata_in_def,
      event_decl_unique_def] >>
  Cases_on `s = ename` >> gvs[] >>
  Cases_on `lookup_event_metadata_in tenv ename tops`
  >- simp[] >>
  drule lookup_event_metadata_in_some >>
  strip_tac >>
  strip_tac >>
  qpat_x_assum `∀args args'. _`
    (qspecl_then [`l`, `args`] mp_tac) >>
  simp[]
QED

Theorem build_event_info_empty_lookup_event_metadata_in:
  event_decl_unique ename tops ⇒
  build_event_info tenv tops (K NONE) ename =
  lookup_event_metadata_in tenv ename tops
Proof
  strip_tac >>
  drule build_event_info_lookup_event_metadata_in >>
  Cases_on `lookup_event_metadata_in tenv ename tops` >> simp[]
QED

Theorem build_event_info_empty_lookup_event_metadata:
  ALOOKUP sources target = SOME mods ⇒
  ALOOKUP mods NONE = SOME tops ⇒
  event_decl_unique ename tops ⇒
  build_event_info tenv tops (K NONE) ename =
  lookup_event_metadata tenv sources target (NONE, ename)
Proof
  simp[lookup_event_metadata_def,
       build_event_info_empty_lookup_event_metadata_in]
QED

(* ===== Nonreentrant Keys ===== *)

Definition assign_nkeys_def:
  assign_nkeys ([] : toplevel list) (next : num) = (K 0n : string -> num) ∧
  assign_nkeys (top :: rest) next =
    case top of
      FunctionDecl _ _ T _ fname _ _ _ _ =>
        let nkey_map = assign_nkeys rest (next + 1) in
        (λn. if n = fname then next else nkey_map n)
    | _ => assign_nkeys rest next
End

(* ===== Function Classification ===== *)

(* Classify functions into external, internal, fallback, and constructor.
   Deploy (__init__) goes into a separate ctor slot, NOT into internal fns.
   In Python, runtime and deploy are separate IRContexts:
   - Runtime: external fns + internal fns (is_ctor_context=False)
   - Deploy: __init__ + ctor-reachable internal fns (is_ctor_context=True)
   raw_return is threaded through the tuples for ce_raw_return. *)
Definition classify_function_def:
  classify_function (FunctionDecl vis mut nr rr fname fargs dflts ret body)
    (exts, ints, fb, ctor) =
    (case vis of
       External =>
         if fname = "__default__" then
           (exts, ints, SOME (mut, nr, rr, fname, fargs, dflts, ret, body),
            ctor)
         else
           ((mut, nr, rr, fname, fargs, dflts, ret, body) :: exts,
            ints, fb, ctor)
     | Internal =>
         (exts,
          (mut, nr, rr, fname, fargs, dflts, ret, body) :: ints,
          fb, ctor)
     | Deploy =>
         (exts, ints, fb,
          SOME (mut, nr, rr, fname, fargs, dflts, ret, body))) ∧
  classify_function _ acc = acc
End

Definition classify_functions_def:
  classify_functions tops = FOLDR classify_function ([], [], NONE, NONE) tops
End

(* ===== Memory Allocation ===== *)

Definition allocate_args_def:
  allocate_args sft [] (offset : num) vars = (vars, offset) ∧
  allocate_args sft ((name, ty) :: rest) offset vars =
    let sz = type_mem_bytes sft ty in
    allocate_args sft rest (offset + sz)
      (vars |+ (name, MemLoc offset sz))
End

(* Slots of an internal function's return buffer pointer (if it has one) and
   return PC, after its parameters. They go to ce_return_buf / ce_return_pc, not
   ce_vars, so they cannot collide with user identifiers. *)
Definition allocate_internal_special_vars_def:
  allocate_internal_special_vars has_return_buf offset =
    if has_return_buf then
      (SOME (MemLoc offset 32), SOME (MemLoc (offset + 32) 32))
    else (NONE, SOME (MemLoc offset 32))
End

Definition add_module_var_locations_def:
  add_module_var_locations ([] : toplevel list)
    (vars : (nsid, var_location) fmap) = vars ∧
  add_module_var_locations (top :: rest) vars =
    let vars' =
      case top of
        VariableDecl _ Storage name _ (SOME slot) =>
          vars |+ ((NONE, name), StorageLoc (n2w slot))
      | VariableDecl _ Transient name _ (SOME slot) =>
          vars |+ ((NONE, name), TransientLoc (n2w slot))
      | HashMapDecl _ transient name _ _ (SOME slot) =>
          vars |+ ((NONE, name),
            if transient then TransientLoc (n2w slot)
            else StorageLoc (n2w slot))
      | _ => vars in
    add_module_var_locations rest vars'
End

(* Immutable offsets use the same module namespace as storage variables. *)
Definition add_immutable_locations_def:
  add_immutable_locations sft ([] : toplevel list) (off : num)
    (vars : (nsid, var_location) fmap) = vars /\
  add_immutable_locations sft (top :: rest) off vars =
    case top of
      VariableDecl _ Immutable name ty _ =>
        add_immutable_locations sft rest (off + type_mem_bytes sft ty)
          (vars |+ ((NONE, name), ImmutableLoc off))
    | _ => add_immutable_locations sft rest off vars
End

Theorem compute_immutables_len_append:
  !xs ys. compute_immutables_len sft (xs ++ ys) =
    compute_immutables_len sft xs + compute_immutables_len sft ys
Proof
  Induct >> simp[compute_immutables_len_def] >>
  Cases_on `h` >> simp[compute_immutables_len_def] >>
  CASE_TAC >> decide_tac
QED

Theorem add_immutable_locations_append:
  !xs ys off vars.
    add_immutable_locations sft (xs ++ ys) off vars =
    add_immutable_locations sft ys (off + compute_immutables_len sft xs)
      (add_immutable_locations sft xs off vars)
Proof
  Induct >> simp[add_immutable_locations_def, compute_immutables_len_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[add_immutable_locations_def, compute_immutables_len_def] >>
  CASE_TAC >>
  simp[add_immutable_locations_def, compute_immutables_len_def, arithmeticTheory.ADD_ASSOC]
QED

Theorem add_immutable_locations_lookup_unchanged:
  !tops off vars key.
    (!vis name ty slot.
      MEM (VariableDecl vis Immutable name ty slot) tops ==>
      (NONE, name) <> key) ==>
    FLOOKUP (add_immutable_locations sft tops off vars) key = FLOOKUP vars key
Proof
  Induct >- simp[add_immutable_locations_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h` >>
  gvs[add_immutable_locations_def] >>
  (CASE_TAC ORELSE all_tac) >>
  gvs[add_immutable_locations_def] >>
  TRY (last_x_assum irule >> metis_tac[] >> NO_TAC) >>
  rename1 `add_immutable_locations sft tops (off + type_mem_bytes sft ty)
    (vars |+ ((NONE, name), ImmutableLoc off))` >>
  `(NONE, name) <> key` by metis_tac[] >>
  last_x_assum (qspecl_then
    [`off + type_mem_bytes sft ty`,
     `vars |+ ((NONE, name), ImmutableLoc off)`, `key`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem add_immutable_locations_declaration_lookup:
  (!vis' name' ty' slot'.
    MEM (VariableDecl vis' Immutable name' ty' slot') suffix ==>
    name' <> name) ==>
  FLOOKUP (add_immutable_locations sft
    (prefix ++ VariableDecl vis Immutable name ty slot :: suffix) off vars)
    ((NONE, name)) =
  SOME (ImmutableLoc (off + compute_immutables_len sft prefix))
Proof
  strip_tac >> simp[add_immutable_locations_append,
    add_immutable_locations_def] >>
  qmatch_goalsub_abbrev_tac `FLOOKUP (add_immutable_locations sft suffix o2 v2) _` >>
  `FLOOKUP (add_immutable_locations sft suffix o2 v2) (NONE,name) =
   FLOOKUP v2 (NONE,name)`
    by (irule add_immutable_locations_lookup_unchanged >> simp[] >>
        metis_tac[]) >>
  simp[Abbr `v2`, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem immutable_declaration_interval_bound:
  off + compute_immutables_len sft prefix + type_mem_bytes sft ty <=
  off + compute_immutables_len sft
    (prefix ++ VariableDecl vis Immutable name ty slot :: suffix)
Proof
  simp[compute_immutables_len_append, compute_immutables_len_def]
QED

Theorem last_immutable_region_end:
  off + compute_immutables_len sft prefix + type_mem_bytes sft ty =
  off + compute_immutables_len sft
    (prefix ++ [VariableDecl vis Immutable name ty slot])
Proof
  simp[compute_immutables_len_append, compute_immutables_len_def]
QED

(* ===== Dynamic Array Capacity ===== *)

Definition dynarray_capacity_of_type_def:
  dynarray_capacity_of_type (ArrayT _ (Dynamic n)) = SOME n ∧
  dynarray_capacity_of_type _ = NONE
End

Definition build_dynarray_capacity_def:
  build_dynarray_capacity ([] : ('a # type) list) = (K 0n : 'a -> num) ∧
  build_dynarray_capacity ((vname, ty) :: rest) =
    let rest_map = build_dynarray_capacity rest in
    case dynarray_capacity_of_type ty of
      SOME n => (λs. if s = vname then n else rest_map s)
    | NONE => rest_map
End

Definition collect_module_vars_def:
  collect_module_vars ([] : toplevel list) = ([] : (nsid # type) list) ∧
  collect_module_vars (top :: rest) =
    (case top of
       VariableDecl _ _ vname ty _ => [((NONE, vname), ty)]
     | _ => []) ++ collect_module_vars rest
End

(* ===== Internal Function Info ===== *)

Definition build_func_info_def:
  build_func_info sft ([] : toplevel list) =
    (K (0n, 0n, [] : bool list) : string -> num # num # bool list) ∧
  build_func_info sft (top :: rest) =
    let rest_map = build_func_info sft rest in
    case top of
      FunctionDecl vis _ _ _ fname fargs _ ret _ =>
        if vis = External then rest_map
        else
          let arg_types = MAP SND fargs in
          let ret_mem = type_mem_bytes sft ret in
          let info = compute_func_info (λn. MAP (FST o SND) (sft n))
                       ret ret_mem arg_types in
          (λs. if s = fname then info else rest_map s)
    | _ => rest_map
End

Definition build_func_param_types_def:
  build_func_param_types ([] : toplevel list) = (K [] : string -> type list) ∧
  build_func_param_types (top :: rest) =
    let rest_map = build_func_param_types rest in
    case top of
      FunctionDecl vis _ _ _ fname fargs _ _ _ =>
        if vis = External then rest_map
        else (λs. if s = fname then MAP SND fargs else rest_map s)
    | _ => rest_map
End

(* Function ids for internal labels (internal_fn_label): a function's
   position among the source's function declarations, counting from n, and
   the first non-external declaration of a name wins, as in
   build_func_param_types. Python numbers the functions it compiles in
   reachability order instead (codegen_venom/module.py IDGenerator); the
   labels only need ids that differ for different names. *)
Definition build_func_ids_def:
  build_func_ids (n : num) ([] : toplevel list) = (K 0 : string -> num) ∧
  build_func_ids n (top :: rest) =
    case top of
      FunctionDecl vis _ _ _ fname _ _ _ _ =>
        let rest_map = build_func_ids (n + 1) rest in
        if vis = External then rest_map
        else (λs. if s = fname then n else rest_map s)
    | _ => build_func_ids n rest
End

(* ===== Positional Args for ABI Decoding ===== *)

Definition build_positional_arg_def:
  build_positional_arg cenv ((name, ty) : string # type) =
    let is_prim = is_word_type ty in
    let is_dyn = is_abi_dynamic cenv.ce_struct_fields ty in
    let abi_sz = abi_embedded_static_size cenv.ce_struct_fields ty in
    let dec = type_to_abi_dec_info cenv.ce_struct_fields cenv ty in
    (name, is_prim, is_dyn, abi_sz, dec)
End

Definition build_positional_args_def:
  build_positional_args cenv args =
    MAP (build_positional_arg cenv) args
End

(* ===== Min Calldata Size ===== *)

Definition min_calldata_size_def:
  min_calldata_size cenv (args : (string # type) list) (n_defaults : num) =
    let required = TAKE (LENGTH args - n_defaults) args in
    let sizes = MAP (λ(_,ty). abi_embedded_static_size cenv.ce_struct_fields ty)
                    required in
    4 + SUM sizes
End
Theorem build_positional_args_single_uint256:
  !cenv name.
    build_positional_args cenv [(name, BaseT (UintT 256))] =
      [(name, T, F, 32, DecPrimWord NoClamp)]
Proof
  simp[build_positional_args_def, build_positional_arg_def,
       is_word_type_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, abi_static_size_def,
       type_to_abi_dec_info_def, type_to_abi_clamp_def]
QED

Theorem min_calldata_size_single_uint256:
  !cenv name.
    min_calldata_size cenv [(name, BaseT (UintT 256))] 0 = 36
Proof
  simp[min_calldata_size_def, abi_embedded_static_size_def,
       is_abi_dynamic_def, abi_static_size_def]
QED


(* ===== Storage Layout from AST ===== *)

(* Extract storage/transient layout from the annotated AST.
   Slots are set on VariableDecl/HashMapDecl during JSON translation. *)
Definition extract_layout_def:
  extract_layout ([] : toplevel list) = (FEMPTY : (string, bytes32) fmap) ∧
  extract_layout (VariableDecl _ (Storage) name _ (SOME slot) :: rest) =
    extract_layout rest |+ (name, n2w slot) ∧
  extract_layout (VariableDecl _ (Transient) name _ (SOME slot) :: rest) =
    extract_layout rest |+ (name, n2w slot) ∧
  extract_layout (HashMapDecl _ _ name _ _ (SOME slot) :: rest) =
    extract_layout rest |+ (name, n2w slot) ∧
  extract_layout (_ :: rest) = extract_layout rest
End

(* ===== Compile Env Construction ===== *)

(* Build a compile_env for a function.
   Storage slots come from the annotated AST (set during JSON translation). *)
Definition build_compile_env_def:
  build_compile_env tops
    vis (mut : function_mutability) func_name
    (args : (string # type) list) (ret_type : type)
    (body : stmt list) (use_transient_locks : bool) =
    let sft = make_struct_fields_map tops in
    let sft_fn = get_struct_fields sft in
    let sft_types = (λname. MAP (FST o SND) (sft_fn name)) in
    let (flag_member_id, flag_n_members) = build_flag_info tops (K (K 0)) (K 0) in
    let storage_layout = extract_layout tops in
    let var_type_map = build_var_type_map tops in
    let hashmap_info = build_hashmap_info tops in
    let tenv = type_env tops in
    let event_info =
          build_event_info tenv tops
            ((K NONE) : string -> (num # type list # bool list) option) in
    let is_external = (vis = External) in
    let rc = returns_stack_count sft_types ret_type in
    let has_return_buf = (rc = 0 ∧ ret_type ≠ NoneT) in
    let module_vars = add_immutable_locations sft_fn tops 0
      (add_module_var_locations tops FEMPTY) in
    let (arg_vars, args_end) = allocate_args sft_fn args 0 FEMPTY in
    let locals = collect_locals body in
    (* Every body allocates each local at its declaration (declare_local), so
       locals get no slot here.
       Mirrors Python: Context.new_variable -> allocate_buffer -> alloca *)
    let (ret_buf, ret_pc) =
      if is_external then (NONE, NONE)
      else allocate_internal_special_vars has_return_buf args_end in
    let dynarray_cap = build_dynarray_capacity (args ++ locals) in
    let func_info = build_func_info sft_fn tops in
    let local_var_type = (λn. ALOOKUP (REVERSE (args ++ locals)) n) in
    <| ce_target := all_capabilities;
       ce_vars := arg_vars;
       ce_module_vars := module_vars;
       ce_storage_layout := storage_layout;
       (* TODO: NONE = main module. For multi-module (imports), should
          be SOME src_id. Currently single-module only. *)
       ce_module := NONE;
       ce_struct_fields := sft;
       ce_dynarray_capacity := dynarray_cap;
       ce_module_dynarray_capacity :=
         build_dynarray_capacity (collect_module_vars tops);
       ce_method_id := (λs tys. w2n (calldata_method_id
                          (function_selector s (vyper_to_abi_types tenv tys))));
       ce_flag_member_id := flag_member_id;
       ce_flag_n_members := flag_n_members;
       ce_var_type := local_var_type;
       ce_module_var_type := var_type_map;
       ce_hashmap_info := hashmap_info;
       ce_event_info := event_info;
       ce_type_env := tenv;
       ce_returns_count := rc;
       ce_return_buf := ret_buf;
       ce_return_pc := ret_pc;
       ce_is_external := is_external;
       ce_ret_enc_info := AbiPrimWord;
       ce_ret_dec_info := DecPrimWord NoClamp;
       ce_max_return_size := 0;
       (* Default: overridden by package_internal_fn for ctor context *)
       ce_is_ctor := (vis = Deploy);
       ce_imm_alloca := NONE;
       ce_func_info := func_info;
       ce_func_param_types := build_func_param_types tops;
       ce_func_ids := build_func_ids 0 tops;
       ce_nonreentrant := (F, 0n, use_transient_locks, mut = View);
       (* Default: overridden by package_*_fn from FunctionDecl raw_return field *)
       ce_raw_return := F;
       ce_alloca_locals := T
    |> : compile_env
End

Theorem build_compile_env_ce_target[simp]:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops vis mut func_name args ret_type body use_trans).
      ce_target = all_capabilities
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem build_compile_env_ce_struct_fields:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops vis mut func_name args ret_type body use_trans).
      ce_struct_fields = make_struct_fields_map tops
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem build_compile_env_ce_func_info:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops vis mut func_name args ret_type body use_trans).
      ce_func_info =
    build_func_info (get_struct_fields (make_struct_fields_map tops)) tops
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem build_compile_env_ce_func_param_types:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops vis mut func_name args ret_type body use_trans).
      ce_func_param_types =
    build_func_param_types tops
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem build_compile_env_ce_func_ids:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops vis mut func_name args ret_type body use_trans).
      ce_func_ids =
    build_func_ids 0 tops
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem build_func_ids_ge[local]:
  !tops n v fm nr rr s args dflts ret body.
    v <> External /\ MEM (FunctionDecl v fm nr rr s args dflts ret body) tops ==>
    n <= build_func_ids n tops s
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >>
  simp[build_func_ids_def] >> rw[] >> gvs[] >>
  first_x_assum drule_all >> simp[] >>
  disch_then (qspec_then `n + 1` mp_tac) >> rw[] >> simp[]
QED

(* Different non-external functions get different ids, so their labels
   differ (internal_fn_label_id_11). *)
Theorem build_func_ids_11:
  !tops n v1 fm1 nr1 rr1 s1 args1 dflts1 ret1 body1
          v2 fm2 nr2 rr2 s2 args2 dflts2 ret2 body2.
    v1 <> External /\ v2 <> External /\
    MEM (FunctionDecl v1 fm1 nr1 rr1 s1 args1 dflts1 ret1 body1) tops /\
    MEM (FunctionDecl v2 fm2 nr2 rr2 s2 args2 dflts2 ret2 body2) tops /\
    build_func_ids n tops s1 = build_func_ids n tops s2 ==>
    s1 = s2
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >>
  simp[build_func_ids_def] >> rw[] >> gvs[] >>
  metis_tac[build_func_ids_ge, DECIDE ``!n:num. ~(n + 1 <= n)``]
QED

(* The call site's parameter types for fname are those of the first
   non-external declaration named fname, so its label agrees with the one
   package_internal_fn gives that declaration. *)
Theorem build_func_param_types_first_decl:
  !pre post vis fm nr rr fname fargs dflts ret body.
    vis <> External /\
    EVERY (\top. !v fm' nr' rr' args' dflts' ret' body'.
             top = FunctionDecl v fm' nr' rr' fname args' dflts' ret' body' ==>
             v = External) pre ==>
    build_func_param_types
      (pre ++ FunctionDecl vis fm nr rr fname fargs dflts ret body :: post)
      fname = MAP SND fargs
Proof
  Induct
  >- simp[build_func_param_types_def]
  >> rpt gen_tac >> strip_tac
  >> Cases_on `h` >> gvs[build_func_param_types_def]
  >> rw[] >> gvs[]
QED

Theorem build_compile_env_external_single_uint_arg_lookup:
  !tops mut func_name arg_name ret_type (body : stmt list) use_trans.
    collect_locals body = [] ==>
    FLOOKUP
      (build_compile_env tops External mut func_name
         [(arg_name, BaseT (UintT 256))] ret_type body use_trans).ce_vars
      arg_name = SOME (MemLoc 0 32)
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[allocate_args_def, type_mem_bytes_def])
  >> EVAL_TAC
QED

(* External functions have no return PC, whatever their argument names. *)
Theorem build_compile_env_external_no_return_pc:
  !tops mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops External mut func_name args ret_type body
       use_trans).ce_return_pc = NONE
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

(* allocate_args places each argument at a MemLoc slot and leaves every
   other name as vars has it. *)
Theorem allocate_args_FLOOKUP_other:
  !sft args off vars vars' off' n.
    allocate_args sft args off vars = (vars', off') /\
    ~MEM n (MAP FST args) ==>
    FLOOKUP vars' n = FLOOKUP vars n
Proof
  gen_tac >> Induct >> simp[allocate_args_def] >>
  Cases_on `h` >> rw[allocate_args_def] >>
  first_x_assum drule >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem allocate_args_FLOOKUP_arg:
  !sft args off vars vars' off' n.
    allocate_args sft args off vars = (vars', off') /\
    MEM n (MAP FST args) ==>
    ?moff sz. FLOOKUP vars' n = SOME (MemLoc moff sz)
Proof
  gen_tac >> Induct >> simp[allocate_args_def] >>
  Cases_on `h` >> simp[allocate_args_def] >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
  Cases_on `MEM n (MAP FST args)`
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[] >> drule_all allocate_args_FLOOKUP_other >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem add_module_var_locations_FLOOKUP:
  !tops vars n loc.
    FLOOKUP (add_module_var_locations tops vars) n = SOME loc ==>
    FLOOKUP vars n = SOME loc \/
    ?slot. loc = StorageLoc slot \/ loc = TransientLoc slot
Proof
  Induct >> simp[add_module_var_locations_def] >>
  rpt gen_tac >> simp[Once add_module_var_locations_def] >>
  strip_tac >> first_x_assum drule >>
  Cases_on `h` >> simp[] >> rpt (CASE_TAC >> simp[]) >>
  rw[finite_mapTheory.FLOOKUP_UPDATE] >> simp[]
QED

Theorem add_immutable_locations_FLOOKUP:
  !sft tops off vars n loc.
    FLOOKUP (add_immutable_locations sft tops off vars) n = SOME loc ==>
    FLOOKUP vars n = SOME loc \/ ?imm_off. loc = ImmutableLoc imm_off
Proof
  gen_tac >> Induct >> simp[add_immutable_locations_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[add_immutable_locations_def] >> rpt (CASE_TAC >> simp[]) >>
  strip_tac >> first_x_assum drule >>
  rw[finite_mapTheory.FLOOKUP_UPDATE] >> simp[]
QED

(* build_compile_env holds the parameters at MemLoc slots and nothing else
   in ce_vars: no other MemLoc variable and no PtrVar. *)
Theorem build_compile_env_vars:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (!n. MEM n (MAP FST args) ==>
         ?off sz.
           FLOOKUP (build_compile_env tops vis mut func_name args ret_type
                      body use_trans).ce_vars n = SOME (MemLoc off sz)) /\
    (!n off sz.
       FLOOKUP (build_compile_env tops vis mut func_name args ret_type
                  body use_trans).ce_vars n = SOME (MemLoc off sz) ==>
       MEM n (MAP FST args)) /\
    (!n p sz.
       FLOOKUP (build_compile_env tops vis mut func_name args ret_type
                  body use_trans).ce_vars n <> SOME (PtrVar p sz))
Proof
  rpt gen_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `!n. MEM n (MAP FST args) ==>
       ?off sz. FLOOKUP arg_vars n = SOME (MemLoc off sz)`
    by (rpt strip_tac >> drule_all allocate_args_FLOOKUP_arg >> simp[]) >>
  `!n loc. FLOOKUP arg_vars n = SOME loc ==> MEM n (MAP FST args)`
    by (rpt strip_tac >> spose_not_then assume_tac >>
        drule_all allocate_args_FLOOKUP_other >> simp[]) >>
  rpt conj_tac
  >- metis_tac[]
  >- metis_tac[] >>
  rpt strip_tac >> `MEM n (MAP FST args)` by metis_tac[] >>
  qpat_x_assum `!n. MEM n _ ==> _` drule >> strip_tac >> gvs[]
QED


Definition external_return_needs_wrap_def:
  external_return_needs_wrap ret_type = needs_external_call_wrap ret_type
End

Theorem external_return_needs_wrap_cases:
  external_return_needs_wrap ty =
    (case ty of TupleT (_::_::_) => F | _ => T)
Proof
  Cases_on `ty` >>
  simp[external_return_needs_wrap_def, vyperABITheory.needs_external_call_wrap_def] >>
  rename1 `LENGTH ts` >> Cases_on `ts` >> simp[] >>
  rename1 `LENGTH rest` >> Cases_on `rest` >> simp[]
QED

Definition update_cenv_ret_abi_def:
  update_cenv_ret_abi cenv ret_type =
    let child_enc = type_to_abi_enc_info cenv.ce_struct_fields cenv ret_type in
    let child_dec = type_to_abi_dec_info cenv.ce_struct_fields cenv ret_type in
    let child_bound = abi_size_bound cenv.ce_struct_fields ret_type in
    let child_dynamic = is_abi_dynamic cenv.ce_struct_fields ret_type in
    let needs_wrap = external_return_needs_wrap ret_type in
    (* Python's calculate_type_for_external_return wraps every single return
       value (including one-tuples and structs) in an ABI tuple.  Dynamic
       children therefore gain a 32-byte offset head. *)
    let enc_info =
      if needs_wrap /\ child_dynamic then
        AbiComplex [(child_enc,
                     abi_embedded_static_size cenv.ce_struct_fields ret_type,
                     type_memory_bytes cenv ret_type,
                     T)]
      else child_enc in
    let max_ret =
      if needs_wrap /\ child_dynamic then 32 + child_bound else child_bound in
    cenv with <| ce_ret_enc_info := enc_info;
                 ce_ret_dec_info := child_dec;
                 ce_max_return_size := max_ret |>
End

Definition update_cenv_nonreentrant_def:
  update_cenv_nonreentrant cenv is_nr nkey use_trans is_view =
    cenv with ce_nonreentrant := (is_nr, nkey, use_trans, is_view)
End

Theorem update_cenv_ret_abi_ce_target[simp]:
  (update_cenv_ret_abi cenv ret_type).ce_target = cenv.ce_target
Proof
  simp[update_cenv_ret_abi_def]
QED

Theorem update_cenv_nonreentrant_ce_target[simp]:
  (update_cenv_nonreentrant cenv nr nkey use_trans is_view).ce_target =
  cenv.ce_target
Proof
  simp[update_cenv_nonreentrant_def]
QED
Theorem compile_env_ce_raw_return_fupd[simp]:
  (cenv with ce_raw_return := rr).ce_target = cenv.ce_target
Proof
  Cases_on `cenv` >> simp[]
QED

Theorem compile_env_ce_is_ctor_fupd[simp]:
  (cenv with ce_is_ctor := is_ctor).ce_target = cenv.ce_target
Proof
  Cases_on `cenv` >> simp[]
QED


Theorem compile_env_target_update_id:
  cenv.ce_target = target ==>
  (cenv with ce_target := target) = cenv
Proof
  Cases_on `cenv` >> simp[compile_env_component_equality]
QED

(* ===== Selector Construction ===== *)

Definition selector_has_trailing_zeroes_def:
  selector_has_trailing_zeroes (sel_num : num) = (sel_num MOD 256 = 0)
End

Definition compute_selector_def:
  compute_selector tenv func_name (arg_types : type list) =
    let abi_types = vyper_to_abi_types tenv arg_types in
    let sel_bytes = function_selector func_name abi_types in
    let sel_num = w2n (calldata_method_id sel_bytes) in
    let entry_lbl = "fn_" ++ func_name in
    (sel_num, entry_lbl, selector_has_trailing_zeroes sel_num)
End

Definition build_selectors_def:
  build_selectors tenv [] = [] ∧
  build_selectors tenv
    ((_, _, _, fname, fargs, _, _, _) :: rest) =
    compute_selector tenv fname (MAP SND fargs) ::
    build_selectors tenv rest
End

(* ===== Function Packaging ===== *)

Definition package_external_fn_def:
  package_external_fn tops use_trans nkey_map
    (mut, nr, rr, fname, fargs, dflts, ret, body) =
    let entry_lbl = "fn_" ++ fname in
    let cenv_base = build_compile_env tops
                      External mut fname fargs ret body use_trans in
    let cenv0 = cenv_base with ce_raw_return := rr in
    let cenv = if ret ≠ NoneT then update_cenv_ret_abi cenv0 ret
               else cenv0 in
    let nkey = nkey_map fname in
    let cenv_final = update_cenv_nonreentrant cenv nr nkey use_trans
                       (mut = View) in
    let pos_args = build_positional_args cenv_final fargs in
    let min_cds = min_calldata_size cenv_final fargs (LENGTH dflts) in
    let is_payable = (mut = Payable) in
    let is_view = (mut = View) in
    (entry_lbl, cenv_final, pos_args, min_cds,
     is_payable, nr, nkey, use_trans, is_view,
     body, if ret = NoneT then NONE else SOME ret)
End

(* ===== Allocation Limit ===== *)

(* A statement (list) contains a valued return.  Mirrors where Python lowers
   one: vyper/codegen_venom/stmt.py:lower_Return. *)
Definition stmt_valued_return_def:
  stmt_valued_return (Return (SOME _)) = T ∧
  stmt_valued_return (Return NONE) = F ∧
  stmt_valued_return (If _ ss1 ss2) =
    (stmts_valued_return ss1 ∨ stmts_valued_return ss2) ∧
  stmt_valued_return (For _ _ _ _ ss) = stmts_valued_return ss ∧
  stmt_valued_return Pass = F ∧
  stmt_valued_return Continue = F ∧
  stmt_valued_return Break = F ∧
  stmt_valued_return (Expr _) = F ∧
  stmt_valued_return (Assert _ _) = F ∧
  stmt_valued_return (Log _ _) = F ∧
  stmt_valued_return (Raise _) = F ∧
  stmt_valued_return (Assign _ _) = F ∧
  stmt_valued_return (AugAssign _ _ _ _) = F ∧
  stmt_valued_return (Append _ _) = F ∧
  stmt_valued_return (AnnAssign _ _ _) = F ∧
  stmts_valued_return [] = F ∧
  stmts_valued_return (st::sts) =
    (stmt_valued_return st ∨ stmts_valued_return sts)
End

(* The return buffer of compile_external_return's ABI-encoding branch is
   below Python's allocation limit, as is the AbiCopy size of an ABI-static
   return type, which is the same number there.
   Mirrors Python: vyper/codegen_venom/context.py:Context.allocate_buffer,
   which raises MemoryAllocationException at 2**64 bytes or more. *)
Definition return_buffer_ok_def:
  return_buffer_ok cenv ⇔
    cenv.ce_max_return_size < 2 ** 64 ∧
    (case cenv.ce_ret_enc_info of
       AbiCopy m => m < 2 ** 64
     | _ => T)
End

(* Python allocates the return buffer each time it lowers a valued return
   of an external function that is neither @raw_return nor a word type.
   Python does the same for a valued return in __default__; the fallback
   isn't checked here, since its compile env keeps no ABI return encoding.
   Mirrors Python: vyper/codegen_venom/stmt.py:_lower_external_return. *)
Definition external_return_buffer_ok_def:
  external_return_buffer_ok
    (entry_lbl, cenv, pos_args, min_cds, is_payable, nr, nkey, use_trans,
     is_view, body, ret_opt) ⇔
    case ret_opt of
      NONE => T
    | SOME ret =>
        ¬cenv.ce_raw_return ∧ ¬is_word_type ret ∧ stmts_valued_return body ⇒
        return_buffer_ok cenv
End

(* Package an internal function for compilation.
   is_ctor_context: T in deploy context (internal fns called from __init__),
                    F in runtime context.
   Mirrors Python: _generate_internal_function(is_ctor_context=...) *)
Definition package_internal_fn_def:
  package_internal_fn tops use_trans nkey_map is_ctor_context immutables_len
    (mut, nr, rr, fname, fargs, _, ret, body) =
    let fn_lbl = internal_fn_label (build_func_ids 0 tops fname) fname
                   (MAP SND fargs) is_ctor_context in
    let sft = make_struct_fields_map tops in
    let sft_fn = get_struct_fields sft in
    let sft_types = (λname. MAP (FST o SND) (sft_fn name)) in
    let vis = if is_ctor_context then Deploy else Internal in
    let cenv = (build_compile_env tops
                  vis mut fname fargs ret body use_trans)
                 with <| ce_is_ctor := is_ctor_context;
                         ce_raw_return := rr |> in
    let rc = returns_stack_count sft_types ret in
    let has_ret_buf = (rc = 0 ∧ ret ≠ NoneT) in
    let nkey = nkey_map fname in
    let cenv_final = update_cenv_nonreentrant cenv nr nkey use_trans
                       (mut = View) in
    let is_view = (mut = View) in
    let pvs = compute_pass_via_stack (MAP SND fargs) rc in
    let params = ZIP (MAP FST fargs, pvs) in
    (fn_lbl, cenv_final, params, has_ret_buf,
     nr, nkey, use_trans, is_view,
     is_ctor_context, (if is_ctor_context then immutables_len else 0n),
     body, if ret = NoneT then NONE else SOME ret)
End

Theorem package_internal_fn_call_label:
  !tops use_trans nkey_map is_ctor_context immutables_len
   mut nr rr fname fargs dflts ret body.
    FST (package_internal_fn tops use_trans nkey_map is_ctor_context
           immutables_len
           (mut, nr, rr, fname, fargs, dflts, ret, body)) =
    internal_fn_label (build_func_ids 0 tops (nsid_to_string (NONE, fname)))
      (nsid_to_string (NONE, fname)) (MAP SND fargs) is_ctor_context
Proof
  simp[package_internal_fn_def, nsid_to_string_def]
QED

Definition source_internal_fn_descriptor_def:
  source_internal_fn_descriptor tops is_ctor_context
    (mut, nr, rr, fname, fargs, dflts, ret, body) =
    let sft_types =
      (\name. MAP (FST o SND)
                    (get_struct_fields (make_struct_fields_map tops) name)) in
    let rc = returns_stack_count sft_types ret in
    (internal_fn_label (build_func_ids 0 tops fname) fname (MAP SND fargs)
       is_ctor_context,
     rc = 0 /\ ret <> NoneT, rc)
End

Theorem build_compile_env_returns_count:
  !tops vis mut fname fargs ret body use_trans.
    (build_compile_env tops vis mut fname fargs ret body use_trans).
      ce_returns_count =
    returns_stack_count
      (\name. MAP (FST o SND)
                    (get_struct_fields (make_struct_fields_map tops) name)) ret
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem package_internal_fn_descriptor:
  !tops use_trans nkey_map is_ctor_context immutables_len
   mut nr rr fname fargs dflts ret body.
    internal_fn_descriptors
      [package_internal_fn tops use_trans nkey_map is_ctor_context
         immutables_len
         (mut, nr, rr, fname, fargs, dflts, ret, body)] =
    [source_internal_fn_descriptor tops is_ctor_context
       (mut, nr, rr, fname, fargs, dflts, ret, body)]
Proof
  simp[internal_fn_descriptors_def, package_internal_fn_def,
       source_internal_fn_descriptor_def, update_cenv_nonreentrant_def,
       build_compile_env_returns_count]
QED

Theorem internal_fn_descriptors_MAP_package_internal_fn:
  !fs tops use_trans nkey_map is_ctor_context immutables_len.
    internal_fn_descriptors
      (MAP (package_internal_fn tops use_trans nkey_map is_ctor_context
              immutables_len) fs) =
    MAP (source_internal_fn_descriptor tops is_ctor_context) fs
Proof
  Induct
  >- simp[internal_fn_descriptors_def]
  >> Cases_on `h`
  >> PairCases_on `r`
  >> simp[internal_fn_descriptors_def, package_internal_fn_def,
          source_internal_fn_descriptor_def, update_cenv_nonreentrant_def,
          build_compile_env_returns_count]
QED

Definition package_fallback_fn_def:
  package_fallback_fn tops use_trans nkey_map NONE = NONE ∧
  package_fallback_fn tops use_trans nkey_map
    (SOME (mut, nr, rr, fname, fargs, _, ret, body)) =
    let cenv = (build_compile_env tops
                  External mut fname fargs ret body use_trans)
                 with ce_raw_return := rr in
    let nkey = nkey_map fname in
    let is_payable = (mut = Payable) in
    let is_view = (mut = View) in
    SOME (cenv, is_payable, nr, nkey, use_trans, is_view,
          body, if ret = NoneT then NONE else SOME ret)
End

(* ===== Constructor Packaging ===== *)

(* Package the constructor for deploy-phase compilation.
   ctor_fn: the Deploy function from classify_functions.
   Returns: (cenv, args, is_payable, is_nr, nkey, use_trans, body, ret). *)
Definition package_constructor_def:
  package_constructor tops use_trans nkey_map
    (mut, nr, rr, fname, fargs, _, ret, body) =
    let cenv = (build_compile_env tops
                  Deploy mut fname fargs ret body use_trans)
                 with <| ce_is_ctor := T; ce_raw_return := rr |> in
    let nkey = nkey_map fname in
    let cenv_final = update_cenv_nonreentrant cenv nr nkey use_trans
                       (mut = View) in
    let pos_args = build_positional_args cenv_final fargs in
    (cenv_final, pos_args, (mut = Payable), nr, nkey, use_trans, body, ret)
End

(* ===== Full Compilation ===== *)

(* compile_vyper: the top-level compiler function.

   Two-phase compilation matching Python's module.py:
   Phase 1 (runtime): selector dispatch + external fns + internal fns (is_ctor=F)
   Phase 2 (deploy):  __init__ + ctor-reachable internal fns (is_ctor=T)

   Returns: SOME (deploy_bytecode, runtime_bytecode) or NONE on codegen failure.

   Takes:
   - tops: Vyper AST (toplevel list, with storage slots annotated)
   - pipeline: Venom optimization passes
   - dispatch_strategy: Linear, Sparse, or Dense

   Derived from AST (not external inputs):
   - immutables_len: sum of memory_bytes_required for Immutable vars
   - deploy data section: [runtime_bytecode] (built internally)

   Storage/transient slots come from the annotated AST.
   fn_eom is internal to the Venom pipeline (codegen defaults to 0).
   raw_return is per-function (from @raw_return decorator). *)
(* Build entry_info map from packaged external functions.
   Each packaged fn has (entry_lbl, cenv, pos_args, min_cds,
   is_payable, nr, nkey, use_trans, is_view, body, ret).
   entry_info: method_id -> (label, min_cds, is_nonpayable). *)
Definition build_dense_entry_info_def:
  build_dense_entry_info [] [] = (K ("", 0n, F) : num -> string # num # bool) /\
  build_dense_entry_info ((sel_num, _, _) :: srest)
    ((entry_lbl, _, _, min_cds, is_payable, _, _, _, _, _, _) :: erest) =
    (let rest_map = build_dense_entry_info srest erest in
     (\n. if n = sel_num then (entry_lbl, min_cds, ~is_payable)
          else rest_map n)) /\
  build_dense_entry_info _ _ = K ("", 0n, F)
End
(* Install the one resolved target into packaged function environments without
   changing source-visible ABI metadata or any other package field. *)
Definition set_external_package_target_def:
  set_external_package_target target
    (entry_lbl, cenv, pos_args, min_cds, is_payable, nr, nkey, use_trans,
     is_view, body, ret) =
    (entry_lbl, cenv with ce_target := target, pos_args, min_cds, is_payable,
     nr, nkey, use_trans, is_view, body, ret)
End

Definition set_internal_package_target_def:
  set_internal_package_target target
    (fn_lbl, cenv, params, has_ret_buf, nr, nkey, use_trans, is_view,
     is_ctor, immutables_len, body, ret) =
    (fn_lbl, cenv with ce_target := target, params, has_ret_buf, nr, nkey,
     use_trans, is_view, is_ctor, immutables_len, body, ret)
End

Definition set_fallback_package_target_def:
  set_fallback_package_target target NONE = NONE /\
  set_fallback_package_target target
    (SOME (cenv, is_payable, nr, nkey, use_trans, is_view, body, ret)) =
    SOME (cenv with ce_target := target, is_payable, nr, nkey, use_trans,
          is_view, body, ret)
End

Definition set_constructor_package_target_def:
  set_constructor_package_target target
    (cenv, pos_args, is_payable, nr, nkey, use_trans, body, ret) =
    (cenv with ce_target := target, pos_args, is_payable, nr, nkey,
     use_trans, body, ret)
End

Theorem internal_fn_descriptors_set_internal_package_target:
  internal_fn_descriptors
    (MAP (set_internal_package_target target) internal_fns) =
  internal_fn_descriptors internal_fns
Proof
  Induct_on `internal_fns`
  >- simp[internal_fn_descriptors_def]
  >> Cases_on `h` >> PairCases_on `r`
  >> simp[set_internal_package_target_def, internal_fn_descriptors_def]
QED

Theorem set_internal_package_target_capability:
  set_internal_package_target target
    (fn_lbl, cenv, params, has_ret_buf, nr, nkey, use_trans, is_view,
     is_ctor, immutables_len, body, ret) =
    (fn_lbl, cenv', params, has_ret_buf, nr, nkey, use_trans, is_view,
     is_ctor, immutables_len, body, ret) ==>
  cenv'.ce_target = target /\
  cenv'.ce_returns_count = cenv.ce_returns_count
Proof
  simp[set_internal_package_target_def] >> strip_tac >> gvs[]
QED

Theorem set_external_package_target_all_capabilities[simp]:
  set_external_package_target all_capabilities
    (package_external_fn tops use_trans nkey_map source) =
  package_external_fn tops use_trans nkey_map source
Proof
  Cases_on `source` >> PairCases_on `r` >>
  simp[set_external_package_target_def, package_external_fn_def] >>
  irule compile_env_target_update_id >> IF_CASES_TAC >> simp[]
QED

Theorem set_internal_package_target_all_capabilities[simp]:
  set_internal_package_target all_capabilities
    (package_internal_fn tops use_trans nkey_map is_ctor immutables_len source) =
  package_internal_fn tops use_trans nkey_map is_ctor immutables_len source
Proof
  Cases_on `source` >> PairCases_on `r` >>
  simp[set_internal_package_target_def, package_internal_fn_def] >>
  irule compile_env_target_update_id >> simp[]
QED

Theorem set_fallback_package_target_all_capabilities[simp]:
  set_fallback_package_target all_capabilities
    (package_fallback_fn tops use_trans nkey_map source) =
  package_fallback_fn tops use_trans nkey_map source
Proof
  Cases_on `source`
  >- simp[set_fallback_package_target_def, package_fallback_fn_def]
  >> Cases_on `x` >> PairCases_on `r` >>
  simp[set_fallback_package_target_def, package_fallback_fn_def] >>
  irule compile_env_target_update_id >> simp[]
QED

Theorem set_constructor_package_target_all_capabilities[simp]:
  set_constructor_package_target all_capabilities
    (package_constructor tops use_trans nkey_map source) =
  package_constructor tops use_trans nkey_map source
Proof
  Cases_on `source` >> PairCases_on `r` >>
  simp[set_constructor_package_target_def, package_constructor_def] >>
  irule compile_env_target_update_id >> simp[]
QED

Theorem set_external_package_target_all[simp]:
  set_external_package_target (K T)
    (package_external_fn tops use_trans nkey_map source) =
  package_external_fn tops use_trans nkey_map source
Proof
  rw[GSYM venomPolicyTypesTheory.all_capabilities_def]
QED

Theorem set_internal_package_target_all[simp]:
  set_internal_package_target (K T)
    (package_internal_fn tops use_trans nkey_map is_ctor immutables_len source) =
  package_internal_fn tops use_trans nkey_map is_ctor immutables_len source
Proof
  rw[GSYM venomPolicyTypesTheory.all_capabilities_def]
QED

Theorem set_fallback_package_target_all[simp]:
  set_fallback_package_target (K T)
    (package_fallback_fn tops use_trans nkey_map source) =
  package_fallback_fn tops use_trans nkey_map source
Proof
  rw[GSYM venomPolicyTypesTheory.all_capabilities_def]
QED

Theorem set_constructor_package_target_all[simp]:
  set_constructor_package_target (K T)
    (package_constructor tops use_trans nkey_map source) =
  package_constructor tops use_trans nkey_map source
Proof
  rw[GSYM venomPolicyTypesTheory.all_capabilities_def]
QED


(* ===== Policy-driven complete-unit lowering ===== *)

(* Package runtime metadata from source, but keep the raw lowering result atomic.
   The checked raw boundary accepts only Linear O1 policies, so no independent
   dispatch or jumptable choice is exposed here. *)
Definition lower_vyper_runtime_unit_def:
  lower_vyper_runtime_unit (tops : toplevel list)
                           (rpolicy : resolved_compiler_policy) =
    let tenv = type_env tops in
    let nkey_map = assign_nkeys tops 0 in
    let use_trans = F in
    let (ext_fns, int_fns, fb_fn, ctor_fn) = classify_functions tops in
    let selectors = build_selectors tenv ext_fns in
    let external_fns =
          MAP (set_external_package_target rpolicy.rpol_target o
               package_external_fn tops use_trans nkey_map) ext_fns in
    let runtime_int_fns =
          MAP (set_internal_package_target rpolicy.rpol_target o
               package_internal_fn tops use_trans nkey_map F 0) int_fns in
    let fallback_fn =
          set_fallback_package_target rpolicy.rpol_target
            (package_fallback_fn tops use_trans nkey_map fb_fn) in
    let entry_info = build_dense_entry_info selectors external_fns in
    if EVERY external_return_buffer_ok external_fns then
      run_lowering selectors external_fns runtime_int_fns fallback_fn
        rpolicy 0 0 ([] : dense_bucket list) entry_info "__entry"
    else NONE
End

(* A unit that lowers has every external return buffer below the limit. *)
Theorem lower_vyper_runtime_unit_return_buffer_ok:
  ∀tops rpolicy unit exts ints fb ctor x.
    lower_vyper_runtime_unit tops rpolicy = SOME unit ∧
    classify_functions tops = (exts, ints, fb, ctor) ∧ MEM x exts ⇒
    external_return_buffer_ok
      (set_external_package_target rpolicy.rpol_target
         (package_external_fn tops F (assign_nkeys tops 0) x))
Proof
  rw[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
  gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP, PULL_EXISTS]
QED

(* Deploy lowering receives the actual runtime bytes.  Their size and data
   section are both owned by run_deploy_lowering. *)
Definition lower_vyper_deploy_unit_def:
  lower_vyper_deploy_unit (tops : toplevel list)
                          (rpolicy : resolved_compiler_policy)
                          (runtime_bytecode : byte list) =
    let sft = make_struct_fields_map tops in
    let sft_fn = get_struct_fields sft in
    let immutables_len = compute_immutables_len sft_fn tops in
    let nkey_map = assign_nkeys tops 0 in
    let use_trans = F in
    let (ext_fns, int_fns, fb_fn, ctor_fn) = classify_functions tops in
    let has_constructor = IS_SOME ctor_fn in
    let deploy_int_fns =
          if has_constructor then
            MAP (set_internal_package_target rpolicy.rpol_target o
                 package_internal_fn tops use_trans nkey_map T immutables_len)
                int_fns
          else [] in
    let (ctor_cenv, ctor_args, ctor_payable, ctor_nr, ctor_nkey,
         ctor_trans, ctor_body, ctor_ret) =
      set_constructor_package_target rpolicy.rpol_target
        (case ctor_fn of
           SOME cf => package_constructor tops use_trans nkey_map cf
         | NONE => (ARB, ([] : (string # bool # bool # num # abi_dec_info) list),
                    F, F, 0n, F, ([] : stmt list), NoneT)) in
    run_deploy_lowering has_constructor rpolicy runtime_bytecode
      immutables_len ctor_args 0 deploy_int_fns ctor_cenv ctor_body
      ctor_payable ctor_nr ctor_nkey ctor_trans "__deploy"
End


(* Run one complete compilation unit through a resolved-policy pipeline and
   reject any output whose final-assembly policy disagrees with that policy. *)
Definition checked_unit_pipeline_def:
  checked_unit_pipeline
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    (finalizer : assembly_finalizer)
    (rpolicy : resolved_compiler_policy)
    (unit : compilation_unit) =
    case pipeline rpolicy unit of
      NONE => NONE
    | SOME out =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen finalizer rpolicy out.po_unit
End

(* Bounded planning is deliberately exposed only as a testing boundary. *)
Definition finalize_codegen_fuel_for_testing_def:
  finalize_codegen_fuel_for_testing fuel
    (finalizer : assembly_finalizer)
    (rpolicy : resolved_compiler_policy)
    (unit : compilation_unit) =
    case codegen_assembly_fuel fuel rpolicy unit of
      NONE => NONE
    | SOME asm =>
        case finalizer rpolicy asm of
          NONE => NONE
        | SOME finalized_asm =>
            if assembly_target_safe rpolicy.rpol_target finalized_asm
            then SOME (assemble finalized_asm)
            else NONE
End

Definition checked_unit_pipeline_fuel_for_testing_def:
  checked_unit_pipeline_fuel_for_testing fuel
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    (finalizer : assembly_finalizer)
    (rpolicy : resolved_compiler_policy)
    (unit : compilation_unit) =
    case pipeline rpolicy unit of
      NONE => NONE
    | SOME out =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen_fuel_for_testing fuel finalizer rpolicy out.po_unit
End

Definition compile_vyper_with_def:
  compile_vyper_with
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    (finalizer : assembly_finalizer)
    (policy : compiler_policy)
    (tops : toplevel list) =
    case resolve_o1_policy policy of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME runtime_unit =>
            case checked_unit_pipeline pipeline finalizer rpolicy runtime_unit of
              NONE => NONE
            | SOME runtime_bytecode =>
                case lower_vyper_deploy_unit tops rpolicy runtime_bytecode of
                  NONE => NONE
                | SOME deploy_unit =>
                    case checked_unit_pipeline pipeline finalizer rpolicy deploy_unit of
                      NONE => NONE
                    | SOME deploy_bytecode =>
                        SOME (deploy_bytecode, runtime_bytecode)
End

(* The bounded wrapper mirrors the normative unit sequencing exactly, but is
   named explicitly as a testing-only interface. *)
Definition compile_vyper_fuel_for_testing_def:
  compile_vyper_fuel_for_testing fuel
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    (finalizer : assembly_finalizer)
    (policy : compiler_policy)
    (tops : toplevel list) =
    case resolve_o1_policy policy of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME runtime_unit =>
            case checked_unit_pipeline_fuel_for_testing fuel pipeline finalizer
                    rpolicy runtime_unit of
              NONE => NONE
            | SOME runtime_bytecode =>
                case lower_vyper_deploy_unit tops rpolicy runtime_bytecode of
                  NONE => NONE
                | SOME deploy_unit =>
                    case checked_unit_pipeline_fuel_for_testing fuel pipeline finalizer
                            rpolicy deploy_unit of
                      NONE => NONE
                    | SOME deploy_bytecode =>
                        SOME (deploy_bytecode, runtime_bytecode)
End

(* The shortest generic compiler fixes the exact O1 pipeline but leaves target
   policy and final assembly implementation explicit. *)
Definition compile_vyper_def:
  compile_vyper (finalizer : assembly_finalizer)
                (policy : compiler_policy)
                (tops : toplevel list) =
    compile_vyper_with
      (\rpolicy unit.
         run_venom_pipeline (K T) (K T) (K T)
           rpolicy o1_pipeline_spec unit)
      finalizer policy tops
End

(* The exact O1 specialization, targeting all capabilities. *)
Definition compile_vyper_o1_def:
  compile_vyper_o1 (finalizer : assembly_finalizer)
                   (tops : toplevel list) =
    compile_vyper finalizer (o1_policy all_capabilities) tops
End
