(*
 * The compiler over a linked unit of modules.
 *
 * compileVyper compiles one module's toplevels.  A program that imports
 * modules is a unit (mods, exps): mods is the source's (source id,
 * toplevels) list, the main module at NONE, as the frontend gives it and as
 * the source semantics runs it (get_module_code); exps maps each function
 * the main module exports (`exports:`) to the module declaring it.  The
 * definitions here are compileVyper's builders over the whole unit:
 *   - every compile_env table covers every module, keyed by the module and
 *     the name: nsid_to_string (src, name) for the string-keyed tables, as
 *     compile_call and the type and event lowering already look them up,
 *     and (src, name) for module variables;
 *   - internal function ids are one counter over the modules in list order,
 *     then over each module's declarations;
 *   - module constants are substituted for every module (constSubstMods);
 *   - the runtime exposes the exported functions, then the main module's
 *     external functions and getters, as Python's exposed_functions orders
 *     them (vyper/semantics/types/module.py), and an imported module's
 *     __init__ is an internal function the constructor calls (Python lowers
 *     lib.__init__() as an internal call, codegen_venom/expr.py).
 * Immutables: on the single module [(NONE, tops)] they are placed one after
 * another from offset 0, as compileVyper does; on several modules each
 * immutable carries the offset the compiler's code_layout gives it
 * (frontend annotate_sources_slots_mods), since Python allocates an
 * initialized module's immutables inline at its `initializes:` declaration,
 * which the AST doesn't keep (semantics/analysis/data_positions.py).
 *
 * At [(NONE, tops)] with no exports each definition equals its compileVyper
 * counterpart: the *_singleton theorems below.
 *
 * TOP-LEVEL:
 *   compile_vyper_mods, compile_vyper_with_mods
 *   lower_vyper_runtime_unit_mods, lower_vyper_deploy_unit_mods
 *   build_compile_env_unit, classify_functions_unit
 *   package_internal_fn_unit (and the external, fallback, constructor and
 *   external group packagers)
 *)

Theory compileUnit
Ancestors
  compileVyper constSubstMods constSubst vyperContext vyperEvent vyperGetter
  compileEnv vyperAST finite_map list pair

(* ===== Struct fields, flags, events, errors over the unit ===== *)

Definition build_struct_fields_map_src_def:
  build_struct_fields_map_src tenv src []
    (sft : (string, (string # type # num) list) fmap) = sft ∧
  build_struct_fields_map_src tenv src (top :: rest) sft =
    case top of
      StructDecl sname args =>
        build_struct_fields_map_src tenv src rest
          (sft |+ (nsid_to_string (src, sname),
                   build_struct_fields_one tenv args))
    | _ => build_struct_fields_map_src tenv src rest sft
End

Definition build_struct_fields_map_mods_def:
  build_struct_fields_map_mods tenv []
    (sft : (string, (string # type # num) list) fmap) = sft ∧
  build_struct_fields_map_mods tenv ((src, tops) :: rest) sft =
    build_struct_fields_map_mods tenv rest
      (build_struct_fields_map_src tenv src tops sft)
End

(* Field sizes resolve against every module's types, so a field of an
   imported struct or flag type has its size. *)
Definition make_struct_fields_map_mods_def:
  make_struct_fields_map_mods mods =
    build_struct_fields_map_mods (type_env_all_modules mods) mods FEMPTY
End

Definition build_flag_info_src_def:
  build_flag_info_src src [] fmid fnm = (fmid, fnm) ∧
  build_flag_info_src src (top :: rest) fmid fnm =
    case top of
      FlagDecl fname members =>
        build_flag_info_src src rest
          (λfn. if fn = nsid_to_string (src, fname)
                then build_flag_member_id_one members 0 else fmid fn)
          (λfn. if fn = nsid_to_string (src, fname) then LENGTH members
                else fnm fn)
    | _ => build_flag_info_src src rest fmid fnm
End

Definition build_flag_info_mods_def:
  build_flag_info_mods [] fmid fnm = (fmid, fnm) ∧
  build_flag_info_mods ((src, tops) :: rest) fmid fnm =
    let (fmid', fnm') = build_flag_info_src src tops fmid fnm in
    build_flag_info_mods rest fmid' fnm'
End

Definition build_event_info_src_def:
  build_event_info_src tenv src ([] : toplevel list) eim = eim ∧
  build_event_info_src tenv src (top :: rest) eim =
    case top of
      EventDecl ename args_indexed =>
        let arg_types = MAP (SND o FST) args_indexed in
        let ehash = event_hash tenv ename arg_types in
        let indexed_flags = MAP SND args_indexed in
        build_event_info_src tenv src rest
          (λn. if n = nsid_to_string (src, ename)
               then SOME (ehash, arg_types, indexed_flags) else eim n)
    | _ => build_event_info_src tenv src rest eim
End

Definition build_event_info_mods_def:
  build_event_info_mods tenv [] eim = eim ∧
  build_event_info_mods tenv ((src, tops) :: rest) eim =
    build_event_info_mods tenv rest (build_event_info_src tenv src tops eim)
End

Definition lookup_custom_error_args_src_def:
  lookup_custom_error_args_src src s [] = NONE ∧
  lookup_custom_error_args_src src s (top :: rest) =
    case top of
    | ErrorDecl name args =>
        if nsid_to_string (src, name) = s then SOME args
        else lookup_custom_error_args_src src s rest
    | _ => lookup_custom_error_args_src src s rest
End

Definition lookup_custom_error_args_mods_def:
  lookup_custom_error_args_mods [] s = NONE ∧
  lookup_custom_error_args_mods ((src, tops) :: rest) s =
    case lookup_custom_error_args_src src s tops of
      SOME args => SOME args
    | NONE => lookup_custom_error_args_mods rest s
End

(* ===== Module variables over the unit ===== *)

Definition extract_layout_src_def:
  extract_layout_src src ([] : toplevel list) =
    (FEMPTY : (string, bytes32) fmap) ∧
  extract_layout_src src (VariableDecl _ (Storage) name _ (SOME slot) :: rest) =
    extract_layout_src src rest |+ (nsid_to_string (src, name), n2w slot) ∧
  extract_layout_src src (VariableDecl _ (Transient) name _ (SOME slot) :: rest) =
    extract_layout_src src rest |+ (nsid_to_string (src, name), n2w slot) ∧
  extract_layout_src src (HashMapDecl _ _ name _ _ (SOME slot) :: rest) =
    extract_layout_src src rest |+ (nsid_to_string (src, name), n2w slot) ∧
  extract_layout_src src (_ :: rest) = extract_layout_src src rest
End

Definition extract_layout_mods_def:
  extract_layout_mods [] = (FEMPTY : (string, bytes32) fmap) ∧
  extract_layout_mods ((src, tops) :: rest) =
    FUNION (extract_layout_src src tops) (extract_layout_mods rest)
End

Definition build_var_type_map_src_def:
  build_var_type_map_src src ([] : toplevel list)
    (rest_map : nsid -> type option) = rest_map ∧
  build_var_type_map_src src (top :: rest) rest_map =
    case top of
      VariableDecl _ _ vname ty _ =>
        (λn. if n = (src, vname) then SOME ty
             else build_var_type_map_src src rest rest_map n)
    | _ => build_var_type_map_src src rest rest_map
End

Definition build_var_type_map_mods_def:
  build_var_type_map_mods [] = (K NONE : nsid -> type option) ∧
  build_var_type_map_mods ((src, tops) :: rest) =
    build_var_type_map_src src tops (build_var_type_map_mods rest)
End

Definition build_hashmap_info_src_def:
  build_hashmap_info_src src ([] : toplevel list)
    (rest_map : nsid -> (bool # type # value_type) option) = rest_map ∧
  build_hashmap_info_src src (top :: rest) rest_map =
    case top of
      HashMapDecl _ tr hname kt vt _ =>
        (λn. if n = (src, hname) then SOME (tr, kt, vt)
             else build_hashmap_info_src src rest rest_map n)
    | _ => build_hashmap_info_src src rest rest_map
End

Definition build_hashmap_info_mods_def:
  build_hashmap_info_mods [] =
    (K NONE : nsid -> (bool # type # value_type) option) ∧
  build_hashmap_info_mods ((src, tops) :: rest) =
    build_hashmap_info_src src tops (build_hashmap_info_mods rest)
End

Definition collect_module_vars_src_def:
  collect_module_vars_src src ([] : toplevel list) = ([] : (nsid # type) list) ∧
  collect_module_vars_src src (top :: rest) =
    (case top of
       VariableDecl _ _ vname ty _ => [((src, vname), ty)]
     | _ => []) ++ collect_module_vars_src src rest
End

Definition collect_module_vars_mods_def:
  collect_module_vars_mods [] = ([] : (nsid # type) list) ∧
  collect_module_vars_mods ((src, tops) :: rest) =
    collect_module_vars_src src tops ++ collect_module_vars_mods rest
End

Definition add_module_var_locations_src_def:
  add_module_var_locations_src src ([] : toplevel list)
    (vars : (nsid, var_location) fmap) = vars ∧
  add_module_var_locations_src src (top :: rest) vars =
    let vars' =
      case top of
        VariableDecl _ Storage name _ (SOME slot) =>
          vars |+ ((src, name), StorageLoc (n2w slot))
      | VariableDecl _ Transient name _ (SOME slot) =>
          vars |+ ((src, name), TransientLoc (n2w slot))
      | HashMapDecl _ transient name _ _ (SOME slot) =>
          vars |+ ((src, name),
            if transient then TransientLoc (n2w slot)
            else StorageLoc (n2w slot))
      | _ => vars in
    add_module_var_locations_src src rest vars'
End

Definition add_module_var_locations_mods_def:
  add_module_var_locations_mods [] (vars : (nsid, var_location) fmap) = vars ∧
  add_module_var_locations_mods ((src, tops) :: rest) vars =
    add_module_var_locations_mods rest (add_module_var_locations_src src tops vars)
End

(* ===== Immutables over the unit ===== *)

(* Immutables with a code_layout offset, at that offset. *)
Definition add_annotated_immutables_src_def:
  add_annotated_immutables_src src ([] : toplevel list)
    (vars : (nsid, var_location) fmap) = vars ∧
  add_annotated_immutables_src src (top :: rest) vars =
    case top of
      VariableDecl _ Immutable name ty (SOME off) =>
        add_annotated_immutables_src src rest
          (vars |+ ((src, name), ImmutableLoc off))
    | _ => add_annotated_immutables_src src rest vars
End

Definition add_annotated_immutables_mods_def:
  add_annotated_immutables_mods [] (vars : (nsid, var_location) fmap) = vars ∧
  add_annotated_immutables_mods ((src, tops) :: rest) vars =
    add_annotated_immutables_mods rest (add_annotated_immutables_src src tops vars)
End

Definition annotated_immutables_len_def:
  annotated_immutables_len sft ([] : toplevel list) = (0 : num) ∧
  annotated_immutables_len sft (top :: rest) =
    (case top of
       VariableDecl _ Immutable _ ty (SOME _) =>
         type_mem_bytes sft ty + annotated_immutables_len sft rest
     | _ => annotated_immutables_len sft rest)
End

(* One module: compileVyper's sequential layout.  Several: the annotated
   offsets, and the section is the sum of the annotated immutables' sizes,
   as Python's immutable_section_bytes sums a module's immutables and its
   initialized modules' sections; a module only `uses:`-ed allocates
   nothing, its immutables having no code_layout entry. *)
Definition add_immutable_locations_unit_def:
  add_immutable_locations_unit sft mods vars =
    case mods of
      [(NONE, tops)] => add_immutable_locations sft tops 0 vars
    | _ => add_annotated_immutables_mods mods vars
End

Definition compute_immutables_len_unit_def:
  compute_immutables_len_unit sft mods =
    case mods of
      [(NONE, tops)] => compute_immutables_len sft tops
    | _ => SUM (MAP (λ(src, tops). annotated_immutables_len sft tops) mods)
End

(* ===== Internal function tables over the unit ===== *)

Definition build_func_info_src_def:
  build_func_info_src sft src ([] : toplevel list)
    (rest_map : string -> num # num # bool list) = rest_map ∧
  build_func_info_src sft src (top :: rest) rest_map =
    let map' = build_func_info_src sft src rest rest_map in
    case top of
      FunctionDecl vis _ _ _ fname fargs _ ret _ =>
        if vis = External then map'
        else
          let arg_types = MAP SND fargs in
          let ret_mem = type_mem_bytes sft ret in
          let info = compute_func_info (λn. MAP (FST o SND) (sft n))
                       ret ret_mem arg_types in
          (λs. if s = nsid_to_string (src, fname) then info else map' s)
    | _ => map'
End

Definition build_func_info_mods_def:
  build_func_info_mods sft [] =
    (K (0n, 0n, [] : bool list) : string -> num # num # bool list) ∧
  build_func_info_mods sft ((src, tops) :: rest) =
    build_func_info_src sft src tops (build_func_info_mods sft rest)
End

Definition build_func_param_types_src_def:
  build_func_param_types_src src ([] : toplevel list)
    (rest_map : string -> type list) = rest_map ∧
  build_func_param_types_src src (top :: rest) rest_map =
    let map' = build_func_param_types_src src rest rest_map in
    case top of
      FunctionDecl vis _ _ _ fname fargs _ _ _ =>
        if vis = External then map'
        else (λs. if s = nsid_to_string (src, fname) then MAP SND fargs
                  else map' s)
    | _ => map'
End

Definition build_func_param_types_mods_def:
  build_func_param_types_mods [] = (K [] : string -> type list) ∧
  build_func_param_types_mods ((src, tops) :: rest) =
    build_func_param_types_src src tops (build_func_param_types_mods rest)
End

Definition build_func_return_type_src_def:
  build_func_return_type_src src ([] : toplevel list)
    (rest_map : string -> type) = rest_map ∧
  build_func_return_type_src src (top :: rest) rest_map =
    let map' = build_func_return_type_src src rest rest_map in
    case top of
      FunctionDecl vis _ _ _ fname _ _ ret _ =>
        if vis = External then map'
        else (λs. if s = nsid_to_string (src, fname) then ret else map' s)
    | _ => map'
End

Definition build_func_return_type_mods_def:
  build_func_return_type_mods [] = (K NoneT : string -> type) ∧
  build_func_return_type_mods ((src, tops) :: rest) =
    build_func_return_type_src src tops (build_func_return_type_mods rest)
End

Definition build_func_mutability_src_def:
  build_func_mutability_src src ([] : toplevel list)
    (rest_map : string -> function_mutability) = rest_map ∧
  build_func_mutability_src src (top :: rest) rest_map =
    let map' = build_func_mutability_src src rest rest_map in
    case top of
      FunctionDecl vis mut _ _ fname _ _ _ _ =>
        if vis = External then map'
        else (λs. if s = nsid_to_string (src, fname) then mut else map' s)
    | _ => map'
End

Definition build_func_mutability_mods_def:
  build_func_mutability_mods [] = (K Nonpayable) ∧
  build_func_mutability_mods ((src, tops) :: rest) =
    build_func_mutability_src src tops (build_func_mutability_mods rest)
End

Definition count_function_decls_def:
  count_function_decls ([] : toplevel list) = (0 : num) ∧
  count_function_decls (top :: rest) =
    (case top of
       FunctionDecl _ _ _ _ _ _ _ _ _ => 1 + count_function_decls rest
     | _ => count_function_decls rest)
End

(* One counter over the modules in list order, then each module's function
   declarations; labels need only distinct ids (compileVyper's
   build_func_ids). *)
Definition build_func_ids_src_def:
  build_func_ids_src (n : num) src ([] : toplevel list)
    (rest_map : string -> num) = rest_map ∧
  build_func_ids_src n src (top :: rest) rest_map =
    case top of
      FunctionDecl vis _ _ _ fname _ _ _ _ =>
        let map' = build_func_ids_src (n + 1) src rest rest_map in
        if vis = External then map'
        else (λs. if s = nsid_to_string (src, fname) then n else map' s)
    | _ => build_func_ids_src n src rest rest_map
End

Definition build_func_ids_mods_def:
  build_func_ids_mods (n : num) [] = (K 0 : string -> num) ∧
  build_func_ids_mods n ((src, tops) :: rest) =
    build_func_ids_src n src tops
      (build_func_ids_mods (n + count_function_decls tops) rest)
End

(* ===== Function classification over the unit ===== *)

(* public_getter for a variable of module src. *)
Definition public_getter_src_def:
  public_getter_src src (VariableDecl (Public nr) mut id typ slot) =
    (let ne = TopLevelName typ (src, id) in
     if ~is_ArrayT typ then
       SOME (View, nr, F, id, [], [], typ, [Return (SOME ne)])
     else
       let (gm, gn, args, dflts, ret, body) =
         getter nr ne (BaseT (UintT 256)) (Type (ArrayT_type typ)) in
       SOME (gm, gn, F, id, args, dflts, ret, body)) /\
  public_getter_src src (HashMapDecl (Public nr) tr id kt vt slot) =
    (let (gm, gn, args, dflts, ret, body) =
       getter nr (TopLevelName NoneT (src, id)) kt vt in
     SOME (gm, gn, F, id, args, dflts, ret, body)) /\
  public_getter_src src _ = NONE
End

Definition fn_decl_name_def:
  fn_decl_name ((mut, nr, rr, fname, fargs, dflts, ret, body) :
    function_mutability # bool # bool # string # (string # type) list #
    expr list # type # stmt list) = fname
End

(* An exported name: the module's external function of that name, else its
   public getter of that name. *)
Definition exported_fn_def:
  exported_fn src tops fname =
    let (exts, ints, fb, ctor) = FOLDR classify_function ([], [], NONE, NONE) tops in
    case FILTER (λf. fn_decl_name f = fname) exts of
      f :: _ => [(src, f)]
    | [] =>
        case FILTER (λg. fn_decl_name g = fname)
               (FLAT (MAP (λt. case public_getter_src src t of
                                 NONE => [] | SOME g => [g]) tops)) of
          g :: _ => [(src, g)]
        | [] => []
End

Definition exported_fns_def:
  exported_fns mods ([] : (string # num) list) = [] ∧
  exported_fns mods ((fname, n) :: exps) =
    (case ALOOKUP mods (SOME n) of
       NONE => []
     | SOME tops => exported_fn (SOME n) tops fname) ++ exported_fns mods exps
End

(* Every module's internal functions, in module then declaration order. *)
Definition unit_internal_fns_def:
  unit_internal_fns [] = [] ∧
  unit_internal_fns ((src, tops) :: rest) =
    (let (exts, ints, fb, ctor) = FOLDR classify_function ([], [], NONE, NONE) tops in
     MAP (λf. (src, f)) ints) ++ unit_internal_fns rest
End

(* The imported modules' constructors, called from the main constructor. *)
Definition imported_ctors_def:
  imported_ctors [] = [] ∧
  imported_ctors ((src, tops) :: rest) =
    (let (exts, ints, fb, ctor) = FOLDR classify_function ([], [], NONE, NONE) tops in
     case (src, ctor) of
       (SOME _, SOME f) => [(src, f)]
     | _ => []) ++ imported_ctors rest
End

Definition main_module_def:
  main_module mods = case ALOOKUP mods NONE of SOME tops => tops | NONE => []
End

(* The functions the exports expose at run time, in export order: the
   exported functions of exported_fns, with an exported __default__ (which
   classify_function keeps out of the external functions) at its export
   position.  The pinned compiler orders the runtime internals by walking
   these first. *)
Definition exported_runtime_fns_def:
  exported_runtime_fns mods ([] : (string # num) list) = [] ∧
  exported_runtime_fns mods ((fname, n) :: exps) =
    (case ALOOKUP mods (SOME n) of
       NONE => []
     | SOME tops =>
         if fname = "__default__" then
           (case FOLDR classify_function ([], [], NONE, NONE) tops of
              (exts, ints, SOME f, ctor) => [(SOME n, f)]
            | _ => [])
         else exported_fn (SOME n) tops fname) ++
    exported_runtime_fns mods exps
End

(* The fallback an export names (`exports: lib.__default__`, or through
   `lib.__interface__`): the first exported `__default__` whose module
   declares one. *)
Definition exported_fallback_def:
  exported_fallback mods ([] : (string # num) list) = NONE ∧
  exported_fallback mods ((fname, n) :: exps) =
    if fname = "__default__" then
      case ALOOKUP mods (SOME n) of
        SOME tops =>
          (case FOLDR classify_function ([], [], NONE, NONE) tops of
             (exts, ints, SOME f, ctor) => SOME (SOME n, f)
           | _ => exported_fallback mods exps)
      | NONE => exported_fallback mods exps
    else exported_fallback mods exps
End

(* (exposed externals, internals, fallback, main constructor, imported
   constructors), each function tagged with its module and with every
   module's constants substituted.  The fallback is the main module's, else
   an exported one. *)
Definition classify_functions_unit_def:
  classify_functions_unit mods exps =
    let env = consts_env_mods mods in
    let sub = (λ(src, f). (src, subst_consts_fn_mods env f)) in
    let main = main_module mods in
    let (exts, ints, fb, ctor) = FOLDR classify_function ([], [], NONE, NONE) main in
    (MAP sub (exported_fns mods exps ++
              MAP (λf. (NONE, f)) (exts ++ public_getters main)),
     MAP sub (unit_internal_fns mods),
     OPTION_MAP sub (case fb of
                       SOME f => SOME (NONE, f)
                     | NONE => exported_fallback mods exps),
     OPTION_MAP (subst_consts_fn_mods env) ctor,
     MAP sub (imported_ctors mods))
End

Definition build_func_defaults_mods_def:
  build_func_defaults_mods mods : (string # expr list) list =
    let env = consts_env_mods mods in
    MAP (\(src, f). (nsid_to_string (src, fn_decl_name f),
                     FST (SND (SND (SND (SND (SND (subst_consts_fn_mods env f))))))))
      (unit_internal_fns mods)
End

(* ===== Compile env over the unit ===== *)

Definition build_compile_env_unit_def:
  build_compile_env_unit (mods : (num option # toplevel list) list) src
    vis (mut : function_mutability) func_name
    (args : (string # type) list) (ret_type : type)
    (body : stmt list) (use_transient_locks : bool) =
    let sft = make_struct_fields_map_mods mods in
    let sft_fn = get_struct_fields sft in
    let sft_types = (λname. MAP (FST o SND) (sft_fn name)) in
    let (flag_member_id, flag_n_members) =
          build_flag_info_mods mods (K (K 0)) (K 0) in
    let storage_layout = extract_layout_mods mods in
    let var_type_map = build_var_type_map_mods mods in
    let hashmap_info = build_hashmap_info_mods mods in
    let tenv = type_env_all_modules mods in
    let event_info =
          build_event_info_mods tenv mods
            ((K NONE) : string -> (num # type list # bool list) option) in
    let is_external = (vis = External) in
    let rc = returns_stack_count sft_types ret_type in
    let has_return_buf = (rc = 0 ∧ ret_type ≠ NoneT) in
    let module_vars = add_immutable_locations_unit sft_fn mods
      (add_module_var_locations_mods mods FEMPTY) in
    let (arg_vars, args_end) = allocate_args sft_fn args 0 FEMPTY in
    let locals = collect_locals body in
    let (ret_buf, ret_pc) =
      if vis <> Internal then (NONE, NONE)
      else allocate_internal_special_vars has_return_buf args_end in
    let dynarray_cap = build_dynarray_capacity (args ++ locals) in
    let func_info = build_func_info_mods sft_fn mods in
    let local_var_type = (λn. ALOOKUP (REVERSE (args ++ locals)) n) in
    <| ce_target := all_capabilities;
       ce_vars := arg_vars;
       ce_module_vars := module_vars;
       ce_storage_layout := storage_layout;
       ce_module := src;
       ce_struct_fields := sft;
       ce_dynarray_capacity := dynarray_cap;
       ce_module_dynarray_capacity :=
         build_dynarray_capacity (collect_module_vars_mods mods);
       ce_method_id := (λs tys. w2n (calldata_method_id
                          (function_selector s (vyper_to_abi_types tenv tys))));
       ce_flag_member_id := flag_member_id;
       ce_flag_n_members := flag_n_members;
       ce_var_type := local_var_type;
       ce_module_var_type := var_type_map;
       ce_hashmap_info := hashmap_info;
       ce_event_info := event_info;
       ce_error_info := (λname. lookup_custom_error_args_mods mods name);
       ce_type_env := tenv;
       ce_returns_count := rc;
       ce_return_buf := ret_buf;
       ce_return_pc := ret_pc;
       ce_ctor_exit_label := NONE;
       ce_is_external := is_external;
       ce_ret_enc_info := AbiPrimWord;
       ce_ret_dec_info := DecPrimWord NoClamp;
       ce_max_return_size := 0;
       ce_is_ctor := (vis = Deploy);
       ce_imm_alloca := NONE;
       ce_func_info := func_info;
       ce_func_param_types := build_func_param_types_mods mods;
       ce_func_defaults := build_func_defaults_mods mods;
       ce_func_return_type := build_func_return_type_mods mods;
       ce_func_mutability := build_func_mutability_mods mods;
       ce_func_ids := build_func_ids_mods 0 mods;
       ce_modules := mods;
       ce_nonreentrant := (F, 0n, use_transient_locks, mut = View);
       ce_raw_return := F;
       ce_alloca_locals := T
    |> : compile_env
End

(* ===== Function packaging over the unit ===== *)

Definition package_external_fn_unit_def:
  package_external_fn_unit mods use_trans nkey_map
    (src, (mut, nr, rr, fname, fargs, dflts, ret, body)) =
    let entry_lbl = "fn_" ++ fname in
    let cenv_base = build_compile_env_unit mods src
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

Definition fn_allocs_ok_unit_def:
  fn_allocs_ok_unit mods (src, (mut, nr, rr, fname, fargs, dflts, ret, body)) ⇔
    let cenv = build_compile_env_unit mods src Internal mut fname fargs ret body F in
    EVERY (λ(_,ty). type_memory_bytes cenv ty < 2 ** 64) fargs ∧
    abi_size_bound cenv.ce_struct_fields (TupleT (MAP SND fargs)) < 2 ** 128 ∧
    alloc_limits_exprs cenv dflts ∧ alloc_limits_stmts cenv body ∧
    type_memory_bytes cenv ret < 2 ** 64
End

(* The label spells nsid_to_string (src, fname), as compile_call does. *)
Definition package_internal_fn_unit_def:
  package_internal_fn_unit mods use_trans nkey_map is_ctor_context
    immutables_len (src, (mut, nr, rr, fname, fargs, dflts, ret, body)) =
    let key = nsid_to_string (src, fname) in
    let fn_lbl = internal_fn_label (build_func_ids_mods 0 mods key) key
                   (MAP SND fargs) is_ctor_context in
    let sft = make_struct_fields_map_mods mods in
    let sft_fn = get_struct_fields sft in
    let sft_types = (λname. MAP (FST o SND) (sft_fn name)) in
    let cenv = (build_compile_env_unit mods src
                  Internal mut fname fargs ret body use_trans)
                 with <| ce_is_ctor := is_ctor_context;
                         ce_raw_return := rr |> in
    let rc = returns_stack_count sft_types ret in
    let has_ret_buf = (rc = 0 ∧ ret ≠ NoneT) in
    let nkey = nkey_map key in
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

Definition package_fallback_fn_unit_def:
  package_fallback_fn_unit mods use_trans nkey_map NONE = NONE ∧
  package_fallback_fn_unit mods use_trans nkey_map
    (SOME (src, (mut, nr, rr, fname, fargs, dflts, ret, body))) =
    let cenv0 = (build_compile_env_unit mods src
                   External mut fname fargs ret body use_trans)
                  with ce_raw_return := rr in
    let cenv = if ret ≠ NoneT then update_cenv_ret_abi cenv0 ret
               else cenv0 in
    let nkey = nkey_map fname in
    let is_payable = (mut = Payable) in
    let is_view = (mut = View) in
    let cenv_final = update_cenv_nonreentrant cenv nr nkey use_trans is_view in
    SOME (cenv_final, is_payable, nr, nkey, use_trans, is_view,
          body, if ret = NoneT then NONE else SOME ret)
End

Definition package_constructor_unit_def:
  package_constructor_unit mods use_trans nkey_map
    (mut, nr, rr, fname, fargs, dflts, ret, body) =
    let cenv = (build_compile_env_unit mods NONE
                  Deploy mut fname fargs ret body use_trans)
                 with <| ce_is_ctor := T; ce_raw_return := rr |> in
    let nkey = nkey_map fname in
    let cenv_final = update_cenv_nonreentrant cenv nr nkey use_trans
                       (mut = View) in
    let pos_args = build_positional_args cenv_final fargs in
    (cenv_final, pos_args, (mut = Payable), nr, nkey, use_trans, body, ret)
End

Definition package_external_group_unit_def:
  package_external_group_unit mods target use_trans nkey_map
    (src, (mut, nr, rr, fname, fargs, dflts, ret, body)) =
    let tenv = type_env_all_modules mods in
    let package = set_external_package_target target
          (package_external_fn_unit mods use_trans nkey_map
            (src, (mut, nr, rr, fname, fargs, dflts, ret, body))) in
    if NULL dflts then
      ExternalSingle (compute_selector tenv fname (MAP SND fargs))
                     package
    else
      let (lbl, cenv, pos_args, min_cds, payable, nonreentrant,
           nkey, trans, view, stmts, ret_type) = package in
      let npos = LENGTH fargs - LENGTH dflts in
      let positional = TAKE npos fargs in
      let specs = MAP (\((name,ty),default_e). (name,ty,default_e))
                      (ZIP (DROP npos fargs,dflts)) in
      let entries = MAP (\(prefix,k).
          let (sel,unused,tz) =
            compute_selector tenv fname (MAP SND prefix) in
          (sel,external_prefix_label fname k,
           min_calldata_size cenv prefix 0,k)) (abi_entries fargs dflts) in
      ExternalDefaults
        <| ec_env := cenv;
           ec_pos_args := build_positional_args cenv positional;
           ec_common_label := external_common_label fname;
           ec_nonreentrant := nonreentrant; ec_nkey := nkey;
           ec_transient := trans; ec_view := view; ec_payable := payable;
           ec_body := stmts; ec_return := ret_type |>
        entries specs (min_calldata_size cenv positional 0)
End

(* ===== Internal functions in the pinned compiler's order ===== *)

(* compileVyper's internal_callees, reach_internals and order_internals,
   with each internal function keyed by nsid_to_string (src, fname), the
   name src_calls_expr gives a call. *)
Definition internal_callees_unit_def:
  internal_callees_unit ints g =
    FLAT (MAP (λ(src, f). src_calls_fn f)
      (FILTER (λ(src, f). nsid_to_string (src, fn_decl_name f) = g) ints))
End

Definition reach_internals_unit_def:
  reach_internals_unit ints 0 seen gs = seen ∧
  reach_internals_unit ints (SUC n) seen gs =
    FOLDL (λseen g.
      if MEM g seen then seen else
      let seen' = reach_internals_unit ints n seen (internal_callees_unit ints g) in
      if MEM g seen' then seen' else SNOC g seen') seen gs
End

Definition runtime_internal_order_unit_def:
  runtime_internal_order_unit exported main ints =
    reach_internals_unit ints (LENGTH ints) []
      (FLAT (MAP (λ(src, f). src_calls_fn f) exported) ++
       FLAT (MAP external_calls main))
End

Definition deploy_internal_order_unit_def:
  deploy_internal_order_unit ctor ints =
    reach_internals_unit ints (LENGTH ints) []
      (case ctor of NONE => [] | SOME f => src_calls_fn f)
End

Definition order_internals_unit_def:
  order_internals_unit names ints =
    FLAT (MAP (λn. FILTER (λ(src, f). nsid_to_string (src, fn_decl_name f) = n)
                     ints) names)
End

(* ===== Complete-unit lowering ===== *)

Definition lower_vyper_runtime_unit_mods_def:
  lower_vyper_runtime_unit_mods mods exps
                                (rpolicy : resolved_compiler_policy) =
    let tenv = type_env_all_modules mods in
    let nkey_map = (K global_nonreentrant_slot : string -> num) in
    let use_trans = T in
    let main = main_module mods in
    let (ext_fns, int_fns, fb_fn, ctor_fn, imp_ctors) =
          classify_functions_unit mods exps in
    let exported = exported_runtime_fns mods exps in
    let selectors = build_selectors tenv (MAP SND ext_fns) in
    let external_fns =
          MAP (set_external_package_target rpolicy.rpol_target o
               package_external_fn_unit mods use_trans nkey_map) ext_fns in
    let runtime_int_fns =
          MAP (set_internal_package_target rpolicy.rpol_target o
               package_internal_fn_unit mods use_trans nkey_map F 0)
              (order_internals_unit
                 (runtime_internal_order_unit exported main int_fns) int_fns) in
    let fallback_fn =
          set_fallback_package_target rpolicy.rpol_target
            (package_fallback_fn_unit mods use_trans nkey_map fb_fn) in
    let entry_info = build_dense_entry_info selectors external_fns in
    if compute_immutables_len_unit
         (get_struct_fields (make_struct_fields_map_mods mods)) mods < 0x6000 ∧
       EVERY external_return_buffer_ok external_fns ∧
       OPTION_ALL (λ(cenv,pay,nr,nkey,ut,iv,body,ret_opt).
                     external_return_buffer_ok
                       ("", cenv, ([] : num list), 0, pay, nr, nkey, ut, iv, body,
                        ret_opt))
         fallback_fn ∧
       EVERY (fn_allocs_ok_unit mods)
         (ext_fns ++ int_fns ++
          (case fb_fn of NONE => [] | SOME sf => [sf])) ∧
       EVERY (no_sha256_expr o SND) (consts_env_mods mods) ∧
       EVERY (no_neg_exp_expr o SND) (consts_env_mods mods) ∧
       EVERY (no_neg_exp_fn o SND)
         (ext_fns ++ int_fns ++
          (case fb_fn of NONE => [] | SOME sf => [sf]))
    then
      if EXISTS (external_has_defaults o SND) ext_fns then
        if EVERY (external_defaults_no_sha256 o SND) ext_fns then
          run_grouped_lowering
            (MAP (package_external_group_unit mods rpolicy.rpol_target
                                             use_trans nkey_map) ext_fns)
            runtime_int_fns fallback_fn rpolicy "__entry"
        else NONE
      else
        run_lowering selectors external_fns runtime_int_fns fallback_fn
          rpolicy 0 0 ([] : dense_bucket list) entry_info "__entry"
    else NONE
End

Definition lower_vyper_deploy_unit_mods_def:
  lower_vyper_deploy_unit_mods mods exps
                               (rpolicy : resolved_compiler_policy)
                               (runtime_bytecode : byte list) =
    let sft = make_struct_fields_map_mods mods in
    let sft_fn = get_struct_fields sft in
    let immutables_len = compute_immutables_len_unit sft_fn mods in
    let nkey_map = (K global_nonreentrant_slot : string -> num) in
    let use_trans = T in
    let (ext_fns, int_fns0, fb_fn, ctor_fn, imp_ctors) =
          classify_functions_unit mods exps in
    let int_fns = int_fns0 ++ imp_ctors in
    let has_constructor = IS_SOME ctor_fn in
    let deploy_int_fns =
          if has_constructor then
            MAP (set_internal_package_target rpolicy.rpol_target o
                 package_internal_fn_unit mods use_trans nkey_map T immutables_len)
                (order_internals_unit (deploy_internal_order_unit ctor_fn int_fns)
                   int_fns)
          else [] in
    if ¬(immutables_len < 0x6000) ∨
       ¬EVERY (fn_allocs_ok_unit mods)
          (int_fns ++ (case ctor_fn of NONE => [] | SOME f => [(NONE, f)])) ∨
       ¬EVERY (no_sha256_expr o SND) (consts_env_mods mods) ∨
       ¬EVERY (no_neg_exp_expr o SND) (consts_env_mods mods) ∨
       ¬EVERY (no_neg_exp_fn o SND)
          (int_fns ++ (case ctor_fn of NONE => [] | SOME f => [(NONE, f)])) ∨
       ¬ctor_named_init ctor_fn
    then NONE else
    let (ctor_cenv, ctor_args, ctor_payable, ctor_nr, ctor_nkey,
         ctor_trans, ctor_body, ctor_ret) =
      set_constructor_package_target rpolicy.rpol_target
        (case ctor_fn of
           SOME cf => package_constructor_unit mods use_trans nkey_map cf
         | NONE => (ARB, ([] : (string # bool # bool # num # abi_dec_info) list),
                    F, F, 0n, F, ([] : stmt list), NoneT)) in
    run_deploy_lowering has_constructor rpolicy runtime_bytecode
      immutables_len ctor_args 0 deploy_int_fns ctor_cenv ctor_body
      ctor_payable ctor_nr ctor_nkey ctor_trans "__deploy"
End

Definition compile_vyper_with_mods_def:
  compile_vyper_with_mods
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    (finalizer : assembly_finalizer)
    (policy : compiler_policy)
    mods exps =
    case resolve_o1_policy policy of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit_mods mods exps rpolicy of
          NONE => NONE
        | SOME runtime_unit =>
            case checked_unit_pipeline pipeline finalizer rpolicy runtime_unit of
              NONE => NONE
            | SOME runtime_bytecode =>
                case lower_vyper_deploy_unit_mods mods exps rpolicy
                       runtime_bytecode of
                  NONE => NONE
                | SOME deploy_unit =>
                    case checked_unit_pipeline pipeline finalizer rpolicy deploy_unit of
                      NONE => NONE
                    | SOME deploy_bytecode =>
                        SOME (deploy_bytecode, runtime_bytecode)
End

Definition compile_vyper_mods_def:
  compile_vyper_mods (finalizer : assembly_finalizer)
                     (policy : compiler_policy)
                     mods exps =
    compile_vyper_with_mods
      (\rpolicy unit.
         run_venom_pipeline (K T) (K T) (K T)
           rpolicy o1_pipeline_spec unit)
      finalizer policy mods exps
End

(* ===== At one module: compileVyper's definitions ===== *)

Theorem make_struct_fields_map_mods_singleton:
  make_struct_fields_map_mods [(NONE, tops)] = make_struct_fields_map tops
Proof
  `∀tenv tops sft. build_struct_fields_map_src tenv NONE tops sft =
              build_struct_fields_map tenv tops sft`
    by (gen_tac >> Induct >>
        simp[build_struct_fields_map_src_def, build_struct_fields_map_def,
             nsid_to_string_def]) >>
  simp[make_struct_fields_map_mods_def, make_struct_fields_map_def,
       build_struct_fields_map_mods_def, type_env_all_modules_def,
       type_env_def, FUNION_FEMPTY_2]
QED

Theorem build_flag_info_mods_singleton:
  build_flag_info_mods [(NONE, tops)] fmid fnm = build_flag_info tops fmid fnm
Proof
  `∀tops fmid fnm. build_flag_info_src NONE tops fmid fnm =
                   build_flag_info tops fmid fnm`
    by (Induct >>
        simp[build_flag_info_src_def, build_flag_info_def,
             nsid_to_string_def]) >>
  simp[build_flag_info_mods_def] >>
  Cases_on `build_flag_info tops fmid fnm` >> simp[build_flag_info_mods_def]
QED

Theorem build_event_info_mods_singleton:
  build_event_info_mods tenv [(NONE, tops)] eim = build_event_info tenv tops eim
Proof
  `∀tops eim. build_event_info_src tenv NONE tops eim =
              build_event_info tenv tops eim`
    by (Induct >>
        simp[build_event_info_src_def, build_event_info_def,
             nsid_to_string_def]) >>
  simp[build_event_info_mods_def]
QED

Theorem lookup_custom_error_args_mods_singleton:
  lookup_custom_error_args_mods [(NONE, tops)] s =
  lookup_custom_error_args_in s tops
Proof
  `∀tops. lookup_custom_error_args_src NONE s tops =
          lookup_custom_error_args_in s tops`
    by (Induct >>
        simp[lookup_custom_error_args_src_def, lookup_custom_error_args_in_def,
             nsid_to_string_def]) >>
  simp[lookup_custom_error_args_mods_def] >>
  Cases_on `lookup_custom_error_args_in s tops` >>
  simp[lookup_custom_error_args_mods_def]
QED

Theorem extract_layout_mods_singleton:
  extract_layout_mods [(NONE, tops)] = extract_layout tops
Proof
  `∀tops. extract_layout_src NONE tops = extract_layout tops`
    by (ho_match_mp_tac extract_layout_ind >>
        simp[extract_layout_src_def, extract_layout_def, nsid_to_string_def]) >>
  simp[extract_layout_mods_def, FUNION_FEMPTY_2]
QED

Theorem build_var_type_map_mods_singleton:
  build_var_type_map_mods [(NONE, tops)] = build_var_type_map tops
Proof
  `∀tops. build_var_type_map_src NONE tops (K NONE) = build_var_type_map tops`
    by (Induct >> simp[build_var_type_map_src_def, build_var_type_map_def]) >>
  simp[build_var_type_map_mods_def]
QED

Theorem build_hashmap_info_mods_singleton:
  build_hashmap_info_mods [(NONE, tops)] = build_hashmap_info tops
Proof
  `∀tops. build_hashmap_info_src NONE tops (K NONE) = build_hashmap_info tops`
    by (Induct >> simp[build_hashmap_info_src_def, build_hashmap_info_def]) >>
  simp[build_hashmap_info_mods_def]
QED

Theorem collect_module_vars_mods_singleton:
  collect_module_vars_mods [(NONE, tops)] = collect_module_vars tops
Proof
  `∀tops. collect_module_vars_src NONE tops = collect_module_vars tops`
    by (Induct >> simp[collect_module_vars_src_def, collect_module_vars_def]) >>
  simp[collect_module_vars_mods_def]
QED

Theorem add_module_var_locations_mods_singleton:
  add_module_var_locations_mods [(NONE, tops)] vars =
  add_module_var_locations tops vars
Proof
  `∀tops vars. add_module_var_locations_src NONE tops vars =
               add_module_var_locations tops vars`
    by (Induct >>
        simp[add_module_var_locations_src_def, add_module_var_locations_def]) >>
  simp[add_module_var_locations_mods_def]
QED

Theorem add_immutable_locations_unit_singleton:
  add_immutable_locations_unit sft [(NONE, tops)] vars =
  add_immutable_locations sft tops 0 vars
Proof
  simp[add_immutable_locations_unit_def]
QED

Theorem compute_immutables_len_unit_singleton:
  compute_immutables_len_unit sft [(NONE, tops)] = compute_immutables_len sft tops
Proof
  simp[compute_immutables_len_unit_def]
QED

Theorem build_func_info_mods_singleton:
  build_func_info_mods sft [(NONE, tops)] = build_func_info sft tops
Proof
  `∀tops. build_func_info_src sft NONE tops (K (0, 0, [])) =
          build_func_info sft tops`
    by (Induct >>
        simp[build_func_info_src_def, build_func_info_def, nsid_to_string_def]) >>
  simp[build_func_info_mods_def]
QED

Theorem build_func_param_types_mods_singleton:
  build_func_param_types_mods [(NONE, tops)] = build_func_param_types tops
Proof
  `∀tops. build_func_param_types_src NONE tops (K []) =
          build_func_param_types tops`
    by (Induct >>
        simp[build_func_param_types_src_def, build_func_param_types_def,
             nsid_to_string_def]) >>
  simp[build_func_param_types_mods_def]
QED

Theorem build_func_return_type_mods_singleton:
  build_func_return_type_mods [(NONE, tops)] = build_func_return_type tops
Proof
  `∀tops. build_func_return_type_src NONE tops (K NoneT) =
          build_func_return_type tops`
    by (Induct >>
        simp[build_func_return_type_src_def, build_func_return_type_def,
             nsid_to_string_def]) >>
  simp[build_func_return_type_mods_def]
QED

Theorem build_func_mutability_mods_singleton:
  build_func_mutability_mods [(NONE, tops)] = build_func_mutability tops
Proof
  `∀tops. build_func_mutability_src NONE tops (K Nonpayable) =
          build_func_mutability tops`
    by (Induct >>
        simp[build_func_mutability_src_def, build_func_mutability_def,
             nsid_to_string_def]) >>
  simp[build_func_mutability_mods_def]
QED

Theorem build_func_ids_mods_singleton:
  build_func_ids_mods n [(NONE, tops)] = build_func_ids n tops
Proof
  `∀tops n. build_func_ids_src n NONE tops (K 0) = build_func_ids n tops`
    by (Induct >>
        simp[build_func_ids_src_def, build_func_ids_def, nsid_to_string_def]) >>
  simp[build_func_ids_mods_def]
QED

(* ===== Internal function ids over the unit are injective ===== *)

(* A key no non-external function of the module has keeps the later
   modules' id. *)
Theorem build_func_ids_src_absent[local]:
  !tops n src R k.
    (!v fm nr rr s args dflts ret body.
       v <> External /\ MEM (FunctionDecl v fm nr rr s args dflts ret body) tops ==>
       nsid_to_string (src,s) <> k) ==>
    build_func_ids_src n src tops R k = R k
Proof
  Induct >- simp[build_func_ids_src_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[build_func_ids_src_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  rw[] >> metis_tac[]
QED

(* A key of a non-external function of the module gets an id in the
   module's block. *)
Theorem build_func_ids_src_range[local]:
  !tops n src R v fm nr rr s args dflts ret body.
    v <> External /\ MEM (FunctionDecl v fm nr rr s args dflts ret body) tops ==>
    n <= build_func_ids_src n src tops R (nsid_to_string (src,s)) /\
    build_func_ids_src n src tops R (nsid_to_string (src,s)) <
      n + count_function_decls tops
Proof
  Induct >- simp[] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[build_func_ids_src_def, count_function_decls_def] >>
  strip_tac >> gvs[] >> rw[] >>
  first_x_assum (drule_all_then assume_tac) >>
  FIRST [first_x_assum (qspecl_then [`n + 1`, `src`, `R`] mp_tac) >>
         rw[] >> NO_TAC,
         first_x_assum (qspecl_then [`n`, `src`, `R`] mp_tac) >> rw[]]
QED

Theorem build_func_ids_src_11[local]:
  !tops n src R v1 fm1 nr1 rr1 s1 args1 dflts1 ret1 body1
               v2 fm2 nr2 rr2 s2 args2 dflts2 ret2 body2.
    v1 <> External /\ v2 <> External /\
    MEM (FunctionDecl v1 fm1 nr1 rr1 s1 args1 dflts1 ret1 body1) tops /\
    MEM (FunctionDecl v2 fm2 nr2 rr2 s2 args2 dflts2 ret2 body2) tops /\
    build_func_ids_src n src tops R (nsid_to_string (src,s1)) =
    build_func_ids_src n src tops R (nsid_to_string (src,s2)) ==>
    nsid_to_string (src,s1) = nsid_to_string (src,s2)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >>
  simp[build_func_ids_src_def] >> rw[] >> gvs[] >>
  metis_tac[build_func_ids_src_range, DECIDE ``!n:num. ~(n + 1 <= n)``]
QED

Theorem build_func_ids_mods_range[local]:
  !mods n src tops v fm nr rr s args dflts ret body.
    MEM (src,tops) mods /\ v <> External /\
    MEM (FunctionDecl v fm nr rr s args dflts ret body) tops ==>
    n <= build_func_ids_mods n mods (nsid_to_string (src,s))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> simp[build_func_ids_mods_def] >>
  strip_tac >> gvs[] >- metis_tac[build_func_ids_src_range] >>
  Cases_on `?v' fm' nr' rr' s' args' dflts' ret' body'.
    v' <> External /\
    MEM (FunctionDecl v' fm' nr' rr' s' args' dflts' ret' body') h1 /\
    nsid_to_string (h0,s') = nsid_to_string (src,s)`
  >- metis_tac[build_func_ids_src_range] >>
  `build_func_ids_src n h0 h1
     (build_func_ids_mods (n + count_function_decls h1) mods)
     (nsid_to_string (src,s)) =
   build_func_ids_mods (n + count_function_decls h1) mods
     (nsid_to_string (src,s))` by
    (irule build_func_ids_src_absent >> metis_tac[]) >>
  first_x_assum (drule_all_then (qspec_then `n + count_function_decls h1`
    mp_tac)) >>
  simp[]
QED

(* Distinct keys of non-external functions anywhere in the unit get
   distinct ids, so equal internal labels mean equal keys. *)
Theorem build_func_ids_mods_11:
  !mods n src1 tops1 v1 fm1 nr1 rr1 s1 args1 dflts1 ret1 body1
          src2 tops2 v2 fm2 nr2 rr2 s2 args2 dflts2 ret2 body2.
    MEM (src1,tops1) mods /\ MEM (src2,tops2) mods /\
    v1 <> External /\ v2 <> External /\
    MEM (FunctionDecl v1 fm1 nr1 rr1 s1 args1 dflts1 ret1 body1) tops1 /\
    MEM (FunctionDecl v2 fm2 nr2 rr2 s2 args2 dflts2 ret2 body2) tops2 /\
    build_func_ids_mods n mods (nsid_to_string (src1,s1)) =
    build_func_ids_mods n mods (nsid_to_string (src2,s2)) ==>
    nsid_to_string (src1,s1) = nsid_to_string (src2,s2)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  qpat_x_assum `build_func_ids_mods _ _ _ = _` mp_tac >>
  simp[build_func_ids_mods_def] >> strip_tac >>
  qabbrev_tac `occ = \k. ?v fm nr rr s args dflts ret body.
    v <> External /\
    MEM (FunctionDecl v fm nr rr s args dflts ret body) h1 /\
    nsid_to_string (h0,s) = k` >>
  `!src tops v fm nr rr s args dflts ret body.
     MEM (src,tops) ((h0,h1)::mods) /\ v <> External /\
     MEM (FunctionDecl v fm nr rr s args dflts ret body) tops /\
     ~occ (nsid_to_string (src,s)) ==>
     MEM (src,tops) mods /\
     build_func_ids_src n h0 h1
       (build_func_ids_mods (n + count_function_decls h1) mods)
       (nsid_to_string (src,s)) =
     build_func_ids_mods (n + count_function_decls h1) mods
       (nsid_to_string (src,s)) /\
     n + count_function_decls h1 <=
       build_func_ids_mods (n + count_function_decls h1) mods
         (nsid_to_string (src,s))` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `~occ _` mp_tac >> simp[Abbr `occ`] >> strip_tac >>
     `MEM (src,tops) mods` by
       (qpat_x_assum `MEM (src,tops) (_::_)` mp_tac >> rw[] >> metis_tac[]) >>
     simp[] >>
     conj_tac >- (irule build_func_ids_src_absent >> metis_tac[]) >>
     metis_tac[build_func_ids_mods_range]) >>
  `!k. occ k ==> ?s. k = nsid_to_string (h0,s) /\
     ?v fm nr rr args dflts ret body. v <> External /\
       MEM (FunctionDecl v fm nr rr s args dflts ret body) h1` by
    (simp[Abbr `occ`] >> metis_tac[]) >>
  Cases_on `occ (nsid_to_string (src1,s1))` >>
  Cases_on `occ (nsid_to_string (src2,s2))`
  >- metis_tac[build_func_ids_src_11]
  >- metis_tac[build_func_ids_src_range,
       DECIDE ``!x a y:num. x < a /\ a <= y ==> x <> y``]
  >- metis_tac[build_func_ids_src_range,
       DECIDE ``!x a y:num. x < a /\ a <= y ==> x <> y``] >>
  first_assum (qspecl_then [`src1`, `tops1`, `v1`, `fm1`, `nr1`, `rr1`, `s1`,
    `args1`, `dflts1`, `ret1`, `body1`] mp_tac) >>
  impl_tac >- gs[] >> strip_tac >>
  first_assum (qspecl_then [`src2`, `tops2`, `v2`, `fm2`, `nr2`, `rr2`, `s2`,
    `args2`, `dflts2`, `ret2`, `body2`] mp_tac) >>
  impl_tac >- gs[] >> strip_tac >>
  qpat_x_assum `!n src1 tops1 v1 fm1 nr1 rr1 s1 args1 dflts1 ret1 body1
                  src2 tops2 v2 fm2 nr2 rr2 s2 args2 dflts2 ret2 body2. _`
    (qspecl_then [`n + count_function_decls h1`, `src1`, `tops1`, `v1`, `fm1`,
      `nr1`, `rr1`, `s1`, `args1`, `dflts1`, `ret1`, `body1`, `src2`, `tops2`,
      `v2`, `fm2`, `nr2`, `rr2`, `s2`, `args2`, `dflts2`, `ret2`, `body2`]
      mp_tac) >>
  impl_tac >- gs[] >> simp[]
QED

Theorem classify_functions_unit_singleton:
  classify_functions_unit [(NONE, tops)] [] =
  case classify_functions tops of
    (exts, ints, fb, ctor) =>
      (MAP (λf. (NONE, f)) exts, MAP (λf. (NONE, f)) ints,
       OPTION_MAP (λf. (NONE, f)) fb, ctor, [])
Proof
  `∃exts ints fb ctor.
     FOLDR classify_function ([], [], NONE, NONE) tops = (exts, ints, fb, ctor)`
    by metis_tac[pairTheory.PAIR] >>
  pop_assum strip_assume_tac >>
  Cases_on `fb` >> Cases_on `ctor` >>
  simp[classify_functions_unit_def, classify_functions_def, main_module_def,
       alistTheory.ALOOKUP_def, unit_internal_fns_def, imported_ctors_def,
       exported_fns_def, exported_fallback_def, consts_env_mods_singleton,
       subst_consts_fn_mods_singleton, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem build_func_defaults_mods_singleton:
  build_func_defaults_mods [(NONE, tops)] = build_func_defaults tops
Proof
  `∃exts ints fb ctor.
     FOLDR classify_function ([], [], NONE, NONE) tops = (exts, ints, fb, ctor)`
    by metis_tac[pairTheory.PAIR] >>
  pop_assum strip_assume_tac >>
  simp[build_func_defaults_mods_def, build_func_defaults_def,
       classify_functions_def, unit_internal_fns_def,
       consts_env_mods_singleton, subst_consts_fn_mods_singleton,
       nsid_to_string_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >>
  rpt strip_tac >> rename1 `MEM fd _` >> PairCases_on `fd` >>
  simp[fn_decl_name_def, subst_consts_fn_def]
QED

Theorem build_compile_env_unit_singleton:
  build_compile_env_unit [(NONE, tops)] NONE vis mut fname args ret stmts ut =
  build_compile_env tops vis mut fname args ret stmts ut
Proof
  simp[build_compile_env_unit_def, build_compile_env_def,
       make_struct_fields_map_mods_singleton, build_flag_info_mods_singleton,
       extract_layout_mods_singleton, build_var_type_map_mods_singleton,
       build_hashmap_info_mods_singleton, build_event_info_mods_singleton,
       lookup_custom_error_args_mods_singleton,
       add_module_var_locations_mods_singleton,
       add_immutable_locations_unit_singleton,
       collect_module_vars_mods_singleton, build_func_info_mods_singleton,
       build_func_param_types_mods_singleton,
       build_func_defaults_mods_singleton,
       build_func_return_type_mods_singleton,
       build_func_mutability_mods_singleton, build_func_ids_mods_singleton,
       type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED

Theorem package_external_fn_unit_singleton:
  package_external_fn_unit [(NONE, tops)] ut nkey_map (NONE, f) =
  package_external_fn tops ut nkey_map f
Proof
  PairCases_on `f` >>
  simp[package_external_fn_unit_def, package_external_fn_def,
       build_compile_env_unit_singleton]
QED

Theorem fn_allocs_ok_unit_singleton:
  fn_allocs_ok_unit [(NONE, tops)] (NONE, f) = fn_allocs_ok tops f
Proof
  PairCases_on `f` >>
  simp[fn_allocs_ok_unit_def, fn_allocs_ok_def,
       build_compile_env_unit_singleton]
QED

Theorem package_internal_fn_unit_singleton:
  package_internal_fn_unit [(NONE, tops)] ut nkey_map is_ctor imm_len (NONE, f) =
  package_internal_fn tops ut nkey_map is_ctor imm_len f
Proof
  PairCases_on `f` >>
  simp[package_internal_fn_unit_def, package_internal_fn_def,
       build_compile_env_unit_singleton, build_func_ids_mods_singleton,
       make_struct_fields_map_mods_singleton, nsid_to_string_def]
QED

Theorem package_fallback_fn_unit_singleton:
  package_fallback_fn_unit mods ut nkey_map NONE = NONE ∧
  package_fallback_fn_unit [(NONE, tops)] ut nkey_map (SOME (NONE, f)) =
  package_fallback_fn tops ut nkey_map (SOME f)
Proof
  conj_tac >- simp[package_fallback_fn_unit_def, package_fallback_fn_def] >>
  PairCases_on `f` >>
  simp[package_fallback_fn_unit_def, package_fallback_fn_def,
       build_compile_env_unit_singleton]
QED

Theorem package_constructor_unit_singleton:
  package_constructor_unit [(NONE, tops)] ut nkey_map f =
  package_constructor tops ut nkey_map f
Proof
  PairCases_on `f` >>
  simp[package_constructor_unit_def, package_constructor_def,
       build_compile_env_unit_singleton]
QED

Theorem package_external_group_unit_singleton:
  package_external_group_unit [(NONE, tops)] target ut nkey_map (NONE, f) =
  package_external_group tops target ut nkey_map f
Proof
  PairCases_on `f` >>
  simp[package_external_group_unit_def, package_external_group_def,
       package_external_fn_unit_singleton, type_env_all_modules_def,
       type_env_def, FUNION_FEMPTY_2]
QED

Theorem filter_unit_internal_names_singleton[local]:
  ∀P. FILTER (λ(src, f). P (nsid_to_string (src, fn_decl_name f)))
    (MAP (λf. (NONE, f)) ints) =
  MAP (λf. (NONE, f))
    (FILTER (λ(mut, nr, rr, fname, fargs, dflts, ret, body). P fname) ints)
Proof
  simp[rich_listTheory.FILTER_MAP, combinTheory.o_DEF, nsid_to_string_def] >>
  gen_tac >> AP_TERM_TAC >>
  simp[rich_listTheory.FILTER_EQ, FORALL_PROD, fn_decl_name_def]
QED

Theorem order_internals_unit_singleton:
  order_internals_unit names (MAP (λf. (NONE, f)) ints) =
  MAP (λf. (NONE, f)) (order_internals names ints)
Proof
  simp[order_internals_unit_def, order_internals_def,
       MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF,
       BETA_RULE (Q.SPEC `λfname. fname = n` filter_unit_internal_names_singleton)]
QED

Theorem internal_callees_unit_singleton[local]:
  internal_callees_unit (MAP (λf. (NONE, f)) ints) g =
  internal_callees ints g
Proof
  simp[internal_callees_unit_def, internal_callees_def,
       BETA_RULE (Q.SPEC `λfname. fname = g` filter_unit_internal_names_singleton),
       MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
QED

Theorem reach_internals_unit_singleton[local]:
  ∀n seen gs.
    reach_internals_unit (MAP (λf. (NONE, f)) ints) n seen gs =
    reach_internals ints n seen gs
Proof
  Induct >>
  simp[reach_internals_unit_def, reach_internals_def,
       internal_callees_unit_singleton]
QED

Theorem runtime_internal_order_unit_singleton:
  runtime_internal_order_unit [] tops (MAP (λf. (NONE, f)) ints) =
  runtime_internal_order tops ints
Proof
  simp[runtime_internal_order_unit_def, runtime_internal_order_def,
       reach_internals_unit_singleton]
QED

Theorem deploy_internal_order_unit_singleton:
  deploy_internal_order_unit ctor (MAP (λf. (NONE, f)) ints) =
  deploy_internal_order ctor ints
Proof
  simp[deploy_internal_order_unit_def, deploy_internal_order_def,
       reach_internals_unit_singleton]
QED

Theorem lower_vyper_runtime_unit_mods_singleton:
  lower_vyper_runtime_unit_mods [(NONE, tops)] [] rpolicy =
  lower_vyper_runtime_unit tops rpolicy
Proof
  `∃exts ints fb ctor. classify_functions tops = (exts, ints, fb, ctor)`
    by metis_tac[pairTheory.PAIR] >>
  pop_assum strip_assume_tac >>
  Cases_on `fb` >>
  simp[lower_vyper_runtime_unit_mods_def, lower_vyper_runtime_unit_def,
       classify_functions_unit_singleton, main_module_def, alistTheory.ALOOKUP_def,
       type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2,
       rich_listTheory.FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP, EXISTS_MAP,
       runtime_internal_order_unit_singleton, order_internals_unit_singleton,
       package_external_fn_unit_singleton, package_internal_fn_unit_singleton,
       package_fallback_fn_unit_singleton, cj 1 package_fallback_fn_def,
       cj 1 exported_runtime_fns_def,
       package_external_group_unit_singleton,
       compute_immutables_len_unit_singleton, make_struct_fields_map_mods_singleton,
       fn_allocs_ok_unit_singleton, consts_env_mods_singleton, EVERY_APPEND] >>
  simp[UNCURRY, SF ETA_ss]
QED

Theorem lower_vyper_deploy_unit_mods_singleton:
  lower_vyper_deploy_unit_mods [(NONE, tops)] [] rpolicy bytes =
  lower_vyper_deploy_unit tops rpolicy bytes
Proof
  `∃exts ints fb ctor. classify_functions tops = (exts, ints, fb, ctor)`
    by metis_tac[pairTheory.PAIR] >>
  pop_assum strip_assume_tac >>
  Cases_on `ctor` >>
  simp[lower_vyper_deploy_unit_mods_def, lower_vyper_deploy_unit_def,
       classify_functions_unit_singleton, make_struct_fields_map_mods_singleton,
       compute_immutables_len_unit_singleton, consts_env_mods_singleton,
       deploy_internal_order_unit_singleton, order_internals_unit_singleton,
       MAP_MAP_o, combinTheory.o_DEF, EXISTS_APPEND, EXISTS_MAP,
       fn_allocs_ok_unit_singleton,
       package_internal_fn_unit_singleton, package_constructor_unit_singleton] >>
  simp[UNCURRY, SF ETA_ss]
QED

Theorem compile_vyper_with_mods_singleton:
  compile_vyper_with_mods pipeline fin policy [(NONE, tops)] [] =
  compile_vyper_with pipeline fin policy tops
Proof
  simp[compile_vyper_with_mods_def, compile_vyper_with_def,
       lower_vyper_runtime_unit_mods_singleton,
       lower_vyper_deploy_unit_mods_singleton]
QED

Theorem compile_vyper_mods_singleton:
  compile_vyper_mods fin policy [(NONE, tops)] [] = compile_vyper fin policy tops
Proof
  simp[compile_vyper_mods_def, compile_vyper_def,
       compile_vyper_with_mods_singleton]
QED
