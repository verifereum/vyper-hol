(*
 * Module Analysis: Extract Compilation Metadata from Vyper AST
 *
 * Extracts all module-level metadata needed to build compile_env
 * and the arguments for compile_generate_runtime, from a toplevel list.
 *
 * Mirrors Python: VenomCompiler.__init__, _compile_fn, and
 * various metadata extraction in vyper/semantics/.
 *
 * TOP-LEVEL:
 *   build_struct_fields_map  -- struct name → (field_name, type, mem_size)
 *   build_flag_info          -- flag name → member count, member → index
 *   build_event_info_map     -- event name → (hash, indexed flags, bytestring flags)
 *   build_storage_layout     -- variable name → storage slot
 *   build_transient_layout   -- variable name → transient slot
 *   assign_nkeys             -- nonreentrant key assignment
 *   classify_functions       -- split toplevels into external/internal/fallback
 *   build_positional_args    -- prepare ABI decode info for function args
 *   build_compile_env        -- build compile_env for a function
 *   compute_fn_eom           -- end-of-memory for a function's alloca region
 *)

Theory moduleAnalysis
Ancestors
  exprLowering
  compileEnv
  selectorDispatch
  vyperContext
  vyperAST

(* ===== Struct Fields ===== *)

(* Build struct fields with memory sizes from StructDecl list.
   Each field is (field_name, field_type, memory_bytes).
   The struct_fields_map is needed for type_memory_bytes, creating
   a mutual dependency. We break it by building incrementally:
   each struct can only reference previously-defined structs
   (Vyper guarantees no recursive structs). *)

(* Compute memory bytes for a type given a struct field map.
   Standalone version that takes sft explicitly. *)
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
  type_mem_bytes sft (StructT name) =
    SUM (MAP (SND o SND) (sft name)) ∧
  type_mem_bytes sft (TupleT tys) =
    SUM (MAP (type_mem_bytes sft) tys) ∧
  type_mem_bytes sft NoneT = 0
Termination
  WF_REL_TAC `measure (type_size o SND)`
End

(* Build struct fields for a single struct, given already-built map *)
Definition build_struct_fields_one_def:
  build_struct_fields_one sft (args : (string # type) list) =
    MAP (λ(name, ty). (name, ty, type_mem_bytes sft ty)) args
End

(* Build the struct fields map incrementally from toplevel list.
   Non-struct toplevels are skipped. Each StructDecl extends the map. *)
Definition build_struct_fields_map_def:
  build_struct_fields_map [] (sft : string -> (string # type # num) list) = sft ∧
  build_struct_fields_map (top :: rest) sft =
    case top of
      StructDecl sname args =>
        build_struct_fields_map rest
          (λn. if n = sname then build_struct_fields_one sft args else sft n)
    | _ => build_struct_fields_map rest sft
End

(* Top-level: build struct fields map from toplevel list.
   Initial map returns [] for unknown structs. *)
Definition make_struct_fields_map_def:
  make_struct_fields_map tops = build_struct_fields_map tops (K [])
End

(* ===== Flag Info ===== *)

(* Build flag member index: (flag_name, member_name) → positional index *)
Definition build_flag_member_id_one_def:
  build_flag_member_id_one [] (idx : num) = (K 0n) ∧
  build_flag_member_id_one (m :: ms) idx =
    let rest = build_flag_member_id_one ms (idx + 1) in
    (λname. if name = m then idx else rest name)
End

Definition build_flag_info_def:
  build_flag_info []
    (fmid : string -> string -> num)
    (fnm : string -> num) = (fmid, fnm) ∧
  build_flag_info (top :: rest) fmid fnm =
    case top of
      FlagDecl fname members =>
        build_flag_info rest
          (λflag_name. if flag_name = fname
                       then build_flag_member_id_one members 0
                       else fmid flag_name)
          (λflag_name. if flag_name = fname
                       then LENGTH members
                       else fnm flag_name)
    | _ => build_flag_info rest fmid fnm
End

(* Top-level: extract flag info from toplevel list *)
Definition make_flag_info_def:
  make_flag_info tops = build_flag_info tops (K (K 0)) (K 0)
End

(* ===== Event Info ===== *)

(* Compute event topic0 hash: keccak256 of event signature.
   Event signature format: "EventName(type1,type2,...)"
   Same as function_signature from contractABI. *)
Definition event_hash_def:
  event_hash tenv ename (arg_types : type list) =
    let abi_types = vyper_to_abi_types tenv arg_types in
    let sig_str = function_signature ename abi_types in
    let hash_bytes = Keccak_256_w64 (MAP (n2w o ORD) sig_str) in
    w2n (word_of_bytes_be hash_bytes : bytes32)
End

(* Build event info from EventDecl.
   Result: event_name → (event_hash, indexed_flags, topic_is_bytestring)
   indexed_flags: bool list from EventDecl annotations
   topic_is_bytestring: whether each indexed arg is bytes/string *)
Definition is_bytestring_type_def:
  is_bytestring_type (BaseT (BytesT _)) = T ∧
  is_bytestring_type (BaseT (StringT _)) = T ∧
  is_bytestring_type _ = F
End

(* Helper: extract topic_is_bytestring from event args *)
Definition event_topic_bs_def:
  event_topic_bs [] = ([] : bool list) ∧
  event_topic_bs (((_,ty),is_idx) :: rest) =
    (if is_idx then is_bytestring_type ty else F) :: event_topic_bs rest
End

Definition build_event_info_aux_def:
  build_event_info_aux tenv ename args_indexed
    (eim : string -> num # bool list # bool list) =
    let arg_types = MAP (SND o FST) args_indexed in
    let ehash = event_hash tenv ename arg_types in
    let indexed_flags = MAP SND args_indexed in
    let topic_bs = event_topic_bs args_indexed in
    (λn. if n = ename then (ehash, indexed_flags, topic_bs) else eim n)
End

Definition build_event_info_def:
  build_event_info tenv ([] : toplevel list)
    (eim : string -> num # bool list # bool list) = eim ∧
  build_event_info tenv (top :: rest) eim =
    case top of
      EventDecl ename args_indexed =>
        build_event_info tenv rest
          (build_event_info_aux tenv ename args_indexed eim)
    | _ => build_event_info tenv rest eim
End

Definition make_event_info_def:
  make_event_info tenv tops = build_event_info tenv tops (K (0, [], []))
End

(* ===== Storage Layout ===== *)

(* Assign sequential storage slots to state variables.
   VariableDecl with Storage mutability get sequential slots.
   HashMapDecl (non-transient) also get sequential slots.
   Slot size depends on type: word types = 1 slot,
   arrays/structs = ceil(memory_bytes / 32) slots. *)
Definition storage_slots_for_type_def:
  storage_slots_for_type sft ty =
    let mem_bytes = type_mem_bytes sft ty in
    (mem_bytes + 31) DIV 32
End

Definition build_storage_layout_def:
  build_storage_layout ([] : toplevel list) sft (next_slot : num) =
    (FEMPTY : (string, bytes32) fmap) ∧
  build_storage_layout (top :: rest) sft next_slot =
    case top of
      VariableDecl _ Storage vname ty =>
        (build_storage_layout rest sft
          (next_slot + storage_slots_for_type sft ty))
        |+ (vname, n2w next_slot)
    | HashMapDecl _ F hname _ _ =>
        (build_storage_layout rest sft (next_slot + 1))
        |+ (hname, n2w next_slot)
    | _ => build_storage_layout rest sft next_slot
End

Definition make_storage_layout_def:
  make_storage_layout tops =
    build_storage_layout tops (make_struct_fields_map tops) 0
End

(* ===== Transient Storage Layout ===== *)

Definition build_transient_layout_def:
  build_transient_layout ([] : toplevel list) sft (next_slot : num) =
    (FEMPTY : (string, bytes32) fmap) ∧
  build_transient_layout (top :: rest) sft next_slot =
    case top of
      VariableDecl _ Transient vname ty =>
        (build_transient_layout rest sft
          (next_slot + storage_slots_for_type sft ty))
        |+ (vname, n2w next_slot)
    | HashMapDecl _ T hname _ _ =>
        (build_transient_layout rest sft (next_slot + 1))
        |+ (hname, n2w next_slot)
    | _ => build_transient_layout rest sft next_slot
End

Definition make_transient_layout_def:
  make_transient_layout tops =
    build_transient_layout tops (make_struct_fields_map tops) 0
End

(* ===== Variable Type Map ===== *)

(* Build var_type map: variable name → type option.
   Covers state variables declared at module level. *)
Definition build_var_type_map_def:
  build_var_type_map ([] : toplevel list) = (K NONE : string -> type option) ∧
  build_var_type_map (top :: rest) =
    case top of
      VariableDecl _ _ vname ty =>
        (λn. if n = vname then SOME ty else build_var_type_map rest n)
    | _ => build_var_type_map rest
End

(* ===== HashMap Detection ===== *)

(* Build is_hashmap map: variable name → T if HashMapDecl *)
Definition build_is_hashmap_def:
  build_is_hashmap ([] : toplevel list) = (K F : string -> bool) ∧
  build_is_hashmap (top :: rest) =
    case top of
      HashMapDecl _ _ hname _ _ =>
        (λn. if n = hname then T else build_is_hashmap rest n)
    | _ => build_is_hashmap rest
End

(* ===== Nonreentrant Key Assignment ===== *)

(* Assign sequential nkeys to nonreentrant functions.
   Nonreentrant lock slots start at 0. Each nonreentrant function
   gets a unique key. The lock is stored in storage (or transient
   if use_transient is set). *)
Definition assign_nkeys_def:
  assign_nkeys ([] : toplevel list) (next : num) = (K 0n : string -> num) ∧
  assign_nkeys (top :: rest) next =
    case top of
      FunctionDecl _ _ T fname _ _ _ _ =>
        let nkey_map = assign_nkeys rest (next + 1) in
        (λn. if n = fname then next else nkey_map n)
    | _ => assign_nkeys rest next
End

Definition make_nkey_map_def:
  make_nkey_map tops = assign_nkeys tops 0
End

(* ===== Function Classification ===== *)

(* Classify functions from toplevel list into external, internal,
   and fallback (default). *)
Definition classify_function_def:
  classify_function (FunctionDecl vis mut nr fname fargs dflts ret body)
    (exts, ints, fb) =
    (case vis of
       External =>
         if fname = "__default__" then
           (exts, ints,
            SOME (External, mut, nr, fname, fargs, dflts, ret, body))
         else
           ((External, mut, nr, fname, fargs, dflts, ret, body) :: exts,
            ints, fb)
     | Internal =>
         (exts,
          (Internal, mut, nr, fname, fargs, dflts, ret, body) :: ints, fb)
     | Deploy =>
         (exts,
          (Deploy, mut, nr, fname, fargs, dflts, ret, body) :: ints, fb)) ∧
  classify_function _ acc = acc
End

Definition classify_functions_def:
  classify_functions tops =
    FOLDR classify_function ([], [], NONE) tops
End

(* ===== Memory Allocation ===== *)

(* Allocate memory for function-local variables.
   Walks the argument list and assigns sequential alloca offsets.
   Returns (var_map, next_offset) where var_map maps names to MemLoc. *)
Definition allocate_args_def:
  allocate_args sft [] (offset : num) vars = (vars, offset) ∧
  allocate_args sft ((name, ty) :: rest) offset vars =
    let sz = type_mem_bytes sft ty in
    allocate_args sft rest (offset + sz)
      (vars |+ (name, MemLoc offset sz))
End

(* Allocate special internal variables:
   __return_buf__ (for memory returns) and __return_pc__ *)
Definition allocate_internal_special_vars_def:
  allocate_internal_special_vars has_return_buf offset vars =
    let (vars1, off1) =
      if has_return_buf then
        (vars |+ ("__return_buf__", MemLoc offset 32), offset + 32)
      else (vars, offset) in
    (vars1 |+ ("__return_pc__", MemLoc off1 32), off1 + 32)
End

(* ===== Positional Args for ABI Decoding ===== *)

(* Build the positional argument info needed by compile_decode_args.
   Each arg becomes (name, is_prim, is_dynamic, abi_size, dec_info). *)
Definition build_positional_arg_def:
  build_positional_arg cenv ((name, ty) : string # type) =
    let is_prim = is_word_type ty in
    let is_dyn = is_abi_dynamic (cenv_sft cenv) ty in
    let abi_sz = abi_embedded_static_size (cenv_sft cenv) ty in
    let dec = type_to_abi_dec_info cenv ty in
    (name, is_prim, is_dyn, abi_sz, dec)
End

Definition build_positional_args_def:
  build_positional_args cenv args =
    MAP (build_positional_arg cenv) args
End

(* ===== Local Variable Collection ===== *)

(* Collect local variable declarations (AnnAssign) from a statement list.
   Walks into If/For/nested blocks. Each AnnAssign declares a local
   that Python pre-allocates before lowering the body. *)
(* Collect all local variable declarations (AnnAssign) from a statement list.
   Walks into If/For blocks to find nested declarations.
   Vyper variables are function-scoped, so Python pre-allocates all
   locals at function entry regardless of nesting. *)
Definition collect_locals_def:
  collect_locals ([] : stmt list) = ([] : (string # type) list) ∧
  collect_locals (AnnAssign id ty _ :: rest) =
    (id, ty) :: collect_locals rest ∧
  collect_locals (If _ then_stmts else_stmts :: rest) =
    collect_locals then_stmts ++
    collect_locals else_stmts ++
    collect_locals rest ∧
  collect_locals (For _ _ _ _ for_body :: rest) =
    collect_locals for_body ++ collect_locals rest ∧
  collect_locals (_ :: rest) = collect_locals rest
End

(* ===== Dynamic Array Capacity ===== *)

(* Extract dynamic array capacity from a type.
   Returns SOME n for ArrayT _ (Dynamic n), NONE otherwise. *)
Definition dynarray_capacity_of_type_def:
  dynarray_capacity_of_type (ArrayT _ (Dynamic n)) = SOME n ∧
  dynarray_capacity_of_type _ = NONE
End

(* Build dynarray_capacity map from variable declarations + locals.
   Maps variable name → max capacity for dynamic arrays. *)
Definition build_dynarray_capacity_def:
  build_dynarray_capacity ([] : (string # type) list) = (K 0n : string -> num) ∧
  build_dynarray_capacity ((vname, ty) :: rest) =
    let rest_map = build_dynarray_capacity rest in
    case dynarray_capacity_of_type ty of
      SOME n => (λs. if s = vname then n else rest_map s)
    | NONE => rest_map
End

(* Collect module-level variable declarations as (name, type) pairs *)
Definition collect_module_vars_def:
  collect_module_vars ([] : toplevel list) = ([] : (string # type) list) ∧
  collect_module_vars (top :: rest) =
    let here = (case top of
        VariableDecl _ _ vname ty => [(vname, ty)]
      | _ => []) in
    here ++ collect_module_vars rest
End

(* ===== Method ID Map ===== *)

(* Build method_id map: func_name → selector num.
   Uses function_selector and calldata_method_id from selectorDispatch. *)
Definition build_method_id_map_def:
  build_method_id_map tenv ([] : toplevel list) = (K 0n : string -> num) ∧
  build_method_id_map tenv (top :: rest) =
    let rest_map = build_method_id_map tenv rest in
    case top of
      FunctionDecl External _ _ fname fargs _ _ _ =>
        let abi_types = vyper_to_abi_types tenv (MAP SND fargs) in
        let sel_bytes = function_selector fname abi_types in
        let sel_num = w2n (calldata_method_id sel_bytes) in
        (λs. if s = fname then sel_num else rest_map s)
    | _ => rest_map
End

(* ===== Internal Function Info ===== *)

(* Build func_info map: fn_label → (returns_count, return_buf_size, pass_via_stack).
   Iterates over internal/deploy functions, computes calling convention. *)
Definition build_func_info_def:
  build_func_info sft ([] : toplevel list) =
    (K (0n, 0n, [] : bool list) : string -> num # num # bool list) ∧
  build_func_info sft (top :: rest) =
    let rest_map = build_func_info sft rest in
    case top of
      FunctionDecl vis _ _ fname fargs _ ret _ =>
        if vis = External then rest_map
        else
          let fn_lbl = "fn_" ++ fname in
          let arg_types = MAP SND fargs in
          let ret_mem = type_mem_bytes sft ret in
          let info = compute_func_info (λn. MAP (FST o SND) (sft n))
                       ret ret_mem arg_types in
          (λs. if s = fn_lbl then info else rest_map s)
    | _ => rest_map
End

(* ===== Compile Env Construction ===== *)

(* Build a compile_env for a function given module-level metadata.
   This is the core function that packages everything together.
   Arguments:
   - tops: full toplevel list (for module-level metadata)
   - vis: function visibility (External/Internal/Deploy)
   - mut: function mutability
   - func_name: function name
   - args: function arguments
   - ret_type: return type
   - body: function body (for local variable discovery)
   - use_transient_locks: whether to use transient storage for locks *)
Definition build_compile_env_def:
  build_compile_env tops vis (mut : function_mutability) func_name
    (args : (string # type) list) (ret_type : type)
    (body : stmt list) (use_transient_locks : bool) =
    let sft = make_struct_fields_map tops in
    let sft_types = (λname. MAP (FST o SND) (sft name)) in
    let (flag_member_id, flag_n_members) = make_flag_info tops in
    let storage_layout = make_storage_layout tops in
    let transient_layout = make_transient_layout tops in
    (* Combine storage + transient into ce_storage_layout.
       Storage vars map to their slot, transient vars also (they're
       accessed via TLOAD/TSTORE, not SLOAD/SSTORE, so no conflict). *)
    let combined_layout = FUNION storage_layout transient_layout in
    let var_type_map = build_var_type_map tops in
    let is_hashmap = build_is_hashmap tops in
    let tenv = type_env tops in
    let event_info = make_event_info tenv tops in
    let is_external = (vis = External) in
    let rc = returns_stack_count sft_types ret_type in
    let has_return_buf = (rc = 0 ∧ ret_type ≠ NoneT) in
    (* Allocate memory for arguments *)
    let (arg_vars, args_end) = allocate_args sft args 0 FEMPTY in
    (* Allocate memory for local variables *)
    let locals = collect_locals body in
    let (local_vars, locals_end) = allocate_args sft locals args_end arg_vars in
    (* For internal functions, allocate special vars *)
    let (all_vars, total_mem) =
      if is_external then (local_vars, locals_end)
      else allocate_internal_special_vars has_return_buf locals_end local_vars in
    (* Return buffer offset *)
    let ret_buf = if has_return_buf then
                    SOME (total_mem : num) (* placeholder *)
                  else NONE in
    let nr_info = (F, 0n, use_transient_locks, mut = View) in
    (* Dynamic array capacity: from module vars + local vars *)
    let all_decls = collect_module_vars tops ++ args ++ locals in
    let dynarray_cap = build_dynarray_capacity all_decls in
    (* Method ID map *)
    let method_id_map = build_method_id_map tenv tops in
    (* Internal function info *)
    let func_info = build_func_info sft tops in
    (* Variable type map: combine module-level + args + locals *)
    let local_var_type = (λn.
          case ALOOKUP (REVERSE (args ++ locals)) n of
            SOME ty => SOME ty
          | NONE => var_type_map n) in
    <| ce_vars := all_vars;
       ce_storage_layout := combined_layout;
       ce_module := NONE;
       ce_struct_fields := sft;
       ce_dynarray_capacity := dynarray_cap;
       ce_method_id := method_id_map;
       ce_flag_member_id := flag_member_id;
       ce_flag_n_members := flag_n_members;
       ce_var_type := local_var_type;
       ce_is_hashmap := is_hashmap;
       ce_event_info := event_info;
       ce_returns_count := rc;
       ce_return_buf := ret_buf;
       ce_is_external := is_external;
       ce_ret_enc_info := AbiPrimWord; (* updated below for external *)
       ce_ret_dec_info := DecPrimWord NoClamp;
       ce_max_return_size := 0;
       ce_is_ctor := (vis = Deploy);
       ce_func_info := func_info;
       ce_nonreentrant := nr_info;
       ce_raw_return := F
    |> : compile_env
End

(* Update compile_env with ABI return info for external functions *)
Definition update_cenv_ret_abi_def:
  update_cenv_ret_abi cenv ret_type =
    let enc_info = type_to_abi_enc_info cenv ret_type in
    let dec_info = type_to_abi_dec_info cenv ret_type in
    let max_ret = abi_size_bound (cenv_sft cenv) ret_type in
    cenv with <| ce_ret_enc_info := enc_info;
                 ce_ret_dec_info := dec_info;
                 ce_max_return_size := max_ret |>
End

(* Update compile_env with nonreentrant info *)
Definition update_cenv_nonreentrant_def:
  update_cenv_nonreentrant cenv is_nr nkey use_trans is_view =
    cenv with ce_nonreentrant := (is_nr, nkey, use_trans, is_view)
End

(* ===== End-of-Memory Computation ===== *)

(* Compute fn_eom for a function: maximum alloca offset + size.
   This is the end-of-memory marker that codegen uses to place spills. *)
Definition compute_fn_eom_def:
  compute_fn_eom (cenv : compile_env) =
    let entries = fmap_to_alist cenv.ce_vars in
    FOLDL (λacc (_, loc).
      case loc of
        MemLoc offset sz => MAX acc (offset + sz)
      | _ => acc)
    0 entries
End

(* ===== Min Calldata Size ===== *)

(* Minimum calldata size for an external function.
   4 (selector) + sum of ABI embedded static sizes of required args.
   Default args are optional, so only non-default args count. *)
Definition min_calldata_size_def:
  min_calldata_size cenv (args : (string # type) list) (n_defaults : num) =
    let required = TAKE (LENGTH args - n_defaults) args in
    let sizes = MAP (λ(_,ty). abi_embedded_static_size (cenv_sft cenv) ty)
                    required in
    4 + SUM sizes
End
