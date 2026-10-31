(* Pinned Venom ABI operands: lowering produces locations; unwrap loads words
   and copies non-memory locations; staging later reads complex memory. *)
Theory vyperAbiOperand
Ancestors
  arithmetic alist list option pair rich_list words vyperMisc
  vyperAST vyperValue vyperValueOperation vyperStorage vyperContext vyperState
Libs
  monadsyntax

Datatype:
  abi_operand = AbiSnapshot value
              | AbiMemory num num type_value
              | AbiImmutable num num type_value
              | AbiStorage bool bytes32 type_value
              | AbiMapping bool bytes32 type value_type
End

Definition abi_primitive_def:
  abi_primitive (BaseTV (BytesT (Dynamic _))) = F ∧
  abi_primitive (BaseTV (StringT _)) = F ∧
  abi_primitive (BaseTV _) = T ∧
  abi_primitive (FlagTV _) = T ∧
  abi_primitive _ = F
End

Definition mark_abi_memory_def:
  mark_abi_memory st = return (LENGTH st.abi_memory) st
End

Definition release_abi_memory_def:
  release_abi_memory mark st =
    return () (st with abi_memory := TAKE mark st.abi_memory)
End

(* Representation captures are scoped to an ABI encoding. Existing backing
   stays live (including writes); only this scope's fresh suffix is discarded.
   Logical immutable values are authoritative beyond the representation scope. *)
Definition mark_abi_captures_def:
  mark_abi_captures st = return (LENGTH st.abi_memory, LENGTH st.abi_immutables) st
End

Definition release_abi_captures_def:
  release_abi_captures mark st = return () (st with <|
    abi_memory := TAKE (FST mark) st.abi_memory;
    abi_immutables := TAKE (SND mark) st.abi_immutables |>)
End

Definition read_abi_operand_def:
  read_abi_operand cx (AbiSnapshot v) = return v ∧
  read_abi_operand cx (AbiMemory token off tv) = (λst.
    case oEL token st.abi_memory of
    | NONE => raise (Error (TypeError "ABI memory token")) st
    | SOME (key,mem) => lift_option (decode_value mem off tv) "ABI memory read" st) ∧
  read_abi_operand cx (AbiImmutable token off tv) = (λst.
    case oEL token st.abi_immutables of
    | NONE => raise (Error (TypeError "ABI immutable token")) st
    | SOME (key,mem) => lift_option (decode_value mem off tv) "ABI immutable read" st) ∧
  read_abi_operand cx (AbiStorage tr slot tv) = read_storage_slot cx tr slot tv ∧
  read_abi_operand cx (AbiMapping _ _ _ _) =
    raise (Error (TypeError "ABI mapping value"))
End

(* This phase is deliberately NOT a snapshot of complex memory operands. *)
Definition unwrap_abi_operand_def:
  unwrap_abi_operand cx (AbiMemory token off tv) =
    (if abi_primitive tv then do
      v <- read_abi_operand cx (AbiMemory token off tv);
      return (AbiSnapshot v)
    od else return (AbiMemory token off tv)) ∧
  (* ctx.unwrap/load_immutable_to_memory copies complex immutable operands
     BEFORE lowering the next argument, in constructor and runtime alike. *)
  unwrap_abi_operand cx (AbiImmutable token off tv) = do
    v <- read_abi_operand cx (AbiImmutable token off tv);
    return (AbiSnapshot v)
  od ∧
  unwrap_abi_operand cx (AbiStorage tr slot tv) = do
    v <- read_storage_slot cx tr slot tv;
    return (AbiSnapshot v)
  od ∧
  unwrap_abi_operand cx (AbiSnapshot v) = return (AbiSnapshot v) ∧
  unwrap_abi_operand cx (AbiMapping _ _ _ _) =
    raise (Error (TypeError "ABI mapping unwrap"))
End

Definition stage_abi_operands_def:
  stage_abi_operands cx [] = return [] ∧
  stage_abi_operands cx (arg::args) = do
    v <- read_abi_operand cx arg;
    vs <- stage_abi_operands cx args;
    return (v::vs)
  od
End

Definition lookup_abi_local_def:
  lookup_abi_local cx id = do
    scopes <- get_scopes;
    entry <- lift_option_type (lookup_scopes id scopes) "Name not in scope";
    if abi_primitive entry.type then return (AbiSnapshot entry.value)
    else do
      token <- capture_abi_memory cx id entry.type entry.value;
      return (AbiMemory token 0 entry.type)
    od
  od
End

(* The general evaluator has already validated this location. In particular,
   a target index may have popped an ancestor after capturing the parent.
   Resolve its type-directed offset, not its dynamic ancestor bounds. *)
Definition lookup_abi_memory_place_def:
  lookup_abi_memory_place cx id path = do
    scopes <- get_scopes;
    entry <- lift_option_type (lookup_scopes id scopes) "Name not in scope";
    (off,tv) <- lift_option_type (abi_path_offset entry.type path) "ABI memory path";
    child <- lift_sum (read_memory_path entry path);
    token <- capture_abi_memory_at cx id entry.type entry.value off tv child;
    return (AbiMemory token off tv)
  od
End

Definition lookup_abi_immutable_def:
  lookup_abi_immutable cx src id = do
    imms <- get_immutables cx src;
    (tv,v) <- lift_option_type (FLOOKUP imms id) "ABI immutable lookup";
    if abi_primitive tv then return (AbiSnapshot v)
    else do
      token <- capture_abi_immutable cx src id tv v;
      return (AbiImmutable token 0 tv)
    od
  od
End

Definition lookup_abi_global_def:
  lookup_abi_global cx src id = do
    ts <- lift_option_type (get_module_code cx src) "ABI global module";
    case find_var_decl_by_name id ts of
    | SOME (StorageVarDecl tr typ, name) => do
        slot <- lift_option_type (lookup_var_slot_from_layout cx tr src name) "ABI global slot";
        tv <- lift_option_type (evaluate_type (get_tenv cx) typ) "ABI global type";
        return (AbiStorage tr (n2w slot) tv)
      od
    | SOME (HashMapVarDecl tr kt vt, name) => do
        slot <- lift_option_type (lookup_var_slot_from_layout cx tr src name) "ABI mapping slot";
        return (AbiMapping tr (n2w slot) kt vt)
      od
    | NONE => lookup_abi_immutable cx src id
  od
End

(* Bounds are runtime checks, distinct from invalid projection shapes/types.
   Check capacity before asking abi_subscript_offset for an address: its NONE
   also represents malformed projections and must not be blanket-reclassified.
   Checks happen while forming the pointer, not when staging, so an index
   evaluated once remains valid even if a later child pops the array. *)
Definition check_abi_projection_def:
  check_abi_projection cx arg (ArrayTV tv (Dynamic n)) (ValueSubscript (IntV i)) = do
    check (0 ≤ i ∧ Num i < n) "ABI subscript bounds";
    len <- (case arg of
      | AbiMemory token off _ => (λst.
          case oEL token st.abi_memory of
          | NONE => raise (Error (TypeError "ABI projection token")) st
          | SOME (key,mem) => return (w2n (lookup_storage (n2w off) mem)) st)
      | AbiImmutable token off _ => (λst.
          case oEL token st.abi_immutables of
          | NONE => raise (Error (TypeError "ABI immutable projection token")) st
          | SOME (key,mem) => return (w2n (lookup_storage (n2w off) mem)) st)
      | AbiStorage tr slot _ => do
          mem <- get_storage_backend cx tr;
          return (w2n (lookup_storage slot mem))
        od
      | _ => raise (Error (TypeError "ABI projection location")));
    check (0 ≤ i ∧ Num i < len) "ABI subscript dynamic bounds"
  od ∧
  check_abi_projection cx arg (ArrayTV tv (Fixed n)) (ValueSubscript (IntV i)) =
    check (0 ≤ i ∧ Num i < n) "ABI subscript bounds" ∧
  check_abi_projection cx arg tv sub = return ()
End

Definition project_abi_operand_def:
  project_abi_operand cx (AbiMemory token off tv) sub = do
    check_abi_projection cx (AbiMemory token off tv) tv sub;
    (delta,t) <- lift_option_type (abi_subscript_offset tv sub) "ABI memory projection";
    return (AbiMemory token (off + delta) t)
  od ∧
  project_abi_operand cx (AbiImmutable token off tv) sub = do
    check_abi_projection cx (AbiImmutable token off tv) tv sub;
    (delta,t) <- lift_option_type (abi_subscript_offset tv sub) "ABI immutable projection";
    return (AbiImmutable token (off + delta) t)
  od ∧
  project_abi_operand cx (AbiStorage tr slot tv) sub = do
    check_abi_projection cx (AbiStorage tr slot tv) tv sub;
    (delta,t) <- lift_option_type (abi_subscript_offset tv sub) "ABI storage projection";
    return (AbiStorage tr (slot + n2w delta) t)
  od ∧
  project_abi_operand cx (AbiMapping tr slot kt vt) (ValueSubscript key) =
    (let slot = hashmap_slot slot (encode_hashmap_key kt key) in
     case vt of
     | HashMapT kt' vt' => return (AbiMapping tr slot kt' vt')
     | Type typ => do
         tv <- lift_option_type (evaluate_type (get_tenv cx) typ) "ABI mapping type";
         return (AbiStorage tr slot tv)
       od) ∧
  project_abi_operand cx _ _ = raise (Error (TypeError "ABI projection"))
End

Definition subscript_abi_operand_def:
  subscript_abi_operand cx arr_tv (AbiSnapshot v) index = do
    child <- lift_sum (evaluate_subscripts arr_tv v [ValueSubscript index]);
    return (AbiSnapshot child)
  od ∧
  subscript_abi_operand cx arr_tv arg index =
    project_abi_operand cx arg (ValueSubscript index)
End

Definition attribute_abi_operand_def:
  attribute_abi_operand cx (AbiSnapshot v) id = do
    child <- lift_sum (evaluate_attribute v id);
    return (AbiSnapshot child)
  od ∧
  attribute_abi_operand cx arg id = project_abi_operand cx arg (AttrSubscript id)
End

Definition project_abi_path_def:
  project_abi_path cx arg [] = return arg ∧
  project_abi_path cx arg (sub::subs) = do
    arg <- project_abi_operand cx arg sub;
    project_abi_path cx arg subs
  od
End

Definition abi_target_operand_def:
  abi_target_operand cx (ScopedVar id) subs = do
    arg <- lookup_abi_local cx id;
    project_abi_path cx arg (REVERSE subs)
  od ∧
  abi_target_operand cx (TopLevelVar src id) subs = do
    arg <- lookup_abi_global cx src id;
    project_abi_path cx arg (REVERSE subs)
  od ∧
  (* Only direct immutable mutations are banned by the pinned constructor
     checker. Projected constructor targets are genuine immutable locations.
     Venom's current pop codegen panics for these; the location semantics here
     also describes legacy's executable constructor behavior, not that panic. *)
  abi_target_operand cx (ImmutableVar src id) [] =
    raise (Error (TypeError "ABI immutable pop")) ∧
  abi_target_operand cx (ImmutableVar src id) (sub::subs) = do
    arg <- lookup_abi_immutable cx src id;
    project_abi_path cx arg (REVERSE (sub::subs))
  od
End

Definition abi_pop_pointer_def:
  abi_pop_pointer cx arg = do
    v <- read_abi_operand cx arg;
    case v of
    | ArrayV (DynArrayV vs) => do
        check (vs ≠ []) "pop empty ABI array";
        project_abi_operand cx arg (ValueSubscript (IntV (&(LENGTH vs - 1))))
      od
    | _ => raise (Error (TypeError "ABI pop array"))
  od
End

(* No readiness/bounds premise on the index: these include negative,
   capacity-OOB, and logical-length-OOB indices. Only memory token liveness
   matters; malformed projection shapes retain their separate TypeErrors. *)
Theorem abi_array_memory_projection_no_type_error:
  oEL token st.abi_memory = SOME (key,mem) ==>
  FST (project_abi_operand cx (AbiMemory token off (ArrayTV tv bd))
    (ValueSubscript (IntV i)) st) <> INR (Error (TypeError msg))
Proof
  Cases_on `bd` >>
  rw[project_abi_operand_def, check_abi_projection_def, abi_subscript_offset_def,
     bound_length_def, ignore_bind_def, bind_def, check_def, assert_def,
     lift_option_type_def, return_def, raise_def]
QED

Theorem abi_array_immutable_projection_no_type_error:
  oEL token st.abi_immutables = SOME (key,mem) ==>
  FST (project_abi_operand cx (AbiImmutable token off (ArrayTV tv bd))
    (ValueSubscript (IntV i)) st) <> INR (Error (TypeError msg))
Proof
  Cases_on `bd` >>
  rw[project_abi_operand_def, check_abi_projection_def, abi_subscript_offset_def,
     bound_length_def, ignore_bind_def, bind_def, check_def, assert_def,
     lift_option_type_def, return_def, raise_def]
QED

Theorem abi_array_storage_projection_no_type_error:
  FST (project_abi_operand cx (AbiStorage tr slot (ArrayTV tv bd))
    (ValueSubscript (IntV i)) st) <> INR (Error (TypeError msg))
Proof
  Cases_on `bd` >> Cases_on `tr` >>
  rw[project_abi_operand_def, check_abi_projection_def, abi_subscript_offset_def,
     bound_length_def, ignore_bind_def, bind_def, check_def, assert_def,
     lift_option_type_def, return_def, raise_def, get_storage_backend_def,
     get_accounts_def, get_transient_storage_def]
QED

Theorem abi_capacity_runtime_error:
  ~(0 <= i /\ Num i < bound_length bd) ==>
  project_abi_operand cx (AbiMemory token off (ArrayTV tv bd))
    (ValueSubscript (IntV i)) st =
      (INR (Error (RuntimeError "ABI subscript bounds")),st) /\
  project_abi_operand cx (AbiStorage tr slot (ArrayTV tv bd))
    (ValueSubscript (IntV i)) st =
      (INR (Error (RuntimeError "ABI subscript bounds")),st)
Proof
  Cases_on `bd` >>
  rw[project_abi_operand_def, check_abi_projection_def, bound_length_def,
     ignore_bind_def, bind_def, check_def, assert_def]
QED

Theorem stage_abi_operands_length:
  ∀args cx st vs rt.
    stage_abi_operands cx args st = (INL vs,rt) ⇒ LENGTH vs = LENGTH args
Proof
  Induct >> rw[stage_abi_operands_def, bind_def, return_def] >>
  gvs[AllCaseEqs()] >> first_x_assum irule >> goal_assum drule
QED

Theorem stage_abi_operands_preserves_state:
  ∀args cx st vs rt.
    stage_abi_operands cx args st = (INL vs,rt) ⇒ rt = st
Proof
  Induct >> rw[stage_abi_operands_def, bind_def, return_def] >>
  gvs[AllCaseEqs()] >>
  rename1 `read_abi_operand cx arg st = _` >>
  Cases_on `arg` >>
  TRY (rename1 `read_abi_operand cx (AbiStorage tr slot tv) st = _` >>
       Cases_on `tr`) >>
  gvs[read_abi_operand_def, read_storage_slot_def, bind_def,
      get_storage_backend_def, get_accounts_def, get_transient_storage_def,
      return_def, lift_option_def, raise_def, option_CASE_rator,
      AllCaseEqs()] >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  first_x_assum drule >> simp[]
QED
