(*
 * Compilation Environment and State Relation
 *
 * TOP-LEVEL:
 *   compile_env      — maps Vyper vars to Venom locations
 *   compile_state    — monad state for code generation
 *   cs_extends       — a compile state only appended to another;
 *                      cs_extends_* for the monad primitives
 *   state_rel        — cross-level simulation relation
 *   result_rel       — maps Vyper exceptions to Venom exec_result
 *   is_word_type     — type fits in single EVM word (calling convention)
 *   is_signed_type   — signed integer or decimal
 *   type_bits        — bit width of integer type
 *   type_bounds      — (lo, hi) word256 bounds for type
 *   struct_field_offset — byte offset of struct field
 *   nsid_to_string   — namespace ID to lookup string
 *   internal_fn_label — Venom label of an internal function (Vyper's spelling)
 *   local_ptrs_rel   — live locals held through pointer variables match memory
 *   compile_state_ok — well-formedness: bound labels disjoint from future fresh labels
 *   label_external   — label not bound and not in future fresh-label co-domain
 *
 * Helper:
 *   fresh_var, fresh_label, emit, new_block — compilation monad ops
 *   fresh_label_output   — canonical shape of compiler-generated labels (@suffix_k)
 *   fresh_vars_wrt       — compiler var counter ahead of existing venom vars
 *   local_region         — a live local's region through its pointer variable
 *   local_backed         — what backs a live local's region in the current frame
 *   not_local_ptr        — a variable is not a live local's pointer
 *   bound_labels         — set of labels bound to blocks in compile state
 *   compiler_labels_future — co-domain of fresh_label for counter values ≥ n
 *)

Theory compileEnv
Ancestors
  valueEncoding venomExecSemantics venomInst venomPolicyTypes
  vyperState vyperContext vyperValue vyperABI contractABI
  byte keccak finite_map pred_set list rich_list
Libs
  monadsyntax

(* ===== Variable Location ===== *)

(* ===== Data Location ===== *)
(* Where a Vyper value lives in the EVM.
   Mirrors Python: vyper/semantics/data_locations.py
   Shared here (not in context) so exprLowering can use it. *)
Datatype:
  data_location =
    LocMemory      (* byte-addressed, word_scale = 32 *)
  | LocStorage     (* slot-addressed, word_scale = 1 *)
  | LocTransient   (* slot-addressed, word_scale = 1 (EIP-1153) *)
  | LocCode        (* immutables: iload/dload *)
  | LocCalldata    (* calldata: calldataload *)
End

(* VyperValue: StackValue | LocatedValue — see contextScript.sml *)

(* Word scale: 1 for slot-addressed (storage/transient), 32 for byte-addressed *)
Definition word_scale_def:
  word_scale LocStorage = 1n ∧
  word_scale LocTransient = 1n ∧
  word_scale LocMemory = 32n ∧
  word_scale LocCode = 32n ∧
  word_scale LocCalldata = 32n
End

(* Is location slot-addressed? *)
Definition is_slot_addressed_def:
  is_slot_addressed LocStorage = T ∧
  is_slot_addressed LocTransient = T ∧
  is_slot_addressed LocMemory = F ∧
  is_slot_addressed LocCode = F ∧
  is_slot_addressed LocCalldata = F
End

(* Load opcode for a location. For LocCode, always DLOAD (runtime).
   Ctor uses ILOAD but must be handled separately. *)
Definition load_opc_for_def:
  load_opc_for LocMemory = MLOAD ∧
  load_opc_for LocStorage = SLOAD ∧
  load_opc_for LocTransient = TLOAD ∧
  load_opc_for LocCode = DLOAD ∧
  load_opc_for LocCalldata = CALLDATALOAD
End

(* Store opcode for a location *)
Definition store_opc_for_def:
  store_opc_for LocMemory = MSTORE ∧
  store_opc_for LocStorage = SSTORE ∧
  store_opc_for LocTransient = TSTORE ∧
  store_opc_for LocCode = ISTORE ∧
  store_opc_for LocCalldata = MSTORE  (* calldata is read-only; shouldn't be used *)
End

(* Where a Vyper variable lives in Venom execution *)
Datatype:
  var_location =
    MemLoc num num         (* alloca offset, size in bytes *)
  | StorageLoc bytes32     (* storage slot *)
  | TransientLoc bytes32   (* transient storage slot *)
  | ImmutableLoc num       (* byte offset in data section *)
  | PtrVar operand num     (* operand is the pointer, num is size in bytes.
                              Used for memory-passed internal function params:
                              PARAM register IS the address, no alloca needed.
                              Mirrors Python: register_variable(name, typ, ptr) *)
End

(* Map var_location to its data_location.
   Mirrors Python: each variable's .location attribute *)
Definition var_location_loc_def:
  var_location_loc (MemLoc _ _) = LocMemory ∧
  var_location_loc (StorageLoc _) = LocStorage ∧
  var_location_loc (TransientLoc _) = LocTransient ∧
  var_location_loc (ImmutableLoc _) = LocCode ∧
  var_location_loc (PtrVar _ _) = LocMemory
End

(* ===== ABI Type Info ===== *)
(* These datatypes are defined here (not in abiEncoder) so compile_env
   can reference them without creating circular dependencies.
   Mirrors Python: abi/abi_encoder.py, abi/abi_decoder.py *)

(* What kind of clamping does a decoded value need? *)
Datatype:
  abi_clamp =
    NoClamp                       (* uint256, int256, bytes32 — full width *)
  | IntClamp num bool             (* bits, signed — sub-256-bit integer *)
  | BytesMClamp num               (* m — bytesM right-padding check *)
  | BoolClamp                     (* must be 0 or 1 *)
End

(* ABI encoding info: describes how to encode a value for ABI output. *)
Datatype:
  abi_enc_info =
    AbiPrimWord
  | AbiBytestring num   (* max_len *)
  | AbiCopy num         (* mem_size: fast path, just copy *)
  | AbiDynArray abi_enc_info num num bool
      (* elem_info, elem_abi_static_size, elem_mem_size, elem_is_dynamic *)
  | AbiComplex ((abi_enc_info # num # num # bool) list)
      (* list of (elem_info, abi_static_size, mem_size, is_dynamic) *)
End

(* ABI decoding info: describes how to decode a value from ABI input. *)
Datatype:
  abi_dec_info =
    DecPrimWord abi_clamp  (* clamp info *)
  | DecBytestring num      (* max_len *)
  | DecDynArray abi_dec_info num num bool num
      (* elem_info, elem_abi_static_size, elem_mem_size, elem_is_dynamic, max_count *)
  | DecComplex bool ((abi_dec_info # num # num) list)
      (* is_dynamic, list of (elem_info, abi_embedded_static_size, mem_size) *)
End

(* ===== Namespace ID ===== *)
(* Convert (module_id option, name) to lookup string.
   Mirrors Python: NamespaceID representation *)
Definition nsid_to_string_def:
  nsid_to_string (NONE, name) = name ∧
  nsid_to_string (SOME (n:num), name) = (toString n) ++ "." ++ name
End

(* ===== Internal Function Labels ===== *)
(* Vyper's str(typ), used only to spell internal function labels.
   Mirrors Python (vyper/semantics/types/): primitives.py (int/uint, bytesM),
   bytestrings.py (Bytes[n]/String[n]), subscriptable.py (SArray, DynArray,
   tuple), user.py (flag, struct). An interface-typed parameter is
   BaseT AddressT here and prints as address, where Python prints the
   interface name; labels never reach the bytecode. *)
Definition vyper_type_str_def:
  vyper_type_str (BaseT (UintT n)) = "uint" ++ toString n ∧
  vyper_type_str (BaseT (IntT n)) = "int" ++ toString n ∧
  vyper_type_str (BaseT BoolT) = "bool" ∧
  vyper_type_str (BaseT DecimalT) = "decimal" ∧
  vyper_type_str (BaseT AddressT) = "address" ∧
  vyper_type_str (BaseT (BytesT (Fixed m))) = "bytes" ++ toString m ∧
  vyper_type_str (BaseT (BytesT (Dynamic n))) =
    "Bytes[" ++ toString n ++ "]" ∧
  vyper_type_str (BaseT (StringT n)) = "String[" ++ toString n ++ "]" ∧
  vyper_type_str (ArrayT t (Fixed n)) =
    vyper_type_str t ++ "[" ++ toString n ++ "]" ∧
  vyper_type_str (ArrayT t (Dynamic n)) =
    "DynArray[" ++ vyper_type_str t ++ ", " ++ toString n ++ "]" ∧
  vyper_type_str (TupleT [t]) = "(" ++ vyper_type_str t ++ ",)" ∧
  vyper_type_str (TupleT ts) = "(" ++ vyper_type_strs ", " ts ++ ")" ∧
  vyper_type_str (StructT id) = SND id ∧
  vyper_type_str (FlagT id) = SND id ∧
  vyper_type_str NoneT = "" ∧
  vyper_type_strs sep [] = "" ∧
  vyper_type_strs sep [t] = vyper_type_str t ∧
  vyper_type_strs sep (t :: ts) =
    vyper_type_str t ++ sep ++ vyper_type_strs sep ts
Termination
  WF_REL_TAC `measure (\x. case x of
                              INL t => type_size t
                            | INR (_, ts) => list_size type_size ts)`
End

(* Venom label of an internal function, from its function id, its lookup
   name (nsid_to_string of its nsid) and declared parameter types,
   defaulted ones included. The space keeps it apart from every source
   identifier, external entry label ("fn_" ++ name), unit entry
   ("__entry"/"__deploy"), codegen label ("revert", "code_end") and fresh
   label ("@..."); the id, a decimal followed by a space, keeps the labels
   of differently numbered functions apart whatever their names.
   Mirrors Python: codegen_venom/module.py _generate_internal_function and
   codegen_venom/expr.py lower_Call (internal calls). *)
Definition internal_fn_label_def:
  internal_fn_label (fn_id : num) (name : string) (arg_tys : type list)
                    (is_ctor : bool) =
    "internal " ++ toString fn_id ++ " " ++ name ++ "(" ++
    vyper_type_strs "," arg_tys ++ ")" ++
    (if is_ctor then "_deploy" else "_runtime")
End

Theorem internal_fn_label_prefix:
  !fn_id name arg_tys is_ctor.
    isPREFIX "internal " (internal_fn_label fn_id name arg_tys is_ctor)
Proof
  simp[internal_fn_label_def]
QED

Theorem toString_no_space[local]:
  !n : num. ~MEM #" " (toString n)
Proof
  gen_tac >> strip_tac >>
  qspec_then `n` mp_tac ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string >>
  REWRITE_TAC [listTheory.EVERY_MEM] >>
  disch_then drule >> EVAL_TAC
QED

Theorem APPEND_sep_11[local]:
  !s1 s2 c r1 r2.
    ~MEM c s1 /\ ~MEM c s2 /\ s1 ++ ([c] ++ r1) = s2 ++ ([c] ++ r2) ==>
    s1 = s2
Proof
  Induct >> Cases_on `s2` >> rw[] >>
  first_x_assum irule >> metis_tac[listTheory.APPEND_ASSOC]
QED

(* Equal labels have equal function ids. *)
Theorem internal_fn_label_id_11:
  !i1 i2 n1 n2 tys1 tys2 c1 c2.
    internal_fn_label i1 n1 tys1 c1 = internal_fn_label i2 n2 tys2 c2 ==>
    i1 = i2
Proof
  rpt gen_tac >>
  REWRITE_TAC [internal_fn_label_def, GSYM listTheory.APPEND_ASSOC,
               listTheory.APPEND_11] >>
  strip_tac >> drule_at Any APPEND_sep_11 >> simp[toString_no_space]
QED

(* Equal labels name the same function, for names without "(" (source
   identifiers and nsid_to_string values). *)
Theorem internal_fn_label_11:
  !i1 i2 n1 n2 tys1 tys2 c1 c2.
    ~MEM #"(" n1 /\ ~MEM #"(" n2 /\
    internal_fn_label i1 n1 tys1 c1 = internal_fn_label i2 n2 tys2 c2 ==>
    n1 = n2
Proof
  rpt gen_tac >> strip_tac >>
  `i1 = i2` by metis_tac[internal_fn_label_id_11] >>
  qpat_x_assum `internal_fn_label _ _ _ _ = _` mp_tac >>
  ASM_REWRITE_TAC [internal_fn_label_def, GSYM listTheory.APPEND_ASSOC,
               listTheory.APPEND_11] >>
  strip_tac >> drule_at Any APPEND_sep_11 >> gs[]
QED

(* Key of a module-level variable (storage, transient, HashMap, immutable) in
   the name-keyed compile_env tables. Arguments and locals use their plain
   names; no Vyper identifier contains ".", so a local can never shadow a
   module variable. Mirrors Python, which keeps module variables behind
   self.<name> (codegen_venom/expr.py lower_Attribute) and locals in
   ctx.variables (codegen_venom/context.py). *)
Definition module_var_key_def:
  module_var_key nsid = "self." ++ nsid_to_string nsid
End

(* ===== ABI Type Properties ===== *)

(* Whether a Vyper type has dynamic ABI encoding (requires tail section).
   sfields: finite struct field map.
   Mirrors Python: VyperType.abi_type.is_dynamic()
   StructT: dynamic iff any field type is dynamic.
   Terminates for acyclic struct definitions (Vyper guarantees no recursive structs). *)
Definition is_abi_dynamic_def:
  is_abi_dynamic sfields (BaseT (BytesT (Dynamic _))) = T ∧
  is_abi_dynamic sfields (BaseT (StringT _)) = T ∧
  is_abi_dynamic sfields (ArrayT _ (Dynamic _)) = T ∧
  is_abi_dynamic sfields (ArrayT elem (Fixed _)) =
    is_abi_dynamic sfields elem ∧
  is_abi_dynamic sfields (TupleT tys) =
    EXISTS (is_abi_dynamic sfields) tys ∧
  is_abi_dynamic sfields (StructT nsid) =
    (let name = nsid_to_string nsid in
     case FLOOKUP sfields name of
       SOME fields =>
         EXISTS (is_abi_dynamic (sfields \\ name))
                (MAP (FST o SND) fields)
     | NONE => F) ∧
  is_abi_dynamic sfields _ = F
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(sfields, ty).
    (CARD (FDOM sfields), type_size ty))`
  \\ rw[finite_mapTheory.FDOM_DOMSUB, pred_setTheory.CARD_DELETE]
  >- (Cases_on `CARD (FDOM sfields)` \\ gvs[])
  \\ gvs[finite_mapTheory.TO_FLOOKUP]
End

(* Type depth: used as termination measure for recursive typed copy. *)
Definition type_depth_def:
  type_depth (BaseT _) = 0n ∧
  type_depth (ArrayT elem _) = 1 + type_depth elem ∧
  type_depth (TupleT tys) = 1 + list_size type_depth tys ∧
  type_depth (StructT _) = 1 ∧
  type_depth (FlagT _) = 0 ∧
  type_depth NoneT = 0
Termination
  WF_REL_TAC `measure type_size`
End

(* ABI static section size (in bytes). For dynamic types this is 0.
   sfields: finite struct field map.
   Mirrors Python: ABIType.static_size()
   StructT: sum of embedded_static_size of each field (same as tuple).
   Terminates for acyclic struct definitions. *)
Definition abi_static_size_def:
  abi_static_size sfields (BaseT (BytesT (Dynamic _))) = 0 ∧
  abi_static_size sfields (BaseT (StringT _)) = 0 ∧
  abi_static_size sfields (BaseT _) = 32 ∧
  abi_static_size sfields (FlagT _) = 32 ∧
  abi_static_size sfields NoneT = 0 ∧
  abi_static_size sfields (ArrayT elem (Fixed n)) =
    n * (if is_abi_dynamic sfields elem then 32
         else abi_static_size sfields elem) ∧
  abi_static_size sfields (ArrayT _ (Dynamic _)) = 0 ∧
  abi_static_size sfields (TupleT tys) =
    SUM (MAP (λt. if is_abi_dynamic sfields t then 32
                  else abi_static_size sfields t) tys) ∧
  abi_static_size sfields (StructT nsid) =
    (let name = nsid_to_string nsid in
     case FLOOKUP sfields name of
       SOME fields =>
         SUM (MAP (λt. if is_abi_dynamic (sfields \\ name) t then 32
                       else abi_static_size (sfields \\ name) t)
                  (MAP (FST o SND) fields))
     | NONE => 0)
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(sfields, ty).
    (CARD (FDOM sfields), type_size ty))`
  \\ rw[finite_mapTheory.FDOM_DOMSUB, pred_setTheory.CARD_DELETE]
  >- (Cases_on `CARD (FDOM sfields)` \\ gvs[])
  \\ gvs[finite_mapTheory.TO_FLOOKUP]
End

(* ABI embedded static size: 32 for dynamic types, static_size otherwise.
   Mirrors Python: ABIType.embedded_static_size() *)
Definition abi_embedded_static_size_def:
  abi_embedded_static_size sfields ty =
    if is_abi_dynamic sfields ty then 32
    else abi_static_size sfields ty
End

(* ABI size bound (static + dynamic sections).
   sfields: finite struct field map.
   Mirrors Python: ABIType.size_bound()
   StructT: same as tuple (sum of field size bounds). *)
Definition abi_size_bound_def:
  abi_size_bound sfields (BaseT (BytesT (Dynamic n))) =
    32 + ((n + 31) DIV 32) * 32 ∧
  abi_size_bound sfields (BaseT (StringT n)) =
    32 + ((n + 31) DIV 32) * 32 ∧
  abi_size_bound sfields (ArrayT elem (Dynamic n)) =
    32 + n * (abi_embedded_static_size sfields elem +
              (if is_abi_dynamic sfields elem
               then abi_size_bound sfields elem
               else 0)) ∧
  abi_size_bound sfields (ArrayT elem (Fixed n)) =
    n * (abi_embedded_static_size sfields elem +
         (if is_abi_dynamic sfields elem
          then abi_size_bound sfields elem
          else 0)) ∧
  abi_size_bound sfields (TupleT tys) =
    SUM (MAP (λt. abi_embedded_static_size sfields t +
                  (if is_abi_dynamic sfields t
                   then abi_size_bound sfields t
                   else 0)) tys) ∧
  abi_size_bound sfields (StructT nsid) =
    (let name = nsid_to_string nsid in
     case FLOOKUP sfields name of
       SOME fields =>
         SUM (MAP (λt. abi_embedded_static_size (sfields \\ name) t +
                       (if is_abi_dynamic (sfields \\ name) t
                        then abi_size_bound (sfields \\ name) t
                        else 0))
                  (MAP (FST o SND) fields))
     | NONE => 0) ∧
  abi_size_bound sfields ty = abi_static_size sfields ty
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(sfields, ty).
    (CARD (FDOM sfields), type_size ty))`
  \\ rw[finite_mapTheory.FDOM_DOMSUB, pred_setTheory.CARD_DELETE]
  >- (Cases_on `CARD (FDOM sfields)` \\ gvs[])
  \\ gvs[finite_mapTheory.TO_FLOOKUP]
End

(* ===== Compilation Environment ===== *)

(* Static info about the compilation target *)
Datatype:
  compile_env = <|
    (* Resolved target capabilities used by target-sensitive raw lowering. *)
    ce_target : target_capabilities;
    ce_vars : (string, var_location) fmap;
    ce_storage_layout : (string, bytes32) fmap;
    ce_module : num option;
    (* Struct metadata: struct_name → list of (field_name, member_type, memory_bytes) *)
    ce_struct_fields : (string, (string # type # num) list) fmap;
    (* DynArray metadata: target_name → max capacity *)
    ce_dynarray_capacity : string -> num;
    (* Method ID lookup: func_name → 4-byte keccak selector as num *)
    ce_method_id : string -> type list -> num;
    (* Flag member index: (flag_type_name, member_name) → positional index *)
    ce_flag_member_id : string -> string -> num;
    (* Number of members in a flag type *)
    ce_flag_n_members : string -> num;
    (* Variable type lookup: var_name → type (for Attribute dispatch) *)
    ce_var_type : string -> type option;
    (* HashMap detection: var_name → T if variable is a HashMap (mapping).
       Needed because HashMapT is a value_type, not type, so ce_var_type
       cannot represent it. Used by compile_subscript for dispatch.
       Mirrors Python: isinstance(base_typ, HashMapT) *)
    ce_is_hashmap : string -> bool;
    (* Event metadata: event_nsid → SOME (event_hash, arg_types, indexed_flags).
       NONE means the event is not declared in this compilation unit. Keeping
       absence explicit prevents unknown events from silently compiling/logging
       as hash-0/no-arg events. *)
    ce_event_info : string -> (num # type list # bool list) option;
    (* Type environment used by ABI conversion for structs/flags/interfaces. *)
    ce_type_env : (nsid, type_args) fmap;
    (* Internal return: how many return values passed on stack (0 = memory return).
       Set from func_t.returns_stack_count() at function entry. *)
    ce_returns_count : num;
    (* Internal functions only: where the caller's return buffer pointer is
       (memory returns, returns_count = 0). NONE for external functions and
       stack returns. Kept out of ce_vars so user names cannot collide with it.
       Mirrors Python: FunctionContext.return_buffer *)
    ce_return_buf : var_location option;
    (* Where the return PC is; NONE for external functions. `Return` decides
       "internal or external?" from this field.
       Mirrors Python: FunctionContext.return_pc, tested by lower_Return as
       `ctx.return_pc is not None` *)
    ce_return_pc : var_location option;
    (* External function: T for external functions, F for internal *)
    ce_is_external : bool;
    (* ABI encoding info for external return type.
       Populated from func_t.return_type at function entry.
       Mirrors Python: calculate_type_for_external_return + abi_type *)
    ce_ret_enc_info : abi_enc_info;
    (* ABI decoding info for external call return type.
       Used to decode returndata into Vyper memory layout.
       Mirrors Python: abi_decode_to_buf(ctx, result_val.operand, src, hi=hi) *)
    ce_ret_dec_info : abi_dec_info;
    (* Max ABI-encoded return size in bytes (for ALLOCA sizing).
       Mirrors Python: external_return_type.abi_type.size_bound() *)
    ce_max_return_size : num;
    (* Constructor context: T during __init__ (deploy), F at runtime.
       Affects immutable access: ctor uses ILOAD, runtime uses DLOAD. *)
    ce_is_ctor : bool;
    (* Internal function calling convention info:
       func_label → (returns_count, return_buf_size, pass_via_stack : bool list)
       pass_via_stack: per-arg T=stack, F=memory. Order matches func_t.arguments.
       Mirrors Python: calling_convention.py pass_via_stack + returns_stack_count *)
    ce_func_info : string -> (num # num # bool list);
    (* Internal function declared parameter types, defaulted ones included:
       func_name → arg types. Spells the INVOKE target (internal_fn_label).
       Mirrors Python: func_t.arguments in expr.py lower_Call *)
    ce_func_param_types : string -> type list;
    (* Internal function ids: func_name → id. Spells the INVOKE target
       (internal_fn_label).
       Mirrors Python: func_t._function_id in expr.py lower_Call *)
    ce_func_ids : string -> num;
    (* Nonreentrant lock info for explicit return statements:
       (is_nonreentrant, nkey, use_transient, is_view).
       Python: stmt.py _lower_external_return calls emit_nonreentrant_unlock.
       is_nonreentrant is the boolean flag — nkey CAN be 0 for the first lock slot. *)
    ce_nonreentrant : (bool # num # bool # bool);
    (* Raw return: T for @raw_return decorated functions (proxy patterns).
       Bypasses ABI encoding, returns bytes directly.
       Mirrors Python: func_t.do_raw_return *)
    ce_raw_return : bool;
    (* T when each local and loop variable gets a fresh ALLOCA at its
       declaration (external and fallback bodies); F when it keeps the MemLoc
       slot build_compile_env reserved for its name (internal functions and
       the constructor body).
       Mirrors Python: Context.new_variable -> allocate_buffer -> alloca *)
    ce_alloca_locals : bool
  |>
End

(* Lookup struct fields, defaulting to [] for unknown structs *)
Definition get_struct_fields_def:
  get_struct_fields (sfields : (string, (string # type # num) list) fmap) name =
    case FLOOKUP sfields name of
      SOME fields => fields
    | NONE => []
End

(* ===== Compilation State (monad state) ===== *)

(* Mutable state during code generation *)
Datatype:
  compile_state = <|
    cs_next_var : num;
    cs_next_label : num;
    cs_next_id : num;
    cs_current_bb : string;
    cs_current_insts : instruction list;   (* emission order *)
    cs_blocks : basic_block list;          (* completed blocks, newest first *)
    cs_data_sections : data_section list    (* reversed; data segment for codegen *)
  |>
End

(* ===== Compilation Monad ===== *)

(* Simple state monad: α compiler = compile_state → (α × compile_state) *)
Type compiler = ``:compile_state -> 'a # compile_state``

Definition comp_return_def:
  comp_return (x:'a) (cs:compile_state) = (x, cs)
End

Definition comp_bind_def:
  comp_bind (m:'a compiler) (f:'a -> 'b compiler) (cs:compile_state) =
    let (a, cs') = m cs in f a cs'
End

Definition comp_ignore_bind_def:
  comp_ignore_bind (m:'a compiler) (f:'b compiler) =
    comp_bind m (λ_. f)
End

(* Read the current compile state *)
Definition comp_get_def:
  comp_get (cs:compile_state) = (cs, cs)
End

(* Modify the compile state *)
Definition comp_set_def:
  comp_set (cs':compile_state) (_:compile_state) = ((), cs')
End


Theorem comp_bind_assoc:
  comp_bind (comp_bind m f) g =
  comp_bind m (\x. comp_bind (f x) g)
Proof
  rw[FUN_EQ_THM]
  >> Cases_on `m x`
  >> simp[comp_bind_def]
QED
(* Congruence rule for comp_bind — needed for recursive definitions using the monad *)
Theorem comp_bind_cong[defncong]:
  ∀m1 m2 f1 f2.
    (m1 = m2) ∧ (∀x. f1 x = f2 x) ⇒
    comp_bind m1 f1 = comp_bind m2 f2
Proof
  rw[comp_bind_def, FUN_EQ_THM, pairTheory.FORALL_PROD]
  >> rw[]
QED

Theorem comp_ignore_bind_cong[defncong]:
  ∀m1 m2 f1 f2.
    (m1 = m2) ∧ (f1 = f2) ⇒
    comp_ignore_bind m1 f1 = comp_ignore_bind m2 f2
Proof
  rw[]
QED

val () = declare_monad ("compilation",
  { bind = ``comp_bind``, unit = ``comp_return``,
    ignorebind = SOME ``comp_ignore_bind``, choice = NONE,
    fail = NONE, guard = NONE
  });
val () = enable_monad "compilation";
val () = enable_monadsyntax ();

(* Fresh SSA variable name *)
Definition fresh_var_def:
  fresh_var (cs:compile_state) =
    let n = cs.cs_next_var in
    ("%" ++ (toString n),
     cs with cs_next_var := n + 1)
End

(* Canonical shape of a compiler-generated label: @<suffix>_<counter>.
   Factored out so proofs can talk about the label shape abstractly
   (set membership) rather than decomposing strings. *)
Definition fresh_label_output_def:
  fresh_label_output suffix (k:num) =
    "@" ++ suffix ++ "_" ++ (toString k)
End

(* Fresh label *)
Definition fresh_label_def:
  fresh_label suffix (cs:compile_state) =
    let n = cs.cs_next_label in
    (fresh_label_output suffix n,
     cs with cs_next_label := n + 1)
End

(* Fresh instruction ID *)
Definition fresh_id_def:
  fresh_id (cs:compile_state) =
    let n = cs.cs_next_id in
    (n, cs with cs_next_id := n + 1)
End

(* Emit instruction to current block (appended in order) *)
Definition emit_def:
  emit (inst:instruction) (cs:compile_state) =
    ((), cs with cs_current_insts := cs.cs_current_insts ++ [inst])
End

(* Finalize current block and start a new one *)
Definition new_block_def:
  new_block (label:string) (cs:compile_state) =
    let old_bb = <| bb_label := cs.cs_current_bb;
                    bb_instructions := cs.cs_current_insts |> in
    (cs.cs_current_bb,
     cs with <| cs_blocks := old_bb :: cs.cs_blocks;
                cs_current_bb := label;
                cs_current_insts := [] |>)
End

(* Check if the current block's last instruction is a terminator.
   Mirrors Python: builder.is_terminated() — used to avoid double terminators. *)
Definition block_is_terminated_def:
  block_is_terminated (cs:compile_state) =
    case cs.cs_current_insts of
      [] => F
    | insts => is_terminator (LAST insts).inst_opcode
End

(* Start a new data section with the given label.
   Mirrors Python: ctx.append_data_section(IRLabel(name)). *)
Definition emit_data_section_def:
  emit_data_section (label:string) (cs:compile_state) =
    ((), cs with cs_data_sections :=
      <| ds_label := label; ds_items := [] |> :: cs.cs_data_sections)
End

(* Append a data item to the most recent data section.
   Mirrors Python: ctx.append_data_item(...). *)
Definition emit_data_item_def:
  emit_data_item (item:data_item) (cs:compile_state) =
    case cs.cs_data_sections of
      [] => ((), cs)  (* no section open — silently ignore *)
    | sec :: rest =>
        ((), cs with cs_data_sections :=
          (sec with ds_items := sec.ds_items ++ [item]) :: rest)
End

(* ===== The compile monad only appends ===== *)

(* st' only appended to st: new finished blocks go in front (cs_blocks is
   newest first), the oldest of them is st's current block, and the current
   instructions only grow. *)
Definition cs_extends_def:
  cs_extends (st : compile_state) (st' : compile_state) <=>
    ?new. st'.cs_blocks = new ++ st.cs_blocks /\
      if new = [] then
        st'.cs_current_bb = st.cs_current_bb /\
        isPREFIX st.cs_current_insts st'.cs_current_insts
      else
        (LAST new).bb_label = st.cs_current_bb /\
        isPREFIX st.cs_current_insts (LAST new).bb_instructions
End

Theorem cs_extends_refl:
  !st. cs_extends st st
Proof
  rw[cs_extends_def] >> qexists_tac `[]` >> simp[]
QED

Theorem cs_extends_trans:
  !st1 st2 st3. cs_extends st1 st2 /\ cs_extends st2 st3 ==> cs_extends st1 st3
Proof
  rw[cs_extends_def] >> qexists_tac `new' ++ new` >> simp[] >>
  Cases_on `new = []` >> Cases_on `new' = []` >> gvs[LAST_APPEND_NOT_NIL] >>
  metis_tac[isPREFIX_TRANS]
QED

Theorem cs_extends_same_block:
  !st st'.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts ==>
    cs_extends st st'
Proof
  rw[cs_extends_def] >> qexists_tac `[]` >> simp[]
QED

Theorem cs_extends_emit:
  !inst st x st'. emit inst st = (x, st') ==> cs_extends st st'
Proof
  rw[emit_def] >> irule cs_extends_same_block >> simp[]
QED

Theorem cs_extends_new_block:
  !lbl st x st'. new_block lbl st = (x, st') ==> cs_extends st st'
Proof
  rw[new_block_def, cs_extends_def] >>
  qexists_tac `[<| bb_label := st.cs_current_bb;
                   bb_instructions := st.cs_current_insts |>]` >>
  simp[]
QED

Theorem cs_extends_fresh_var:
  !st x st'. fresh_var st = (x, st') ==> cs_extends st st'
Proof
  rw[fresh_var_def] >> irule cs_extends_same_block >> simp[]
QED

Theorem cs_extends_fresh_label:
  !sfx st x st'. fresh_label sfx st = (x, st') ==> cs_extends st st'
Proof
  rw[fresh_label_def] >> irule cs_extends_same_block >> simp[]
QED

Theorem cs_extends_fresh_id:
  !st x st'. fresh_id st = (x, st') ==> cs_extends st st'
Proof
  rw[fresh_id_def] >> irule cs_extends_same_block >> simp[]
QED

(* ===== State Relation ===== *)

(* ===== Well-Formedness ===== *)

(* Non-overlapping memory regions *)
Definition regions_disjoint_def:
  regions_disjoint o1 s1 o2 s2 ⇔ (o1 + s1 ≤ o2 ∨ o2 + s2 ≤ o1)
End

(* Well-formed compilation environment: memory allocations don't overlap,
   and all offsets are within reasonable bounds.
   Prerequisite for ANY correctness proof about variable access — without this,
   writing one variable could corrupt another. *)
(* Struct field map (sfields) agrees with type environment (tenv).
   Both are built from the same toplevel declarations:
   sfields = make_struct_fields_map tops, tenv = type_env tops.
   This ensures type_to_abi_enc_info and vyper_to_abi_type/evaluate_type
   see the same struct definitions. *)
Definition sfields_tenv_consistent_def:
  sfields_tenv_consistent sfields tenv ⇔
    (* Every struct in tenv exists in sfields with matching field types *)
    (∀ nsid args.
       FLOOKUP tenv nsid = SOME (StructArgs args) ⇒
       ∃ fields.
         FLOOKUP sfields (nsid_to_string nsid) = SOME fields ∧
         MAP FST fields = MAP FST args ∧
         MAP (FST o SND) fields = MAP SND args) ∧
    (* Every struct in sfields exists in tenv *)
    (∀ name fields.
       FLOOKUP sfields name = SOME fields ⇒
       ∃ nsid args.
         name = nsid_to_string nsid ∧
         FLOOKUP tenv nsid = SOME (StructArgs args) ∧
         MAP FST fields = MAP FST args ∧
         MAP (FST o SND) fields = MAP SND args)
End

(* Compiler's fresh variable counter is ahead of all %-named vars in the
   venom state. Ensures emit_op/emit_void produce names that don't alias
   any existing operand. *)
Definition fresh_vars_wrt_def:
  fresh_vars_wrt (st:compile_state) (ss:venom_state) ⇔
    ∀ n. n ≥ st.cs_next_var ⇒
      STRING #"%" (toString n) ∉ FDOM ss.vs_vars
End

(* x is no compiler variable fresh at st, so the code compiled from st on
   never assigns it. *)
Definition not_fresh_at_def:
  not_fresh_at (st:compile_state) x ⇔
    ∀n. st.cs_next_var ≤ n ⇒ x ≠ STRING #"%" (toString n)
End

(* ===== Label-Space Invariants =====
   Track which labels the compiler has allocated (via fresh_label) and
   which labels are currently bound to blocks. Used by module-level
   correctness to rule out collisions between caller-supplied "external"
   labels and compiler-generated labels.

   All predicates are set-valued and phrased in terms of the abstract
   fresh_label_output co-domain; proofs need not do string decomposition. *)

(* Set of labels bound to blocks in the compile state: the current block
   plus all finalized blocks. *)
Definition bound_labels_def:
  bound_labels (st:compile_state) =
    st.cs_current_bb INSERT set (MAP (λbb. bb.bb_label) st.cs_blocks)
End

(* Co-domain of fresh_label for counter values ≥ n. These are the labels
   fresh_label will produce from a state with cs_next_label = n. *)
Definition compiler_labels_future_def:
  compiler_labels_future (n:num) =
    { fresh_label_output s k | s,k | n ≤ k }
End

(* lbl is external to st: not already bound, and not in the future
   fresh_label co-domain starting from st. A caller-supplied label that
   was allocated by a prior fresh_label call (counter < cs_next_label)
   satisfies this. *)
Definition label_external_def:
  label_external (st:compile_state) lbl ⇔
    lbl ∉ bound_labels st ∧
    lbl ∉ compiler_labels_future st.cs_next_label
End

(* Well-formedness invariant on compile_state:
   - Bound block labels are disjoint from the future fresh_label co-domain
     (i.e., every bound label was either caller-supplied before any
     fresh_label allocation, or allocated by a prior fresh_label call).
   - Block labels are pairwise distinct. *)
Definition compile_state_ok_def:
  compile_state_ok (st:compile_state) ⇔
    DISJOINT (bound_labels st) (compiler_labels_future st.cs_next_label) ∧
    ALL_DISTINCT (st.cs_current_bb :: MAP (λbb. bb.bb_label) st.cs_blocks)
End

Definition well_formed_cenv_def:
  well_formed_cenv cenv ⇔
    (* MemLoc regions don't overlap *)
    (∀ n1 n2 o1 s1 o2 s2.
       n1 ≠ n2 ∧
       FLOOKUP cenv.ce_vars n1 = SOME (MemLoc o1 s1) ∧
       FLOOKUP cenv.ce_vars n2 = SOME (MemLoc o2 s2)
       ⇒ regions_disjoint o1 s1 o2 s2) ∧
    (* All sizes are positive multiples of 32 (word-aligned) *)
    (∀ n off sz.
       FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz) ⇒ sz > 0 ∧ (sz MOD 32 = 0))
End

(* ===== Locals held through allocations ===== *)
(* After its declaration in an external or fallback body a local is
   PtrVar (Var p) sz: the ALLOCA emitted at its declaration binds p to the base
   of a fresh region (emit_local_alloca, compile_alloc_buffer), so the address
   depends on vs_allocas and vs_alloca_next at run time, not on a fixed offset.
   Parameters of internal functions are PtrVar (Var p) sz too
   (materialize_internal_params): a stack-passed one is copied into an ALLOCA
   of the callee, a memory-passed one is the PARAM output p pointing into the
   caller's buffer, with no ALLOCA. *)

(* name is a live local held in the region [base, base + sz): it is in scope,
   and its pointer variable holds base. *)
Definition local_region_def:
  local_region cenv scopes (ss:venom_state) name base sz ⇔
    ∃entry p w.
      lookup_scopes name scopes = SOME entry ∧
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ∧
      lookup_var p ss = SOME w ∧ base = w2n w
End

(* x is not the pointer variable of a live local, so assigning it leaves the
   locals in place. *)
Definition not_local_ptr_def:
  not_local_ptr cenv scopes x ⇔
    ∀name entry sz.
      lookup_scopes name scopes = SOME entry ⇒
      FLOOKUP cenv.ce_vars name ≠ SOME (PtrVar (Var x) sz)
End

(* The locals of cenv are held through pointer variables that were handed out
   before st (declare_local, compile_register_positional_args), one per
   local:
   - no variable sits at a fixed MemLoc offset: state_rel does not relate
     those (the locals of internal bodies and of the constructor, and
     default arguments, which compile_register_kwarg_vars keeps at MemLoc),
     and a store to one could hit a live local's region;
   - no compiler variable fresh at st is a local's pointer, so a temporary of
     the code compiled from st on never overwrites one;
   - distinct locals have distinct pointers, so declaring a local leaves the
     others' pointers alone. *)
Definition local_ptrs_reserved_def:
  local_ptrs_reserved cenv (st:compile_state) ⇔
    (∀name off sz. FLOOKUP cenv.ce_vars name ≠ SOME (MemLoc off sz)) ∧
    ∀n1 n2 p sz1 sz2.
      FLOOKUP cenv.ce_vars n1 = SOME (PtrVar (Var p) sz1) ⇒
      not_fresh_at st p ∧
      (FLOOKUP cenv.ce_vars n2 = SOME (PtrVar (Var p) sz2) ⇒ n1 = n2)
End

(* What backs a live local's region [base, base + sz) in the current frame
   of func, the function running, when its pointer variable is p:
   - the allocation recorded for an ALLOCA of func whose output is p (a
     declared local or a stack-passed parameter; re-running that ALLOCA
     returns the same base).  Naming the instruction lets a consumer tell
     the local's allocation from any other ALLOCA's by instruction id
     (fn_inst_ids_distinct, alloca_inv), or
   - a buffer disjoint from every allocation of the frame (a memory-passed
     parameter: the caller's buffer, below the frontier at the call, while
     setup_callee starts the callee with vs_allocas = FEMPTY and every
     allocation of the callee is fresh, at or above that frontier). *)
Definition local_backed_def:
  local_backed (func:ir_function) p (ss:venom_state) base sz ⇔
    (∃inst.
       MEM inst (fn_insts func) ∧ inst.inst_opcode = ALLOCA ∧
       inst.inst_outputs = [p] ∧
       FLOOKUP ss.vs_allocas inst.inst_id = SOME (base, sz)) ∨
    (∀aid b sz'.
       FLOOKUP ss.vs_allocas aid = SOME (b, sz') ⇒
       regions_disjoint base sz b sz')
End

(* Live locals held through pointer variables match Venom memory.
   For each local in scope whose entry is PtrVar (Var p) sz:
   - p holds the base of a region of size sz, backed in func's frame as
     local_backed says;
   - the region lies below vs_alloca_next, so a fresh ALLOCA cannot overlap
     it;
   - the value fits the region and is well formed (val_wf), which is what
     lets a write outside the region leave it unchanged;
   - val_in_memory holds at the base.
   And the regions of distinct live locals are disjoint, so writing one
   local leaves the others unchanged.
   Bump allocation alone gives this for ALLOCA, so it does not depend on the
   frame layout of internal calls (#545).  It says nothing about vs_fmp:
   DALLOCA buffers and DRET's packing bump vs_fmp independently of
   vs_alloca_next, so keeping them off the live locals is left to the
   consumer (see local_ptrs_rel_above_frontier). *)
Definition local_ptrs_rel_def:
  local_ptrs_rel func cenv scopes (ss:venom_state) ⇔
    (∀name entry p sz.
       lookup_scopes name scopes = SOME entry ∧
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ⇒
       ∃w.
         lookup_var p ss = SOME w ∧
         local_backed func p ss (w2n w) sz ∧
         w2n w + sz ≤ ss.vs_alloca_next ∧
         type_memory_size entry.type ≤ sz ∧
         val_wf entry.type entry.value ∧
         val_in_memory entry.type entry.value (w2n w) ss.vs_memory) ∧
    (∀n1 n2 b1 sz1 b2 sz2.
       n1 ≠ n2 ∧
       local_region cenv scopes ss n1 b1 sz1 ∧
       local_region cenv scopes ss n2 b2 sz2 ⇒
       regions_disjoint b1 sz1 b2 sz2)
End

(* Storage is identical between Vyper accounts and Venom state *)
Definition storage_rel_def:
  storage_rel (addr:address) vs ss =
    let acct = lookup_account addr vs.accounts in
    acct.storage = contract_storage ss
End

(* Transient storage is identical between interpreter and Venom state.
   Interpreter: st.tStorage (transient_storage = address -> storage).
   Venom: ss.vs_transient (same type).
   Mirrors EIP-1153: per-address, per-transaction. *)
Definition transient_rel_def:
  transient_rel (addr:address) vs ss ⇔
    (vs.tStorage addr = contract_transient ss)
End

(* ===== Immutables Relation ===== *)
(* Interpreter immutables ↔ Venom code/data section.
   During constructor: interpreter writes to st.immutables, Venom uses ISTORE/ILOAD.
   At runtime: interpreter reads from st.immutables, Venom uses DLOAD from data section.
   The relation ties each interpreter name to its Venom representation.

   Interpreter: st.immutables : (address, module_immutables) alist
     where module_immutables = (num option, string |-> (type_value # value)) alist
     Keyed by (source_id_opt, immutable_name) → typed value.
   Venom (ctor): ss.vs_immutables : (num, bytes32) fmap  (ILOAD/ISTORE slot → word)
   Venom (runtime): ss.vs_data_section : byte list  (DLOAD offset → 32 bytes)

   ce_vars maps module_var_key (src_id_opt, name) to ImmutableLoc byte_offset.
   The interpreter stores by name (string); Venom stores by byte offset. *)
Definition immutables_rel_def:
  immutables_rel cenv (addr:address) src_id_opt is_ctor vs ss ⇔
    let interp_imms = (case ALOOKUP vs.immutables addr of
                         NONE => FEMPTY
                       | SOME mod_imms => get_source_immutables src_id_opt mod_imms) in
    if is_ctor then
      (* Constructor: each interpreter immutable maps to vs_immutables entry *)
      ∀ name tv v byte_offset.
        FLOOKUP cenv.ce_vars (module_var_key (src_id_opt, name)) =
          SOME (ImmutableLoc byte_offset) ∧
        FLOOKUP interp_imms name = SOME (tv, v)
        ⇒
        (* tv from scope provides correct type for typed_val_to_w256 *)
        FLOOKUP ss.vs_immutables (byte_offset DIV 32) = SOME (typed_val_to_w256 tv v)
    else
      (* Runtime: interpreter immutables encoded in data section *)
      ∀ name tv v byte_offset.
        FLOOKUP cenv.ce_vars (module_var_key (src_id_opt, name)) =
          SOME (ImmutableLoc byte_offset) ∧
        FLOOKUP interp_imms name = SOME (tv, v)
        ⇒
        (* DLOAD reads 32 bytes from data section at byte_offset *)
        byte_offset + 32 ≤ LENGTH ss.vs_data_section ∧
        word_of_bytes T 0w (TAKE 32 (DROP byte_offset ss.vs_data_section)) =
          typed_val_to_w256 tv v
End

(* ===== Storage Variables Relation ===== *)
(* Per-variable mapping between interpreter layout slots and cenv StorageLoc.
   The interpreter uses lookup_var_slot_from_layout to get a slot number,
   then read_storage_slot/write_storage_slot to access it.
   The lowering uses FLOOKUP ce_vars (module_var_key nsid), with the
   reference's own nsid, → StorageLoc slot → SLOAD/SSTORE.
   This relation ensures both reference the same storage slot, both ways:
   - every StorageLoc entry of the current module has the layout's slot;
   - every storage variable or hashmap the source reads through
     lookup_global, in any module, has an entry with that slot, as Python
     takes each reference's slot from its varinfo
     (vyper/codegen_venom/expr.py lower_Attribute).  build_compile_env has
     entries for the main module only, so this direction holds only when
     no other module has a variable with a layout slot, as when
     source_deployment_rel limits the sources to [(NONE, tops)].

   cx.layouts : (address, (layout # layout)) alist
     where layout = ((num option # string), bytes32) alist
     Maps (source_id_opt, var_name) → slot.
   cenv.ce_vars : (string, var_location) fmap
     Maps module_var_key (ce_module, var_name) → StorageLoc slot.
   cenv.ce_storage_layout : (string, bytes32) fmap
     Maps var_name → slot (redundant with ce_vars for StorageLoc). *)

(* Whether a declaration found by find_var_decl_by_name is transient. *)
Definition var_decl_transient_def:
  var_decl_transient (StorageVarDecl is_transient _) = is_transient ∧
  var_decl_transient (HashMapVarDecl is_transient _ _) = is_transient
End

Definition storage_vars_rel_def:
  storage_vars_rel cenv (cx:evaluation_context) ⇔
    (∀ name (slot:bytes32).
       FLOOKUP cenv.ce_vars (module_var_key (cenv.ce_module, name)) =
         SOME (StorageLoc slot) ⇒
       (* Interpreter layout maps (src_id_opt, name) → slot_num : num.
          Compile env stores slot as bytes32. Relation: n2w slot_num = slot. *)
       ∃ slot_num. lookup_var_slot_from_layout cx F cenv.ce_module name = SOME slot_num ∧
                   n2w slot_num = slot) ∧
    (∀ src ts name d id slot_num.
       get_module_code cx src = SOME ts ∧
       find_var_decl_by_name name ts = SOME (d, id) ∧
       ¬var_decl_transient d ∧
       lookup_var_slot_from_layout cx F src id = SOME slot_num ⇒
       FLOOKUP cenv.ce_vars (module_var_key (src, name)) =
         SOME (StorageLoc (n2w slot_num)))
End

(* Transient storage variables: same as storage_vars_rel but for transient. *)
Definition transient_vars_rel_def:
  transient_vars_rel cenv (cx:evaluation_context) ⇔
    (∀ name (slot:bytes32).
       FLOOKUP cenv.ce_vars (module_var_key (cenv.ce_module, name)) =
         SOME (TransientLoc slot) ⇒
       ∃ slot_num. lookup_var_slot_from_layout cx T cenv.ce_module name = SOME slot_num ∧
                   n2w slot_num = slot) ∧
    (∀ src ts name d id slot_num.
       get_module_code cx src = SOME ts ∧
       find_var_decl_by_name name ts = SOME (d, id) ∧
       var_decl_transient d ∧
       lookup_var_slot_from_layout cx T src id = SOME slot_num ⇒
       FLOOKUP cenv.ce_vars (module_var_key (src, name)) =
         SOME (TransientLoc (n2w slot_num)))
End

(* Check if a type is a bytestring (dynamic Bytes or String).
   Used by log topics and bytestring-specific copy. *)
Definition is_bytestring_type_def:
  is_bytestring_type (BaseT (BytesT (Dynamic _))) = T ∧
  is_bytestring_type (BaseT (StringT _)) = T ∧
  is_bytestring_type _ = F
End

(* ===== Log Equivalence ===== *)
(* Both the source interpreter and Venom state carry concrete EVM events:
   <| logger; topics : bytes32 list; data : byte list |>.
   Event declarations are encoded by the source semantics when Log executes,
   using the same signature hash, indexed-topic encoding, and ABI data encoding
   as compile_stmt. Consequently the authoritative state relation below is
   concrete event equality. The extraction helpers in this section characterize
   the shared encoder and remain useful to lowering compatibility proofs. *)
(* Extract indexed values from args based on flags *)
Definition indexed_values_def:
  indexed_values [] [] = ([] : value list) ∧
  indexed_values (T :: flags) (v :: vals) = v :: indexed_values flags vals ∧
  indexed_values (F :: flags) (_ :: vals) = indexed_values flags vals ∧
  indexed_values _ _ = []
End

Definition indexed_topic_flags_def:
  indexed_topic_flags [] [] = ([] : bool list) ∧
  indexed_topic_flags (T :: flags) (b :: bs) =
    b :: indexed_topic_flags flags bs ∧
  indexed_topic_flags (F :: flags) (_ :: bs) =
    indexed_topic_flags flags bs ∧
  indexed_topic_flags _ _ = []
End

Definition log_bytestring_topic_def:
  log_bytestring_topic (BytesV bs) =
    SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) ∧
  log_bytestring_topic (StringV s) =
    SOME (word_of_bytes T (0w:bytes32)
            (Keccak_256_w64 (MAP (n2w o ORD) s))) ∧
  log_bytestring_topic _ = NONE
End

Definition log_topic_equiv_def:
  log_topic_equiv T v topic = (log_bytestring_topic v = SOME topic) ∧
  log_topic_equiv F v topic = (topic = val_to_w256 v)
End

Definition log_indexed_topics_equiv_def:
  log_indexed_topics_equiv [] [] [] = T ∧
  log_indexed_topics_equiv (is_bytestring :: bs) (v :: vals) (topic :: topics) =
    (log_topic_equiv is_bytestring v topic ∧
     log_indexed_topics_equiv bs vals topics) ∧
  log_indexed_topics_equiv _ _ _ = F
End

Definition log_non_indexed_values_def:
  log_non_indexed_values [] [] = ([] : value list) ∧
  log_non_indexed_values (T :: flags) (_ :: vals) =
    log_non_indexed_values flags vals ∧
  log_non_indexed_values (F :: flags) (v :: vals) =
    v :: log_non_indexed_values flags vals ∧
  log_non_indexed_values _ _ = []
End

Definition log_non_indexed_types_def:
  log_non_indexed_types [] [] = ([] : type list) ∧
  log_non_indexed_types (T :: flags) (_ :: tys) =
    log_non_indexed_types flags tys ∧
  log_non_indexed_types (F :: flags) (ty :: tys) =
    ty :: log_non_indexed_types flags tys ∧
  log_non_indexed_types _ _ = []
End

Definition log_entry_equiv_def:
  log_entry_equiv _ _ (source_event : log) (ev : event) ⇔ source_event = ev
End

(* Logs relation: pairwise equivalence *)
Definition logs_rel_def:
  logs_rel cenv (addr:address) vs ss ⇔
    LENGTH vs.logs = LENGTH ss.vs_logs ∧
    EVERY2 (log_entry_equiv cenv addr) vs.logs ss.vs_logs
End

(* Call context matches *)
Definition call_ctx_rel_def:
  call_ctx_rel (txn:call_txn) (cc:call_context) (tc:tx_context) (bc:block_context) =
    (cc.cc_caller = txn.sender ∧
     cc.cc_address = txn.target ∧
     cc.cc_callvalue = n2w txn.value ∧
     cc.cc_calldata = txn.calldata ∧
     tc.tc_origin = txn.origin ∧
     tc.tc_gasprice = n2w txn.gas_price ∧
     tc.tc_chainid = n2w txn.chain_id ∧
     bc.bc_coinbase = txn.coinbase ∧
     bc.bc_timestamp = n2w txn.time_stamp ∧
     bc.bc_number = n2w txn.block_number ∧
     bc.bc_prevrandao = n2w txn.prev_randao ∧
     bc.bc_gaslimit = n2w txn.gas_limit ∧
     bc.bc_basefee = n2w txn.base_fee ∧
     bc.bc_blobbasefee = n2w txn.blob_base_fee)
End

(* Top-level oracle-mode source/Venom state relation for the statement and
   expression simulation, in func, the function running.  It ties together
   the sub-relations below and exactly the current oracle suffix and request
   prefix; NONE-mode compatibility does not satisfy it.
   - local_ptrs_rel: locals in scope, held in memory through their pointer
     variables (PtrVar).  MemLoc locals at fixed offsets, which the internal
     function bodies still use until #545, are not related.
   - storage_rel, storage_vars_rel: storage, and the slots of storage
     variables.
   - transient_rel, transient_vars_rel: transient storage, and the slots of
     transient variables.
   - immutables_rel: immutables (vs_immutables in a constructor, the data
     section at runtime).
   - logs_rel: emitted logs.
   - call_ctx_rel: transaction, call and block context.
   - outcomes and requests: the oracle outcomes still to consume and the
     requests recorded so far, as in the result relation. *)
Definition state_rel_def:
  state_rel func cenv cx vs ss =
    (local_ptrs_rel func cenv vs.scopes ss ∧
     storage_rel cx.txn.target vs ss ∧
     storage_vars_rel cenv cx ∧
     transient_rel cx.txn.target vs ss ∧
     transient_vars_rel cenv cx ∧
     immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor vs ss ∧
     logs_rel cenv cx.txn.target vs ss ∧
     call_ctx_rel cx.txn ss.vs_call_ctx ss.vs_tx_ctx ss.vs_block_ctx ∧
     vs.outcomes = SOME ss.vs_outcomes ∧
     vs.requests = ss.vs_requests)
End

(* ===== Result Relation ===== *)

(* Maps Vyper evaluation results to Venom exec_result.
   ret_tv: type_value for the return type — used by typed_val_to_w256
   for correct BytesV encoding (AddressT → PAD_LEFT, BytesT → PAD_RIGHT).

   Internal returns: IntRet vals, with vals matching the value as
   intret_vals_match (below) says.  A memory return has vals = []; its
   value is in the caller's return buffer.

   External returns:
   - Halt: ABI-encoded return data. state_rel on final state.

   Error paths:
   - AssertException → Abort Revert_abort
   - Error → Abort (any abort type) *)
(* Helper: check return values match for internal return.
   Dispatches by the return type, as Python's _lower_internal_return does:
   - Memory return: vals = [] (value in return buffer, not on stack)
   - Tuple or struct (tuple-like), returned on the stack: one word per
     member, vals = MAP typed_val_to_w256 over the members, for any number
     of members, one included
   - Any other value: vals = [typed_val_to_w256 ret_tv v] *)
Definition intret_vals_match_def:
  intret_vals_match ret_tv v vals ⇔
    vals = [] ∨
    vals = (case (ret_tv, v) of
              (TupleTV elem_tvs, ArrayV (TupleV elem_vals)) =>
                MAP (λ(tv,ev). typed_val_to_w256 tv ev)
                  (ZIP (elem_tvs, elem_vals))
            | (StructTV field_tvs, StructV fields) =>
                MAP (λ(tv,ev). typed_val_to_w256 tv ev)
                  (ZIP (MAP SND field_tvs, MAP SND fields))
            | _ => [typed_val_to_w256 ret_tv v])
End

Definition result_rel_def:
  (* Normal completion — no return value *)
  (result_rel func ret_tv cenv cx (INL (), vs') (OK ss') =
    state_rel func cenv cx vs' ss') ∧
  (* Internal return: state + return values *)
  (result_rel func ret_tv cenv cx (INR (ReturnException v), vs') (IntRet ir ss') =
    (state_rel func cenv cx vs' ss' ∧
     intret_vals_match ret_tv v ir.iret_values ∧
     ir.iret_adopt_fmp = NONE)) ∧
  (* External return → Halt with ABI-encoded data *)
  (result_rel func ret_tv cenv cx (INR (ReturnException v), vs') (Halt ss') =
    state_rel func cenv cx vs' ss') ∧
  (* Every reason may REVERT, including an ordinary raise "UNREACHABLE".
     Only the distinguished UNREACHABLE exception may map to ExHalt_abort. *)
  (result_rel func ret_tv cenv cx (INR (AssertException s), vs') (Abort Revert_abort ss') =
    T) ∧
  (result_rel func ret_tv cenv cx (INR (AssertException s), vs') (Abort ExHalt_abort ss') =
    (s = "UNREACHABLE")) ∧
  (* Error → Abort (any type) *)
  (result_rel func ret_tv cenv cx (INR (Error _), vs') (Abort _ ss') = T) ∧
  (* Everything else: no relation *)
  (result_rel _ _ _ _ _ _ = F)
End

(* ===== Type Classification ===== *)

(* Struct field types function from compile_env.
   Used by definitions that still take a struct-name lookup function.
   Extracts just the type from (name, type, byte_size) triples. *)
Definition cenv_sft_def:
  cenv_sft cenv name = MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name)
End

(* True for types that fit in a single EVM word (≤ 256 bits).
   Used by calling convention to decide stack vs memory passing.
   Mirrors Python: calling_convention.py is_word_type *)
Definition is_word_type_def:
  is_word_type (BaseT (UintT _)) = T ∧
  is_word_type (BaseT (IntT _)) = T ∧
  is_word_type (BaseT BoolT) = T ∧
  is_word_type (BaseT AddressT) = T ∧
  is_word_type (BaseT DecimalT) = T ∧
  is_word_type (BaseT (BytesT (Fixed m))) = (m ≤ 32) ∧
  is_word_type (FlagT _) = T ∧
  is_word_type _ = F
End

(* ===== Internal Calling Convention ===== *)

(* Maximum number of word-type arguments passed via the stack.
   Mirrors Python: calling_convention.py MAX_STACK_ARGS = 6 *)
Definition MAX_STACK_ARGS_def:
  MAX_STACK_ARGS = 6n
End

(* Maximum number of word-type return values via stack (for tuples).
   Mirrors Python: calling_convention.py MAX_STACK_RETURNS = 2 *)
Definition MAX_STACK_RETURNS_def:
  MAX_STACK_RETURNS = 2n
End

(* How many values returned via stack for a tuple-like type.
   0 = memory return, 1-2 = stack.
   field_types: list of field types (TupleT tys, or struct field types). *)
Definition tuple_like_stack_count_def:
  tuple_like_stack_count field_types =
    let n = LENGTH field_types in
    if n ≤ MAX_STACK_RETURNS ∧ EVERY is_word_type field_types then n
    else 0
End

(* How many values returned via stack. 0 = memory return, 1-2 = stack.
   Mirrors Python: calling_convention.py returns_stack_count.
   sft: function mapping struct name → field types.
   Typically (λname. MAP (FST o SND) (cenv.ce_struct_fields name)). *)
Definition returns_stack_count_def:
  returns_stack_count (sft : string -> type list) NoneT = (0:num) ∧
  returns_stack_count sft (TupleT tys) = tuple_like_stack_count tys ∧
  returns_stack_count sft (StructT nsid) =
    (* Python: field_types = [ft for (_, ft) in struct_t.members]; then
       tuple_like_stack_count(field_types). Structs with ≤2 word fields use stack.
       Uses is_word_type (not just size=32) to exclude compound types like
       uint256[1] that are 32 bytes but not primitive words. *)
    tuple_like_stack_count (sft (nsid_to_string nsid)) ∧
  returns_stack_count sft ty =
    if is_word_type ty then 1 else (0:num)
End

(* Per-arg: does it pass via stack or memory?
   stack_items accounts for return slots (0, 1, or 2 from returns_stack_count).
   Mirrors Python: calling_convention.py pass_via_stack.
   Python: `stack_items >= MAX_STACK_ARGS` → memory. *)
Definition compute_pass_via_stack_def:
  compute_pass_via_stack [] stack_items = ([] : bool list) ∧
  compute_pass_via_stack (ty :: rest) stack_items =
    if is_word_type ty ∧ stack_items < MAX_STACK_ARGS then
      T :: compute_pass_via_stack rest (stack_items + 1)
    else
      F :: compute_pass_via_stack rest stack_items
End

(* Compute calling convention for an internal function.
   returns_count: number of stack-returned values (0 = memory return).
   return_buf_size: memory return buffer size (0 for stack return).
   pass_via_stack: per-arg T=stack, F=memory.
   Mirrors Python: calling_convention.py + returns_stack_count.
   return_buf_size: For memory returns, caller must supply
   type_memory_bytes to get the right size. Here we use a conservative 32
   since type_memory_bytes requires cenv (available at call sites). *)
Definition compute_func_info_def:
  compute_func_info sft ret_type ret_mem_bytes arg_types =
    let rc = returns_stack_count sft ret_type in
    let return_buf_size = (case ret_type of
        NoneT => 0
      | t => if rc > 0 then 0 else ret_mem_bytes) in
    (* Reserve stack slots for return values (0, 1, or 2).
       Mirrors Python: stack_items += returns_stack_count(func_t) *)
    let init_stack = rc in
    let pvs = compute_pass_via_stack arg_types init_stack in
    (rc, return_buf_size, pvs)
End

(* Is the AST type signed? *)
Definition is_signed_type_def:
  is_signed_type (BaseT (IntT _)) = T ∧
  is_signed_type (BaseT DecimalT) = T ∧
  is_signed_type _ = F
End

(* Is type a decimal? *)
Definition is_decimal_type_def:
  is_decimal_type (BaseT DecimalT) = T ∧
  is_decimal_type _ = F
End

(* Decimal divisor: 10^10 = 10000000000 *)
Definition decimal_divisor_def:
  decimal_divisor (BaseT DecimalT) = 10000000000 ∧
  decimal_divisor _ = 1
End

(* Bit width of an integer type *)
(* Number of significant bits for numeric types.
   Only meaningful for IntT, UintT, DecimalT.
   Catch-all 256 is conservative (full word) for non-numeric types.
   Python: IntegerT.bits, DecimalT is 168-bit internally. *)
Definition type_bits_def:
  type_bits (BaseT (UintT n)) = n ∧
  type_bits (BaseT (IntT n)) = n ∧
  type_bits (BaseT DecimalT) = 168 ∧
  type_bits _ = 256
End

(* Type bounds as word256 values.
   Unsigned N-bit: lo = 0, hi = 2^N - 1
   Signed N-bit:   lo = -2^(N-1), hi = 2^(N-1) - 1 *)
Definition type_bounds_def:
  type_bounds ty =
    let bits = type_bits ty in
    if is_signed_type ty then
      (i2w (- &(2 ** (bits - 1))) : bytes32,
       i2w (&(2 ** (bits - 1) - 1)) : bytes32)
    else
      (0w : bytes32, n2w (2 ** bits - 1) : bytes32)
End

(* is_uint256: true only for UintT 256 *)
Definition is_uint256_def:
  is_uint256 (BaseT (UintT 256)) = T ∧
  is_uint256 _ = F
End

(* ===== Struct Field Offset ===== *)
(* Byte offset of a field in a struct (memory layout).
   Fields are stored sequentially by byte size. *)
Definition struct_field_offset_def:
  struct_field_offset [] target = 0 ∧
  struct_field_offset ((name, fty, sz)::rest) target =
    if name = target then (0:num)
    else sz + struct_field_offset rest target
End

(* Slot offset of a field in a struct (storage layout).
   Fields are stored sequentially, each rounded up to 32 bytes. *)
Definition struct_field_offset_slots_def:
  struct_field_offset_slots [] target = (0:num) ∧
  struct_field_offset_slots ((name, fty, sz)::rest) target =
    if name = target then (0:num)
    else (sz + 31) DIV 32 + struct_field_offset_slots rest target
End

(* nsid_to_string moved above log_entry_equiv_def *)

(* ===== Type Size Computation ===== *)
(* Moved from exprLowering to break circular dependency with context.
   context needs type_memory_bytes for layout-aware typed copy. *)

(* Compute memory footprint of a Vyper type in bytes.
   Mirrors Python: VyperType.memory_bytes_required (base.py).
   - Word types: 32 bytes (single EVM word)
   - Dynamic bytes/strings: 32 (length) + ceil32(max_length)
   - Static arrays: count × element_size
   - Dynamic arrays: 32 (length) + capacity × element_size
   - Structs: sum of field sizes from ce_struct_fields
   - Tuples: sum of element sizes *)
Definition type_memory_bytes_def:
  type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) = 32 + ((n + 31) DIV 32) * 32 ∧
  type_memory_bytes cenv (BaseT (StringT n)) = 32 + ((n + 31) DIV 32) * 32 ∧
  type_memory_bytes cenv (BaseT _) = 32 ∧
  type_memory_bytes cenv (FlagT _) = 32 ∧
  type_memory_bytes cenv (ArrayT elem_ty (Fixed n)) =
    n * type_memory_bytes cenv elem_ty ∧
  type_memory_bytes cenv (ArrayT elem_ty (Dynamic n)) =
    32 + n * type_memory_bytes cenv elem_ty ∧
  type_memory_bytes cenv (StructT nsid) =
    SUM (MAP (SND o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))) ∧
  type_memory_bytes cenv (TupleT tys) =
    SUM (MAP (type_memory_bytes cenv) tys) ∧
  type_memory_bytes cenv NoneT = 0
Termination
  WF_REL_TAC `measure (type_size o SND)`
End

(* Compute element size in a given location.
   Mirrors Python: VyperType.get_size_in(location) (base.py:174).
   Storage/transient: slot-based (ceil(bytes/32)), others: byte-based. *)
Definition elem_size_in_location_def:
  elem_size_in_location cenv loc elem_ty =
    if is_slot_addressed loc then
      let mem_size = type_memory_bytes cenv elem_ty in
      (mem_size + 31) DIV 32
    else
      type_memory_bytes cenv elem_ty
End
