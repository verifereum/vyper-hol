(*
 * Compilation Environment
 *
 * TOP-LEVEL:
 *   compile_env      — maps Vyper vars to Venom locations
 *   compile_state    — monad state for code generation
 *   cs_extends       — a compile state only appended to another;
 *                      cs_extends_* for the monad primitives
 *   is_word_type     — type fits in single EVM word (calling convention)
 *   is_signed_type   — signed integer or decimal
 *   type_bits        — bit width of integer type
 *   type_bounds      — (lo, hi) word256 bounds for type
 *   struct_field_offset — byte offset of struct field
 *   nsid_to_string   — namespace ID to lookup string
 *   internal_fn_label — Venom label of an internal function (Vyper's spelling)
 *
 * Helper:
 *   fresh_var, fresh_label, emit, new_block — compilation monad ops
 *   fresh_label_output   — canonical shape of compiler-generated labels (@suffix_k)
 *
 * The source/Venom state relation is in lowering/proofs/loweringStateRelDefs.
 *)

Theory compileEnv
Ancestors
  venomExecSemantics venomInst venomPolicyTypes
  vyperState vyperContext vyperValue vyperABI vyperEvent contractABI vyperTypeSystem
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
    (* Arguments and locals: name → location. *)
    ce_vars : (string, var_location) fmap;
    (* Module variables (storage, transient, HashMap, immutable):
       nsid → location. A table of their own, so no local can shadow one.
       Mirrors Python, which resolves self.<name> through the declaration's
       varinfo (codegen_venom/expr.py lower_Attribute) and locals through
       ctx.variables (codegen_venom/context.py). *)
    ce_module_vars : (nsid, var_location) fmap;
    ce_storage_layout : (string, bytes32) fmap;
    ce_module : num option;
    (* Struct metadata: struct_name → list of (field_name, member_type, memory_bytes) *)
    ce_struct_fields : (string, (string # type # num) list) fmap;
    (* DynArray metadata: local name → max capacity *)
    ce_dynarray_capacity : string -> num;
    (* DynArray metadata: module variable nsid → max capacity *)
    ce_module_dynarray_capacity : nsid -> num;
    (* Method ID lookup: func_name → 4-byte keccak selector as num *)
    ce_method_id : string -> type list -> num;
    (* Flag member index: (flag_type_name, member_name) → positional index *)
    ce_flag_member_id : string -> string -> num;
    (* Number of members in a flag type *)
    ce_flag_n_members : string -> num;
    (* Variable type lookup: local name → type (for Attribute dispatch) *)
    ce_var_type : string -> type option;
    (* Module variable type lookup: nsid → type *)
    ce_module_var_type : nsid -> type option;
    (* HashMap detection: module variable nsid → SOME (transient, key type,
       value type) if the variable is a HashMap (mapping); only module
       variables can be. Needed because HashMapT is a value_type, not type,
       so ce_module_var_type cannot represent it. Used by compile_subscript
       for dispatch.
       Mirrors Python: isinstance(base_typ, HashMapT) *)
    ce_hashmap_info : nsid -> (bool # type # value_type) option;
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
    (* Where the return PC is; NONE for external functions and constructors.
       Mirrors Python: FunctionContext.return_pc, tested by lower_Return as
       `ctx.return_pc is not None` *)
    ce_return_pc : var_location option;
    (* Constructors return through one shared runtime-copy epilogue.
       Internal functions called during deployment still use ce_return_pc. *)
    ce_ctor_exit_label : string option;
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
    ce_imm_alloca : operand option;
    (* Internal function calling convention info:
       func_label → (returns_count, return_buf_size, pass_via_stack : bool list)
       pass_via_stack: per-arg T=stack, F=memory. Order matches func_t.arguments.
       Mirrors Python: calling_convention.py pass_via_stack + returns_stack_count *)
    ce_func_info : string -> (num # num # bool list);
    (* Internal function declared parameter types, defaulted ones included:
       func_name → arg types. Spells the INVOKE target (internal_fn_label).
       Mirrors Python: func_t.arguments in expr.py lower_Call *)
    ce_func_param_types : string -> type list;
    (* Internal function declared return types: func_name → return type.
       The value of an internal call is its callee's return buffer, laid out
       at this type even where the call is used at a wider type.
       Mirrors Python: func_t.return_type in expr.py _lower_internal_call *)
    ce_func_return_type : string -> type;
    (* Declared internal-call mutability for delayed operand snapshots.
       Mirrors Python: ContractFunctionT.is_modifying. *)
    ce_func_mutability : string -> function_mutability;
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
       declaration, as in every body build_compile_env sets up; F when it
       keeps whatever ce_vars already holds for its name.
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

(* ===== Type Classification ===== *)

Definition is_bytestring_type_def:
  is_bytestring_type (BaseT (BytesT (Dynamic _))) = T ∧
  is_bytestring_type (BaseT (StringT _)) = T ∧
  is_bytestring_type _ = F
End

(* Types of an event's non-indexed arguments, in order. *)
Definition log_non_indexed_types_def:
  log_non_indexed_types [] [] = ([] : type list) ∧
  log_non_indexed_types (T :: flags) (_ :: tys) =
    log_non_indexed_types flags tys ∧
  log_non_indexed_types (F :: flags) (ty :: tys) =
    ty :: log_non_indexed_types flags tys ∧
  log_non_indexed_types _ _ = []
End

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

Theorem type_widens_to_word:
  !tenv t u. type_widens_to tenv t u /\ is_word_type u ==> t = u
Proof
  rw[type_widens_to_def] >>
  Cases_on `t` >> Cases_on `u` >> gvs[arg_type_fits_def, is_word_type_def] >>
  rename1 `arg_type_fits (BaseT b1) (BaseT b2)` >>
  Cases_on `b1` >> Cases_on `b2` >> gvs[arg_type_fits_def, is_word_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT d1)) (BaseT (BytesT d2))` >>
  Cases_on `d1` >> Cases_on `d2` >> gvs[arg_type_fits_def, is_word_type_def]
QED

Theorem arg_type_fits_bytestring_source:
  !t u. is_bytestring_type u /\ arg_type_fits t u ==> is_bytestring_type t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `u` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT ub` >> Cases_on `ub` >> gvs[is_bytestring_type_def]
  >~ [`is_bytestring_type (BaseT (BytesT bd))`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >>
      Cases_on `t` >> gvs[arg_type_fits_def, is_bytestring_type_def] >>
      rename1 `arg_type_fits (BaseT tb) _` >> Cases_on `tb` >>
      gvs[arg_type_fits_def, is_bytestring_type_def] >>
      rename1 `arg_type_fits (BaseT (BytesT bd)) _` >> Cases_on `bd` >>
      gvs[arg_type_fits_def, is_bytestring_type_def]) >>
  Cases_on `t` >> gvs[arg_type_fits_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT tb) _` >> Cases_on `tb` >>
  gvs[arg_type_fits_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT bd)) _` >> Cases_on `bd` >>
  gvs[arg_type_fits_def, is_bytestring_type_def]
QED

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

Theorem LENGTH_compute_pass_via_stack:
  !tys n. LENGTH (compute_pass_via_stack tys n) = LENGTH tys
Proof
  Induct >> rw[compute_pass_via_stack_def]
QED

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

Theorem type_memory_bytes_struct_fields:
  !c ty c'. c'.ce_struct_fields = c.ce_struct_fields ==>
            type_memory_bytes c' ty = type_memory_bytes c ty
Proof
  recInduct type_memory_bytes_ind >> rw[type_memory_bytes_def] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[]
QED

Theorem type_memory_bytes_frame:
  !c c'. c'.ce_struct_fields = c.ce_struct_fields ==>
         type_memory_bytes c' = type_memory_bytes c
Proof
  rw[FUN_EQ_THM] >> irule type_memory_bytes_struct_fields >> simp[]
QED
