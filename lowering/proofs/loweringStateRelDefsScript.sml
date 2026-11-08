(*
 * Source/Venom State Relation
 *
 * TOP-LEVEL:
 *   state_rel        — cross-level simulation relation
 *   result_rel       — maps Vyper exceptions to Venom exec_result
 *   local_ptrs_rel   — live locals held through pointer variables match memory
 *   accounts_rel     — every address's accounts and transient storage match,
 *                      the running contract's storage up to dead bytes
 *   dead_bytes       — the bytes of a stored value past a bytestring's
 *                      length (or a nested DynArray's)
 *   storage_dead     — dead_bytes of a declared storage region, which the
 *                      lowering may overwrite
 *   storage_agree, accounts_agree, transient_agree, request_agree
 *                    — equality up to storage_dead
 *   storage_read_live — a storage read sees no other value's dead bytes
 *   compile_state_ok — well-formedness: bound labels disjoint from future fresh labels
 *   label_external   — label not bound and not in future fresh-label co-domain
 *
 * Helper:
 *   fresh_vars_wrt       — compiler var counter ahead of existing venom vars
 *   local_region         — a live local's region through its pointer variable
 *   local_backed         — what backs a live local's region in the current frame
 *   not_local_ptr        — a variable is not a live local's pointer or the
 *                          constructor's immutable base
 *   bound_labels         — set of labels bound to blocks in compile state
 *   compiler_labels_future — co-domain of fresh_label for counter values ≥ n
 *)

Theory loweringStateRelDefs
Ancestors
  compileEnv valueEncodingDefs immutableValue immutableEncoding vyperStorageLayoutSafety
  venomExecSemantics vyperState vyperContext vyperValue vyperEvent
  byte keccak finite_map pred_set list rich_list

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
Definition not_scope_ptr_def:
  not_scope_ptr cenv scopes x ⇔
    ∀name entry sz.
      lookup_scopes name scopes = SOME entry ⇒
      FLOOKUP cenv.ce_vars name ≠ SOME (PtrVar (Var x) sz)
End

(* x is neither the pointer variable of a live local nor the constructor's
   immutable base, so assigning it leaves the locals and the base in place. *)
Definition not_local_ptr_def:
  not_local_ptr cenv scopes x ⇔
    (∀name entry sz.
       lookup_scopes name scopes = SOME entry ⇒
       FLOOKUP cenv.ce_vars name ≠ SOME (PtrVar (Var x) sz)) ∧
    cenv.ce_imm_alloca ≠ SOME (Var x)
End

(* The locals of cenv are held through pointer variables that were handed out
   before st (declare_local, compile_register_positional_args), one per
   local:
   - no variable sits at a fixed MemLoc offset: state_rel does not relate
     those (the parameters build_compile_env places, until the code that
     registers them rebinds them, and default arguments, which
     compile_register_kwarg_vars keeps at MemLoc), and a store to one could
     hit a live local's region;
   - no compiler variable fresh at st is a local's pointer, so a temporary of
     the code compiled from st on never overwrites one;
   - distinct locals have distinct pointers, so declaring a local leaves the
     others' pointers alone;
   - the constructor's immutable base variable (ASSIGN 0 in the prologue,
     before the body) is no fresh compiler variable and no local's pointer,
     so neither a temporary nor a local's pointer overwrites it. *)
Definition local_ptrs_reserved_def:
  local_ptrs_reserved cenv (st:compile_state) ⇔
    (∀name off sz. FLOOKUP cenv.ce_vars name ≠ SOME (MemLoc off sz)) ∧
    (∀n1 n2 p sz1 sz2.
       FLOOKUP cenv.ce_vars n1 = SOME (PtrVar (Var p) sz1) ⇒
       not_fresh_at st p ∧
       (FLOOKUP cenv.ce_vars n2 = SOME (PtrVar (Var p) sz2) ⇒ n1 = n2)) ∧
    ∀x. cenv.ce_imm_alloca = SOME (Var x) ⇒
      not_fresh_at st x ∧
      ∀name sz. FLOOKUP cenv.ce_vars name ≠ SOME (PtrVar (Var x) sz)
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

(* ===== Offsets inside a value's memory layout ===== *)

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

(* ===== Storage Relation up to Dead Bytes ===== *)
(* The source writes a bytestring as its length and the slots its bytes use
   (encode_dyn_bytes_slots), zero-padding the last one.  The lowering copies
   the value's whole storage block from its memory buffer
   (compile_memory_to_storage, Python's _store_memory_to_storage), so the
   bytes past the length, up to the capacity, hold whatever the buffer held
   there.  A DynArray nested in another value is copied the same way, so its
   elements past its length do too.  Nothing reads them: decoding reads a
   length first and only the bytes or elements below it.  The relation on
   the running contract's storage and transient storage therefore only
   compares the bytes that are not dead.

   dead_bytes st base tv j b: byte b (0 = most significant) of slot j is
   dead in a value of type tv stored at slot base of st, by the lengths
   that st holds:
   - a bytestring: a data byte at or past the length, within the capacity;
   - a DynArray: every byte of an element at or past the length, and the
     dead bytes of the elements below it;
   - a struct, tuple or static array: the dead bytes of its members. *)
Definition dyn_bytes_dead_def:
  dyn_bytes_dead (st:storage) base max (j:num) (b:num) ⇔
    base < j ∧ j ≤ base + word_size max ∧ b < 32 ∧
    w2n (lookup_storage (n2w base) st) ≤ 32 * (j - (base + 1)) + b
End

Definition dead_bytes_def:
  (dead_bytes st base (BaseTV (BytesT (Dynamic max))) j b ⇔
     dyn_bytes_dead st base max j b) ∧
  (dead_bytes st base (BaseTV (StringT max)) j b ⇔
     dyn_bytes_dead st base max j b) ∧
  (dead_bytes st base (BaseTV _) j b ⇔ F) ∧
  (dead_bytes st base (FlagTV _) j b ⇔ F) ∧
  (dead_bytes st base NoneTV j b ⇔ F) ∧
  (dead_bytes st base (TupleTV tvs) j b ⇔ dead_bytes_list st base tvs j b) ∧
  (dead_bytes st base (ArrayTV tv (Fixed n)) j b ⇔
     ∃i. i < n ∧ dead_bytes st (base + i * type_slot_size tv) tv j b) ∧
  (dead_bytes st base (ArrayTV tv (Dynamic n)) j b ⇔
     ∃i. i < n ∧
         if i < w2n (lookup_storage (n2w base) st) then
           dead_bytes st (base + 1 + i * type_slot_size tv) tv j b
         else
           base + 1 + i * type_slot_size tv ≤ j ∧
           j < base + 1 + (i + 1) * type_slot_size tv ∧ b < 32) ∧
  (dead_bytes st base (StructTV fields) j b ⇔
     dead_bytes_fields st base fields j b) ∧
  (dead_bytes_list st base [] j b ⇔ F) ∧
  (dead_bytes_list st base (tv::tvs) j b ⇔
     dead_bytes st base tv j b ∨
     dead_bytes_list st (base + type_slot_size tv) tvs j b) ∧
  (dead_bytes_fields st base [] j b ⇔ F) ∧
  (dead_bytes_fields st base ((_,tv)::fields) j b ⇔
     dead_bytes st base tv j b ∨
     dead_bytes_fields st (base + type_slot_size tv) fields j b)
End

(* Byte b of slot j is dead in the storage (tr = F) or transient storage
   (tr = T) st of the running contract: a declared region (a variable, or a
   hashmap leaf at a complete key) has it dead, and that region fits the slot
   space and is disjoint from every declared region on the same backend at
   another slot or type.  Regions are told apart by where they are, not by
   how they are named: many keys name one hashmap leaf (encode_hashmap_key
   sends IntV i and IntV (i + 2 ** 256) to the same word).  Asking for the
   disjointness here keeps a byte that another region reads live, and keeps
   a region's dead bytes fixed under writes outside it, without assuming
   storage_layout_safe. *)
Definition storage_dead_def:
  storage_dead cx tr st j b ⇔
    ∃mid n subs slot tv.
      declared_storage_region cx mid n subs = SOME (tr, slot, tv) ∧
      w2n slot + type_slot_size tv ≤ dimword (:256) ∧
      (∀mid' n' subs' slot' tv'.
         declared_storage_region cx mid' n' subs' = SOME (tr, slot', tv') ∧
         (slot', tv') ≠ (slot, tv) ⇒
         ranges_disjoint (w2n slot) (type_slot_size tv)
                         (w2n slot') (type_slot_size tv')) ∧
      dead_bytes st (w2n slot) tv j b
End

(* A read of a value of type tv at slot w on backend tr sees no dead byte of
   st but those tv itself leaves dead at w, and the value's slots fit the
   slot space when any byte is dead.  A read of a declared region has it
   (storage_dead), and so does a part of a value that has it. *)
Definition storage_read_live_def:
  storage_read_live cx tr st (w:bytes32) tv ⇔
    ∀j b.
      storage_dead cx tr st j b ⇒
      w2n w + type_slot_size tv ≤ dimword (:256) ∧
      (w2n w ≤ j ∧ j < w2n w + type_slot_size tv ⇒
       dead_bytes st (w2n w) tv j b)
End

(* st1 and st2 agree on every byte that is not dead by D. *)
Definition storage_agree_def:
  storage_agree D (st1:storage) (st2:storage) ⇔
    ∀(k:bytes32) b.
      b < 32 ∧ ¬D (w2n k) b ⇒
      EL b (word_to_bytes (lookup_storage k st1) T) =
      EL b (word_to_bytes (lookup_storage k st2) T)
End

(* Accounts a1 (source) and a2 (Venom): equal at every address but the
   running contract's, whose accounts are equal but for their storage, which
   agrees up to the bytes dead in a1's. *)
Definition accounts_agree_def:
  accounts_agree cx (a1:evm_accounts) (a2:evm_accounts) ⇔
    (∀addr. addr ≠ cx.txn.target ⇒ a1 addr = a2 addr) ∧
    (a1 cx.txn.target with storage := (a2 cx.txn.target).storage) =
      a2 cx.txn.target ∧
    storage_agree (storage_dead cx F (a1 cx.txn.target).storage)
      (a1 cx.txn.target).storage (a2 cx.txn.target).storage
End

(* Transient storage t1 (source) and t2 (Venom): equal at every address but
   the running contract's, which agrees up to the bytes dead in t1's. *)
Definition transient_agree_def:
  transient_agree cx (t1:transient_storage) (t2:transient_storage) ⇔
    (∀addr. addr ≠ cx.txn.target ⇒ t1 addr = t2 addr) ∧
    storage_agree (storage_dead cx T (t1 cx.txn.target))
      (t1 cx.txn.target) (t2 cx.txn.target)
End

(* A call request recorded by the source (r1) and by Venom (r2): equal but
   for the snapshots of the accounts and transient storage, which agree as
   above. *)
Definition request_agree_def:
  request_agree cx (r1:call_request) (r2:call_request) ⇔
    r1 with <| cr_accounts := r2.cr_accounts;
               cr_tStorage := r2.cr_tStorage |> = r2 ∧
    accounts_agree cx r1.cr_accounts r2.cr_accounts ∧
    transient_agree cx r1.cr_tStorage r2.cr_tStorage
End

(* The running contract's storage, Vyper accounts against Venom state. *)
Definition storage_rel_def:
  storage_rel cx (addr:address) (vs:evaluation_state) ss =
    let st = (lookup_account addr vs.accounts).storage in
    storage_agree (storage_dead cx F st) st (contract_storage ss)
End

(* The running contract's transient storage.
   Interpreter: st.tStorage (transient_storage = address -> storage).
   Venom: ss.vs_transient (same type).
   Mirrors EIP-1153: per-address, per-transaction. *)
Definition transient_rel_def:
  transient_rel cx (addr:address) (vs:evaluation_state) ss ⇔
    storage_agree (storage_dead cx T (vs.tStorage addr))
      (vs.tStorage addr) (contract_transient ss)
End

(* The accounts and the transient storage of every address agree.
   Other addresses' accounts and
   transient storage change during a body only through the call oracle,
   whose outcome both sides adopt the same way (adopt_outcome), which makes
   them equal again. Pending deletion queues are related separately by
   state_rel and finalized at the external transaction boundary. *)
Definition accounts_rel_def:
  accounts_rel cx (vs:evaluation_state) ss ⇔
    accounts_agree cx vs.accounts ss.vs_accounts ∧
    transient_agree cx vs.tStorage ss.vs_transient
End

(* ===== Immutables Relation ===== *)
(* Interpreter immutables ↔ Venom code/data section.
   During constructor: interpreter writes to st.immutables, Venom uses ISTORE/ILOAD.
   At runtime: interpreter reads from st.immutables, Venom uses DLOAD from data section.
   The relation ties each interpreter name to its Venom representation.

   Interpreter: st.immutables : (address, module_immutables) alist
     where module_immutables = (num option, string |-> (type_value # value)) alist
     Keyed by (source_id_opt, immutable_name) → typed value.
   Venom (ctor): ss.vs_memory holds the staged capacity-sized encoding.
     ISTORE also records words in byte-addressed vs_immutables, but deploy
     copies memory, so bookkeeping alone is not the representation boundary.
   Venom (runtime): ss.vs_data_section holds the installed suffix bytes.

   ce_module_vars maps (src_id_opt, name) to ImmutableLoc byte_offset.
   Semantic contents and capacity bounds do not determine unused padding;
   exact staging is tracked separately in immutableRelation. *)
(* Constructor accesses keep the region base at zero and retain the runtime
   label needed by the deployment epilogue. *)
Definition immutable_base_zero_def:
  immutable_base_zero cenv ss <=>
    (!base. cenv.ce_imm_alloca = SOME base ==> eval_operand base ss = SOME 0w) /\
    (cenv.ce_is_ctor ==> IS_SOME (FLOOKUP ss.vs_labels "runtime_begin"))
End

Definition immutables_rel_def:
  immutables_rel cenv (addr:address) src_id_opt is_ctor (vs:evaluation_state) ss <=>
    let interp_imms = (case ALOOKUP vs.immutables addr of
                         NONE => FEMPTY
                       | SOME mod_imms => get_source_immutables src_id_opt mod_imms) in
    !name tv v byte_offset.
      FLOOKUP cenv.ce_module_vars (src_id_opt, name) =
        SOME (ImmutableLoc byte_offset) /\
      FLOOKUP interp_imms name = SOME (tv,v) ==>
      immutable_value_admissible tv v /\
      (~is_ctor ==>
         byte_offset + type_memory_size tv <= LENGTH ss.vs_data_section) /\
      val_in_memory tv v byte_offset
        (if is_ctor then ss.vs_memory else ss.vs_data_section) /\
      immutable_value_bytes_rel tv v
        (mem_bytes_at byte_offset (type_memory_size tv)
          (if is_ctor then ss.vs_memory else ss.vs_data_section))
End

(* ===== Storage Variables Relation ===== *)
(* Per-variable mapping between interpreter layout slots and cenv StorageLoc.
   The interpreter uses lookup_var_slot_from_layout to get a slot number,
   then read_storage_slot/write_storage_slot to access it.
   The lowering uses FLOOKUP ce_module_vars nsid, with the
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
   cenv.ce_module_vars : (nsid, var_location) fmap
     Maps (ce_module, var_name) → StorageLoc slot.
   cenv.ce_storage_layout : (string, bytes32) fmap
     Maps var_name → slot (redundant with ce_module_vars for StorageLoc). *)

(* Whether a declaration found by find_var_decl_by_name is transient. *)
Definition var_decl_transient_def:
  var_decl_transient (StorageVarDecl is_transient _) = is_transient ∧
  var_decl_transient (HashMapVarDecl is_transient _ _) = is_transient
End

Definition storage_vars_rel_def:
  storage_vars_rel cenv (cx:evaluation_context) ⇔
    (∀ name (slot:bytes32).
       FLOOKUP cenv.ce_module_vars (cenv.ce_module, name) =
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
       FLOOKUP cenv.ce_module_vars (src, name) =
         SOME (StorageLoc (n2w slot_num)))
End

(* Transient storage variables: same as storage_vars_rel but for transient. *)
Definition transient_vars_rel_def:
  transient_vars_rel cenv (cx:evaluation_context) ⇔
    (∀ name (slot:bytes32).
       FLOOKUP cenv.ce_module_vars (cenv.ce_module, name) =
         SOME (TransientLoc slot) ⇒
       ∃ slot_num. lookup_var_slot_from_layout cx T cenv.ce_module name = SOME slot_num ∧
                   n2w slot_num = slot) ∧
    (∀ src ts name d id slot_num.
       get_module_code cx src = SOME ts ∧
       find_var_decl_by_name name ts = SOME (d, id) ∧
       var_decl_transient d ∧
       lookup_var_slot_from_layout cx T src id = SOME slot_num ⇒
       FLOOKUP cenv.ce_module_vars (src, name) =
         SOME (TransientLoc (n2w slot_num)))
End

(* Check if a type is a bytestring (dynamic Bytes or String).
   Used by log topics and bytestring-specific copy. *)
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
  indexed_topic_flags [] [] = ([] : type list) ∧
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
  log_topic_equiv ty v topic =
    (if is_event_bytestring_type ty then log_bytestring_topic v = SOME topic
     else topic = event_topic_word ty v)
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

Definition log_entry_equiv_def:
  log_entry_equiv _ _ (source_event : log) (ev : event) ⇔ source_event = ev
End

(* Logs relation: pairwise equivalence *)
Definition logs_rel_def:
  logs_rel cenv (addr:address) (vs:evaluation_state) ss ⇔
    LENGTH vs.logs = LENGTH ss.vs_logs ∧
    EVERY2 (log_entry_equiv cenv addr) vs.logs ss.vs_logs
End

(* The transaction's block context is one an EVM block can have: a block
   number past genesis and below 2 ** 255, and the hashes of the last
   MIN 256 block_number blocks.  Under it the source's evaluate_block_hash
   raises exactly where the lowered blockhash(n) range check reverts, and
   block.prevhash always has a hash. *)
Definition tx_env_ok_def:
  tx_env_ok tx <=>
    tx.block_number <> 0 /\ tx.block_number < 2 ** 255 /\
    MIN 256 tx.block_number <= LENGTH tx.block_hashes /\
    LENGTH tx.block_hashes <= 256
End

Theorem tx_env_ok_hash_window:
  tx_env_ok tx ==>
  (n < tx.block_number /\ tx.block_number - n - 1 < LENGTH tx.block_hashes <=>
   n < tx.block_number /\ tx.block_number - 256 <= n)
Proof
  simp[tx_env_ok_def] >> strip_tac >>
  Cases_on `tx.block_number <= 256` >>
  gvs[arithmeticTheory.MIN_DEF] >> decide_tac
QED

Theorem tx_env_ok_evaluate_block_hash:
  tx_env_ok tx ==>
  evaluate_block_hash tx n =
    if n < tx.block_number /\ tx.block_number - 256 <= n then
      INL (BytesV (word_to_bytes_be
        (EL (tx.block_number - n - 1) tx.block_hashes)))
    else INR (RuntimeError "evaluate_block_hash")
Proof
  strip_tac >> drule tx_env_ok_hash_window >>
  disch_then (qspec_then `n` assume_tac) >>
  simp[evaluate_block_hash_def] >>
  `tx.block_number - 1 - n = tx.block_number - n - 1` by decide_tac >>
  Cases_on `n < tx.block_number /\ tx.block_number - 256 <= n` >>
  gvs[] >>
  Cases_on `tx.block_number <= n \/ LENGTH tx.block_hashes <= tx.block_number - (n + 1)` >>
  gvs[] >> decide_tac
QED

Theorem tx_env_ok_evaluate_prevhash:
  tx_env_ok tx ==>
  evaluate_block_hash tx (tx.block_number - 1) =
    INL (BytesV (word_to_bytes_be (EL 0 tx.block_hashes)))
Proof
  strip_tac >> drule tx_env_ok_evaluate_block_hash >>
  disch_then (qspec_then `tx.block_number - 1` mp_tac) >>
  gvs[tx_env_ok_def]
QED

(* Call context matches.  BLOCKHASH answers from the transaction's block
   hashes within the last 256 blocks, and 0 elsewhere, as the EVM does. *)
Definition call_ctx_rel_def:
  call_ctx_rel (txn:call_txn) (cc:call_context) (tc:tx_context) (bc:block_context) =
    (cc.cc_caller = txn.sender ∧
     cc.cc_address = txn.target ∧
     cc.cc_callvalue = n2w txn.value ∧
     cc.cc_calldata = txn.calldata ∧
     tc.tc_origin = txn.origin ∧
     tc.tc_gasprice = n2w txn.gas_price ∧
     tc.tc_chainid = n2w txn.chain_id ∧
     tc.tc_blobhashes = txn.blob_hashes ∧
     bc.bc_coinbase = txn.coinbase ∧
     bc.bc_timestamp = n2w txn.time_stamp ∧
     bc.bc_number = n2w txn.block_number ∧
     bc.bc_prevrandao = n2w txn.prev_randao ∧
     bc.bc_gaslimit = n2w txn.gas_limit ∧
     bc.bc_basefee = n2w txn.base_fee ∧
     bc.bc_blobbasefee = n2w txn.blob_base_fee ∧
     tx_env_ok txn ∧
     (∀n. bc.bc_blockhash n =
          if n < txn.block_number ∧ txn.block_number - 256 ≤ n ∧
             txn.block_number - n - 1 < LENGTH txn.block_hashes
          then EL (txn.block_number - n - 1) txn.block_hashes else 0w))
End

Theorem call_ctx_rel_prevhash:
  call_ctx_rel tx cc tc bc ==>
  bc.bc_blockhash (w2n (bc.bc_number - 1w)) = HD tx.block_hashes
Proof
  strip_tac >>
  `0 < tx.block_number /\ tx.block_number < 2 ** 255 /\
   0 < LENGTH tx.block_hashes` by
    gvs[call_ctx_rel_def, tx_env_ok_def] >>
  `bc.bc_number = n2w tx.block_number` by gvs[call_ctx_rel_def] >>
  `bc.bc_number - 1w = (n2w (tx.block_number - 1) : bytes32)` by
    simp[wordsTheory.n2w_sub] >>
  `w2n (bc.bc_number - 1w) = tx.block_number - 1` by
    (simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
     simp_tac (srw_ss() ++ wordsLib.SIZES_ss) [] >> fs[]) >>
  gvs[call_ctx_rel_def]
QED

(* Top-level oracle-mode source/Venom state relation for the statement and
   expression simulation, in func, the function running.  It ties together
   the sub-relations below and exactly the current oracle suffix and request
   prefix; NONE-mode compatibility does not satisfy it.
   - local_ptrs_rel: locals in scope, held in memory through their pointer
     variables (PtrVar).  MemLoc variables at fixed offsets are not
     related.
   - storage_rel, storage_vars_rel: storage up to dead bytes, and the slots
     of storage variables.
   - transient_rel, transient_vars_rel: transient storage up to dead bytes,
     and the slots of transient variables.
   - accounts_rel: the accounts and transient storage of every address (the
     running contract's storage up to dead bytes); storage_rel and
     transient_rel are its case for the running contract.
   - immutables_rel: immutables (vs_immutables in a constructor, the data
     section at runtime).
   - logs_rel: emitted logs.
   - call_ctx_rel: transaction, call and block context.
   - the call context is not static: the entry relation (venom_env_rel)
     assumes it and the lowered code never writes cc_static, so a CALL
     asks a static request exactly when the source does.
   - neither is the source frame (txn.is_static), so source writes succeed.
   - outcomes and requests: the oracle outcomes still to consume and the
     requests recorded so far, as in the result relation; a request's
     snapshot of the running contract's storage agrees up to dead bytes.
   - pending_deletions: equality with vs_pending_deletions, including effects
     accumulated from adopted external-call outcomes. *)
Definition state_rel_def:
  state_rel func cenv cx (vs:evaluation_state) ss =
    (local_ptrs_rel func cenv vs.scopes ss ∧
     storage_rel cx cx.txn.target vs ss ∧
     storage_vars_rel cenv cx ∧
     transient_rel cx cx.txn.target vs ss ∧
     transient_vars_rel cenv cx ∧
     accounts_rel cx vs ss ∧
     immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor vs ss ∧
     logs_rel cenv cx.txn.target vs ss ∧
     call_ctx_rel cx.txn ss.vs_call_ctx ss.vs_tx_ctx ss.vs_block_ctx ∧
     ¬ss.vs_call_ctx.cc_static ∧
     ¬cx.txn.is_static ∧
     vs.outcomes = SOME ss.vs_outcomes ∧
     LIST_REL (request_agree cx) vs.requests ss.vs_requests ∧
     vs.pending_deletions = ss.vs_pending_deletions)
End

Theorem state_rel_gas_obs:
  state_rel func cenv cx (es with gas_obs := readings) s =
  state_rel func cenv cx es s
Proof
  simp[state_rel_def, storage_rel_def, transient_rel_def, accounts_rel_def,
       immutables_rel_def, logs_rel_def]
QED

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

Theorem result_rel_gas_obs:
  result_rel func ret_tv cenv cx (res, es with gas_obs := readings) r =
  result_rel func ret_tv cenv cx (res, es) r
Proof
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >> Cases_on `r` >>
      simp[result_rel_def, state_rel_gas_obs]) >>
  rename1 `INR exc` >> Cases_on `exc` >> Cases_on `r` >>
  simp[result_rel_def, state_rel_gas_obs] >>
  Cases_on `a` >> simp[result_rel_def]
QED
