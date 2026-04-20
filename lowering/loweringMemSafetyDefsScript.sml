(*
 * Lowering Memory Safety Definitions
 *
 * Theorems establishing that the Vyper→Venom lowering produces code
 * where all memory accesses through alloca-backed pointers stay
 * within their allocated region (alloca_safe_access).
 *
 * Three-layer decomposition:
 *
 *   Layer 1 — Main theorem: lowering_alloca_safe_access
 *     For well-typed Vyper source, the lowered function satisfies
 *     alloca_safe_access at every reachable execution state.
 *     Requires type soundness (eval_preserves_swt) to guarantee
 *     runtime values match declared types, so ALLOCA sizes are
 *     adequate.
 *
 *   Layer 2 — Bridge: bp_ptrs_bounded_imp_alloca_safe_access
 *     Structural bound (base_ptr analysis) implies runtime safety.
 *     bp_ptrs_bounded checks memloc_within_alloca for every alloca-
 *     backed access in the function. bp_ptr_sound connects the
 *     analysis result to runtime state. Together they yield
 *     alloca_safe_access.
 *
 *   Layer 3 — Structural: lowering_bp_ptrs_bounded
 *     The lowering produces code where base_ptr analysis concludes
 *     all accesses are bounded. This is a structural property:
 *     ALLOCA(N) where N = type_memory_bytes, pointer arithmetic
 *     via ADD with compile-time-bounded offsets.
 *
 * Key lemma: value_type_fits_alloca
 *   value_has_type tv v ⇒ encoded memory footprint ≤ type_memory_bytes
 *   Bridges Vyper type soundness to Venom ALLOCA sizing.
 *
 * Runtime check correctness:
 *   The lowering emits bounds checks matching Vyper semantics:
 *   - compile_array_subscript: ASSERT(not negative AND idx < length)
 *   - compile_clamp: sub-256-bit range check
 *   - compile_safe_add/sub/mul/div: overflow checks
 *   Type soundness ensures runtime lengths ≤ declared capacity,
 *   so the emitted checks are adequate.
 *
 * TOP-LEVEL:
 *   lowering_alloca_safe_access     — main theorem
 *   bp_ptrs_bounded_imp_alloca_safe_access — analysis→runtime bridge
 *   lowering_bp_ptrs_bounded        — structural bound from lowering
 *   value_type_fits_alloca          — type soundness→memory layout
 *   lowering_step_preserves_safety  — step_preserves_safety for lowered code
 *)

Theory loweringMemSafetyDefs
Ancestors
  allocaRemapDefs pointerConfinedDefs basePtrDefs basePtrProps
  venomMemDefs venomExecSemantics venomWf passSharedDefs
  compileEnv context vyperTyping vyperValue vyperInterpreter
  vyperTypeSoundness vyperTypeSoundnessDefs

(* ===== Key Lemma: Type Soundness → Memory Layout ===== *)

(* A well-typed value's encoded memory footprint fits within
   the ALLOCA sized by type_memory_bytes.
   Uses the existing type_memory_bytes (compileEnv) which operates
   on Vyper types. The bridge from type_value to type is via
   evaluate_type: if evaluate_type tenv ty = SOME tv, then
   type_memory_bytes cenv ty gives the ALLOCA size for that type.

   For arrays: value_has_type (ArrayTV tv (Dynamic N)) v ⟹
     runtime length ≤ N, so accesses at indices < length are within
     [base, base + 32 + N * elem_size).

   For structs: value_has_type (StructTV fields) v ⟹
     v has exactly the declared fields, so field offsets (computed
     from field sizes) are within [base, base + struct_size).

   For bytestrings: value_has_type (BaseTV (BytesT (Dynamic N))) v ⟹
     byte length ≤ N, so data at [base+32, base+32+N) is in bounds.

   No new size function needed — type_memory_bytes already computes
   the memory-layout size from the type, and evaluate_type bridges
   type_value back to type for the ALLOCA sizing connection. *)

(* A well-typed value's runtime memory footprint fits within
   the ALLOCA sized by type_memory_bytes for the corresponding type.
   - DynArray[T,N]: length ≤ N, data ≤ N * elem_size, total ≤ 32 + N*elem_size
   - Fixed array: exact N elements, total = N * elem_size
   - Struct: exact fields, total = sum of field sizes
   - Bytes/String: data length ≤ declared max
   - Base types: 1 word = 32 bytes
   evaluate_type connects the type_value to the original type,
   so type_memory_bytes (which the lowering uses for ALLOCA sizes)
   gives the correct bound. *)
Theorem value_type_fits_alloca:
  ∀cenv tenv ty tv v.
    evaluate_type tenv ty = SOME tv ∧
    value_has_type tv v ∧ well_formed_type_value tv
    ⇒
    runtime_mem_footprint v ≤ type_memory_bytes cenv ty
Proof
  cheat
QED

(* ===== Layer 2: bp_ptrs_bounded → alloca_safe_access ===== *)

(* Structural bounds from base_ptr analysis imply runtime memory safety.
   Requires:
   1. bp_ptr_sound: analysis result accurately tracks runtime pointers
   2. bp_ptrs_bounded: every alloca-backed access is within bounds
   3. Coverage: all pointer-derived vars are tracked by the analysis
   4. Memory adequacy: alloca regions fit within vs_memory length

   The coverage condition (3) is the key: in Vyper-compiled code,
   all pointer derivation goes through ALLOCA → ADD → PHI, which
   the analysis tracks. Variables produced by MLOAD, MUL, etc. are
   data (not pointers) and don't need tracking.

   The memory adequacy condition (4) is clause 1 of alloca_safe_access.
   It ensures alloca regions don't extend beyond allocated memory. *)
Theorem bp_ptrs_bounded_imp_alloca_safe_access:
  ∀bp fn s roots.
    bp_ptr_sound bp s ∧
    bp_ptrs_bounded bp fn s ∧
    pointer_derived_vars fn roots ⊆ {v | bp_get_ptrs bp v ≠ []} ∧
    (∀aid off asz.
       FLOOKUP s.vs_allocas aid = SOME (off, asz) ⇒
       off + asz ≤ LENGTH s.vs_memory)
    ⇒ alloca_safe_access fn roots s
Proof
  cheat
QED

(* ===== Layer 3: Lowering produces structurally bounded pointers ===== *)

(* The lowered function's base_ptr analysis result shows all
   alloca-backed accesses are within bounds.

   This holds because:
   1. Lowering emits ALLOCA(N) where N = type_memory_bytes(cenv, ty)
   2. Pointer arithmetic is ADD(base, Lit offset) where offset is a
      compile-time constant derived from type layout (struct field offset,
      array element offset)
   3. Array accesses go through compile_array_subscript which emits
      bounds checks (ASSERT valid) before computing the offset
   4. Bytestring accesses use lengths ≤ declared max (guaranteed by
      type soundness)

   The alloca_inv precondition ensures the Venom state has coherent
   alloca metadata — distinct allocas are disjoint. *)
Theorem lowering_bp_ptrs_bounded:
  ∀selectors ext_fns int_fns fb_fn dispatch bucket_count
    fn_meta_bytes dense_buckets entry_info entry_label
    fn cenv bp s.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label)).ctx_functions ∧
    compile_env_for fn cenv ∧
    alloca_inv s ∧
    bp_result_for fn bp ∧
    well_typed_lowering_inputs cenv  (* source well-typed *)
    ⇒ bp_ptrs_bounded bp fn s
Proof
  cheat
QED

(* ===== Step Preservation ===== *)

(* The lowered code preserves alloca_safe_access across every
   non-terminating, non-external-call instruction step.
   This is the step_preserves_safety oracle specialized to
   lowered code.

   For lowered code this holds because:
   1. ALLOCA instructions extend vs_allocas without changing existing
      regions; alloca_inv is preserved (proven in venomInstProofs)
   2. MSTORE/MLOAD don't change vs_allocas or pointer values
   3. ASSIGN/PHI/ADD/SUB propagate pointer values with same bounds
   4. The bounds checks emitted by the lowering survive execution
   5. Non-pointer instructions can't increase pointer-derived values
      beyond their alloca region

   The well_typed_lowering_inputs precondition connects to type
   soundness: well-typed execution preserves value_has_type, which
   ensures runtime lengths stay ≤ declared capacity. *)
Theorem lowering_step_preserves_safety:
  ∀selectors ext_fns int_fns fb_fn dispatch bucket_count
    fn_meta_bytes dense_buckets entry_info entry_label
    fn cenv roots.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label)).ctx_functions ∧
    compile_env_for fn cenv ∧
    well_typed_lowering_inputs cenv
    ⇒ step_preserves_safety fn roots
Proof
  cheat
QED

(* ===== Layer 1: Main Theorem ===== *)

(* For a well-typed Vyper source, the lowered function satisfies
   alloca_safe_access at the initial execution state, and
   step_preserves_safety ensures it holds at every reachable state.

   The theorem says: starting from an initial Venom state where
   alloca_inv holds (bump allocator invariant), every memory access
   through an alloca-backed pointer stays within the allocated region.

   This is the theorem that downstream consumers (concretize_mem_loc,
   codegen) actually need. It abstracts away all pointer analysis
   details — consumers only see alloca_safe_access.

   Preconditions:
   - well_typed_lowering_inputs: source is well-typed (enables
     type soundness, which ensures runtime values match declared types)
   - alloca_inv s: Venom state has coherent alloca metadata
   - compile_env_for: compile_env accurately reflects the function
     (connects type_memory_bytes to the actual ALLOCA sizes)
   - Initial state: memory exists for alloca regions (clause 1) *)
Theorem lowering_alloca_safe_access:
  ∀selectors ext_fns int_fns fb_fn dispatch bucket_count
    fn_meta_bytes dense_buckets entry_info entry_label
    fn cenv s.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label)).ctx_functions ∧
    compile_env_for fn cenv ∧
    alloca_inv s ∧
    well_typed_lowering_inputs cenv ∧
    (∀aid off asz.
       FLOOKUP s.vs_allocas aid = SOME (off, asz) ⇒
       off + asz ≤ LENGTH s.vs_memory)
    ⇒ alloca_safe_access fn (alloca_roots fn) s
Proof
  cheat
QED

(* ===== Combined: Safety at every reachable state ===== *)

(* For any state reachable from an initial state satisfying the
   lowering preconditions, alloca_safe_access holds.

   This composes lowering_alloca_safe_access (initial state) with
   lowering_step_preserves_safety (preservation under execution)
   to get the full invariant.

   The "reachable" predicate characterizes states reachable by
   executing non-terminating, non-external-call instructions from
   the initial state. External calls (INVOKE) modify the context
   but the callee's safety follows from the same theorem applied
   to the callee function. *)
Theorem lowering_alloca_safe_access_reachable:
  ∀selectors ext_fns int_fns fb_fn dispatch bucket_count
    fn_meta_bytes dense_buckets entry_info entry_label
    fn cenv s s'.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label)).ctx_functions ∧
    compile_env_for fn cenv ∧
    alloca_inv s ∧
    well_typed_lowering_inputs cenv ∧
    (∀aid off asz.
       FLOOKUP s.vs_allocas aid = SOME (off, asz) ⇒
       off + asz ≤ LENGTH s.vs_memory) ∧
    reachable_by_execution fn s s'
    ⇒ alloca_safe_access fn (alloca_roots fn) s'
Proof
  cheat
QED

(* ===== Auxiliary Definitions (to be refined) ===== *)

(* compile_env_for fn cenv: cenv accurately reflects fn's types
   and variable layout. This connects type_memory_bytes(cenv, ty)
   to the actual ALLOCA sizes in fn. Placeholder — exact
   definition depends on how compile_env is constructed. *)

(* well_typed_lowering_inputs cenv: the Vyper source from which
   cenv was derived is well-typed. Enables eval_preserves_swt.
   Placeholder — will be refined once we know what preconditions
   eval_preserves_swt needs on the Vyper side. *)

(* bp_result_for fn bp: bp is a valid analysis result for fn.
   Placeholder — will connect to bp_analyze_function or equivalent. *)

(* reachable_by_execution fn s s': s' is reachable from s by executing
   non-terminating, non-external-call instructions of fn.
   Uses run_block or step_inst in some bounded fashion.
   Placeholder — exact definition to be determined. *)
