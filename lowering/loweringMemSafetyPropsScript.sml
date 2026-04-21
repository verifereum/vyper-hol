(*
 * Lowering Memory Safety — Properties
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
 *     all accesses are bounded. ALLOCA(N) where N = type_memory_bytes,
 *     pointer arithmetic via ADD with compile-time-bounded offsets.
 *
 * Key lemma: value_type_fits_alloca
 *   value_has_type tv v ⟹ value_within_alloca_size — bridges
 *   Vyper type soundness to Venom ALLOCA sizing.
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

Theory loweringMemSafetyProps
Ancestors
  loweringMemSafetyDefs basePtrProps vyperTypeSoundness
  vyperTypeSoundnessDefs vyperTyping

(* ===== Key Lemma: Type Soundness → Memory Layout ===== *)

(* A well-typed value's runtime structure fits within the ALLOCA
   sized by type_memory_bytes for the corresponding type.
   This is the core fact connecting Vyper type soundness to memory
   safety: the ALLOCA is sized by the declared type capacity (via
   type_memory_bytes), and type soundness ensures runtime lengths
   respect those capacities.

   For DynArray[T,N]: value_has_type (ArrayTV tv (Dynamic N)) v ⟹
     LENGTH vs ≤ N, so the MLOAD'd length word ≤ N and
     bounds check (idx < len) correctly rejects OOB access.
   For Bytes[M]: byte data length ≤ M.
   For String[M]: string length ≤ M.
   Fixed arrays, structs, base types: structurally exact. *)
Theorem value_type_fits_alloca:
  ∀cenv tenv ty tv v.
    evaluate_type tenv ty = SOME tv ∧
    value_has_type tv v ∧ well_formed_type_value tv
    ⇒
    value_within_alloca_size cenv ty v
Proof
  cheat
QED

(* ===== Layer 2: bp_ptrs_bounded → alloca_safe_access ===== *)

(* Structural bounds from base_ptr analysis imply runtime memory safety.
   Requires:
   1. bp_ptr_sound: analysis result accurately tracks runtime pointers
   2. bp_ptrs_bounded: every alloca-backed access is within bounds
   3. Coverage: all pointer-derived vars are tracked by the analysis
   4. Memory adequacy: alloca regions fit within vs_memory length *)
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
   Holds because:
   1. Lowering emits ALLOCA(N) where N = type_memory_bytes(cenv, ty)
   2. Pointer arithmetic is ADD(base, Lit offset) where offset is a
      compile-time constant derived from type layout
   3. Array accesses go through compile_array_subscript which emits
      bounds checks (ASSERT valid) before computing the offset
   4. Bytestring accesses use lengths ≤ declared max (guaranteed by
      type soundness via value_type_fits_alloca) *)
Theorem lowering_bp_ptrs_bounded:
  ∀selectors ext_fns int_fns fb_fn dispatch bucket_count
    fn_meta_bytes dense_buckets entry_info entry_label
    fn cenv bp s.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label)).ctx_functions ∧
    cenv_matches_fn cenv fn ∧
    alloca_inv s ∧
    bp_result_is fn bp ∧
    well_typed_lowering cenv
    ⇒ bp_ptrs_bounded bp fn s
Proof
  cheat
QED

(* ===== Step Preservation ===== *)

(* The lowered code preserves alloca_safe_access across every
   non-terminating, non-external-call instruction step.
   This is the step_preserves_safety oracle specialized to
   lowered code. *)
Theorem lowering_step_preserves_safety:
  ∀selectors ext_fns int_fns fb_fn dispatch bucket_count
    fn_meta_bytes dense_buckets entry_info entry_label
    fn cenv roots.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label)).ctx_functions ∧
    cenv_matches_fn cenv fn ∧
    well_typed_lowering cenv
    ⇒ step_preserves_safety fn roots
Proof
  cheat
QED

(* ===== Layer 1: Main Theorem ===== *)

(* For a well-typed Vyper source, the lowered function satisfies
   alloca_safe_access at the initial execution state.
   This is the theorem that downstream consumers (concretize_mem_loc,
   codegen) actually need. It abstracts away all pointer analysis
   details — consumers only see alloca_safe_access. *)
Theorem lowering_alloca_safe_access:
  ∀selectors ext_fns int_fns fb_fn dispatch bucket_count
    fn_meta_bytes dense_buckets entry_info entry_label
    fn cenv s.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label)).ctx_functions ∧
    cenv_matches_fn cenv fn ∧
    alloca_inv s ∧
    well_typed_lowering cenv ∧
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
   Composes lowering_alloca_safe_access (initial) with
   lowering_step_preserves_safety (preservation). *)
Theorem lowering_alloca_safe_access_reachable:
  ∀selectors ext_fns int_fns fb_fn dispatch bucket_count
    fn_meta_bytes dense_buckets entry_info entry_label
    fn cenv s s'.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label)).ctx_functions ∧
    cenv_matches_fn cenv fn ∧
    alloca_inv s ∧
    well_typed_lowering cenv ∧
    (∀aid off asz.
       FLOOKUP s.vs_allocas aid = SOME (off, asz) ⇒
       off + asz ≤ LENGTH s.vs_memory) ∧
    reachable_by_execution fn s s'
    ⇒ alloca_safe_access fn (alloca_roots fn) s'
Proof
  cheat
QED
