Theory extRetNormalizeRangePtr
Ancestors
  bodyPtrDefs exprLoweringProps venomMemDefs compileEnv exprSimTypedAlloc

(* Whole lowered-buffer provenance, not concrete allocation membership. *)
Theorem ptr_buf_ok_range:
  !ce e op G s w n.
    ptr_buf_ok ce e op G s /\ eval_operand op s = SOME w /\
    type_memory_bytes ce (lowered_value_type ce e) = n /\ n <> 0 ==>
    ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
      b <= w2n w /\ w2n w + n <= b+sz
Proof
  simp[ptr_buf_ok_def] >> metis_tac[]
QED

Theorem covered_range_strict_bound:
  !(b:num) a n sz.
    b <= a /\ a+n <= b+sz /\ b+sz < dimword (:256) ==>
    a+n < dimword (:256)
Proof
  rpt strip_tac >> decide_tac
QED

(* Concrete allocation bounds must be obtained independently of G. *)
Theorem stmt_state_rel_alloca_end_bound:
  !ctx fn ce cx es s aid b sz.
    stmt_state_rel ctx fn ce cx es s /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    b+sz < dimword (:256)
Proof
  rpt strip_tac >>
  fs[stmt_state_rel_def] >>
  drule alloca_room_next_lt >>
  fs[alloca_inv_def, alloca_next_valid_def] >>
  first_x_assum drule >> decide_tac
QED

(* Boundary probes: dynamic capacity is not the live read window. Even an
   outer empty dynamic array has a header; empty tuples have no read window. *)
Theorem normalization_range_shape_probes:
  !ce.
    type_memory_bytes ce (TupleT []) = 0 /\
    type_memory_bytes ce
      (ArrayT (ArrayT (TupleT []) (Dynamic 3)) (Dynamic 2)) = 96 /\
    type_memory_bytes ce (ArrayT (TupleT []) (Dynamic 0)) = 32
Proof
  simp[type_memory_bytes_def]
QED

(* CONTRACT AUDIT (not assertions of contextual implication).

   stmtLowering:1055-1072 sets sty = lowered_value_type ce e both in
   needs_normalize and in compile_store_memory_typed. Thus ptr_buf_ok's
   whole-buffer size is exactly the compiler's SOURCE size. No replacement
   by expr_type e is justified (internal calls and bytelike producers differ).
   expr_sim_ptr:234-241 provides ptr_buf_ok for non-word expr_type e;
   needs_normalize tests non-word DESTINATION ty. Bridging these tests is a
   typing obligation, not a consequence of needs_normalize alone.

   expr_post supplies expr_val_at at expr_type e, not sty. Its concrete
   placement is only val_footprint and may be the zero-footprint disjunct.
   stmt_state_rel_alloca_end_bound supplies strict end bounds for concrete
   allocations. It cannot be applied to a FLOOKUP G entry: no allocation id
   occurs in ptr_buf_ok_range. Whole G coverage therefore solves access_ok's
   mathematical interval containment, NOT concrete full-size placement or
   strict no-wrap. S1 compile_return_normalize_frag:356-361 needs both and
   cannot simply be invoked from this boundary.

   Actual source reads in context:673-807 (offsets are natural, subject to
   separate no-wrap proofs for emitted word ADD/MUL):
   * scalar: MLOAD [src], 32 bytes;
   * bytes: MLOAD header, then MCOPY of 32 + runtime length (not padding);
   * fixed bulk: count * source element size when sizes equal;
   * dynamic bulk: header MLOAD, then length * element size at src+32;
   * nonbulk arrays: child window at src+i*source stride (plus 32 for dyn);
   * tuple: child at cumulative source type sizes;
   * struct: child at cumulative metadata source sizes;
   * fallback: destination-size MCOPY, must exclude incompatible type pairs
     using typing, not infer destination size <= source size universally.
   Zero-size copy branches must avoid demanding provenance or no-wrap of a
   non-read address; dynamic zero-length values still read their header.

   Proposed implementation contract: retain ptr_buf_ok for maximum ghost
   coverage, but obtain address arithmetic bounds for actual read windows
   from robust source representation plus expr_val_at's footprint placement,
   with a separate local-region bound. Recursive child pointers inherit G's
   root allocation and source-footprint window; do not demand full declared
   capacity in a concrete allocation for each child. Fresh destination needs
   full destination capacity and separation from live source windows. Before
   implementing, prove that the lowered source representation/type (including
   internal calls) and non-word condition are supplied by the Return context.
   None of these outstanding implications is a frozen-theorem counterexample.
*)
