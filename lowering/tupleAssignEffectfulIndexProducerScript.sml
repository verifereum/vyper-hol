(* Producer checkpoint: a non-view conditional can still return a borrowed
   memory pointer.  This is compiler provenance evidence, not a counterexample
   to tuple_assign_effectful_index. *)
Theory tupleAssignEffectfulIndexProducer
Ancestors
  exprLowering stmtLowering compileEnv vyperState

Theorem ifexp_memory_arm_borrow_probe[local]:
  !ce rt at p sa.
    ~is_word_type at /\ p.ptr_location = LocMemory /\
    same_memory_layout ce at rt ==>
    compile_ifexp_arm ce rt at (LocatedValue at p) sa = (p.ptr_operand,sa)
Proof
  simp[compile_ifexp_arm_def, unwrap_value_def, comp_return_def]
QED

Theorem ifexp_tuple_unstaged_probe[local]:
  !ann cond left right vv.
    ~(is_memory_view (IfExp ann cond left right) /\
      vv_location vv = SOME LocMemory)
Proof
  simp[is_memory_view_def]
QED

(* A reachable arm producer, rather than an arbitrary expr_post: a local
   aggregate Name followed by equal-layout arm conversion emits no copy. *)
Theorem ifexp_local_arm_no_allocation_probe[local]:
  !ce rt at id off cap sa.
    FLOOKUP ce.ce_vars id = SOME (MemLoc off cap) /\
    ~is_word_type at /\ same_memory_layout ce at rt ==>
    (do vv <- compile_name_vv ce at id;
        compile_ifexp_arm ce rt at vv od) sa = (Lit (n2w off),sa)
Proof
  simp[compile_name_vv_def, compile_ifexp_arm_def, unwrap_value_def,
       contextTheory.mk_ptr_def, comp_return_def, comp_bind_def]
QED

(* Source conditionals retain the local place, including its full path. *)
Theorem conditional_tuple_place_probe[local]:
  !cx id path s tvs.
    place_type_value cx (MemoryPlace id path) s = (INL (TupleTV tvs),s) ==>
    conditional_result cx (PlaceR (MemoryPlace id path)) s =
      (INL (PlaceR (MemoryPlace id path)),s)
Proof
  simp[conditional_result_def, bind_def, return_def]
QED

(* BORROWED CHECKPOINT LEDGER (not a claimed suffix theorem).

   Proposed index boundary, at ONE target_post endpoint:
     expr_sim_inv ce cx env ee /\ stmt_state_rel ctx fn ce cx ee s /\
     local_region ce ee.scopes s name base cap /\
     local_path_at ce cx name off (TupleTV tvs) /\
     off + type_memory_size (TupleTV tvs) <= cap /\
     target_post ctx fn ce cx ee ca cb s ff pv vt r t /\
     [actual saved RHS place provenance and successful typed target prefix]
       ==>
     mem_bytes_at (base+off) (type_memory_size (TupleTV tvs)) t.vs_memory =
       mem_bytes_at (base+off) (type_memory_size (TupleTV tvs)) s.vs_memory.

   Available: expr_sim_inv from the frozen hypotheses and successful-prefix
   preservation; region/path/containment from the borrowed snapshot alternative
   and tuple_place_local_path_extent; target_post from the target bridge.
   Actual-execution obligation: associate the saved RHS MemoryPlace path with
   this pointer after conditional-result, read_result, unwrap and tuple loads.
   conditional_tuple_place_probe preserves that source path, while
   read_result_def reduces the final RHS read to read_place. Equal-layout
   memory arm conversion retains the pointer. A full branch-to-pointer
   provenance theorem is still unresolved, not supplied by expr_post alone.

   Unresolved index obligation: target_post only provides locals_kept.
   Its first byte clause excludes EVERY dynarray_len_at, including dynamic
   headers INSIDE a tuple, since type_step_offset permits tuple steps.
   It therefore does not imply the proposed whole-tuple frame. Its other
   whole-region clause needs unchanged lookup_scopes, false after popping
   an ancestor array. Actual Pop lowering changes only its selected length
   word (exprSimPopNestedLocalSuffix:77); writable mutable_place_path forbids
   tuple descent, so a separate restricted-header geometry frame looks
   appropriate. Pop of an ancestor can invalidate the saved path's liveness
   without touching its old payload. Nested expressions can consume Pop;
   lifting this restricted frame through their evaluation is unresolved.
   Calls must use their actual local/callee frames, not a metadata assumption
   or an assertion that arbitrary calls preserve caller scopes. No actual
   typed/support-valid payload-overwrite counterexample has been established.

   Proposed store boundary, at SAME correctness endpoint t:
     [antecedent of tuple_place_equal_value_run_frame] /\
     local_region ce ee.scopes s name base cap /\
     base <= a /\ a+n <= base+cap /\
     (loc = LocMemory ==> a+n <= w2n w \/
       w2n w + type_memory_size stv <= a)
       ==> ?t. [that theorem's correctness, gas and frame conclusions] /\
          mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory.
   This is an immediate use of its final local-region clause, not a second
   execution witness. Remaining antecedents include nonword source end bound
   and separation from new allocations, destination end+64 bound, positive
   slot size, storage region, and local declared/evaluated entry agreement.
   Typing/code/operand facts come from the loop and target_post; deriving the
   arithmetic/allocation bridges at that endpoint remains separate work.

   Earlier-write geometry audit: tuple_place_borrow_destination_apart uses
   purity ONLY to derive int_calls_target=[] and hence call safety. It also
   assumes eval_base_place returns in the same ee, so it cannot be applied
   literally to an effectful prefix. At the post-index state the geometric
   argument needs actual eval_target_place reachability, well_typed_target,
   and call safety to obtain mutable_place_path, not just place_ptr_rel.
   Same-root descendants crossing TupleTV are forbidden. Ancestor and equal
   paths are blocked by the target's member type versus whole tuple type
   (tuple_place_tuple_barrier_apart). Divergent array/struct paths use
   tuple_place_paths_apart. Different roots use local_ptrs_rel disjointness.
   Containment and declared-local alignment must be retained at ff via
   scopes-domain/progress and env consistency, not saved path liveness.
   Generalizing that reachable geometry to distinct source states is still
   an unproved boundary; these notes do not silently remove its hypotheses.
*)
