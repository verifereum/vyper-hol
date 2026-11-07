(* Production-fuel boundary diagnostics, not convergence certificates. *)
Theory concretizePtrFuelProbe
Ancestors concretizeMemLocDefs venomWf
Libs wordsLib

Definition ptr_fuel_leaf_def:
  ptr_fuel_leaf = mk_raw_function "fuel_leaf"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 411 ALLOCA [Lit (32w:256 word)] ["b"];
        mk_inst 412 MSTORE [Var "b"; Lit 7w] [];
        mk_inst 413 RET [] []] |>]
End

Definition ptr_fuel_leaf_done_def:
  ptr_fuel_leaf_done = THE (concretize_function_fuel_in_context
    (concretize_memloc_fuel ptr_fuel_leaf)
    (mk_venom_context [ptr_fuel_leaf] (SOME "fuel_leaf")) [] ptr_fuel_leaf)
End

Definition ptr_fuel_loop_def:
  ptr_fuel_loop = mk_raw_function "fuel_loop"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 401 ALLOCA [Lit (32w:256 word)] ["a"];
        mk_inst 402 MSTORE [Var "a"; Lit 1w] [];
        mk_inst 403 JMP [Label "loop"] []] |>;
     <| bb_label := "loop"; bb_instructions :=
       [mk_inst 404 PHI [Label "entry"; Var "a"; Label "loop"; Var "q"] ["p"];
        mk_inst 405 INVOKE [Label "fuel_leaf"] [];
        mk_inst 406 MLOAD [Var "p"] ["x"];
        mk_inst 407 ADD [Var "p"; Lit 0w] ["q"];
        mk_inst 408 JNZ [Lit 1w; Label "loop"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 409 STOP [] []] |>]
End

Definition ptr_fuel_ctx_def:
  ptr_fuel_ctx = mk_venom_context [ptr_fuel_leaf_done; ptr_fuel_loop]
    (SOME "fuel_loop")
End

Definition ptr_fuel_bp_def:
  ptr_fuel_bp n = bp_analyze_fuel n (cfg_analyze ptr_fuel_loop) ptr_fuel_loop
End

Definition ptr_fuel_ml_def:
  ptr_fuel_ml n = ml_iterate_fuel n
    (ptr_fuel_bp (concretize_memloc_fuel ptr_fuel_loop))
    (\name. incr_ssort alloc_to (MAP FST (callee_mems_used ptr_fuel_ctx name)))
    (\a. if context_alloca_size ptr_fuel_loop
       (imported_mems_used ptr_fuel_ctx ptr_fuel_loop) a = 0 then NONE
       else SOME (context_alloca_size ptr_fuel_loop
         (imported_mems_used ptr_fuel_ctx ptr_fuel_loop) a))
    [] (cfg_analyze ptr_fuel_loop) ptr_fuel_loop FEMPTY FEMPTY
End

Theorem ptr_fuel_parameters:
  concretize_memloc_fuel ptr_fuel_leaf = 20 /\
  concretize_memloc_fuel ptr_fuel_loop = 52 /\
  ptr_fuel_leaf_done.fn_mems_used = [(Allocation 411,0,32)] /\
  ssa_form ptr_fuel_loop
Proof
  EVAL_TAC >> simp[]
QED

Theorem ptr_fuel_bp_closed:
  bp_one_pass ptr_fuel_loop (cfg_analyze ptr_fuel_loop).cfg_dfs_pre
    (ptr_fuel_bp 52) = (F, ptr_fuel_bp 52)
Proof
  EVAL_TAC >> simp[finite_mapTheory.fmap_eq_flookup,
                   finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem ptr_fuel_bp_truncated:
  FST (bp_one_pass ptr_fuel_loop (cfg_analyze ptr_fuel_loop).cfg_dfs_pre
    (ptr_fuel_bp 0)) = T /\
  find_base_allocas (ptr_fuel_bp 52) (Var "q") = [Allocation 401] /\
  find_base_allocas (ptr_fuel_bp 0) (Var "q") = []
Proof
  EVAL_TAC
QED

Theorem ptr_fuel_ml_closed:
  ml_one_pass (ptr_fuel_bp 52)
    (\name. incr_ssort alloc_to (MAP FST (callee_mems_used ptr_fuel_ctx name)))
    (\a. if context_alloca_size ptr_fuel_loop
       (imported_mems_used ptr_fuel_ctx ptr_fuel_loop) a = 0 then NONE
       else SOME (context_alloca_size ptr_fuel_loop
         (imported_mems_used ptr_fuel_ctx ptr_fuel_loop) a))
    [] (cfg_analyze ptr_fuel_loop) ptr_fuel_loop
    (FST (ptr_fuel_ml 52)) (SND (ptr_fuel_ml 52)) =
    (F, FST (ptr_fuel_ml 52), SND (ptr_fuel_ml 52))
Proof
  EVAL_TAC >> simp[finite_mapTheory.fmap_eq_flookup,
                   finite_mapTheory.FLOOKUP_UPDATE]
QED

Definition ptr_fuel_ls_def:
  ptr_fuel_ls n = context_mem_livesets n ptr_fuel_ctx ptr_fuel_loop
    (ptr_fuel_bp 52) (cfg_analyze ptr_fuel_loop)
End

Theorem ptr_fuel_loop_demand:
  MEM ("loop",1)
    (THE (FLOOKUP (ptr_fuel_ls 52) (Allocation 401))) /\
  MEM ("loop",1)
    (THE (FLOOKUP (ptr_fuel_ls 52) (Allocation 411))) /\
  ptr_fuel_ml 0 = (FEMPTY,FEMPTY) /\
  FLOOKUP (ptr_fuel_ls 0) (Allocation 411) = NONE
Proof
  EVAL_TAC
QED

Theorem ptr_fuel_layout_exists:
  compute_function_layout_fuel_in_context 52 ptr_fuel_ctx [] ptr_fuel_loop <> NONE
Proof
  EVAL_TAC
QED

Theorem ptr_fuel_layout_positions:
  FLOOKUP (THE (compute_function_layout_fuel_in_context 52
    ptr_fuel_ctx [] ptr_fuel_loop)).cl_positions (Allocation 401) = SOME 32 /\
  (THE (compute_function_layout_fuel_in_context 52
    ptr_fuel_ctx [] ptr_fuel_loop)).cl_eom = 64
Proof
  EVAL_TAC
QED

Theorem ptr_fuel_truncated_layout:
  compute_function_layout_fuel_in_context 0 ptr_fuel_ctx [] ptr_fuel_loop <> NONE /\
  FLOOKUP (THE (compute_function_layout_fuel_in_context 0
    ptr_fuel_ctx [] ptr_fuel_loop)).cl_positions (Allocation 401) = SOME 32
Proof
  EVAL_TAC
QED

(* Production boundary audit (no universal convergence theorem).

   Dispatcher source: execute_configured_fn_pass, VP_ConcretizeMemLoc,
   calls concretize_function_fuel_in_context (concretize_memloc_fuel fn)
   with the current unit context and ctx_global_reserved.  The exact bound
   is 4 * (LENGTH (fn_insts fn) + LENGTH fn.fn_blocks + 1).
   The context path runs fuel analyses if there are multiple local allocas
   OR imported_mems_used is nonempty; otherwise it uses checked linear
   completion.  This fixture exercises the imported-metadata path with
   one local alloca.  The leaf's metadata is computed from its actual
   successful concretization, not supplied as an arbitrary summary.

   bp_iterate_fuel 0 returns its current map; SUC does bp_one_pass and
   recurs only when changed. ml_iterate_fuel 0 returns current (la,us);
   SUC computes ml_one_pass and recurs only when changed. Neither returns
   an exhaustion/error flag. mem_liveness_analyze_fuel always computes
   livesets and store marking from the returned states, even at fuel 0.
   Checked layout completion checks coverage/physical layout endpoints;
   it does not assert that the dataflow states are closed.

   Changed flags:
   BP compares bp_get_ptrs at each single output; block/pass flags OR all
   instruction flags. Existing concretizeAnalysisBoundaryTheory
   bp_one_pass_stable_ptrs establishes observable lookup stability, not
   map-domain equality. Avoid adding a duplicate lemma here.
   ML backward blocks compare ONLY (label,0); forward blocks compare ONLY
   (label,PRE length). The two flags are ORed by ml_one_pass. A universal
   early-stop proof must derive stability of every interior entry from
   stable boundaries and deterministic block transfer, including empty
   blocks and the actual traversal orders; the flags alone are not such
   a proof. ptr_fuel_ml_closed checks ALL maps on this fixture, not merely
   its boundary flags.

   Concrete outcome: at production fuel 52 both maps equal one further
   transfer with changed=F. Local allocation 401 and imported allocation
   411 both cover the INVOKE address (loop,1). Caller 401 is at 32, eom 64,
   separated from imported [0,32). With deliberately zero analysis fuel,
   imported demand is absent, but checked completion still yields 401 at
   32 on THIS fixture. Thus the truncation control is a harmless fallback
   here, not evidence of an unsafe production placement. It also shows
   that a missing analysis fact alone is not a task counterexample.
   These are static analyses of the CFG loop; no concrete frame_reachable
   trace, whole-context ptr_discipline, or universal adequacy is claimed.

   Remaining general contracts (all unproved by these examples):
   1. BP closure/coverage: under SSA, definite assignment, all_reachable,
      unique labels/IDs, affine/PHI restrictions from fn_ptr_ok and actual
      cfg_analyze traversal coverage, production bp covers every reachable
      local allocation origin. Closure should be expressed by bp_get_ptrs
      equivalence, allowing absent and explicit [] entries to agree.
   2. Quantitative BP propagation: use variable-definition dependencies,
      with finite local allocation keys and normalised offset abstract
      values. Candidate rank counts unpropagated origin memberships plus
      exact-to-unknown offset widenings. A naive finite-height bound is a
      PRODUCT of variables and allocation keys, not the supplied linear
      fuel. To justify 4*(I+B+1), establish a parallel per-origin path bound
      on propagation/widening rounds. Offset transfer and PHI normalisation
      must be shown monotone in that abstraction; it is not assumed from
      sorted-list invariants or from these finite equalities.
   3. For fixed sound bp and exact callee metadata/size functions, backward
      liveat transfer must be sound for future untainted-read demands;
      its kill needs singleton-runtime identity and exact overwrite, with
      the non-exempt containment guard from the SemanticProbe report.
      Forward used must cover first reads as well as prior stores and
      INVOKEs. Parameter origins require suspended-caller retention.
   4. ML quantitative closure: fixed bp, finite well-formed CFG traversals,
      fixed sorted summaries and valid allocation sizes. Candidate proof:
      each allocation membership is a Boolean gen/kill dataflow over CFG
      boundaries; propagate along simple paths, bound rounds by block
      count plus an interior materialisation round. Prove distributivity
      and monotonicity for fixed kills, then the actual two Gauss-Seidel
      orders. Naive global rank counts (allocation,address) memberships
      and again does not imply this linear fuel without per-element path
      reasoning. Separately prove full-state early-stop stability.
   5. Even closed analyses need semantic demand soundness, callee summary
      completeness and interference-to-layout separation before relocation
      can use them. No fixed-point example discharges these premises.
*)

Theorem ptr_fuel_leaf_success:
  concretize_function_fuel_in_context (concretize_memloc_fuel ptr_fuel_leaf)
    (mk_venom_context [ptr_fuel_leaf] (SOME "fuel_leaf")) [] ptr_fuel_leaf <>
  NONE
Proof
  EVAL_TAC
QED
