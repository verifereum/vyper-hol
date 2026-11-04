(* Bounded runtime probe. General alignment is deliberately not asserted. *)
Theory makeSsaCurrentAlignmentProbe
Ancestors
  makeSsaCurrentSimDefs makeSsaCurrentPhiBatch makeSsaCurrentPhiRuntime
  venomExecSemantics venomState stateFrame finite_map

Definition current_probe_incoming_def:
  current_probe_incoming prev =
    (update_var "b" 2w (update_var "a" 1w (init_venom_state "D")))
      with vs_prev_bb := SOME prev
End

(* Both actual incoming edges are tested. In particular b is already defined
   on the back edge; the later ordinary ASSIGN must not supply its PHI value. *)
Theorem current_probe_whole_prefix:
  !prev. prev = "E" \/ prev = "D" ==>
  eval_phis (current_probe_incoming prev)
    (EL 1 current_probe_loop.fn_blocks).bb_instructions =
    OK (update_var "v" (if prev = "E" then 1w else 2w)
          (current_probe_incoming prev)) /\
  eval_phis (current_probe_incoming prev)
    (EL 1 (FST (make_ssa_current_fn current_probe_supply
      current_probe_loop)).fn_blocks).bb_instructions =
    OK (update_var "formal_var_0" (if prev = "E" then 1w else 2w)
          (current_probe_incoming prev)) /\
  step_inst_base
    (EL 1 (EL 1 (FST (make_ssa_current_fn current_probe_supply
      current_probe_loop)).fn_blocks).bb_instructions)
    (update_var "formal_var_0" (if prev = "E" then 1w else 2w)
      (current_probe_incoming prev)) =
    OK (update_var "v" (if prev = "E" then 1w else 2w)
      (update_var "formal_var_0" (if prev = "E" then 1w else 2w)
        (current_probe_incoming prev)))
Proof
  rpt strip_tac >> gvs[] >> EVAL_TAC
QED

(* DESIGN CHECKPOINT -- signatures below are proposals, NOT proved lemmas.

   Source-linked certificate data must contain the actual insertion result,
   actual tree trace, immutable annotation map A and final allocation history
   H. For a local event
     ev = (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)
   require MEM ev events and current_event_trace A H ev, not merely a pair
   of chosen indices. current_actual_tree_trace supplies events;
   current_tree_trace_events supplies the local trace;
   current_tree_trace_paths supplies the entry environment. Final edge
   rewriting and cleanup must additionally link ren to lookup_block l fn'.
   That last link is NOT a consequence of current_event_trace alone.

   Suggested exact cut predicate, with p the inserted-prefix length:
     cut A ev p i rs E <=>
       ?ap aq xp xq yp yq sm Hm.
         A l = ap ++ aq /\ LENGTH ap = p + i /\
         bb.bb_instructions = xp ++ xq /\ LENGTH xp = p + i /\
         ren = yp ++ yq /\ LENGTH yp = p + i /\
         current_local_trace ap xp s0 rs0 H0 E0 yp sm rs Hm E /\
         current_local_trace aq xq sm rs Hm E yq s1 rs1 H1 E1
   Here ev is destructured as above and must itself be in events.
   p is determined by current_block_provenance fn old bb (A l),
   bb.bb_instructions = pre ++ old.bb_instructions and LENGTH pre = p.
   This uses prefix lengths, not instruction ids: cleanup reassigns ids.

   At OrdinaryCode source index i, require i >= LENGTH (collect_phis
   old.bb_instructions), and cut A ev p i rs E. The output index j is
   derived from the corresponding suffix after simplify_current_phi_prefix,
   including edge rewriting, NOT supplied as an arbitrary positions list.
   Demands should be sets expressed pointwise, avoiding enumeration:
     values H E fn l i st st' <=>
       !v. current_demand fn v l i ==>
         ?n. current_token_name H (E v) = SOME n /\
             lookup_var v st = lookup_var n st'
   Demand equality does not imply IS_SOME: definedness needs a separate
   dynamic-path argument from fn_defs_reach_uses.

   Exact intended theorem shapes (Cert/Entry/Ord are proposed predicates,
   not existing constants; each must be defined from the data above):

   Initialization:
     Cert fn fn' A H events /\ entry_block fn = SOME eb /\
     entry_block fn' = SOME eb' /\ st = init_venom_state eb.bb_label /\
     st' = init_venom_state eb'.bb_label ==>
     Entry fn fn' A H events NONE eb.bb_label st st'
   Real contract initialization must generalize this to the initialized
   call state in fn_bisim, including params, labels, data and frame fields.
   current_token_values_initial covers empty stores only. Entry must retain
   the actual previous edge and a selected-edge demand relation; simply
   using the successor dominator entry environment before PHIs is wrong.

   Whole-prefix correspondence:
     Cert fn fn' A H events /\ Entry fn fn' A H events prev l st st' ==>
     ?post post' copies k.
       eval_phis st old.bb_instructions = OK post /\
       eval_phis st' new.bb_instructions = OK post' /\
       copies = TAKE k (DROP (LENGTH (collect_phis new.bb_instructions))
                                      new.bb_instructions) /\
       LENGTH (collect_phis old.bb_instructions) <=
         LENGTH old.bb_instructions
   This is only the success/batch part. Its companion must specify values
   on retained original-PHI tokens and inserted-PHI tokens separately,
   plus unchanged demanded names outside the write set. The exact token
   equalities come from the cut after ALL PHIs, not a sequential PHI IH.
   current_eval_phis_batch[_lookup,_frame] supply evaluation boundaries;
   current_selected_slots_correspond supplies a single selected pair.
   Missing: selected-slot coverage and definedness on actual dynamic edges,
   injective/separated write names, and old/inserted token value cases.

   Ordered cleanup:
     Cert fn fn' A H events /\ Entry fn fn' A H events prev l st st' /\
     eval_phis st old.bb_instructions = OK post /\
     eval_phis st' new.bb_instructions = OK post' ==>
     ?ready. copies_run copies post' = OK ready /\
       Ord fn fn' A H events l
         (LENGTH (collect_phis old.bb_instructions)) post ready
   copies_run must be a new finite sequential ASSIGN/NOP runner, not
   eval_phis. Its list and the output index must be obtained from actual
   simplify_current_phi_prefix_parts and reassign_current_inst_ids.
   Missing: existing PHIs retained by non-degeneracy/single-definition,
   inserted copies read defined retained outputs, copies do not clobber
   other demanded token names, and prefix order supplies every copy read.
   The checked probe above validates exactly one such retained-PHI/copy
   pattern, on entry AND back edge; it is not a general preservation proof.

   Ordinary step (OK case; terminal cases use current_result_agree):
     Cert fn fn' A H events /\ Ord fn fn' A H events l i st st' /\
     step_inst fuel C (EL i old.bb_instructions) st = OK next /\
     ctx_bisim C C' ==>
     ?fuel' next'.
       step_inst fuel' C' (EL j new.bb_instructions) st' = OK next' /\
       Ord fn fn' A H events l (SUC i) next next'
   j must be extracted by Ord, and excludes cleanup-prefix positions.
   current_step_inst_ctx_agree supplies the semantic kernel both ways.
   Missing: convert trace/cut facts to current_outputs_compatible and
   demanded before-output agreement; preserve source-linked positions.

   Successor:
     Cert fn fn' A H events /\ Ord fn fn' A H events l i st st' /\
     step_inst fuel C (EL i old.bb_instructions) st = OK next /\
     step_inst fuel' C' (EL j new.bb_instructions) st' = OK next' /\
     next.vs_current_bb = succ /\ succ <> l ==>
     Entry fn fn' A H events (SOME l) succ next next'
   Also needs a self-edge case: succ <> l cannot be a permanent premise.
   The actual branch/JMP opcode, not changed label alone, detects entry.
   current_actual_demanded_cut_tokens covers only noninserted, cut-clear,
   live-selected variables. current_demand_edge_transfer supplies demand
   transfer. Missing: bridge runtime branch to fn_cfg_edge and handle
   inserted PHI/retained PHI selected operands separately.

   Finite-run boundary, after interfaces above are proved:
     Cert fn fn' A H events /\ Entry fn fn' A H events prev l st st' /\
     ctx_bisim C C' ==>
     (!fuel. terminates (run_blocks fuel C fn st) ==>
       ?fuel'. step_result_rel (run_blocks fuel C fn st)
                              (run_blocks fuel' C' fn' st')) /\
     (!fuel'. terminates (run_blocks fuel' C' fn' st') ==>
       ?fuel. step_result_rel (run_blocks fuel C fn st)
                             (run_blocks fuel' C' fn' st'))
   Argument order matches venomExecSemantics run_blocks_def.
   There is deliberately no same-fuel claim. Administrative copies and
   cross-context INVOKE use existential fuel and need monotonicity when
   composing runs. Frame simulation needs reachable administrative states
   as well as Ord/Entry states; finite terminating transport alone does
   not establish it. No general integration proof is authorized here.
*)

Definition current_probe_ready_def:
  current_probe_ready prev =
    update_var "v" (if prev = "E" then 1w else 2w)
      (update_var "formal_var_0" (if prev = "E" then 1w else 2w)
        (current_probe_incoming prev))
End

Theorem current_probe_ready_values:
  !prev. prev = "E" \/ prev = "D" ==>
    lookup_var "formal_var_0" (current_probe_ready prev) =
      SOME (if prev = "E" then 1w else 2w) /\
    lookup_var "v" (current_probe_ready prev) =
      SOME (if prev = "E" then 1w else 2w) /\
    lookup_var "a" (current_probe_ready prev) = SOME 1w /\
    lookup_var "b" (current_probe_ready prev) = SOME 2w /\
    execution_frame (current_probe_ready prev) =
      execution_frame (current_probe_incoming prev)
Proof
  rpt strip_tac >> gvs[] >> EVAL_TAC
QED
