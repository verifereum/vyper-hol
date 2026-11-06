(* C1.4.6: static annotation feasibility test, NOT a universal invariant.

   Stress syntax (all annotations well typed and scalar):
     IfExp ty c0
       (IfExp ty c1 (TypeBuiltin ty Convert ty [Name ty x])
                    (Call ty (IntCall id) args drv))
       (TypeBuiltin ty Convert ty [Name ty y]).
   Choose ty = BaseT (UintT 256).  This exercises a real forwarding conversion,
   not a claim that Convert always creates a new variable.  Ordinary parent
   expr_sim_ptr and expr_vv_sim_ptr are the ONLY semantic witnesses allowed.
   No child body predicate or successful source evaluation is used below.

   Candidate certificate, stated without adding a new definition:
     C : (string # num) -> string set
     R : venom_state -> bool
     I s G = R s /\
       (!x. x IN C (s.vs_current_bb,s.vs_inst_idx) ==>
             op_prov G (Var x) = NONE).
   Obligations for the actual counted-path relation:
     INITIAL: I s0 G0.
     EDGE: !G tn s k H tm u. I s G /\
       gas_path_ptr_edge D 0 ctx fn PG G tn s k H tm (OK u) ==> I u H.
     ENDPOINT: !s G. I s G /\
       s.vs_current_bb = sb.cs_current_bb /\
       s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
       op_prov G op = NONE.
   For literal op endpoint is unconditional.  For Var r it needs r in C
   at that endpoint.  Dead/exiting edges do not require I on a non-OK state.
   A generic gas_path_ptr_ind proof would preserve I, but would say NOTHING
   about compiler synthesis of C or R.  No generic lemma is added here.

   Static transfer table on the stress fragment:
   * Entry: C may be empty, because G0 on fresh temporaries is unrestricted.
     Local pointer variables are covered, not untagged.
   * Name unwrap MLOAD: add its fresh output to C.  The pointer address itself
     is not added.  Uint256 avoids the separate BytesV representation issue.
   * Convert Uint256 -> Uint256: compile_type_convert returns original op;
     preserve its membership in C.  For narrowing, comparison temporaries
     are fresh; assertions terminate or preserve that membership normally.
   * Call: compile_call returns LocatedValue of declared type; static metadata
     equality identifies ty.  INVOKE is atomic in gas_path_ptr_edge, not a
     jump into callee blocks in fn.  A successful INVOKE removes provenance
     of caller outputs, and leaves other caller variables alone.  Return
     buffer pointer remains tagged.  store_multi_results and actual unwrap
     load must be included in region/layout; add ONLY final load output to C.
   * Inner and outer arm ASSIGN [operand] [r]: add r if operand is in C (or
     is literal).  No fresh-instruction-ID condition implies this transfer:
     it follows from out_prov copying first_prov of that operand.
   * JMP and JNZ: transfer through BOTH block-entry alternatives of the actual
     gas_path_ptr_edge, not just raw jump.  With no leading PHIs at target,
     entry_prov is identity.  With PHIs, every required result variable needs
     an appropriate selected incoming clean operand.  Completed compiled
     arm blocks begin with known instructions and have no PHI prefix here.
   * Join: intersection of incoming sets retains result r because both arms
     ASSIGN a clean word.  At inner exit, r feeds the outer arm ASSIGN; at
     outer exit, final output is its shared result variable.
   This table explains the INTENDED fragment traversal using syntax equations
   only.  It does not establish EDGE for all steps of the supplied witness.

   Exact interface checks and obstruction:
   fragGasPathPtrScript.sml:23-50 defines gas_path_ptr_edge.  Its normal
   nonterminator alternative advances the index and uses ghost_step.  The
   terminator entry alternative (38-46) evaluates PHIs and uses entry_prov fn
   t G.  The raw jump alternative (47-49) leaves G and tn unchanged at the
   block start.  Both must satisfy EDGE.  The path relation at 53-62 allows
   arbitrary finite concatenation; no first-arrival or confinement predicate
   occurs.  gas_summary_ptr_at_def:67-76 requires LENGTH marks and source
   equality for every tail, but still imposes no first-arrival restriction.

   fragExec.fn_has_code_def (Script:112-118), EXACT signature:
     fn_has_code st st' fn <=>
       (!bb. MEM bb (emitted_blocks st st') ==>
             lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
       ?bb. lookup_block st'.cs_current_bb fn.fn_blocks = SOME bb /\
            isPREFIX st'.cs_current_insts bb.bb_instructions.
   venomWf.fn_inst_ids_distinct_def (Script:513-517), EXACT signature:
     fn_inst_ids_distinct fn <=> ALL_DISTINCT
       (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)).
   Neither constrains outputs or jumps of the final block suffix, nor forces
   the whole function to come from the compiler.  New instruction IDs can
   write the SAME result variable.  stmt_state_rel's code side does not turn
   this prefix relation into a definition-uniqueness or region-closure fact.

   In the stress shape sb is new_block exit_lbl with empty instruction prefix
   (exprLowering.compile_expr_def:2942-2969).  Consequently fn_has_code allows
   an arbitrary suffix at the exit block.  Consider the layout extension
     exit: ASSIGN [Var p] [result]; JMP [Label exit]
   with new distinct instruction IDs and p an older covered local pointer.
   For the intended clean arrival at (exit,0), the FIRST suffix instruction
   copies p's SOME provenance into result.  The raw jump alternative can
   return to (exit,0), retaining that provenance.  Thus any certificate that
   insists result is clean at every (exit,0) and is closed on all such edges
   must either exclude the suffix traversal using R, or prove it impossible.
   R = 'within emitted region including endpoint' is NOT closed: at endpoint
   the suffix is a genuine executable edge.  R = 'not past first endpoint'
   is history-dependent and not known of the supplied witness.  A history
   flag alone does not help: later endpoint must still imply cleanliness.
   This is an explicit failed transfer/layout obligation, not a checked
   counterexample to the frozen task.  Value equality and gas marks have not
   been constructed for this layout extension; no claim is made that this
   extension is necessarily selected by the ordinary semantic witness.

   Leading PHIs at this same empty-prefix exit block are also unconstrained.
   entry_prov (ptrDisciplineScript.sml:220) applies phis_prov to its leading
   PHIs, whereas the endpoint requires index 0.  The entered alternative
   lands at phi_prefix_length, so adding a PHI does NOT directly prove a bad
   endpoint: one must analyze all edges and indices.  Treating entry_prov as
   identity merely because the compiler emitted no PHIs would be unsound.

   Mapping to frozen RHS use site:
     AVAILABLE                     DOES NOT SUPPLY
     lower_value compile equation  whole-function compiler origin
     fn_has_code sa sb func        suffix restrictions or first-arrival
     fn_inst_ids_distinct func     variable definition uniqueness
     stmt_state_rel + ghost_inv    NONE provenance for fresh result vars
     parent body_expr_ptr_ok       child semantic outcomes
     parent ordinary outcome       prefix ending at first visit to endpoint
     endpoint expr_post            ghost provenance of scalar result
     ghost_kept                    restrictions on fresh result variable
   expr_post is in loweringPostsScript.sml:251-266 and concerns value/state,
   older variables and allocations, not result provenance.  ghost_inv and
   ghost_kept are in bodyPtrDefsScript.sml:80-105.  ptr_val_ok for word types
   is a taint property, not a no-provenance property.  No separate child
   evaluation theorem was used to derive the static table or obstruction.

   Conclusion: syntax-directed certificates plausibly describe a fragment
   UP TO first arrival, but current assumptions do not establish the global
   EDGE obligation on an arbitrary supplied path.  This architecture has NOT
   yet solved the witness gap.  Exact missing boundary: either a checked
   compiler-prefix restriction on the SAME outcome path (with original marks,
   post and exempt branch retained), or a proof that an unrestricted witness
   can be replaced by such a path WITHOUT changing source gas observations
   or final post.  A first-exit path theorem alone is not that boundary.
   Adding global suffix restrictions to the frozen judgment is forbidden.
   No universal theorem, source repair, or task falsehood follows from this
   negative diagnostic.  Ancestor review should decide whether to investigate
   marked-path normalization or abandon this architecture, not assume R.
*)
Theory augAssignPtrRegionArchitecture
Ancestors
  augAssignPtrEnrichmentArchitecture fragGasPathPtr fragExec venomWf
