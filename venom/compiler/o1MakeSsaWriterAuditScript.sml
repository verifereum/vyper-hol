Theory o1MakeSsaWriterAudit
Ancestors
  o1MakeSsaSnapshotWitness o1MakeSsaActualNames o1MakeSsaVisitNames list

(* Consumer of a selected ancestor source, not another traversal induction.
   last_name_source supplies the selected (x,v) pair; splitting path_pairs
   determines which snapshot contains it. No dominance premise is needed. *)
Theorem root_ancestor_source_pair:
  MEM e (SND (visit_blocks [] s rs bbs sm tree)) /\
  e.sve_path = pre ++ [(l,is,js)] ++ post /\
  MEM (x,v) (block_output_pairs is js) ==>
  ?a. MEM a (SND (visit_blocks [] s rs bbs sm tree)) /\
    a.sve_label = l /\ a.sve_before = is /\ a.sve_after = js /\
    a.sve_path = pre /\ MEM (x,v) (block_output_pairs a.sve_before a.sve_after)
Proof
  strip_tac >> drule_all root_snapshot_witness >> strip_tac >>
  qexists `a` >> simp[]
QED

(* UNIVERSAL BRIDGE AUDIT -- the statements below are proposals, NOT theorems.

   Case table (all names refer to the pre-simplification output):

   ordinary Var x / visited block:
     actual_final_operand_name gives last_name x x
       (path_pairs e.sve_path ++
        block_output_pairs (TAKE i e.sve_before) (TAKE i e.sve_after)).
     Apply last_name_source to this pair list, not to a global visit order.
     - default: result = x. This does NOT imply no original writer exists,
       nor even that this pair list has no writer (a writer can reuse x).
       Missing: connectivity of the initial spelling under the actual
       insertion algorithm and the unique-return-PC-writer hypothesis.
     - local prefix: selected (x,v) belongs to the TAKE-prefix pair list.
       block_operand_prefix_name and actual_prepared_event_positions locate
       ordinary original writers versus inserted PHIs. Missing: P v for
       that writer, either from original closure induction or inserted-PHI
       generation/path propagation. Provenance alone cannot supply P v.
     - ancestor: selected pair belongs to block_output_pairs is js at a
       snapshot of e.sve_path. root_ancestor_source_pair above recovers its
       actual event. actual_snapshot_dominates supplies strict dominance
       ONLY IF e.sve_label is reachable. Missing: P v for that definition;
       instruction membership and dominance are not copy/PHI edges.

   PHI pair (p,x) / patched predecessor:
     actual_phi_slot_name gives last_name x x (path_pairs
       (e.sve_path ++ [(p,e.sve_before,e.sve_after)])).
     visit_event_last_source supplies default or a last source in this
       path. Same three subcases as above, now using the whole predecessor
       block rather than a TAKE-prefix. Missing: generation-parent dominated
       suffix path propagation to the ACTUAL exiting name, not equality
       to the generation parent's output name. Intervening PHIs may shadow.

   PHI pair / no matching patch event:
     actual_phi_slot_unchanged keeps x. Its premise is absence of an event
       with label p AND successor q, not merely non-reachability of p.
     Missing: closure seeding for x and, for reachable_fn, proof this pair
       survives predecessor filtering. Full-function edges are insufficient.

   label excluded from the tree:
     visit_excluded_frame preserves outputs/opcodes/non-PHI instructions;
       PHI operands MAY change through successor patches. This is not an
       identity theorem for the entire block. Original unrenamed seed/copy
       writers retain their spelling; seed RETPC_PARAM outputs can seed P x
       without definite assignment, provided final instruction membership
       (or reachable membership) has been transported. An unrenamed PHI
       writer still requires a connected retained operand.

   unreachable BUT visited label:
     actual_final_operand_name, actual_phi_slot_name and the snapshot
       consumer remain applicable. actual_snapshot_dominates does not.
       No rule here identifies its path with a CFG dominance path. Original
       writers may be renamed; treating them as untouched would be wrong.
       Missing: separate handling of these writers and generated PHIs in
       the full closure; reachable closure must not use dead witnesses.

   Proposed exact consumer endpoints (UNPROVED):

   FULL:
     o1_fn_shape ctx fn /\ ir_supply_inst_ok s /\
     make_ssa_current_fn s fn = (out,t) /\ retpc_var fn x /\
     cp_closed RETPC_PARAM out P ==>
       P x

   A reachable consumer must NOT test the concrete renamed operand against
   retpc_var fn: that operand need not be an original spelling. A usable
   name-aware endpoint must quantify over the exact last_name expression
   at the visited input operand, and keep initial-name and ancestor cases.
   The following is the precise local closure boundary proposed for that
   purpose:

   Let cfg/dom/live/had_phis/pred_map/succ_map/frontiers/live_in/dtree/
   ordered_bbs/defs/bbs1/s1/rs0/bbs2/s2 have EXACTLY the values bound in
   make_ssa_current_fn_def (entry branch), and let
     raw = fn with fn_blocks := bbs2;
     events = SND (visit_blocks [] s1 rs0 bbs1 succ_map dtree).
   The following universally quantified implication is UNPROVED:

     o1_fn_shape ctx fn /\ ir_supply_inst_ok s /\
     fn_entry_label fn = SOME entry /\ MEM e events /\
     i < LENGTH e.sve_before /\
     (EL i e.sve_before).inst_opcode <> PHI /\
     j < LENGTH (EL i e.sve_before).inst_operands /\
     EL j (EL i e.sve_before).inst_operands = Var x /\ retpc_var fn x /\
     cp_closed RETPC_PARAM raw P ==>
       P (last_name x x (path_pairs e.sve_path ++
          block_output_pairs (TAKE i e.sve_before) (TAKE i e.sve_after)))

   REACHABLE variant: replace raw by reachable_fn raw in cp_closed and
   add cfg_reachable_of (cfg_analyze fn) e.sve_label. Still UNPROVED;
   requires retained PHI predecessor edges as well as CFG preservation.

   PHI-EXIT variant: replace the index/operand premises by retpc_var fn x
   and use last_name x x (path_pairs (e.sve_path ++
     [(e.sve_label,e.sve_before,e.sve_after)])) as conclusion argument.
   Both full and reachable variants are UNPROVED. The reachable variant
   must require a reachable event and target and a retained CFG predecessor
   pair when used to propagate P through a successor PHI.

   These are targets, not assumptions discharged by this diagnostic.
   In particular even FULL above requires the initial-name connectivity
   argument, and post-simplification transport is a separate obligation.

   Next semantic gap: iteration/generation provenance of inserted PHIs,
   dominance-frontier predecessor witnesses, liveness/default propagation,
   and a dominated-path closed-predicate induction that handles PHI
   shadowing. None is provided by exact last-name provenance. Search found
   makeSsaCurrentPhiLocality and makeSsaCurrentCutTokens in makessa3, but
   their stronger input interfaces cannot be imported as weak-input facts.
   No definite-assignment premise has been introduced here.
*)
