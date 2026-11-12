Theory concretizeAnalysisScan
Ancestors concretizeAnalysisBoundary basePtrDefs execEquivParamBase allocaRemapSSA
  list pred_set venomInst pair basePtrProofs concretizeMemLocDefs

Definition bp_scan_insts_def:
  bp_scan_insts fn [] = [] /\
  bp_scan_insts fn (lbl::ls) =
    (case FIND (\bb. bb.bb_label = lbl) fn.fn_blocks of
       NONE => [] | SOME bb => bb.bb_instructions) ++ bp_scan_insts fn ls
End

Theorem bp_process_block_append:
  !xs r ys. bp_process_block r (xs ++ ys) =
    (FST (bp_process_block r xs) \/
       FST (bp_process_block (SND (bp_process_block r xs)) ys),
     SND (bp_process_block (SND (bp_process_block r xs)) ys))
Proof
  Induct >> simp[bp_process_block_def] >> rpt gen_tac >>
  Cases_on `bp_handle_inst r h` >> simp[] >>
  rename1 `bp_handle_inst r h = (c,r1)` >>
  Cases_on `bp_process_block r1 xs` >> simp[DISJ_ASSOC]
QED

Theorem bp_one_pass_scan:
  !order r. bp_one_pass fn order r =
    bp_process_block r (bp_scan_insts fn order)
Proof
  Induct >> simp[bp_one_pass_def, bp_one_pass_aux_def, bp_scan_insts_def,
                 bp_process_block_def] >>
  rpt gen_tac >> Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >>
  gvs[bp_one_pass_def, bp_process_block_append, bp_process_block_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem bp_scan_insts_member:
  !order i. MEM i (bp_scan_insts fn order) ==> MEM i (fn_insts fn)
Proof
  Induct >> simp[bp_scan_insts_def] >> rpt gen_tac >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >> simp[] >>
  metis_tac[FIND_MEM, mem_fn_insts_intro]
QED

(* Quantitative BASE-coverage audit; the argument below is a proposed proof
   interface, NOT an established convergence theorem.

   Let S = bp_scan_insts fn order, and V = {v | exists i in S.
   inst_output i = SOME v}. Define a directed dependency edge x -> y
   only at a visited instruction with inst_output = SOME y:
     ASSIGN [Var x]; ADD [Var x;Lit c] or [Lit c;Var x];
     SUB [Var x;Lit c]; ADD [Var x;Var z] when x is pointer-derived,
     and symmetrically z -> y; SUB [Var x;Var z] only x -> y;
     PHI when x occurs in MAP SND (phi_pairs operands).
   Variable arithmetic uses fn_ptr_ok's syntactic exclusions, not a guess
   that the other BP operand will stay empty. Local seeds are ALLOCA
   outputs y with base Allocation inst_id. PARAM/DALLOCA are not seeds.

   Precise proposed coverage theorem: under ssa_form fn, fn_ptr_ok P fn,
   and a path [v0;...;vk] of k dependency edges in S whose first vertex
   is a visited ALLOCA output of base a, a belongs to bp_bases
     (bp_iterate_fuel (SUC k) fn order FEMPTY) vk.
   All visited instructions must belong to fn_insts fn (already proved
   above); every path vertex must have a single-output defining instruction
   in S. A local path theorem needs no dominance and does not assert
   runtime completeness. Membership/edge predicates still need definitions
   and proofs under a subsequent strategist-owned component.

   Rank: for a fixed root, shortest dependency-path edge length to v.
   Cycle erasure gives rank < CARD V for reachable vertices. Each vertex
   has a distinct defining instruction by SSA, so CARD V <= LENGTH
   (fn_insts fn), even with multi-output instructions elsewhere. Thus at
   most LENGTH (fn_insts fn) passes suffice for local base coverage.
   The ACTUAL budget is concretize_memloc_fuel fn =
     4 * (LENGTH (fn_insts fn) + LENGTH fn.fn_blocks + 1)
   (concretizeMemLocDefsTheory), comfortably above that bound. No claim
   about convergence of exact offsets or of the changed flag follows.

   Main missing invariant: base growth along the chronological execution
   of FEMPTY-start scans, NOT arbitrary-map transfer inflation. ASSIGN
   with an empty source can erase an arbitrary old output. Single-writer
   SSA plus the history that previously installed output bases came from
   that same source should establish retention. Other instructions cannot
   overwrite that output (existing non-output preservation interface).
   The source bases never disappear under the simultaneous history
   invariant. PHI unions its previous output and operand bases, so
   backedges add paths and cycles do not require new ranks indefinitely.
   Literal affine ops preserve bases; variable affine ops additionally use
   bp_supported and bp_supported_*_empty (concretizeAnalysisAffineTheory).

   Challenges / outstanding obligations:
   1. Prove single-writer history retention and one-round path extension,
      including initially empty ASSIGN and repeated order labels. Repeated
      visits to one defining instruction are permitted, different writers
      are not. SSA is ALL_DISTINCT flattened outputs, not dominance.
   2. Prove early-exit adequacy: a false pass flag means every transfer's
      ptr lookup is unchanged, not necessarily fmap equality. Use
      bp_one_pass_stable_ptrs plus transfer extensionality to preserve all
      base coverage for subsequent omitted passes; do not assume convergence.
   3. Formalize finite shortest-path/rank bound and the numeric budget.
   4. Production bp_analyze_fuel visits cfg.cfg_dfs_pre. cfgAnalysisProps
      exports cfg_analyze_dfs_pre_distinct (unconditional), reachable_sets
      (wf_function), preorder_entry_first (entry_block), and
      semantic_reachability (wf_function + entry_block). Combine these
      with FIND uniqueness from wf_function labels to cover runtime
      reachable blocks. Unvisited dead blocks are NOT covered by the local
      path theorem; they must not be used as definition witnesses.
   5. Runtime-to-dependency-path correspondence is separate: ssa_form only
      gives uniqueness, and initial vs_vars may supply values before any
      definition. def_available_at fn target_bb use_inst_opt v encodes
      domination and same-block strict order (venomWfTheory); it is NOT
      entailed by SSA. Decide at integration whether the task-permitted
      availability premise is necessary, including PHI edge availability.
   6. No base-path argument supplies memory-liveness demand closure or
      fn_mems_used soundness. Those remain independent integration gates.
*)

Theorem bp_handle_inst_lookup_cong:
  (!v. bp_get_ptrs r v = bp_get_ptrs s v) ==>
  FST (bp_handle_inst r i) = FST (bp_handle_inst s i) /\
  (!v. bp_get_ptrs (SND (bp_handle_inst r i)) v =
       bp_get_ptrs (SND (bp_handle_inst s i)) v)
Proof
  strip_tac >>
  `bp_get_ptrs r = bp_get_ptrs s` by simp[FUN_EQ_THM] >>
  Cases_on `inst_output i` >> simp[bp_handle_inst_def] >>
  Cases_on `i.inst_opcode` >> simp[bp_handle_inst_def, bp_get_ptrs_update]
  >~ [`i.inst_opcode = PHI`]
  >- (IF_CASES_TAC >> simp[bp_get_ptrs_update])
  >~ [`i.inst_opcode = ASSIGN`]
  >- (namedCases_on `i.inst_operands` ["", "a tl"] >> simp[] >>
      Cases_on `tl` >> simp[] >>
      Cases_on `a` >> simp[bp_get_ptrs_update]) >>
  namedCases_on `i.inst_operands` ["", "a tl"] >> simp[] >>
  namedCases_on `tl` ["", "b rest"] >> simp[] >>
  Cases_on `rest` >> simp[] >>
  Cases_on `a` >> simp[bp_get_ptrs_update] >>
  Cases_on `b` >> simp[bp_get_ptrs_update] >>
  rpt (IF_CASES_TAC >> simp[bp_get_ptrs_update])
QED

Theorem bp_process_block_lookup_cong:
  !xs r s. (!v. bp_get_ptrs r v = bp_get_ptrs s v) ==>
  FST (bp_process_block r xs) = FST (bp_process_block s xs) /\
  (!v. bp_get_ptrs (SND (bp_process_block r xs)) v =
       bp_get_ptrs (SND (bp_process_block s xs)) v)
Proof
  Induct >> simp[bp_process_block_def] >> rpt gen_tac >> strip_tac >>
  drule bp_handle_inst_lookup_cong >>
  disch_then (qspec_then `h` strip_assume_tac) >>
  first_x_assum (qspecl_then
    [`SND (bp_handle_inst r h)`, `SND (bp_handle_inst s h)`] mp_tac) >>
  simp[] >>
  Cases_on `bp_handle_inst r h` >> Cases_on `bp_handle_inst s h` >>
  simp[] >> strip_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> gvs[]
QED

Theorem bp_one_pass_lookup_cong:
  (!v. bp_get_ptrs r v = bp_get_ptrs s v) ==>
  FST (bp_one_pass fn order r) = FST (bp_one_pass fn order s) /\
  (!v. bp_get_ptrs (SND (bp_one_pass fn order r)) v =
       bp_get_ptrs (SND (bp_one_pass fn order s)) v)
Proof
  simp[bp_one_pass_scan, bp_process_block_lookup_cong]
QED

Definition bp_unconditional_passes_def:
  bp_unconditional_passes 0 fn order r = r /\
  bp_unconditional_passes (SUC n) fn order r =
    bp_unconditional_passes n fn order (SND (bp_one_pass fn order r))
End

Theorem bp_unconditional_passes_stable_ptrs:
  !n r. FST (bp_one_pass fn order r) = F ==>
  !v. bp_get_ptrs (bp_unconditional_passes n fn order r) v = bp_get_ptrs r v
Proof
  Induct >> simp[bp_unconditional_passes_def] >>
  rpt gen_tac >> strip_tac >>
  drule (SRULE [] bp_one_pass_stable_ptrs) >> strip_tac >>
  `FST (bp_one_pass fn order (SND (bp_one_pass fn order r))) = F`
    by (drule bp_one_pass_lookup_cong >>
        disch_then (qspecl_then [`order`, `fn`] strip_assume_tac) >> gvs[]) >>
  first_x_assum drule >> simp[]
QED

Theorem bp_iterate_fuel_unconditional_ptrs:
  !n r v. bp_get_ptrs (bp_iterate_fuel n fn order r) v =
          bp_get_ptrs (bp_unconditional_passes n fn order r) v
Proof
  Induct >> simp[bp_iterate_fuel_def, bp_unconditional_passes_def] >>
  rpt gen_tac >> Cases_on `bp_one_pass fn order r` >> simp[] >>
  rename1 `bp_one_pass fn order r = (changed,r1)` >>
  Cases_on `changed` >> simp[] >>
  `FST (bp_one_pass fn order r) = F` by simp[] >>
  drule bp_one_pass_stable_ptrs >> strip_tac >>
  `FST (bp_one_pass fn order r1) = F`
    by (drule bp_one_pass_lookup_cong >>
        disch_then (qspecl_then [`order`, `fn`] strip_assume_tac) >> gvs[]) >>
  simp[bp_unconditional_passes_stable_ptrs]
QED
