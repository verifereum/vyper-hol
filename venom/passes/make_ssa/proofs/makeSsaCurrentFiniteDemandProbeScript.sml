(* Finite static graph probe. No operational simulation is asserted here. *)
Theory makeSsaCurrentFiniteDemandProbe
Ancestors makeSsaCurrentStaticDemandProbe makeSsaCurrentHistoryProbe
  makeSsaCurrentSimDefs makeSsaCurrentDefs makeSsaCurrentSourceCuts
  cfgHelpers venomExecSemantics list alist

Definition current_finite_contexts_def:
  current_finite_contexts fn h =
    if fn_entry_label fn = SOME h then [""] else
      case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps => ps
End

Definition current_finite_block_cuts_def:
  current_finite_block_cuts p old out =
    CurrentStaticCut p old.bb_label 0 0 ::
    (GENLIST (\k. CurrentStaticCut p old.bb_label
        (phi_prefix_length old.bb_instructions)
        (phi_prefix_length out.bb_instructions + k))
      (SUC (current_static_body_start old.bb_instructions out.bb_instructions -
             phi_prefix_length out.bb_instructions)) ++
     GENLIST (\k. CurrentStaticCut p old.bb_label
        (phi_prefix_length old.bb_instructions + k)
        (current_static_body_start old.bb_instructions out.bb_instructions + k))
      (SUC (LENGTH old.bb_instructions - phi_prefix_length old.bb_instructions)))
End

Definition current_finite_cuts_def:
  current_finite_cuts fn fn' = FLAT (MAP (\old.
    case lookup_block old.bb_label fn'.fn_blocks of NONE => [] | SOME out =>
      FLAT (MAP (\p. current_finite_block_cuts p old out)
        (current_finite_contexts fn old.bb_label))) fn.fn_blocks)
End

Definition current_finite_edge_def:
  current_finite_edge fn fn' c d kind <=>
    MEM c (current_finite_cuts fn fn') /\ MEM d (current_finite_cuts fn fn') /\
    current_static_edge fn fn' c d kind
End

Definition current_finite_seed_def:
  current_finite_seed fn fn' H c x y <=>
    MEM c (current_finite_cuts fn fn') /\ current_static_seed fn fn' H c x y
End

Inductive current_finite_demand:
  (!fn fn' H c x y. current_finite_seed fn fn' H c x y ==>
    current_finite_demand fn fn' H c x y) /\
  (!fn fn' H c d kind x y u v.
    current_finite_demand fn fn' H d x y /\ current_finite_edge fn fn' c d kind /\
    current_static_back fn fn' c kind x y (CurrentStaticRead u) (CurrentStaticRead v) ==>
    current_finite_demand fn fn' H c u v)
End

Definition current_finite_target_def:
  current_finite_target fn = FST (make_ssa_current_fn history_probe_supply fn)
End

(* Check the whole aligned ordinary suffix, not only ZIP's truncated pairs. *)
Definition current_finite_alignment_def:
  current_finite_alignment fn fn' = EVERY (\old.
    case lookup_block old.bb_label fn'.fn_blocks of NONE => F | SOME out =>
      phi_prefix_length out.bb_instructions <=
        current_static_body_start old.bb_instructions out.bb_instructions /\
      LIST_REL (\i j. i.inst_opcode = j.inst_opcode /\
        LENGTH i.inst_operands = LENGTH j.inst_operands /\
        LENGTH i.inst_outputs = LENGTH j.inst_outputs)
        (DROP (phi_prefix_length old.bb_instructions) old.bb_instructions)
        (DROP (current_static_body_start old.bb_instructions out.bb_instructions)
          out.bb_instructions)) fn.fn_blocks
End

Theorem current_finite_probe_alignment:
  current_finite_alignment current_probe_loop (current_finite_target current_probe_loop) /\
  current_finite_alignment history_probe_backedges (current_finite_target history_probe_backedges)
Proof
  EVAL_TAC
QED

(* Canonical entry predecessor is sound for the actual fixtures because both
   batches are empty, on both sides, independently of the predecessor text. *)
Theorem current_finite_probe_entry_batches:
  !p op. current_static_phi_subst p
    (TAKE (phi_prefix_length (HD current_probe_loop.fn_blocks).bb_instructions)
      (HD current_probe_loop.fn_blocks).bb_instructions) op = SOME (CurrentStaticRead op) /\
  current_static_phi_subst p
    (TAKE (phi_prefix_length (HD (current_finite_target current_probe_loop).fn_blocks).bb_instructions)
      (HD (current_finite_target current_probe_loop).fn_blocks).bb_instructions) op = SOME (CurrentStaticRead op) /\
  current_static_phi_subst p
    (TAKE (phi_prefix_length (HD history_probe_backedges.fn_blocks).bb_instructions)
      (HD history_probe_backedges.fn_blocks).bb_instructions) op = SOME (CurrentStaticRead op) /\
  current_static_phi_subst p
    (TAKE (phi_prefix_length (HD (current_finite_target history_probe_backedges).fn_blocks).bb_instructions)
      (HD (current_finite_target history_probe_backedges).fn_blocks).bb_instructions) op = SOME (CurrentStaticRead op)
Proof
  EVAL_TAC >> Cases_on `op` >> simp[]
QED

Theorem current_finite_probe_contexts:
  MAP (\h. (h,current_finite_contexts current_probe_loop h)) ["E";"D";"X"] =
    [("E",[""]);("D",["E";"D"]);("X",["D"])] /\
  MAP (\h. (h,current_finite_contexts history_probe_backedges h)) ["E";"H";"D";"S"] =
    [("E",[""]);("H",["E";"D";"S"]);("D",["H"]);("S",["H"])]
Proof
  EVAL_TAC
QED

(* Candidate history is extracted from actual precleanup output occurrences
   and immutable source annotations. It is not trusted until trace-checked. *)
Definition current_finite_annotations_def:
  current_finite_annotations fn = MAP (\old.
    case lookup_block old.bb_label (FST (history_probe_insert fn)) of
      NONE => [] | SOME ins => current_block_annotations old
        (TAKE (LENGTH ins.bb_instructions - LENGTH old.bb_instructions) ins.bb_instructions))
    fn.fn_blocks
End

Definition current_finite_history_def:
  current_finite_history fn = FLAT (MAP (\(anns,bb).
    FLAT (MAP (\(a,inst). MAP (\((t,v),n). (t,v,n))
        (ZIP (a,inst.inst_outputs))) (ZIP (anns,bb.bb_instructions))))
    (ZIP (current_finite_annotations fn, history_probe_rename fn)))
End

(* UNPROVED boundary: the extracted current_finite_history must be shown to
   be the history of current_tree_trace with the actual annotation map,
   insertion result, initial rename state and dom tree. Expanding that entire
   existential trace by EVAL leaves a huge goal; global simp exceeds policy.
   No ownership or closure result may assume this extraction correct. *)
