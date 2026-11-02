(*
 * What DFT's schedule keeps in order.
 *
 * dft_fn reschedules the non-pseudo instructions of each block (the body
 * and its terminator) and keeps the pseudo prefix (PHI, PARAM, ...) as is.
 * dft_block_rel says what the result is, block by block: the same label,
 * the same pseudos first, then a permutation of the input's non-pseudo
 * instructions, each one either unchanged or with its operands flipped,
 * in which every pair the input orders by dft_must_order keeps that order.
 *
 * dft_must_order x y (x before y in the input) holds when
 *   - y uses an output of x;
 *   - x and y have conflicting effects (one writes an effect the other
 *     reads or writes);
 *   - x is a root of the dependency graph that nothing can depend on: it
 *     has no outputs and no effects (ASSERT, ASSERT_UNREACHABLE, INVALID).
 *     DFT schedules roots in block order, after only their own earlier
 *     dependencies, so nothing after a root is scheduled before it;
 *   - y is a terminator.
 *
 * The schedule does not keep fallible instructions (is_fallible: ASSERT,
 * ASSERT_UNREACHABLE, RETURNDATACOPY, INVALID, INVOKE) in order: an ASSERT
 * can move above an INVOKE that came before it.  dft_fallible_order_kept
 * states that it does, for one input function and its schedule; the pass
 * contract takes it as its pre-condition, until the pinned DFT orders
 * fallible instructions (add_abort_deps).
 *)
Theory dftScheduleOrder
Ancestors
  dftCorrectness dftStructural dftDefs venomWf venomInst venomEffects list

(* a comes before b in the list l. *)
Definition id_before_def:
  id_before l a b <=> ?i j. i < j /\ j < LENGTH l /\ EL i l = a /\ EL j l = b
End

Definition dft_must_order_def:
  dft_must_order x y <=>
    ~DISJOINT (set (inst_defs x)) (set (inst_uses y)) \/
    ~DISJOINT (write_effects x.inst_opcode)
              (read_effects y.inst_opcode UNION write_effects y.inst_opcode) \/
    ~DISJOINT (read_effects x.inst_opcode) (write_effects y.inst_opcode) \/
    (x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
     write_effects x.inst_opcode = empty_effects) \/
    is_terminator y.inst_opcode
End

Definition dft_block_rel_def:
  dft_block_rel bb bb' <=>
    bb'.bb_label = bb.bb_label /\
    ?body.
      bb'.bb_instructions =
        FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ body /\
      PERM (MAP (\i. i.inst_id) body)
           (MAP (\i. i.inst_id)
              (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)) /\
      EVERY (from_block bb.bb_instructions) body /\
      !x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
            ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
            id_before (MAP (\i. i.inst_id) bb.bb_instructions)
              x.inst_id y.inst_id /\
            dft_must_order x y ==>
            id_before (MAP (\i. i.inst_id) body) x.inst_id y.inst_id
End

(* Fallible instructions keep their relative order in every block. *)
Definition dft_fallible_order_kept_def:
  dft_fallible_order_kept fn fn' <=>
    LIST_REL
      (\bb bb'.
         !x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
               is_fallible x /\ is_fallible y /\
               id_before (MAP (\i. i.inst_id) bb.bb_instructions)
                 x.inst_id y.inst_id ==>
               id_before (MAP (\i. i.inst_id) bb'.bb_instructions)
                 x.inst_id y.inst_id)
      fn.fn_blocks fn'.fn_blocks
End

(* Why it holds (unchecked notes):
   - Permutation, flips, labels and pseudo prefix: dft_fn_all_perm_of and
     dft_fn_dft_inv (dftCorrectness).  Blocks the loop never reaches come out
     unchanged, which is why fn_pseudos_prefix is needed.
   - A root (no outputs, no effects) is never a dependency: inst_data_deps
     (terminator order deps too) only finds producers, build_eda only records
     instructions with effects.  So it is an entry; entries are processed in
     block order, every dependency is earlier in the block (SSA
     defs-before-uses), so nothing after a root is emitted before it.  The
     terminator is the last entry.
   - Effect conflicts: WAW chain, RAW to the last writer, WAR (reads are
     cleared after a write, but ordered through the intermediate writer).
     schedule_output_eda_before (dftTopoSort) gives dependencies first.
   - Each loop iteration keeps dft_inv, flip_operands keeps outputs, used
     variables, effects and is_terminator, and flips are involutive. *)
Theorem dft_fn_block_rel:
  !fn. wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
       (dft_fn fn).fn_name = fn.fn_name /\
       LIST_REL dft_block_rel fn.fn_blocks (dft_fn fn).fn_blocks
Proof
  cheat
QED
