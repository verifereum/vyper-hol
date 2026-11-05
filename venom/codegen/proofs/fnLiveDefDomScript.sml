(*
 * Where a live variable is defined.
 *
 * TOP-LEVEL:
 *   live_def_dominates — in a codegen-ready function, a variable live at a
 *                        point of a reachable block, other than as an
 *                        operand of a PHI at or after that point, has a
 *                        definition whose block dominates the block, and
 *                        that definition comes before the point when it is
 *                        in the same block
 *)

Theory fnLiveDefDom
Ancestors
  stackPlanGen livenessDefs venomWf

(* Used by fnLineageStatic: no stack slot of a lineage state is an output
   of the block it enters.

   Why it should hold: v is live at (lbl, idx), so along some real
   execution path from that point (instructions run in order, a block left
   only after its last instruction, PHI operands read on the incoming edge)
   v is used before any definition of v.  That use has a definition
   available at it (def_dominates_uses: dominating the using block, and
   earlier in it when in the same block; for a PHI operand, available at
   the end of the incoming predecessor).  Prefixing an entry path to lbl
   that doesn't pass through lbl's own instructions after idx, the def must
   lie on the combined path before the use, hence on the entry path or
   before idx in lbl, since the part from (lbl, idx) defines no v.  A PHI
   operand of lbl itself at or after idx is a use on an edge into lbl,
   which this path doesn't reach; hence its exclusion.  Note that the
   liveness soundness witness (livenessProofs$liveness_sound_proof) uses
   cfg_exec_path, which may leave a block early; it is too weak by itself
   for the same-block case. *)
Theorem live_def_dominates:
  !fn lbl bb idx v.
    codegen_ready_fn fn /\ fn_reachable fn lbl /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    idx <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) lbl idx) /\
    (!j. idx <= j /\ j < LENGTH bb.bb_instructions /\
         (EL j bb.bb_instructions).inst_opcode = PHI ==>
         ~MEM (Var v) (EL j bb.bb_instructions).inst_operands) ==>
    ?def_bb def_inst.
      MEM def_bb fn.fn_blocks /\ MEM def_inst def_bb.bb_instructions /\
      MEM v def_inst.inst_outputs /\
      fn_dominates fn def_bb.bb_label lbl /\
      (def_bb.bb_label = lbl ==>
       ?i. i < idx /\ EL i bb.bb_instructions = def_inst)
Proof
  cheat
QED
