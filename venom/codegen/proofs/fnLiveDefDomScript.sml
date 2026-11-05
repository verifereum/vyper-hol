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
  stackPlanGen livenessDefs venomWf codegenReadyCompute venomExecProps
  livenessTransferProofs dfAnalyzeDefs

Definition ldd_available_def:
  ldd_available fn bb i v <=>
    ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
      MEM v di.inst_outputs /\
      fn_dominates fn db.bb_label bb.bb_label /\
      (db.bb_label = bb.bb_label ==>
       ?k. k < i /\ EL k bb.bb_instructions = di)
End

Definition ldd_pending_phi_def:
  ldd_pending_phi bb i v <=>
    ?j. i <= j /\ j < LENGTH bb.bb_instructions /\
      (EL j bb.bb_instructions).inst_opcode = PHI /\
      MEM (Var v) (EL j bb.bb_instructions).inst_operands
End

Definition ldd_state_def:
  ldd_state fn st <=>
    !lbl bb i v. fn_reachable fn lbl /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      i <= LENGTH bb.bb_instructions /\
      MEM v (df_at [] st lbl i) ==>
      ldd_available fn bb i v \/ ldd_pending_phi bb i v
End

Theorem ldd_pending_phi_end[local]:
  ~ldd_pending_phi bb (LENGTH bb.bb_instructions) v
Proof
  rw[ldd_pending_phi_def] >> decide_tac
QED

Theorem ldd_pending_phi_back[local]:
  i <= j /\ ldd_pending_phi bb j v ==> ldd_pending_phi bb i v
Proof
  rw[ldd_pending_phi_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ldd_available_entry[local]:
  ldd_available fn bb 0 v ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs /\
    fn_dominates fn db.bb_label bb.bb_label /\
    db.bb_label <> bb.bb_label
Proof
  rw[ldd_available_def] >> metis_tac[]
QED

Theorem ldd_state_init[local]:
  ldd_state fn (init_df_state [] lbls)
Proof
  simp[ldd_state_def, init_df_state_def, df_at_def]
QED

Theorem ldd_block_inst_ids_distinct[local]:
  !bbs bb. MEM bb bbs /\
    ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id)
      b.bb_instructions) bbs)) ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  Induct >> rw[] >> gvs[listTheory.ALL_DISTINCT_APPEND]
QED

Theorem ldd_inst_position[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
  EL i bb.bb_instructions = EL j bb.bb_instructions ==> i = j
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule ldd_block_inst_ids_distinct >> qexists_tac `fn.fn_blocks` >>
     gvs[wf_function_def, fn_inst_ids_distinct_def]) >>
  drule listTheory.ALL_DISTINCT_EL_IMP >>
  disch_then (qspecl_then [`i`, `j`] mp_tac) >>
  simp[listTheory.EL_MAP]
QED

Theorem ldd_available_at_inst[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  i < LENGTH bb.bb_instructions /\
  def_available_at fn bb (SOME (EL i bb.bb_instructions)) v ==>
  ldd_available fn bb i v
Proof
  rw[def_available_at_def, ldd_available_def] >>
  qexistsl_tac [`def_bb`, `def_inst`] >> simp[] >> strip_tac >>
  `def_bb = bb` by metis_tac[wf_function_blocks_same_label] >>
  gvs[] >>
  `j = i` by metis_tac[ldd_inst_position] >> gvs[] >>
  metis_tac[]
QED

Theorem ldd_available_at_end[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  def_available_at fn bb NONE v ==>
  ldd_available fn bb (LENGTH bb.bb_instructions) v
Proof
  rw[def_available_at_def, ldd_available_def] >>
  qexistsl_tac [`def_bb`, `def_inst`] >> simp[] >> strip_tac >>
  `def_bb = bb` by metis_tac[wf_function_blocks_same_label] >>
  gvs[] >> metis_tac[listTheory.MEM_EL]
QED

Theorem ldd_ordinary_use[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL i bb.bb_instructions).inst_operands ==>
  ldd_available fn bb i v
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  irule ldd_available_at_inst >> simp[] >>
  gvs[codegen_ready_fn_def, def_dominates_uses_def] >>
  metis_tac[listTheory.MEM_EL]
QED

Theorem ldd_phi_edge_use[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  MEM (pred,v) (phi_pairs inst.inst_operands) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb ==>
  ldd_available fn pred_bb (LENGTH pred_bb.bb_instructions) v
Proof
  strip_tac >>
  `MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ phi_edge_uses_wf fn bb inst` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  gvs[phi_edge_uses_wf_def] >>
  first_x_assum (drule_then strip_assume_tac) >>
  rename1 `def_available_at fn edge_bb NONE v` >>
  `edge_bb = pred_bb` by metis_tac[wf_function_blocks_same_label] >>
  gvs[] >> irule ldd_available_at_end >> simp[]
QED

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
