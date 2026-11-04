Theory livenessDemandWitness
Ancestors
  livenessTransferProofs livenessBlockProofs livenessDefs venomInst list

(* A local finite witness, suitable as the block part of a worklist invariant.
   This does not yet assert a finite inter-block use witness. *)
Theorem liveness_fold_use_witness:
  !insts out.
    MEM v (FOLDR (liveness_transfer bbs) out insts) ==>
    (?pre inst post. insts = pre ++ inst::post /\
      EVERY (\i. ~MEM v (inst_defs i)) pre /\ MEM v (inst_uses inst)) \/
    (EVERY (\i. ~MEM v (inst_defs i)) insts /\ MEM v out)
Proof
  Induct >> simp[liveness_transfer_def, live_update_mem] >>
  rpt strip_tac
  >- (first_x_assum drule >> strip_tac
      >- (disj1_tac >> qexistsl_tac [`h::pre`, `inst`, `post`] >> simp[]) >>
      disj2_tac >> simp[]) >>
  disj1_tac >> qexistsl_tac [`[]`, `h`, `insts`] >> simp[]
QED

Theorem liveness_edge_use_origin:
  lookup_block succ bbs = SOME bb /\
  MEM v (liveness_edge_transfer bbs succ pred live) ==>
  MEM v live \/
  ?inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    MEM (pred,v) (phi_pairs inst.inst_operands)
Proof
  strip_tac >> gvs[liveness_edge_transfer_def] >>
  drule input_vars_from_phi_correct_proof >> simp[]
QED
