Theory fnAliasInvLiveness
Ancestors
  livenessTerminationProofs livenessTransferProofs livenessBlockProofs
  livenessDefs

(* Sufficient closure under exactly the transfers used by the analysis. *)
Definition alias_live_closed_def:
  alias_live_closed fn P <=>
    (!l bb i live.
      lookup_block l fn.fn_blocks = SOME bb /\
      i < LENGTH bb.bb_instructions /\
      (!v. MEM v live ==> P l (SUC i) v) ==>
      !v. MEM v (liveness_transfer fn.fn_blocks
                    (EL i bb.bb_instructions) live) ==> P l i v) /\
    (!l s live.
      MEM s (cfg_succs_of (cfg_analyze fn) l) /\
      (!v. MEM v live ==> P s 0 v) ==>
      !v. MEM v (liveness_edge_transfer fn.fn_blocks s l live) ==>
        P l (LENGTH (liveness_instrs fn.fn_blocks l)) v)
End

Theorem alias_live_closed_inst:
  alias_live_closed fn P /\
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (!w. MEM w live ==> P l (SUC i) w) /\
  MEM v (liveness_transfer fn.fn_blocks (EL i bb.bb_instructions) live) ==>
  P l i v
Proof
  simp[alias_live_closed_def] >> metis_tac[]
QED

Theorem alias_live_closed_edge:
  alias_live_closed fn P /\
  MEM s (cfg_succs_of (cfg_analyze fn) l) /\
  (!w. MEM w live ==> P s 0 w) /\
  MEM v (liveness_edge_transfer fn.fn_blocks s l live) ==>
  P l (LENGTH (liveness_instrs fn.fn_blocks l)) v
Proof
  simp[alias_live_closed_def] >> metis_tac[]
QED

Theorem alias_liveness_transfer_rule:
  (!v. MEM v (inst_uses inst) ==> A v) /\
  (!v. MEM v live /\ ~MEM v (inst_defs inst) ==> A v) ==>
  !v. MEM v (liveness_transfer bbs inst live) ==> A v
Proof
  simp[liveness_transfer_def, live_update_mem] >> metis_tac[]
QED

Theorem alias_liveness_edge_present:
  lookup_block s bbs = SOME bb /\
  (!v. MEM v (input_vars_from l bb.bb_instructions live) ==> A v) ==>
  !v. MEM v (liveness_edge_transfer bbs s l live) ==> A v
Proof
  simp[liveness_edge_transfer_def]
QED

Theorem alias_liveness_edge_absent:
  lookup_block s bbs = NONE /\ (!v. MEM v live ==> A v) ==>
  !v. MEM v (liveness_edge_transfer bbs s l live) ==> A v
Proof
  simp[liveness_edge_transfer_def]
QED
