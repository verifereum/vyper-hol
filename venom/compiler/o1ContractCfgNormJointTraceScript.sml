Theory o1ContractCfgNormJointTrace
Ancestors
  o1ContractCfgNormJointCursors frameJointTrace list arithmetic

(* Each normalized edge either retains the source cursor or advances it
   once. Schedules stay fixed while current and saved cells evolve. *)
Theorem cfg_norm_joint_chain_projection:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved) q8 q9 /\
  joint_chain C9 q9 evs qs r9 ==>
  ?current' saved' evs8 qs8 r8.
    joint_chain C8 q8 evs8 qs8 r8 /\
    LENGTH evs8 <= LENGTH evs /\
    cfg_norm_joint_cursors C8 C9 (schedules,current',saved') r8 r9
Proof
  cheat
QED

Theorem cfg_norm_joint_trace_projection:
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) view C8 C9 /\
  o1_ctx_shape C8 /\ EVERY wf_ssa C8.ctx_functions ==>
  ?schedules.
    !vs0 q8 q9.
      vs0.vs_vars = FEMPTY /\ ~vs0.vs_halted /\
      joint_initial vs0 C8 q8 /\ joint_initial vs0 C9 q9 ==>
      ?current.
        cfg_norm_joint_cursors C8 C9 (schedules,current,[]) q8 q9 /\
        !evs qs r9.
          joint_trace vs0 C9 q9 evs qs r9 ==>
          ?current' saved' evs8 qs8 r8.
            joint_trace vs0 C8 q8 evs8 qs8 r8 /\
            LENGTH evs8 <= LENGTH evs /\
            cfg_norm_joint_cursors C8 C9
              (schedules,current',saved') r8 r9
Proof
  cheat
QED
