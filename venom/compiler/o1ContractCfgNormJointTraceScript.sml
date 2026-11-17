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
  map_every qid_spec_tac [`q8`, `q9`, `current`, `saved`, `qs`, `r9`] >>
  Induct_on `evs`
  >- (rpt gen_tac >> Cases_on `qs` >> simp[joint_chain_def] >>
      rpt strip_tac >> gvs[] >>
      qexistsl_tac [`current`, `saved`, `[]`, `q8`] >>
      simp[joint_chain_def]) >>
  rpt gen_tac >> Cases_on `qs` >> simp[joint_chain_def] >>
  rpt strip_tac >> Cases_on `q8` >> Cases_on `q9` >>
  drule_all cfg_norm_joint_cursors_step >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  rename1 `cfg_norm_joint_cursors C8 C9
    (schedules,final,saved_final) r8 r9` >>
  qexistsl_tac [`final`, `saved_final`]
  >- (gvs[] >> qexistsl_tac [`evs8`, `qs8`, `r8`] >> simp[]) >>
  rename1 `joint_transition C8 _ source_event source_next` >>
  qexistsl_tac [`source_event::evs8`, `source_next::qs8`, `r8`] >>
  simp[joint_chain_def]
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
  strip_tac >> drule_all cfg_norm_joint_cursors_initial >>
  disch_then (qx_choose_then `schedules` assume_tac) >>
  qexists_tac `schedules` >> rpt gen_tac >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qexists_tac `current` >> simp[] >>
  rpt gen_tac >> rewrite_tac[joint_trace_def] >> strip_tac >>
  drule_all cfg_norm_joint_chain_projection >> strip_tac >>
  qexistsl_tac [`current'`, `saved'`, `evs8`, `qs8`, `r8`] >>
  simp[]
QED
