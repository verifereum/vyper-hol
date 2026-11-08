(* Resource boundaries for the joint statement step. *)
Theory bodyIntCallJointStmtBoundary
Ancestors
  bodyIntCallJointContract exprLoweringProps loweringPosts compileEnv intCallFrame
  stmtSimProps bodyMemoryDefs freshWrites

Theorem intcall_return_buffer_bound:
  intcall_joint_res fp ce env es sa s /\ fp.jc_rb = SOME (bw,cap) ==>
  w2n bw + cap < dimword (:256)
Proof
  simp[intcall_joint_res_def] >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >>
     fs[stmt_state_rel_def] >> goal_assum (drule_at Any)) >>
  gvs[return_buf_frame_def] >> decide_tac
QED

Theorem intcall_return_buffer_source_disjoint:
  intcall_frame_ok fp /\ fp.jc_rb = SOME (bw,cap) /\
  a <= p /\ p + k <= a + z /\
  (fp.jc_lo <= a \/
   ?b n. fp.jc_staged b n /\ b <= a /\ a + z <= b + n) ==>
  compileEnv$regions_disjoint p k (w2n bw) cap
Proof
  strip_tac >>
  qpat_x_assum `intcall_frame_ok fp` mp_tac >>
  simp[intcall_frame_ok_def] >> strip_tac >>
  gvs[compileEnvTheory.regions_disjoint_def] >>
  qpat_x_assum `!b z. fp.jc_staged b z ==> _ \/ _` drule >>
  strip_tac >> decide_tac
QED

Theorem intcall_joint_res_next_var:
  intcall_joint_res fp ce env es sa s /\
  sa.cs_next_var <= sb.cs_next_var ==>
  intcall_joint_res fp ce env es sb s
Proof
  simp[intcall_joint_res_def] >> strip_tac >>
  `local_ptrs_reserved ce sb` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `ret_pc_ok ce sb s` by
    (drule ret_pc_ok_frame >> disch_then irule >> simp[]) >>
  `return_buf_frame fp.jc_rb ce sb s` by
    (drule return_buf_frame_frame >> disch_then irule >> simp[]) >>
  simp[] >> rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
