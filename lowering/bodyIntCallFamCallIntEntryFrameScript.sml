(* Caller resource reconstruction at the original compiler index. *)
Theory bodyIntCallFamCallIntEntryFrame
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore wordArgsPtr loweringPosts

Theorem intcall_entry_caller_resource:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  intcall_expr_cont fp ce env es sa s ee sb u /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ee.immutables = es.immutables ==>
  intcall_expr_res fp ce env ee sa u
Proof
  strip_tac >>
  `wb_frame ce es sa s u` by (drule intcall_expr_cont_frame >> simp[]) >>
  `!n b sz. local_region ce es.scopes s n b sz <=>
             local_region ce ee.scopes u n b sz` by
    (irule wb_frame_local_regions >>
     fs[intcall_expr_res_def] >> metis_tac[]) >>
  irule intcall_joint_res_frame >>
  fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  qexistsl_tac [`es`, `s`, `sa`] >> simp[] >> metis_tac[]
QED
