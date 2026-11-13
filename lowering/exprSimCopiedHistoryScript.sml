(* Original-history frames across capture followed by index evaluation. *)
Theory exprSimCopiedHistory
Ancestors
  exprBopSimProps exprSimProps loweringPosts freshWrites compileEnv
  vyperState venomState venomMemDefs finite_map list arithmetic

Theorem copied_array_history_after_index:
  expr_post ctx func ce cx idx ec sn si cap ee iv iop s /\
  local_ptrs_rel func ce es.scopes s0 /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x cap = SOME w) /\
  (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
     FLOOKUP cap.vs_allocas id = SOME entry) /\
  (!id off sz. FLOOKUP s0.vs_allocas id = SOME (off,sz) /\ id < sa.cs_next_id /\
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
       off + sz <= lb \/ lb + lsz <= off) ==>
     mem_bytes_at off sz cap.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
  locals_kept ce es ec s0 cap /\
  (~expr_has_effect obj ==> pure_frame ce func es sa s0 cap) ==>
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x s = SOME w) /\
  (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
     FLOOKUP s.vs_allocas id = SOME entry) /\
  (!id off sz. FLOOKUP s0.vs_allocas id = SOME (off,sz) /\ id < sa.cs_next_id /\
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
       off + sz <= lb \/ lb + lsz <= off) ==>
     mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
  locals_kept ce es ee s0 s /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce func es sa s0 s)
Proof
  strip_tac >> fs[expr_post_def] >>
  `MAP FDOM es.scopes = MAP FDOM ec.scopes` by fs[locals_kept_def] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (rpt strip_tac >>
      `!n lb lsz. local_region ce ec.scopes cap n lb lsz ==>
        off + sz <= lb \/ lb + lsz <= off` by
        (rpt strip_tac >>
         `local_region ce es.scopes s0 n lb lsz` by
           (irule local_region_frame >> metis_tac[]) >> metis_tac[]) >>
      `id < sn.cs_next_id` by decide_tac >>
      metis_tac[]) >>
  conj_tac >- (irule locals_kept_trans >> metis_tac[]) >>
  strip_tac >>
  `~expr_has_effect obj /\ ~expr_has_effect idx` by fs[] >>
  irule pure_frame_trans >> simp[] >>
  qexistsl_tac [`ec`,`sn`,`cap`] >> simp[]
QED
