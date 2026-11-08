(* Composition of the original declaration frame with continuation frames. *)
Theory annAssignPtrContinuationFrame
Ancestors
 annAssignPtrDeclarationPost annAssignPtrDestinationFrame annAssignPtrStore
 annAssignPtrBytestring bodyPtrDefs exprSimProps compileEnv loweringStateRelDefs finite_map arithmetic

Theorem annassign_ghost_kept_compose_ptr:
 !cenv es sa sb G0 tn0 s0 G1 tn1 s1 G2 tn2.
 ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
 ghost_kept cenv es sb G1 tn1 s1 G2 tn2 /\
 sa.cs_next_id <= sb.cs_next_id /\
 (!q. not_fresh_at sa q ==> not_fresh_at sb q) /\
 (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
            FLOOKUP s1.vs_allocas aid = SOME ent) /\
 (!n b sz. local_region cenv es.scopes s0 n b sz <=>
           local_region cenv es.scopes s1 n b sz) ==>
 ghost_kept cenv es sa G0 tn0 s0 G2 tn2
Proof
 rw[ghost_kept_def]
 >- (`aid < sb.cs_next_id` by decide_tac >>
     `FLOOKUP s1.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
     `i IN tn1.t_mem` by
       (qpat_x_assum `!aid off sz i. FLOOKUP s1.vs_allocas _ = _ /\ _ ==> _` irule >>
        goal_assum (drule_at Any) >> simp[]) >>
     qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _` irule >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
 `i IN tn1.t_mem` by
   (qpat_x_assum `!n b sz i. local_region _ _ s1 _ _ _ /\ _ ==> _` irule >>
    goal_assum (drule_at Any) >> simp[]) >>
 qpat_x_assum `!n b sz i. local_region _ _ s0 _ _ _ /\ _ ==> _` irule >>
 goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem annassign_local_region_frame_iff_ptr:
 !cenv scopes s t.
 (!name entry p sz. lookup_scopes name scopes = SOME entry /\
   FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
   lookup_var p t = lookup_var p s) ==>
 !n b sz. local_region cenv scopes s n b sz <=> local_region cenv scopes t n b sz
Proof
 simp[local_region_def] >> metis_tac[]
QED
