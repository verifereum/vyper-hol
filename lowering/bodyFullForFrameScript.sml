(* Original-entry frame transport for full For simulations. *)
Theory bodyFullForFrame
Ancestors
  bodySimFull stmtSimDefs allocaHistory compileEnv venomState finite_map
  ptrDiscipline

Theorem for_full_frame_compose:
  (alloca_history func s1 /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s1) /\
   s0.vs_alloca_next <= s1.vs_alloca_next /\
   (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s1 = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
            FLOOKUP s1.vs_allocas aid = SOME b) /\
   (!x. not_fresh_at sa0 x ==>
        FLOOKUP G1 x = FLOOKUP G0 x /\
        op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
   alloca_frame c0 e0 sa0 s0 c1 e1 s1 /\
   (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!n b sz'. local_region c0 e0.scopes s0 n b sz' ==>
                 off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn1.t_mem ==>
      i IN tn0.t_mem)) /\
  (alloca_history func s2 /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s2) /\
   s1.vs_alloca_next <= s2.vs_alloca_next /\
   (!x w. not_fresh_at sa1 x /\ lookup_var x s1 = SOME w ==>
          lookup_var x s2 = SOME w) /\
   (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
            FLOOKUP s2.vs_allocas aid = SOME b) /\
   (!x. not_fresh_at sa1 x ==>
        FLOOKUP G2 x = FLOOKUP G1 x /\
        op_taint tn2 (Var x) = op_taint tn1 (Var x)) /\
   alloca_frame c1 e1 sa1 s1 c2 e2 s2 /\
   (!aid off sz i.
      FLOOKUP s1.vs_allocas aid = SOME (off,sz) /\
      aid < sa1.cs_next_id /\
      (!n b sz'. local_region c1 e1.scopes s1 n b sz' ==>
                 off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn2.t_mem ==>
      i IN tn1.t_mem)) /\
  sa0.cs_next_id <= sa1.cs_next_id /\
  (!x. not_fresh_at sa0 x ==> not_fresh_at sa1 x) ==>
  alloca_history func s2 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s2) /\
  s0.vs_alloca_next <= s2.vs_alloca_next /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s2 = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s2.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa0 x ==>
       FLOOKUP G2 x = FLOOKUP G0 x /\
       op_taint tn2 (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame c0 e0 sa0 s0 c2 e2 s2 /\
  (!aid off sz i.
     FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
     aid < sa0.cs_next_id /\
     (!n b sz'. local_region c0 e0.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN tn2.t_mem ==>
     i IN tn0.t_mem)
Proof
  strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- decide_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (irule alloca_frame_trans >> metis_tac[]) >>
  MATCH_MP_TAC alloca_taint_kept_trans >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
