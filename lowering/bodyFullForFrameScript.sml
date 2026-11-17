(* Accumulated full For frames, anchored at the original fragment entry. *)
Theory bodyFullForFrame
Ancestors
  stmtSimDefs ptrDiscipline allocaHistory loweringStateRelDefs compileEnv
  venomState vyperState finite_map

(* Scope cleanup changes only the final live-local part of the frame. *)
Theorem for_full_frame_pop:
  (alloca_history func t /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
   s0.vs_alloca_next <= t.vs_alloca_next /\
   (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
          lookup_var x t = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
            FLOOKUP t.vs_allocas aid = SOME b) /\
   (!x. not_fresh_at sa0 x ==>
        FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
   alloca_frame c0 e0 sa0 s0 c ee t /\
   (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!n b sz'. local_region c0 e0.scopes s0 n b sz' ==>
                 off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) /\
  cenv_top_ext cenv c ee.scopes /\ ee.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa0 x ==>
       FLOOKUP G x = FLOOKUP G0 x /\
       op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame c0 e0 sa0 s0 cenv (ee with scopes := rest) t /\
  (!aid off sz i.
     FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
     aid < sa0.cs_next_id /\
     (!n b sz'. local_region c0 e0.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >> drule_all alloca_frame_pop >> disch_tac >>
  asm_rewrite_tac[]
QED
