(* Counted statement simulations over the actual source action. *)
Theory stmtSimDefs
Ancestors
  exprSimDefs loweringPosts gasOutcome gasContext allocaHistory
  stmtLowering compileEnv loweringSlice vyperInterpreter vyperState
  venomState venomExecSemantics vyperTypeEnvPreservation finite_map
  vyperEvalExprPreservesScopesDom

Definition stmt_res_ok_def:
  stmt_res_ok lctx (res : unit + exception) <=>
    res = INL () \/
    (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str)) \/
    (?v. res = INR (ReturnException v)) \/
    ((res = INR BreakException \/ res = INR ContinueException) /\
     ?ex inc. lctx = InLoop ex inc)
End

Definition stmt_exit_def:
  stmt_exit RetQ es' (res : unit + exception) r <=>
    expr_exit res r \/
    ?v. res = INR (ReturnException v) /\
        RetQ v (es' with scopes := []) r
End

(* The allocations of s0 made before sa (instruction id below
   sa.cs_next_id) that are clear of every local live at es keep their bytes
   in t, and are still clear of every local live at es' in t, where cenv'
   names the locals' pointers. *)
Definition alloca_frame_def:
  alloca_frame cenv es sa s0 cenv' es' t <=>
    !aid off sz.
      FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                 off + sz <= b \/ b + sz' <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory /\
      !n b sz'. local_region cenv' es'.scopes t n b sz' ==>
                off + sz <= b \/ b + sz' <= off
End

(* Where a statement lowered from sa to sb, started in s0 related at es,
   ends with result res, related at ee: landed where res goes, the
   variables handed out before sa and the allocations of s0 kept, and the
   older allocations clear of the live locals kept (alloca_frame).  The
   statement writes only live locals and its own allocations, and a local
   it declares sits in an allocation of its own (instruction id sa or
   above), so the buffer of an expression lowered before it (a loop's
   iterable) survives it. *)
Definition stmt_post_def:
  stmt_post ctx func cx lctx cenv cenv' sa sb es s0 res ee t <=>
    ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      alloca_frame cenv es sa s0 cenv'' ee t
End

Definition stmt_framed_frag_def:
  stmt_framed_frag Frame ctx func cx lctx RetQ cenv
    (m : compile_env compiler) source es <=>
    !sa sb s0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ret_pc_ok cenv sa s0 /\ ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      Frame s0 /\ stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) source (es, s0)
        (stmt_post ctx func cx lctx cenv cenv' sa sb es s0)
        (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
End

Definition stmt_frag_def:
  stmt_frag ctx func cx lctx RetQ cenv m source es <=>
    stmt_framed_frag (K T) ctx func cx lctx RetQ cenv m source es
End

Definition stmt_frag_mem_def:
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (m : compile_env compiler) source es <=>
    !sa sb s0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ret_pc_ok cenv sa s0 /\ ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      return_buf_frame d cenv sa s0 /\
      stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func) source (es, s0)
        (\res ee t. ?cenv''.
          stmt_lands lctx sb res t /\ ~t.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
          cenv_top_ext cenv cenv'' ee.scopes /\
          stmt_state_rel ctx func cenv'' cx ee t /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x t = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b) /\
          return_buf_frame d cenv'' sb t /\ alloca_history func t /\
          s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
End

Definition alloca_prefix_def:
  alloca_prefix cap (s:venom_state) <=>
    cap <= s.vs_alloca_next /\
    !aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) ==> cap <= b
End

Theorem stmt_exit_loop_ctl:
  !RetQ es rr.
    ~stmt_exit RetQ es (INL ()) rr /\
    ~stmt_exit RetQ es (INR BreakException) rr /\
    ~stmt_exit RetQ es (INR ContinueException) rr
Proof
  rw[stmt_exit_def] >> Cases_on `rr` >> simp[expr_exit_def]
QED

(* ===== The older-allocation frame ===== *)

Theorem alloca_frame_trans:
  alloca_frame c0 e0 sa0 s0 c1 e1 s1 /\ alloca_frame c1 e1 sa1 s1 c2 e2 s2 /\
  sa0.cs_next_id <= sa1.cs_next_id /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s1.vs_allocas aid = SOME b) ==>
  alloca_frame c0 e0 sa0 s0 c2 e2 s2
Proof
  rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s1.vs_allocas _ = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >- (res_tac >> simp[]) >- decide_tac >>
      first_assum ACCEPT_TAC) >>
  strip_tac >> conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC
QED

(* A step that writes neither memory nor variables, and keeps the scopes'
   names, keeps the frame. *)
Theorem alloca_frame_same:
  MAP FDOM es'.scopes = MAP FDOM es.scopes /\
  t.vs_memory = s.vs_memory /\ t.vs_vars = s.vs_vars ==>
  alloca_frame cenv es sa s cenv es' t
Proof
  rewrite_tac[alloca_frame_def] >> rpt strip_tac >- simp[] >>
  first_x_assum irule >>
  fs[local_region_def, lookup_var_def] >>
  `IS_SOME (lookup_scopes n es.scopes)` by
    metis_tac[vyperTypeEnvPreservationTheory.lookup_scopes_same_fdoms_some] >>
  fs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

(* A local live at es' in s, where es' has the scopes' names of es, is
   one live at es in s0 at the same region: its pointer variable is
   handed out before sa, so s keeps its value. *)
Theorem local_region_kept:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es'.scopes = MAP FDOM es.scopes /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w) /\
  local_region cenv es'.scopes s n b sz ==>
  local_region cenv es.scopes s0 n b sz
Proof
  rw[local_region_def] >>
  `IS_SOME (lookup_scopes n es.scopes)` by
    metis_tac[vyperTypeEnvPreservationTheory.lookup_scopes_same_fdoms_some] >>
  gvs[optionTheory.IS_SOME_EXISTS] >> rename1 `lookup_scopes n es.scopes = SOME e0` >>
  `local_ptrs_rel func cenv es.scopes s0` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  fs[local_ptrs_rel_def] >>
  first_x_assum (qspecl_then [`n`, `e0`, `p`, `sz`] mp_tac) >> simp[] >>
  strip_tac >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  res_tac >> gvs[]
QED

(* The memory frame expr_post, vv_post and target_post give, over a
   fragment that keeps the scopes' names, is an alloca_frame. *)
Theorem alloca_frame_of_mem_frame:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es'.scopes = MAP FDOM es.scopes /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w) /\
  (!aid off sz.
     FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) ==>
     mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) ==>
  alloca_frame cenv es sa s0 cenv es' s
Proof
  rw[alloca_frame_def] >> metis_tac[local_region_kept]
QED

(* Leaving the innermost scope keeps the frame: the locals below it are
   bound in cenv as in cenv' (cenv_top_ext). *)
Theorem alloca_frame_pop:
  alloca_frame c0 es sa s0 c ee t /\ cenv_top_ext cenv c ee.scopes /\
  ee.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  alloca_frame c0 es sa s0 cenv (ee with scopes := rest) t
Proof
  rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  gvs[local_region_def] >>
  `n NOTIN FDOM sc` by (strip_tac >> res_tac >> gvs[]) >>
  `FLOOKUP c.ce_vars n = FLOOKUP cenv.ce_vars n` by
    (CCONTR_TAC >> fs[cenv_top_ext_def] >> res_tac >> gvs[]) >>
  qexists_tac `n` >> gvs[lookup_scopes_def, FLOOKUP_DEF]
QED


(* A step that writes neither memory nor variables keeps the frame. *)
Theorem alloca_frame_same_state:
  alloca_frame c0 e0 sa s0 c ee t /\
  u.vs_memory = t.vs_memory /\ u.vs_vars = t.vs_vars ==>
  alloca_frame c0 e0 sa s0 c ee u
Proof
  rewrite_tac[alloca_frame_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> conj_tac >- fs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!n b sz'. local_region c ee.scopes t _ _ _ ==> _` irule >>
  fs[local_region_def, lookup_var_def] >> metis_tac[]
QED

(* An expression's fragment from sa to sm, then a fragment that keeps the
   frame from sm, keeps it from sa. *)
Theorem alloca_frame_expr_prefix:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM em.scopes = MAP FDOM es.scopes /\
  sa.cs_next_id <= sm.cs_next_id /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  (!aid off sz.
     FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) ==>
     mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
  alloca_frame cenv em sm t c ee u ==>
  alloca_frame cenv es sa s0 c ee u
Proof
  strip_tac >>
  `alloca_frame cenv es sa s0 cenv em t` by
    (irule alloca_frame_of_mem_frame >> metis_tac[]) >>
  irule alloca_frame_trans >> metis_tac[]
QED

(* An empty innermost scope binds no local. *)
Theorem alloca_frame_push_pre:
  alloca_frame c (es with scopes := FEMPTY :: es.scopes) sa s0 c' ee t <=>
  alloca_frame c es sa s0 c' ee t
Proof
  simp[alloca_frame_def, local_region_def, lookup_scopes_def]
QED

(* Evaluating and reading an expression keeps the scopes' names. *)
Theorem eval_read_preserves_scopes_dom:
  bind (eval_expr cx e) (read_result cx) st = (res, st') ==>
  MAP FDOM st'.scopes = MAP FDOM st.scopes
Proof
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >>
  imp_res_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
  gvs[]
QED

Theorem expr_post_alloca_frame:
  expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes ==>
  alloca_frame cenv es sa s0 cenv ee t
Proof
  rw[expr_post_def] >> irule alloca_frame_of_mem_frame >> metis_tac[]
QED

Theorem vv_post_alloca_frame:
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes ==>
  alloca_frame cenv es sa s0 cenv ee t
Proof
  rw[vv_post_def] >> irule alloca_frame_of_mem_frame >> metis_tac[]
QED

Theorem target_post_alloca_frame:
  target_post ctx func cenv cx es sa sb s0 ee pv vt r t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes ==>
  alloca_frame cenv es sa s0 cenv ee t
Proof
  rw[target_post_def] >> irule alloca_frame_of_mem_frame >> metis_tac[]
QED

(* A store into a local live after an expression's fragment (s, es1), which
   writes only n0 bytes of the local's region, keeps the frame: an alloca
   clear of es's locals is clear of the written bytes. *)
Theorem alloca_frame_local_store:
  alloca_frame c es sa s0 c es1 s /\
  stmt_state_rel ctx func c cx es s0 /\ local_ptrs_reserved c sa /\
  MAP FDOM es1.scopes = MAP FDOM es.scopes /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w) /\
  local_region c es1.scopes s id b z /\ n0 <= z /\
  MAP FDOM ee.scopes = MAP FDOM es1.scopes /\
  (!n q z'. FLOOKUP c.ce_vars n = SOME (PtrVar (Var q) z') ==>
            lookup_var q t = lookup_var q s) /\
  (!ad len. ad + len <= b \/ b + n0 <= ad ==>
     mem_bytes_at ad len t.vs_memory = mem_bytes_at ad len s.vs_memory) ==>
  alloca_frame c es sa s0 c ee t
Proof
  strip_tac >>
  `local_region c es.scopes s0 id b z` by
    (irule local_region_kept >> metis_tac[]) >>
  qpat_x_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[alloca_frame_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  Q.SUBGOAL_THEN `off + sz <= b \/ b + z <= off` assume_tac
  >- (qpat_x_assum `!n b sz'. local_region c es.scopes s0 _ _ _ ==> _` irule >>
      qexists_tac `id` >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `!ad len. _ ==> mem_bytes_at ad len t.vs_memory = _`
        (qspecl_then [`off`, `sz`] mp_tac) >>
      impl_tac >- decide_tac >>
      disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!n b sz'. local_region c es1.scopes s _ _ _ ==> _` irule >>
  qexists_tac `n` >> fs[local_region_def] >>
  `IS_SOME (lookup_scopes n es1.scopes)` by
    metis_tac[vyperTypeEnvPreservationTheory.lookup_scopes_same_fdoms_some] >>
  fs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED
