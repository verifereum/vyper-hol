(* The scoped outcomes use the ordinary expression pre/post conditions.
   A selected visit is scoped on the caller spine, with descent through a
   single pending edge; its chronological prefix also retains child visits. *)
Theory entryCreateFocusSpec
Ancestors
  entryCreateCompletedCut entryCreateOperandReplay entryCreateBodyCut
  entryCreateNativeResume bodyFullIfExpReach bodyFullPreds createMarkedPath
  createSizePrefixReplay createExprSizeExitDefs s1PrefixDefs exprSimFullBundleProps
  fragExec gasExplicitSites gasOutcomeFull gasSummary fragGasOrigin
  dftGasFromListTraceDefs venomInst venomExecSemantics abiEncoderProps relation list pair

Definition create_operand_exit_post_def:
  create_operand_exit_post ctx cx H res ee gt r <=>
    expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)
End

Definition create_operand_vv_post_def:
  create_operand_vv_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t <=>
    ?tv. res = INL tv /\
      vv_post H ctx func ce cx e es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
           ~is_bytestring_type (post_value_type ce e) ==>
           vv_own ce cx (post_value_type ce e) sa sb ee tv vv t /\
           (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                 eval_operand (vv_operand vv) t = SOME w ==>
                 w2n w + type_memory_size rt <= lo /\
                 (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                        val_in_memory rt val (w2n w) mem)) /\
      (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
               ptr_buf_ok ce e op G t) /\
      (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce e p.ptr_operand G t) /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn
End

Definition expr_sim_scoped_def:
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es <=>
    !st0 sa sb sha shb op s0 G0 tn0.
      expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
        ce cx ty e es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
      scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (cx_tops cx) cx st0 sa sb (bind (eval_expr cx e) (read_result cx))
        (es,s0,G0,tn0)
        (expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,op,G0,tn0))
        (create_operand_exit_post ctx cx)
End

Definition expr_vv_sim_scoped_def:
  expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es <=>
    !st0 sa sb sha shb vv s0 G0 tn0.
      expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
        ce cx ty e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
      scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (cx_tops cx) cx st0 sa sb (eval_expr cx e) (es,s0,G0,tn0)
        (\H res ee G tn t.
          create_operand_vv_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0)
            H res ee G tn t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (create_operand_exit_post ctx cx)
End

(* Replay at the given invocation, with its original all-horizon ghosts. *)
Theorem expr_sim_scoped_completed:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty e es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
  gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,op,G0,tn0))
Proof
  rw[expr_sim_scoped_def] >> irule scoped_outcome_completed_operand >> simp[] >>
  qexists_tac `create_operand_exit_post ctx cx` >> res_tac
QED

Theorem expr_vv_sim_scoped_completed:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
  gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb (eval_expr cx e) (es,s0,G0,tn0)
    (create_operand_vv_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0))
Proof
  rw[expr_vv_sim_scoped_def] >> first_x_assum drule >> strip_tac >>
  drule_all scoped_outcome_completed_operand >>
  simp[gas_completed_operand_def] >> metis_tac[]
QED

Definition create_operand_at_def:
  create_operand_at c s <=>
    s.vs_current_bb = c.cs_current_bb /\ s.vs_inst_idx = LENGTH c.cs_current_insts
End

Definition create_operand_fetch_def:
  create_operand_fetch sa sb func s inst <=>
    ~create_operand_at sb s /\ inst.inst_id IN frag_ids sa sb /\
    ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
         get_instruction bb s.vs_inst_idx = SOME inst
End

(* Only completed caller edges advance the caller cursor. The edge consumes
   the entire native child trace, if any, and that trace supplies its marks. *)
Definition create_operand_native_step_def:
  create_operand_native_step sa sb explicit ctx func p (d,k,u,left) (d',k',v,all) <=>
    ?inst. create_operand_fetch sa sb func u inst /\
      let chunk = ((p,d,inst.inst_id),func,inst,u)::trace_step p d k ctx func inst u in
        create_prefix_step sa sb explicit ctx func u (create_cut_marks explicit chunk) v /\
        create_trace_from p d k ctx func u = chunk ++ create_trace_from p d' k' ctx func v /\
        all = left ++ chunk
End

Definition create_interior_visit_def:
  create_interior_visit sa sb explicit ctx func (p,d,k) s0 (before,hit,after) <=>
    create_operand_at sa s0 /\
    create_trace_from p d k ctx func s0 = before ++ hit::after /\
    ?d' k' u left inst.
      RTC (create_operand_native_step sa sb explicit ctx func p) (d,k,s0,[]) (d',k',u,left) /\
      create_operand_fetch sa sb func u inst /\
      let visit = ((p,d',inst.inst_id),func,inst,u) in
        (before = left /\ hit = visit) \/
        (?inside suffix. before = left ++ visit::inside /\
          trace_step p d' k' ctx func inst u = inside ++ hit::suffix)
End

Definition create_operand_cut_def:
  create_operand_cut sa sb explicit ctx func tops cx st0 source (es,s) <=>
    !p d k before hit after.
      create_interior_visit sa sb explicit ctx func (p,d,k) s (before,hit,after) ==>
      create_body_cut explicit tops cx st0 source (es,s) (before,hit)
End

Theorem create_operand_empty_scope:
  create_operand_at sa s ==>
  create_operand_full_scope sa sa explicit ctx func s [] (OK s) /\
  ~create_interior_visit sa sa explicit ctx func (p,d,k) s (before,hit,after)
Proof
  simp[create_operand_at_def, create_operand_full_scope_def, create_expr_prefix_marked,
       create_interior_visit_def, create_operand_fetch_def, frag_ids_def]
QED

Theorem create_trace_from_fetch:
  create_operand_fetch sa sb func s inst ==>
  ?rest. create_trace_from p d k ctx func s =
    ((p,d,inst.inst_id),func,inst,s)::(trace_step p d k ctx func inst s ++ rest)
Proof
  simp[create_operand_fetch_def, create_trace_from_def] >> strip_tac >>
  drule trace_block_visit >> simp[]
QED

(* Chronological descent does not require a completed INVOKE. *)
Theorem create_interior_pending_at_entry:
  create_operand_at sa s /\ create_operand_fetch sa sb func s inst /\
  trace_step p d k ctx func inst s = inside ++ hit::suffix ==>
  ?after. create_interior_visit sa sb explicit ctx func (p,d,k) s
    (((p,d,inst.inst_id),func,inst,s)::inside,hit,after)
Proof
  strip_tac >> drule create_trace_from_fetch >>
  disch_then (qspecl_then [`p`,`k`,`d`,`ctx`] strip_assume_tac) >>
  rename1 `create_trace_from p d k ctx func s = _ :: (_ ++ rest)` >>
  qexists_tac `suffix ++ rest` >> simp[create_interior_visit_def, APPEND_ASSOC] >>
  qexistsl_tac [`d`,`k`,`s`,`[]`,`inst`] >> simp[] >> metis_tac[]
QED

(* A one-instruction administrative prefix owns its visit, even when the
   continuation itself starts at a CREATE. It cannot own the exit visit. *)
Theorem create_admin_visit_at_entry:
  create_operand_at sa s /\ create_operand_fetch sa sb func s inst /\
  inst.inst_opcode <> INVOKE /\ ~MEM inst.inst_opcode [CREATE;CREATE2] ==>
  ?after. create_interior_visit sa sb explicit ctx func (p,d,k) s
            ([],((p,d,inst.inst_id),func,inst,s),after) /\
          create_body_cut explicit tops cx st0 source (es,s)
            ([],((p,d,inst.inst_id),func,inst,s))
Proof
  strip_tac >> drule create_trace_from_fetch >>
  disch_then (qspecl_then [`p`,`k`,`d`,`ctx`] strip_assume_tac) >>
  qexists_tac `rest` >>
  simp[create_interior_visit_def, trace_step_noninvoke, create_body_cut_def,
       venomRunBoundedTheory.inst_create_size_ok_def] >> conj_tac
  >- (qexists_tac `k` >> simp[]) >>
  fs[] >> metis_tac[]
QED

(* Project the exact chronological prefix into the companion's marked
   caller spine. Pending child marks belong to the selected prefix, not to
   a completed caller edge, so this projection stops at the caller fetch. *)
Theorem create_operand_native_prefix:
  !x y. RTC (create_operand_native_step sa sb explicit ctx func p) x y ==>
  !d k s d' k' u left.
    x = (d,k,s,[]) /\ y = (d',k',u,left) ==>
    create_expr_prefix sa sb explicit ctx func s (create_cut_marks explicit left) u
Proof
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> conj_tac
  >- simp[create_expr_prefix_marked] >>
  simp_tac bool_ss [FORALL_PROD,create_operand_native_step_def,LET_THM] >>
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `create_prefix_step _ _ _ _ _ _ (create_cut_marks explicit chunk) _` >>
  gvs[] >>
  irule entryCreatePathScopeTheory.create_expr_prefix_append >>
  first_assum (irule_at Any) >>
  simp[create_expr_prefix_marked] >> irule RTC_SINGLE >> simp[create_marked_edge_def]
QED

Theorem create_interior_visit_cases:
  create_interior_visit sa sb explicit ctx func (p,d,k) s (before,hit,after) ==>
  (?d' u inst.
      create_expr_prefix sa sb explicit ctx func s (create_cut_marks explicit before) u /\
      create_operand_fetch sa sb func u inst /\ hit = ((p,d',inst.inst_id),func,inst,u)) \/
  (?d' k' u inst left inside suffix.
      create_expr_prefix sa sb explicit ctx func s (create_cut_marks explicit left) u /\
      create_operand_fetch sa sb func u inst /\ inst.inst_opcode = INVOKE /\
      before = left ++ ((p,d',inst.inst_id),func,inst,u)::inside /\
      trace_step p d' k' ctx func inst u = inside ++ hit::suffix)
Proof
  simp[create_interior_visit_def] >> strip_tac >>
  drule create_operand_native_prefix >> simp[GSYM PULL_FORALL] >>
  strip_tac >> gvs[] >>
  metis_tac[trace_step_noninvoke, APPEND_eq_NIL, NOT_CONS_NIL]
QED

(* The reviewed CREATE companion takes a genuinely universal certificate:
   the two scoped judgments must be available for all its inputs. *)
Theorem create_operand_completed_of_scoped:
  (!DF lo d PG tops ctx shctx func shfunc ce env ty es.
     body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
     expr_body_pre ce cx env e es ==>
     expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es /\
     expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es) ==>
  create_operand_completed_ok cx e
Proof
  pure_rewrite_tac[create_operand_completed_ok_def,GSYM create_operand_vv_post_def] >>
  disch_tac >> rpt gen_tac >> strip_tac >> conj_tac >> rpt gen_tac >> strip_tac >>
  `cx_tops cx = tops` by fs[bodySimTheory.body_inv_def,gasContextTheory.cx_tops_def] >>
  qpat_x_assum `cx_tops cx = tops` (SUBST_ALL_TAC o SYM) >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> strip_tac >>
     irule body_inv_no_phi >>
     fs[expr_sim_full_pre_def, expr_vv_sim_full_pre_def] >> metis_tac[]) >>
  FIRST [irule expr_sim_scoped_completed, irule expr_vv_sim_scoped_completed] >>
  rpt (goal_assum (drule_at Any)) >> metis_tac[]
QED
