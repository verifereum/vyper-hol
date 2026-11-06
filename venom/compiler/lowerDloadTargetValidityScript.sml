Theory lowerDloadTargetValidity
Ancestors
  lowerDloadProjectedReachability lowerDloadOwnership
  venomMemProps venomMemDefs venomExecProofs venomExecSemantics calleeTransport
  ptrDiscipline list

(* Unlike annotated source entry, frame_reachable entry does not reset the
   initial allocation map. Initial validity is therefore explicit. *)
Theorem ld_frame_reachable_alloca_inv:
  !vs0 CT stk PG G un gn j t.
    frame_reachable vs0 CT stk PG G un gn j t ==>
    (alloca_inv vs0 ==>
      alloca_inv t /\ (!g. MEM g stk ==> alloca_inv g.cf_state))
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> drule ld_enters_block_allocation_fields >> strip_tac >>
      gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[])
  >- (rpt strip_tac >> `alloca_inv s'` by metis_tac[alloca_inv_step_inst] >>
      gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[])
  >- (rpt strip_tac >> `alloca_inv s'` by metis_tac[alloca_inv_step_inst] >>
      drule ld_enters_block_allocation_fields >> strip_tac >>
      gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[])
  >- (rpt strip_tac >> gvs[] >>
      drule ld_enters_block_allocation_fields >> strip_tac >>
      gvs[setup_callee_def, AllCaseEqs()] >>
      irule alloca_inv_empty >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  drule ld_bind_outputs_allocas >> strip_tac >>
  drule bind_outputs_shared_fields >> strip_tac >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      adopt_return_fmp_allocas] >> metis_tac[]
QED

Theorem ld_frame_reachable_projected_geometry_ind:
  !P.
  (!vs0 ctx name fn lbl inst s1.
    alloca_inv vs0 /\
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    enters_block fn
      (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                  vs_inst_idx := 0|>) s1 /\
    active_inst fn inst s1 ==>
    P vs0 ctx [] entry_taint fn inst s1) /\
  (!vs0 ctx stk tn fn inst inst' s s' fuel.
    alloca_inv vs0 /\ alloca_inv s /\
    (!f i st tv. MEM (f,i,st,tv) stk ==> alloca_inv st) /\
    P vs0 ctx stk tn fn inst s /\ active_inst fn inst s /\
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s = OK s' /\
    active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
    P vs0 ctx stk (step_taint inst s s' tn) fn inst'
      (s' with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!vs0 ctx stk tn fn inst inst' s s' s1 fuel.
    alloca_inv vs0 /\ alloca_inv s /\
    (!f i st tv. MEM (f,i,st,tv) stk ==> alloca_inv st) /\
    P vs0 ctx stk tn fn inst s /\ active_inst fn inst s /\
    is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
    ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
    P vs0 ctx stk (entry_taint_vars fn s' tn) fn inst' s1) /\
  (!vs0 ctx stk tn caller inv s nm ops callee args cs s1 inst.
    alloca_inv vs0 /\ alloca_inv s /\
    (!f i st tv. MEM (f,i,st,tv) stk ==> alloca_inv st) /\
    P vs0 ctx stk tn caller inv s /\ active_inst caller inv s /\
    inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME(nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    P vs0 ctx ((caller,inv,s,tn.t_var)::stk)
      (tn with t_var := FEMPTY) callee inst s1) /\
  (!vs0 ctx caller inv saved T stk tn fn rinst s ret s_end s' inst' fuel.
    alloca_inv vs0 /\ alloca_inv s /\ alloca_inv saved /\
    (!f i st tv. MEM (f,i,st,tv) stk ==> alloca_inv st) /\
    P vs0 ctx ((caller,inv,saved,T)::stk) tn fn rinst s /\
    active_inst fn rinst s /\
    step_inst fuel ctx rinst s = IntRet ret s_end /\
    bind_outputs inv.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state saved s_end)) = SOME s' /\
    active_inst caller inst' (s' with vs_inst_idx := SUC saved.vs_inst_idx) ==>
    P vs0 ctx stk
      (tn with t_var := DRESTRICT T (COMPL (set inv.inst_outputs)))
      caller inst' (s' with vs_inst_idx := SUC saved.vs_inst_idx)) ==>
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    (alloca_inv vs0 ==>
      P vs0 ctx (MAP (\f. (f.cf_fn,f.cf_inst,f.cf_state,f.cf_tvar)) stk)
        tn fn inst s)
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac >>
  rpt strip_tac >>
  TRY (drule ld_frame_reachable_alloca_inv >> simp[] >> strip_tac) >>
  simp[] >> first_x_assum irule >> asm_rewrite_tac [] >>
  rpt gen_tac >> strip_tac >> gvs[MEM_MAP] >> metis_tac[]
QED

(* Initial discharge for the frozen task: o1_run_state_ok_def projects
   o1_initial_state_ok; unitTransformDefs.o1_initial_state_ok_def gives
   vs0.vs_allocas=FEMPTY, so venomMemProps.alloca_inv_empty applies.
   The geometry-enriched induction intentionally has no normal-data anchor:
   it supplies validity only of the actual current and suspended states.
   A segment anchor must separately retain its validity when it is chosen. *)
