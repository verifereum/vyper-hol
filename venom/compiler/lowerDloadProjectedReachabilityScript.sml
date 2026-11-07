Theory lowerDloadProjectedReachability
Ancestors
  ptrDiscipline venomExecSemantics list finite_map

Theorem ld_frame_reachable_projected_ind:
  !P.
  (!vs0 ctx name fn lbl inst s1.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    enters_block fn
      (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                  vs_inst_idx := 0|>) s1 /\
    active_inst fn inst s1 ==>
    P vs0 ctx [] entry_taint fn inst s1) /\
  (!vs0 ctx stk tn fn inst inst' s s' fuel.
    P vs0 ctx stk tn fn inst s /\ active_inst fn inst s /\
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s = OK s' /\
    active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
    P vs0 ctx stk (step_taint inst s s' tn) fn inst'
      (s' with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!vs0 ctx stk tn fn inst inst' s s' s1 fuel.
    P vs0 ctx stk tn fn inst s /\ active_inst fn inst s /\
    is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
    ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
    P vs0 ctx stk (entry_taint_vars fn s' tn) fn inst' s1) /\
  (!vs0 ctx stk tn caller inv s nm ops callee args cs s1 inst.
    P vs0 ctx stk tn caller inv s /\ active_inst caller inv s /\
    inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME(nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    P vs0 ctx ((caller,inv,s,tn.t_var)::stk)
      (tn with t_var := FEMPTY) callee inst s1) /\
  (!vs0 ctx caller inv saved T stk tn fn rinst s ret s_end s' inst' fuel.
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
    P vs0 ctx (MAP (\f. (f.cf_fn,f.cf_inst,f.cf_state,f.cf_tvar)) stk)
      tn fn inst s
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac frame_reachable_ind >> simp[] >> metis_tac[]
QED
