(* Oracle-bounded prefixes use an explicit stack, never an atomic INVOKE. *)
Theory guardedFrameReachable
Ancestors
  ptrDiscipline contextRawReachable

Inductive guarded_frame_reachable:
[~entry:]
  (!vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\
     active_inst fn inst s1 ==>
     guarded_frame_reachable vs0 ctx [] [] FEMPTY entry_taint fn inst s1)
[~next:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' fuel.
     guarded_frame_reachable vs0 ctx stk PG G tn fn inst s /\
     active_inst fn inst s /\
     ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
     (MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]
      ==> s.vs_outcomes <> []) /\
     step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     guarded_frame_reachable vs0 ctx stk PG (step_prov PG G inst s')
       (step_taint inst s s' tn) fn inst'
       (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' s1 fuel.
     guarded_frame_reachable vs0 ctx stk PG G tn fn inst s /\
     active_inst fn inst s /\
     is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     guarded_frame_reachable vs0 ctx stk PG (entry_prov fn s' G)
       (entry_taint_vars fn s' tn) fn inst' s1)
[~call:]
  (!vs0 ctx stk PG G tn caller inv s nm ops callee args cs s1 inst.
     guarded_frame_reachable vs0 ctx stk PG G tn caller inv s /\
     active_inst caller inv s /\
     inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     guarded_frame_reachable vs0 ctx
       (<| cf_fn := caller; cf_inst := inv; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
       (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1)
[~ret:]
  (!vs0 ctx f stk PG G tn fn rinst s ret s_end s' inst' fuel.
     guarded_frame_reachable vs0 ctx (f::stk) PG G tn fn rinst s /\
     active_inst fn rinst s /\
     step_inst fuel ctx rinst s = IntRet ret s_end /\
     bind_outputs f.cf_inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
       SOME s' /\
     active_inst f.cf_fn inst'
       (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
     guarded_frame_reachable vs0 ctx stk f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
       f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))
End

(* This projection does not assert the unrestricted codegen package. *)
Definition guarded_raw_reachable_def:
  guarded_raw_reachable vs ctx fn inst s <=>
    ?stk PG G tn. guarded_frame_reachable vs ctx stk PG G tn fn inst s
End
