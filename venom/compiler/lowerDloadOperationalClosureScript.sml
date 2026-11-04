Theory lowerDloadOperationalClosure
Ancestors
  lowerDloadOpaqueExecution lowerDloadReachability venomExecSemantics
  lowerDloadFrameCertificate lowerDloadReturnBoundary

(* IntRet assembly is already completed_callee_invoke_ok, imported above.
   Terminal propagation is one result-polymorphic boundary rather than
   duplicate Halt and Abort assembly lemmas. This consumes a completed run;
   it does not produce that run or its exit certificate. *)
Theorem ld_completed_callee_invoke_terminal:
  i.inst_opcode = INVOKE /\
  decode_invoke i = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs /\
  run_blocks fuel C callee cs = result /\
  ((?send. result = Halt send) \/ (?a send. result = Abort a send)) ==>
  step_inst fuel C i s = result
Proof
  strip_tac >> simp[Once step_inst_def]
QED

(* Conditional integration: a recursive IH must supply the completed source
   run and common return record. send/tend are completed result states, not
   assumed to be the instruction states at the final RET. Saved memory is
   not used; merge_callee_state retains each completed callee's shared state.
   All exit facts about send/tend remain available to consumers unchanged. *)
Theorem ld_completed_callee_resume_owned:
  f.lf_inst.inst_opcode = INVOKE /\
  decode_invoke f.lf_inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops f.lf_state = SOME args /\
  setup_callee callee args f.lf_state = SOME cs /\
  run_blocks fuel C callee cs = IntRet ret send /\
  ret.iret_adopt_fmp = NONE /\
  f.lf_inst.inst_outputs = g.lf_inst.inst_outputs /\
  bind_outputs g.lf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.lf_state tend)) = SOME t' /\
  ld_saved_embedded V E keys d A f g ==>
  ?s'. step_inst fuel C f.lf_inst f.lf_state = OK s' /\
    bind_outputs f.lf_inst.inst_outputs ret.iret_values
      (merge_callee_state f.lf_state send) = SOME s' /\
    ld_owned_vars V E
      (DRESTRICT f.lf_prov (COMPL (set f.lf_inst.inst_outputs)))
      (DRESTRICT g.lf_prov (COMPL (set g.lf_inst.inst_outputs)))
      (entry_taint with t_var := DRESTRICT f.lf_tvar
        (COMPL (set f.lf_inst.inst_outputs)))
      (entry_taint with t_var := DRESTRICT g.lf_tvar
        (COMPL (set g.lf_inst.inst_outputs))) s' t'
Proof
  strip_tac >> gvs[adopt_return_fmp_def] >>
  drule ld_bind_outputs_target_exists >>
  disch_then (qspec_then `merge_callee_state f.lf_state send` strip_assume_tac) >>
  qexists_tac `s'` >> simp[] >> conj_tac
  >- (irule completed_callee_invoke_ok >>
      goal_assum (drule_at Any) >> simp[adopt_return_fmp_def] >> metis_tac[]) >>
  drule ld_saved_embedded_return_vars >>
  disch_then (qspecl_then [`tend`,`send`] assume_tac) >>
  drule_all ld_owned_bind_outputs >> simp[]
QED

(* Operational interface audit (not an admitted simulation statement).

   Locations must be distinguished:
     ss/ts       setup_callee results, before parallel entry PHIs;
     s/t         active instruction states, after entry PHIs;
     send/tend   completed run_blocks result states;
     s'/t'       restored caller states, before the explicit index increment.
   In particular, ld_annotated_reachable applies at s, not automatically ss
   or send.  An exit certificate cannot simply reuse a boundary certificate.

   The concrete boundary fields already expressible with existing constants
   are the following HOL terms (all variables are schematic):

     ld_annotated_reachable vs0 CS astk k L AP AG tn source i s
     ld_annotated_reachable vs0 CT bstk h H BP BH un target j t
     lower_dload_function_supply supply source = (target,supply')
     ld_owned_vars {v | v IN V /\ ~retpc_var source v}
       E AG BH tn un s t
     (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE))
     LIST_REL (ld_owned_selection E) AP BP
     (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))
     ld_frame_embedding E L H s t
     ld_alloc_account keys d A s t
     ld_byte_rel (ld_site_bytes E live)
       tn.t_mem un.t_mem s.vs_memory t.vs_memory

   These are NOT a sufficient complete boundary: fixed-memory correspondence,
   observable nonmemory agreement, live-owner selection, stack support and the
   strict-tail reserve equation still need exact producer-compatible terms.
   Using arbitrary R in ld_byte_rel or arbitrary d in ld_alloc_account would
   conceal, not solve, these missing interfaces.  In particular the stack
   needs per-frame nonopaque support, not one V shared by all functions.

   Required completed IntRet conclusion, for either run_blocks or exec_block,
   must retain BOTH the completed run and its terminal annotated provenance:

     ?fuelS send k' L' AP' AG' tn' ri sr fuelR.
       run_blocks fuelS CS source ss = IntRet ret send /\
       ld_annotated_reachable vs0 CS astk k' L' AP' AG' tn'
         source ri sr /\
       active_inst source ri sr /\
       step_inst fuelR CS ri sr = IntRet ret send

   This term has the required concrete existing predicates, but is only the
   execution/provenance part, NOT the missing complete exit certificate.
   For exec_block the first conjunct must instead be
     exec_block fuelS CS sourceBB s = IntRet ret send
   and for a synchronized non-expanded instruction it must be
     step_inst fuelS CS i s = OK s'
   with new boundary data at
     s' with vs_inst_idx := SUC s.vs_inst_idx.
   For an expanded instruction, keep the *old* source boundary and use
     ld_target_prefix CT expansion t un n tp up
   at strict prefixes n < LENGTH expansion.  At completion, the source step
   and its new annotated boundary must be produced; a strict prefix is not
   an exec_block exit.  No source run is inferred from the terminal equation.

   Producer audit:
   - Setup: ld_unequal_token_setup supplies cleared variable maps, labels and
     unequal defined tokens.  It does not supply entry PHIs or live memory.
   - RET: ld_nonopaque_ret_backward supplies the common ret record and local
     terminal equation.  It does not supply the original ss-to-sr execution.
   - INVOKE: completed_callee_invoke_ok and the terminal assembly above consume
     completed runs. ld_completed_callee_resume_owned additionally consumes
     the saved certificate and returns caller ownership. It is valid with
     V restricted to caller nonopaque support; whole-support definedness is
     separate and is not its conclusion.
   - Reachability: ld_annotated_reachable_call supplies callee entry from a
     reachable caller and enters_block; ld_annotated_reachable_ret supplies
     resumed caller reachability only from a reachable terminal instruction,
     its actual step equation, binding and next active_inst. Thus the
     provenance conjunct above is essential, not replaceable by run existence.
   - Geometry, memory, strict-tail reserve, request-change agreement, entry
     PHIs and all ordinary opcodes still require simultaneous producers.
     Conditional boundary helpers are not those producers.

   Fuel composition is NOT an unavailable-library blocker. In
   venomExecPropsTheory.fuel_mono the three conjuncts respectively state
     step_inst n C i s = r /\ (!e. r <> Error e) /\ n <= m ==>
       step_inst m C i s = r
   and the analogous exec_block and run_blocks equations. Thus successful
   subruns can be lifted to MAX of their witness fuels, with SUC on source
   run_blocks entry. The older crossBlockSimProps.run_blocks_fuel_mono has a
   terminates side condition; the direct three-way theorem is the appropriate
   interface. Error outcomes cannot be lifted this way, so a completed
   backward signature must not indiscriminately quantify over Error results.

   Audit conclusion: assembly is checked; a complete typed simultaneous
   signature has NOT yet been obtained. The boundary/exit fields above expose
   the remaining semantic design gap. Do not introduce a predicate or start
   run_ind on the strength of this partial list. Strategist review must fix
   the state-only observable, reserve and entry/exit provenance interfaces.
*)
