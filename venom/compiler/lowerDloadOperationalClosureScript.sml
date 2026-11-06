Theory lowerDloadOperationalClosure
Ancestors
  lowerDloadOpaqueExecution lowerDloadReachability venomExecSemantics
  lowerDloadFrameCertificate lowerDloadReturnBoundary
  lowerDloadOwnership lowerDloadProvenanceSupport list

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

   Reachability reconstruction (existing proved interfaces, not a new lemma):
   ld_annotated_erasure maps astk to MAP ld_erase_frame astk, AP to
   MAP (OPTION_MAP SND) AP, and AG to ld_erase AG. With o1_ctx_shape CS,
   ld_frame_reachable_prefix then gives

     ?s0. ld_stack_origin vs0 CS (MAP ld_erase_frame astk) source s0 /\
           frame_reach CS source s0 ri sr.

   ld_stack_origin_member and o1_ctx_shape_distinct_block_labels supply the
   distinct-label premise of ld_frame_return_complete. Thus a terminal
   step_inst fuelR CS ri sr = IntRet ret send gives

     ?s0 fuelS.
       ld_stack_origin vs0 CS (MAP ld_erase_frame astk) source s0 /\
       frame_reach CS source s0 ri sr /\
       run_blocks fuelS CS source s0 = IntRet ret send.

   Types: vs0,s0,sr,send : venom_state; CS : venom_context;
   source : ir_function; ri : instruction; fuelR,fuelS : num.

   This corrects the stronger old claim that source completion is unavailable:
   completion IS reconstructible from annotated terminal reachability. It is
   not reconstructible from a terminal equation alone. It also does not yet
   provide the paired exit certificate or target/source terminal alignment.

   At a call, ld_stack_origin_cons gives, for the SAME erased saved frame f,
     ?caller0 nm ops args.
       ld_stack_origin vs0 CS stk f.cf_fn caller0 /\
       frame_reach CS f.cf_fn caller0 f.cf_inst f.cf_state /\
       f.cf_inst.inst_opcode = INVOKE /\
       decode_invoke f.cf_inst = SOME (nm,ops) /\
       lookup_function nm CS.ctx_functions = SOME callee /\
       eval_operands ops f.cf_state = SOME args /\
       setup_callee callee args f.cf_state = SOME s0.
   Thus assembly may retain existential s0 together with its setup equation.
   ld_completed_callee_resume_owned needs precisely such a setup equation and
   the completed run FROM THAT SAME s0. It does not require the existential
   caller0 to equal a separately chosen historical caller origin. If a
   recursive consumer fixes cs in advance, setup functionality can identify
   s0 with cs only after the saved frame, callee, args and setup equations
   have been aligned. No uniqueness of operational histories is claimed.
   At root, the base origin fixes ctx_entry, lookup_function, fn_entry_label
   and the initial control update of vs0; it is not arbitrary setup_callee.

   Origin/setup bridge implemented below as ld_stack_origin_setup_eq:
     ld_stack_origin vs0 CS (f::stk) callee s0 /\
     decode_invoke f.cf_inst = SOME (nm,ops) /\
     lookup_function nm CS.ctx_functions = SOME callee /\
     eval_operands ops f.cf_state = SOME args /\
     setup_callee callee args f.cf_state = SOME cs ==> s0 = cs.
   This is an origin/setup functionality boundary, NOT whole temporal closure.
   It uses f : call_frame (the erased frame), stk : call_frame list,
   nm : string, ops : operand list, args : 256 word list, cs : venom_state.

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
   Historical coverage inventory (superseded for ordinary data closure by
   ld_normal_ordinary_backward in lowerDloadNormalDispatchTheory). Missing
   producer entries below describe the earlier audit, not current source.
   Temporal, call, allocation, external and terminal gaps remain separate;
   local certificates are NOT temporal successor proofs:
   Coverage table:
   family                          existing local producer / remaining interface
   PARAM, RETPC_PARAM              ParamProducer, RetpcProducer / entry alignment
   ASSIGN, PHI                     AssignProducer, PhiProducer / active_inst, PCs
   ADD,SUB,OFFSET                  AffineProducer, OrdinaryExecution / alignment
   MUL,Div,Mod,SDIV,SMOD,Exp,
     ADDMOD,MULMOD,SLT,SGT,ISZERO,
     AND,OR,XOR,NOT                ScalarProducer / supported operand premises
   EQ,LT,GT                        CompareProducer / owner geometry, alignment
   SHL,SHR,SAR                     ShiftProducer / clean shift selector, alignment
   ALLOCA                         AllocaProducer / owner creation, temporal next
   DLOAD                          LoadCertificate / macro completion, temporal next
   DLOADBYTES                     BytesProducer / macro completion, temporal next
   MLOAD                          MloadProducer / observed range, temporal next
   MSTORE                         StoreCertificate / mask bound, temporal next
   JMP,JNZ,DJMP                   JumpProducer / clean selectors, block lookup+PHI
   RET                            nonopaque_ret_backward / terminal reach+exit data
   INVOKE                         resume_owned / completed run+full exit certificate
   MSTORE8,MCOPY                   no complete simultaneous producer inventoried
   SLOAD,SSTORE,TLOAD,TSTORE,
     ILOAD,ISTORE                  no complete simultaneous producer inventoried
   MEMTOP,DALLOCA,DRET,GETFMP,
     SETFMP,RETFMP,INITIAL_FMP,
     BUMP,FMP_PARAM               must prove excluded or supply boundary; not done
   SIGNEXTEND,BYTE                not in scalar family above; boundary not inventoried
   NOP                            data identity alone insufficient; next annotation open
   RETURN,REVERT,STOP,SINK,
     SELFDESTRUCT,INVALID         terminal observation / revert-forward exit open
   ASSERT,ASSERT_UNREACHABLE       clean guard and abort/next cases not integrated
   CALLER,CALLVALUE,CALLDATALOAD,CALLDATASIZE,CALLDATACOPY,
     ADDRESS,ORIGIN,GASPRICE,GAS,GASLIMIT,COINBASE,TIMESTAMP,NUMBER,
     PREVRANDAO,CHAINID,SELFBALANCE,BALANCE,BLOCKHASH,BASEFEE,
     CODESIZE,CODECOPY,EXTCODESIZE,EXTCODEHASH,EXTCODECOPY,
     RETURNDATASIZE,RETURNDATACOPY,BLOBHASH,BLOBBASEFEE,
     SHA3,CALL,STATICCALL,DELEGATECALL,CREATE,CREATE2,LOG:
       no complete simultaneous producer inventoried for these families;
       require state-only environment/request agreement, range coverage and
       output/taint effects, or an explicit source-shape exclusion theorem.
   This covers every opcode constructor, including opcodes possibly excluded
   by the stage shape: exclusion must itself be checked before omitting cases.
   Geometry/memory/account clauses exist for several local producers, but
   strict-tail reserve and saved-support transport must be threaded across
   transitions. Common-label jump does not establish annotated block entry.
   No row above establishes the complete observation or revert-forward mode.

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

Theorem ld_stack_origin_setup_eq:
  ld_stack_origin vs0 CS (f::stk) callee s0 /\
  decode_invoke f.cf_inst = SOME (nm,ops) /\
  lookup_function nm CS.ctx_functions = SOME callee /\
  eval_operands ops f.cf_state = SOME args /\
  setup_callee callee args f.cf_state = SOME cs ==>
  s0 = cs
Proof
  strip_tac >>
  qpat_x_assum `ld_stack_origin _ _ _ _ _` mp_tac >>
  simp[ld_stack_origin_cons] >> strip_tac >> gvs[]
QED

Theorem ld_annotated_call_pop:
  o1_ctx_shape C /\
  ld_annotated_reachable vs0 C (f::stk) k L AP AG tn callee ri sr /\
  step_inst fuelR C ri sr = IntRet ret send /\
  f.lf_inst.inst_opcode = INVOKE /\
  decode_invoke f.lf_inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops f.lf_state = SOME args /\
  setup_callee callee args f.lf_state = SOME cs /\
  bind_outputs f.lf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.lf_state send)) = SOME s' ==>
  ?fuelS.
    run_blocks fuelS C callee cs = IntRet ret send /\
    step_inst fuelS C f.lf_inst f.lf_state = OK s' /\
    (!inst'. active_inst f.lf_fn inst'
       (s' with vs_inst_idx := SUC f.lf_state.vs_inst_idx) ==>
     ld_annotated_reachable vs0 C stk k f.lf_local f.lf_params
       (DRESTRICT f.lf_prov (COMPL (set f.lf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.lf_tvar
         (COMPL (set f.lf_inst.inst_outputs)))
       f.lf_fn inst' (s' with vs_inst_idx := SUC f.lf_state.vs_inst_idx))
Proof
  strip_tac >>
  drule ld_annotated_erasure >> strip_tac >>
  drule_all ld_frame_reachable_prefix >> strip_tac >>
  gvs[MAP] >>
  `s0 = cs` by
    (irule ld_stack_origin_setup_eq >>
     goal_assum (drule_at Any) >> simp[ld_erase_frame_def]) >>
  gvs[] >>
  `MEM callee C.ctx_functions` by metis_tac[ld_stack_origin_member] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks)` by
    (drule o1_ctx_shape_distinct_block_labels >> simp[EVERY_MEM]) >>
  drule_all ld_frame_return_complete >> strip_tac >>
  qexists_tac `m` >> simp[] >> conj_tac
  >- (irule completed_callee_invoke_ok >> goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >> irule ld_annotated_reachable_ret >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[ld_annotated_active_inst]
QED

(* Recover setup from the actual saved head, not from a caller IH. *)
Theorem ld_annotated_return_pop:
  o1_ctx_shape C /\
  ld_annotated_reachable vs0 C (f::stk) k L AP AG tn callee ri sr /\
  step_inst fuelR C ri sr = IntRet ret send /\
  bind_outputs f.lf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.lf_state send)) = SOME s' ==>
  ?nm ops args cs fuelS.
    f.lf_inst.inst_opcode = INVOKE /\
    decode_invoke f.lf_inst = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops f.lf_state = SOME args /\
    setup_callee callee args f.lf_state = SOME cs /\
    run_blocks fuelS C callee cs = IntRet ret send /\
    step_inst fuelS C f.lf_inst f.lf_state = OK s' /\
    (!inst'. active_inst f.lf_fn inst'
       (s' with vs_inst_idx := SUC f.lf_state.vs_inst_idx) ==>
     ld_annotated_reachable vs0 C stk k f.lf_local f.lf_params
       (DRESTRICT f.lf_prov (COMPL (set f.lf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.lf_tvar
         (COMPL (set f.lf_inst.inst_outputs)))
       f.lf_fn inst' (s' with vs_inst_idx := SUC f.lf_state.vs_inst_idx))
Proof
  strip_tac >> drule ld_annotated_erasure >> strip_tac >>
  drule_all ld_frame_reachable_prefix >> strip_tac >>
  fs[MAP, ld_stack_origin_cons, ld_erase_frame_def] >>
  drule_all ld_annotated_call_pop >> strip_tac >>
  qexists_tac `fuelS` >> asm_rewrite_tac[]
QED

(* Fixed-stack origin functionality aligns a prefix with a consumer's s0;
   it does not assert uniqueness of execution histories. *)
Theorem ld_stack_origin_unique:
  ld_stack_origin vs0 C stk fn s0 /\
  ld_stack_origin vs0 C stk fn s1 ==> s0 = s1
Proof
  Cases_on `stk`
  >- (simp[Once ld_stack_origin_cases] >> rpt strip_tac >>
      gvs[Once ld_stack_origin_cases]) >>
  simp[ld_stack_origin_cons] >> rpt strip_tac >> gvs[]
QED

Theorem ld_annotated_prefix_at_origin:
  o1_ctx_shape C /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  ld_stack_origin vs0 C (MAP ld_erase_frame astk) fn s0 ==>
  frame_reach C fn s0 i s
Proof
  strip_tac >> drule ld_annotated_erasure >> strip_tac >>
  drule_all ld_frame_reachable_prefix >> strip_tac >>
  metis_tac[ld_stack_origin_unique]
QED

(* RECURSIVE CONSUMER AUDIT (C2.coverage.recursive_interface, after E0326).
   Non-theorem design checkpoint. Nothing in this comment is an axiom,
   definition, admitted theorem, or claim of completed recursive coverage.
   The historical inventory above is not the current ordinary interface.

   INDUCTION CHOICE AND ITS LIMIT
   The actual target relation is ptrDisciplineTheory.frame_reachable, not
   run_blocks. Its generated rule induction is frame_reachable_ind:
     !P. entry_clause P /\ next_clause P /\ block_clause P /\
         call_clause P /\ ret_clause P ==>
         !vs0 CT stk PG G un gn j t.
           frame_reachable vs0 CT stk PG G un gn j t ==>
           P vs0 CT stk PG G un gn j t.
   Here the five clause names above denote, IN THIS COMMENT ONLY, the five
   universally quantified rule implications at ptrDisciplineScript.sml
   457-508 with P added for each recursive premise. There is exactly one
   recursive premise in each non-entry rule, not a second completed-run IH.
   In full, their execution/control premises after that recursive premise are:
     entry: ctx_entry/lookup_function/fn_entry_label, enters_block from the
       initial control update, active_inst;
     next: active_inst gn j t, ~is_terminator j.inst_opcode,
       j.inst_opcode <> INVOKE, step_inst fuel CT j t = OK t1,
       active_inst gn j1 (t1 with vs_inst_idx := SUC t.vs_inst_idx);
     block: active_inst gn j t, is_terminator j.inst_opcode,
       step_inst fuel CT j t = OK t1, ~t1.vs_halted,
       enters_block gn t1 t2, active_inst gn j1 t2;
     call: active_inst gn inv t, inv.inst_opcode = INVOKE,
       decode_invoke inv = SOME(nm,ops), lookup_function nm
       CT.ctx_functions = SOME callee, eval_operands ops t = SOME args,
       setup_callee callee args t = SOME ct, enters_block callee ct t1,
       active_inst callee j1 t1;
     ret: active_inst gn j t, step_inst fuel CT j t = IntRet ret tend,
       bind_outputs f.cf_inst.inst_outputs ret.iret_values
         (adopt_return_fmp ret (merge_callee_state f.cf_state tend)) = SOME t1,
       active_inst f.cf_fn j1
         (t1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx).
   next updates G to step_prov PG G j t1 and un to step_taint j t t1 un;
   block uses entry_prov and entry_taint_vars; call pushes the actual saved
   call_frame and clears local G/t_var; ret restores the saved PG/G/t_var.
   Those are the signatures of the source rules, not a fuel-induction IH.
   Choosing this induction matches taint_within's quantifier and gives the
   terminal target instruction in ret. It does NOT give a completed source
   callee run. ld_annotated_call_pop reconstructs that run from the source
   terminal annotation produced by the invariant. A run_ind proof instead
   needs a result-indexed strengthened postcondition, including terminal
   annotations; ordinary forward simulation does not supply it backwards.

   CANDIDATE NORMAL ANCHOR: exact clause inventory
   A target frame_reachable witness fixes stk,PG,G,un,gn,j,t. The intended
   existential source witnesses include astk,k,L,AP,AG,tn,fn,i,s. A tempting
   target annotation alignment would use
     MAP ld_erase_frame bstk = stk /\
     MAP (OPTION_MAP SND) BPT = PG /\ ld_erase BHT = G /\
     ld_annotated_reachable vs0 CT bstk h HT BPT BHT un gn j t.
   IMPORTANT: HT,BPT,BHT here are DISTINCT from the normal-data H,BP,BH.
   In particular HT includes actual scratch ALLOCAs. ld_frame_embedding
   pairs every entry of H with L; a target annotation local table also has
   scratch entries, so using H for HT would be wrong after the first DLOAD.
   Alternatively the coverage induction can keep raw target annotations
   without manufacturing a second target ld_annotated_reachable witness.
   The bridge from raw target stack/provenance to normal-data gstk/BH is
   unresolved; no equality to those normal-data tables is being assumed.
   The normal anchor fragment itself is exactly
     ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
     ld_normal_data CS fn V U lo E L H AP BP AG BH tn ua s ta
       astk live keys (32 * SUM (MAP CARD suspended)) A suspended gstk f /\
     V = set(fn_ir_vars fn) /\ U = {v | v IN V /\ ~retpc_var fn v} /\
     lower_dload_function_supply fa fn = (gn,fb) /\
     fn.fn_blocks = bpre ++ bb::bpost /\
     lower_dload_blocks_supply fa bpre = (qpre,a0) /\
     lower_dload_block_supply a0 bb = (gb,a3) /\
     lower_dload_blocks_supply a3 bpost = (qpost,fb) /\
     gn.fn_blocks = qpre ++ gb::qpost /\
     bb.bb_instructions = pre ++ i::post /\
     lower_dload_insts_supply a0 pre = (p,a1) /\
     lower_dload_inst_supply a1 i = (code,a2) /\
     lower_dload_insts_supply a2 post = (tail,a3) /\
     gb.bb_instructions = p ++ code ++ tail /\
     lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     lookup_block ta.vs_current_bb gn.fn_blocks = SOME gb /\
     s.vs_current_bb = ta.vs_current_bb /\
     s.vs_prev_bb = ta.vs_prev_bb /\
     s.vs_inst_idx = LENGTH pre /\ ta.vs_inst_idx = LENGTH p.
   Actual incoming fa must come from the configured context fold, not an
   arbitrary existence of a function supply. Likewise keys must be the set
   of scratch ALLOCA IDs from those actual block/instruction folds.

   Normal-mode phase conclusion at this anchor is the explicit disjunction
     (n = 0 /\ t = ta /\ un = ua /\ j = HD code) \/
     (0 < n /\ n < LENGTH code /\
       ld_target_prefix CT code ta ua n t un /\ j = EL n code).
   Both alternatives require ~in_revert_forward fn s; the second preserves
   the OLD source annotation and old normal_data, not normal_data at t.
   There is no EL (LENGTH code) code branch. Completion produces a source
   OK step, successor annotation and a new anchor for the next segment or
   block. A DLOAD strict prefix at n=1 contains its scratch allocation; n=2
   has ADD's code offset; n=3 has CODECOPY's memory; these are not source
   DLOAD successors. DLOADBYTES has the analogous ADD/CODECOPY prefix.
   Existing load/bytes certificates establish local effects; they do not
   yet preserve every normal_data companion or the configured next anchor.

   The indexed saved-data obligation is NOT a single caller-independent V:
     LENGTH astk = LENGTH gstk /\ LENGTH supports = LENGTH astk /\
     LENGTH savedkeys = LENGTH astk /\ LENGTH suspended = LENGTH astk /\
     (!q. q < LENGTH astk ==>
       ld_saved_embedded
         {v | v IN EL q supports /\ ~retpc_var (EL q astk).lf_fn v}
         E (EL q savedkeys)
         (32 * SUM (MAP CARD (DROP (SUC q) suspended)))
         (EL q suspended) (EL q astk) (EL q gstk) /\
       (!v. v IN EL q supports ==>
         (lookup_var v (EL q astk).lf_state = NONE <=>
          lookup_var v (EL q gstk).lf_state = NONE)) /\
       (!v. (case FLOOKUP (EL q astk).lf_tvar v of NONE => {} | SOME m => m)
         SUBSET count 32) /\
       (!v. (case FLOOKUP (EL q gstk).lf_tvar v of NONE => {} | SOME m => m)
         SUBSET count 32)).
   ld_saved_indexed_cons/frame are checked destructors for exactly this
   data schema. They do not prove saved configured INVOKE position matching,
   the saved parameter envelope, or identification gstk=bstk. These remain
   extra required control/parameter fields, not consequences of this schema.
   Scratch bounds must also retain, for the same erased source stack,
     LIST_REL (\A g. FINITE A /\ CARD A <= LENGTH
       (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
       (A::suspended) (fn::MAP (\f. f.cf_fn) (MAP ld_erase_frame astk)).
   Seen configured scratch sites A are per frame and persist across loops;
   cardinality cannot count executions instead of sites.

   COMPLETED CALL EXIT (execution part, exact candidate)
   With cs fixed by setup_callee callee args saved_source = SOME cs and
   target terminal step step_inst fuelT CT rj tr = IntRet ret tend, require
     ?fuelS send k1 L1 AP1 AG1 tn1 ri sr.
       run_blocks fuelS CS callee cs = IntRet ret send /\
       ld_annotated_reachable vs0 CS (sf::astk) k1 L1 AP1 AG1 tn1
         callee ri sr /\ active_inst callee ri sr /\
       step_inst fuelS CS ri sr = IntRet ret send /\
       ret.iret_adopt_fmp = NONE.
   This retains the SAME ret record needed by bind_outputs; equal return
   values alone are not the record equality required by resume_owned.
   ld_annotated_prefix_at_origin, ld_stack_origin_setup_eq and
   ld_frame_return_complete reconstruct completion, then fuel_mono can lift
   source witnesses to a common fuel. ld_completed_callee_resume_owned
   supplies only caller owned variables after binding. Full exit data must
   additionally relate CURRENT send/tend memory, storage and taints, restore
   the caller's allocation maps/frontiers and parameter envelope, drop the
   callee's live owners, and advance the saved configured positions. No
   predicate currently packages/proves this exit. send is not automatically
   sr (though a RET-specific theorem can show this); cs is before entry PHIs.

   CONSTRUCTOR/PREMISE LEDGER (checked source interfaces versus open work)
   - Global environment: ctx_pass_stage and stage lookup/function facts
     provide configured function mapping. ptr_discipline, o1_ctx_shape,
     mem_inv dload_headroom_ok and callee_first are frozen source hypotheses
     via o1_src_inv; they are not target induction hypotheses.
   - Entry: actual target enters_block is in the entry rule. Function/block
     supply entry and PHI preservation are checked; frame_data_source_entry
     is only reflexive data. Packaged target-to-source normal_data entry,
     configured scratch key set and initial phase remain unproved.
   - next ordinary: ld_normal_ordinary_backward supplies a single source OK
     and every data field; ld_normal_ordinary_next_backward adds annotation;
     lower_dload_configured_segment_next and ld_ordinary_segment_coverage /
     its configured trace consumer handle sequential positions and iteration.
     Shape/operand support come from annotated inst_wf/original support;
     opaque_use_ok/fn_ptr_ok come from source invariant. These are not new
     semantic gaps. Block lookup preservation is checked for the ordinary
     finite family. Comparison's fixed source origin is obtained using
     ld_annotated_prefix_at_origin; scratch cardinality remains an invariant
     obligation at call/macro boundaries.
   - next ALLOCA: ld_alloca_normal_data_backward produces s',E',k',L',H'
     and step provenance, taints, live geometry and account. AP,BP,astk,
     gstk,keys,A,suspended stay fixed. Saved data needs E extension support
     on its selected live owners; configured singleton position and annotated
     next must still be installed, not inferred from normal_data.
     Fresh zero size: E' adds (old source frontier,old target frontier,0),
     live inserts (0,k); strict endpoints reduce to old frontier bounds.
     Cached: E'=E, live unchanged and frontiers unchanged. Current operand
     size need NOT equal cached sz; exec_alloca ignores it after lookup.
   - next macro: retain anchor at strict prefixes, then complete the source
     step once. Scratch allocation changes A/account, not source L. A DLOAD
     executed again reuses its scratch slot. Prefix source annotation is IH;
     completed normal_data/annotation and seen-site bounds are open work.
   - block: target OK/enters_block is an actual rule premise. JumpProducer
     gives common clean selectors, not paired entry PHIs, new provenance,
     configured position or full entered data. These are still control work.
   - call: one IH at caller, target setup/entry in rule. Paired argument
     evaluation, push of indexed saved data/control and callee normal_data
     entry remain obligations. o1LowerDloadJointCall.ld_joint_boundary_call
     is checked but FORWARD and consumes source setup/entry plus its own
     occurrence relation. It is not backward coverage or this normal_data
     interface; reuse its setup/PHI reasoning, do not invoke it as that IH.
   - ret: one IH at terminal callee instruction, actual target IntRet/bind in
     rule. Nonopaque RET backward gives a common record. Source completion
     is reconstructed at the saved setup origin, then annotated_call_pop
     supplies caller annotation. Full current-memory/data/control resumption
     remains open. o1LowerDloadJointReturn.ld_joint_ret_step is forward and
     returns a jr with equal values, not necessarily the SAME ret token.
   - revert-forward: ~in_revert_forward is required by ordinary wrappers.
     Its negation cannot be dropped. An exact alternate memory/observation
     invariant for copy/revert and intervening assignments is still missing;
     requiring normal_data throughout this mode would hide the exception.
   - terminal/external: frame_reachable stops at observations; taint_within
     still quantifies their read ranges. Existing observation/dead transport
     consumes clean source observations, but phase and revert-forward cases,
     external output effects and terminal alignment remain obligations.

   SMALLEST PRECISE OBSTRUCTION / NEXT RECOMMENDED SEMANTIC BOUNDARY
   A CLOSED GLOBAL CANDIDATE CANNOT YET BE ASSERTED. In addition to the open
   saved-control and revert-mode fields above, the accepted ALLOCA interface
   has an immediate use-site mismatch:
     s.vs_alloca_next + w2n n < dimword(:256) /\
     t.vs_alloca_next + w2n n < dimword(:256).
   Current dload_headroom_ok bounds s.vs_alloca_next plus the CONTEXT scratch
   budget, not the next original allocation. Target step OK imposes no word
   bound: exec_alloca uses unbounded natural addition. The normal_data IH
   bounds existing sites, not a future allocation of w2n n.

   For a FRESH source site, the legitimate route is to construct the source
   exec_alloca success separately (singleton literal syntax is required;
   a clean/equal evaluated scalar operand alone does not suffice),
   establish the next source active instruction from block shape, obtain
   source raw_reachable there, and use mem_inv headroom at that successor.
   Since the new source frontier is old+w2n n, and ld_alloc_account plus
   stack/cardinality bounds charges target excess against the context scratch
   budget, arithmetic can then give BOTH requested endpoint inequalities.
   Invoking the backward normal producer to obtain that source successor
   first is circular. Raw memory alone gives only a source word bound; the
   scratch budget and account are essential for the target inequality.

   For a CACHED site even this argument does NOT yield old+w2n n < dimword:
   source future frontier is just old. This remains so for fixed literal
   allocations on revisits; old can have advanced since the first visit.
   No falsehood of the frozen theorem is claimed. The sufficient local
   producer's hypotheses are stronger than what recursive coverage supplies.
   Recommended next semantic obligation: a source-success/future-headroom
   boundary distinguishing fresh and cached ALLOCA, with conclusion
     ?s1. step_inst fuelS CS i s = OK s1 /\
       (FLOOKUP s.vs_allocas i.inst_id = NONE ==>
         s.vs_alloca_next + w2n n + 32 * ctx_dload_count CS < dimword(:256)).
   Its premises must explicitly provide source current annotation/shape,
   operand evaluation and source mem_inv headroom, plus next activity (or a
   checked shape derivation of it); it must NOT assume source success or
   the desired endpoint bounds. Cached normal-data closure must bypass the
   unnecessarily strong operand-size endpoint premise using the unchanged
   frontier and old site bounds. Strategist authorization is required for
   either new theorem; accepted statements cannot be changed by this audit.

   Types of the displayed terms: vs0,s,ta,t,cs,sr,send,tend : venom_state;
   CS,CT : venom_context; fn,gn,callee : ir_function; i,j,ri,rj : instruction;
   astk,bstk,gstk : ld_saved_frame list; stk : call_frame list;
   V,U : string set; supports : string set list; keys,A : num set;
   savedkeys,suspended : num set list; live : (num # num) set;
   E : (num # num) |-> (num # num # num); L,H : num |-> ((num # num) # num # num);
   AP,BP : ((num # num) # num # num) option list;
   AG,BH : string |-> ((num # num) # num # num); tn,ua,un : taint;
   k,h,n,f,lo,fuelS,fuelT : num; code,p,tail,pre,post : instruction list.
   Supply variables have the type inferred from lower_dload_*_supply;
   they are not legacy integer fresh-ID arithmetic.
*)
