(*
 * One ordinary instruction of FmpLowering's stage simulation, by opcode
 * class: the target runs the same instruction, and the two results are
 * related locally (the outputs, memory, the shared state, the frame
 * fields), or both halt or abort with related results.  fmpStageOpFrame
 * rebuilds the stage relation from the local result.
 *
 * This theory has the instructions that touch no memory or storage.
 *
 * TOP-LEVEL:
 *   fmp_stage_sim_scalar  - register arithmetic, comparisons, shifts
 *   fmp_stage_sim_read    - context reads, PARAM, ASSIGN, no-ops, asserts
 *)
Theory fmpStageOpSimPure
Ancestors
  fmpStageOpSimPureAffine fmpStageOpSimPureCompare fmpStageOpSimPureScalar
  fmpStageOpSimPureShift fmpStageOpSimPureRead fmpStageOpSimPureCopy
  fmpStageOpBase fmpStageRel o1LowerDloadRelocationKernel o1LowerDloadShared
  ptrStaticDiscipline ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst

(* Why: register arithmetic.  Pointer arithmetic (ADD/SUB on a pointer
   and a scalar) moves both sides by the same amount, so the result keeps
   the operand's site; pointer comparisons are within one nonempty site
   (access_ok), where the relocation preserves order and equality; every
   other operand is a scalar with no provenance and, but for shifts,
   untainted (taint_ok), so the values agree. *)
Theorem fmp_stage_sim_scalar:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; OFFSET] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\
        (!v. ~MEM v inst.inst_outputs ==>
             FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
             FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
        (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
           ?y. FLOOKUP t1.vs_vars v = SOME y /\
               (~retpc_var fn v ==>
                fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
                  (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
        ld_memory_agree (fmp_ld_sites sm) eom
          (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
        ld_shared_agree D s.vs_call_ctx.cc_address
          (step_taint inst s s1 tn) s1 t1 /\
        s1.vs_returndata = t1.vs_returndata /\
        ~s1.vs_halted /\ ~t1.vs_halted /\
        s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
        s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
        s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
        s1.vs_block_ctx = s.vs_block_ctx /\
        s1.vs_data_section = s.vs_data_section /\
        s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
        s1.vs_prev_hashes = s.vs_prev_hashes /\
        s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
        t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
        t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
        t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
        t1.vs_block_ctx = t.vs_block_ctx /\
        t1.vs_data_section = t.vs_data_section /\
        t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
        t1.vs_prev_hashes = t.vs_prev_hashes /\
        t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >> Cases_on `MEM inst.inst_opcode [ADD; SUB]`
  >- (drule_all fmp_stage_sim_affine >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [LT; GT; EQ]`
  >- (drule_all fmp_stage_sim_compare >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [SHL; SHR; SAR]`
  >- (drule_all fmp_stage_sim_shift >> simp[]) >>
  `MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET]`
    by gvs[listTheory.MEM] >>
  drule_all fmp_stage_sim_clean >> simp[]
QED

(* Why: reads of the shared context (ld_shared_agree, the frame fields),
   PARAM (fmp_params_rel, at the same positions), ASSIGN (the operand's
   value, provenance and taint carry over; a return pc's copy is a return
   pc, which the post exempts), and the no-ops and assertions (an untainted
   condition with no provenance, so both sides abort alike). *)
Theorem fmp_stage_sim_read:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [GAS; CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
     CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE;
     BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE; EXTCODEHASH;
     CALLDATALOAD; DLOAD; PARAM; ASSIGN; NOP; ASSERT; ASSERT_UNREACHABLE] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\
        (!v. ~MEM v inst.inst_outputs ==>
             FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
             FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
        (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
           ?y. FLOOKUP t1.vs_vars v = SOME y /\
               (~retpc_var fn v ==>
                fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
                  (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
        ld_memory_agree (fmp_ld_sites sm) eom
          (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
        ld_shared_agree D s.vs_call_ctx.cc_address
          (step_taint inst s s1 tn) s1 t1 /\
        s1.vs_returndata = t1.vs_returndata /\
        ~s1.vs_halted /\ ~t1.vs_halted /\
        s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
        s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
        s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
        s1.vs_block_ctx = s.vs_block_ctx /\
        s1.vs_data_section = s.vs_data_section /\
        s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
        s1.vs_prev_hashes = s.vs_prev_hashes /\
        s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
        t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
        t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
        t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
        t1.vs_block_ctx = t.vs_block_ctx /\
        t1.vs_data_section = t.vs_data_section /\
        t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
        t1.vs_prev_hashes = t.vs_prev_hashes /\
        t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode [PARAM; ASSIGN; NOP; ASSERT; ASSERT_UNREACHABLE]`
  >- (drule_all fmp_stage_sim_copy >> simp[]) >>
  `MEM inst.inst_opcode [GAS; CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE;
    CHAINID; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
    BLOBBASEFEE; CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE;
    BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE; EXTCODEHASH;
    CALLDATALOAD; DLOAD]` by gvs[listTheory.MEM] >>
  drule_all fmp_stage_sim_reads >> simp[]
QED
