(*
 * FmpLowering's stage simulation at block level: the entry into a block
 * after a jump, and one source exec_block from a related point matched by
 * the target's block run.  The INVOKE case is the hypothesis
 * fmp_invoke_sim, which the runner induction (fmpStageRunner) discharges.
 *
 * TOP-LEVEL:
 *   fmp_stage_block_entry - a jump's block entry keeps the relation
 *   fmp_stage_block_sim   - one exec_block, from a point before its restores
 *)
Theory fmpStageBlockSim
Ancestors
  fmpStageRel o1PassContract ptrDiscipline contextCodegenRel
  venomExecSemantics venomState venomInst finite_map words list

Theorem fmp_stage_block_entry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn bi sb /\ active_inst fn bi sb /\
  MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn sb lo tb ts /\
  step_inst k C bi sb = OK (jump_to lbl sb) /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  enters_block fn (jump_to lbl sb) s1 /\ active_inst fn inst s1 ==>
  ?t1. enters_block fn' (jump_to lbl tb) t1 /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
      (entry_prov fn (jump_to lbl sb) G)
      (entry_taint_vars fn (jump_to lbl sb) tn) fn s1 lo t1 ts
Proof
  cheat
QED

Theorem fmp_stage_block_sim:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  (!ivk s2. fmp_invoke_sim rpolicy D C C' vs vs' fmp eom k ivk s2) /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block k C bb s = r /\ terminates r ==>
  ?fn' bb' k' r'.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block k' C' bb' t = r' /\
    fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts r r'
Proof
  cheat
QED
