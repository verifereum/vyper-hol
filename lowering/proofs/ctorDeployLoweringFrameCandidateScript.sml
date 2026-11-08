Theory ctorDeployLoweringFrameCandidate
Ancestors
  ctorDeployLoweringDefs ctorDeployLoweringFrameTrace e2eDeployChecks e2eDeployDefs
  vfmExecution vfmState vfmContext vfmOperation callTrace asmParseProofs evmStepSim
  vfmRunCall vfmHandleStep
Libs wordsLib finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset

Theorem pass_candidate_entry:
  deploy_state_rel tops
    [91w;96w;10w;95w;144w;129w;97w;0w;19w;144w;57w;
     96w;10w;144w;243w;91w;95w;128w;253w;
     0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w]
    am tx es /\ constructor_args_encode tops tx [] ==>
  ?ctxt rb.
    es.contexts = [(ctxt,rb)] /\ ctxt.pc = 0 /\ ctxt.stack = [] /\
    ctxt.jumpDest = NONE /\
    ctxt.msgParams.code =
    [91w;96w;10w;95w;144w;129w;97w;0w;19w;144w;57w;
     96w;10w;144w;243w;91w;95w;128w;253w;
     0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w] /\
    ctxt.msgParams.parsed = parse_code 0 FEMPTY ctxt.msgParams.code
Proof
  strip_tac >> fs[deploy_state_rel_def] >>
  `args_bytes = []` by metis_tac[constructor_args_encode_unique] >>
  gvs[]
QED


Theorem parse_segment_recurrence:
  segment <> [] /\ parse_opcode (segment ++ rest) = SOME op /\
  LENGTH (opcode op) = LENGTH segment ==>
  parse_code pc m (segment ++ rest) =
  parse_code (pc + LENGTH segment) (m |+ (pc,op)) rest
Proof
  strip_tac >> CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  Cases_on `segment` >> gvs[] >> simp[listTheory.DROP_APPEND]
QED

Theorem parse_jumpdest_tail:
  parse_opcode (91w :: rest) = SOME JumpDest
Proof
  simp[parse_opcode_cond_thm, wordsTheory.dimword_8]
QED

Theorem parse_push1_tail:
  parse_opcode (96w :: 10w :: rest) = SOME (Push 1 [10w])
Proof
  mp_tac (Q.SPECL [`1`, `[10w]`, `rest`] parse_opcode_push) >> simp[]
QED

Theorem pass_candidate_lookup0:
  FLOOKUP (parse_code 0 FEMPTY
    [91w;96w;10w;95w;144w;129w;97w;0w;19w;144w;57w;
     96w;10w;144w;243w;91w;95w;128w;253w;
     0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w]) 0 =
  SOME JumpDest
Proof
  irule parse_code_entry >> simp[parse_jumpdest_tail]
QED

Theorem pass_candidate_lookup1:
  FLOOKUP (parse_code 0 FEMPTY
    [91w;96w;10w;95w;144w;129w;97w;0w;19w;144w;57w;
     96w;10w;144w;243w;91w;95w;128w;253w;
     0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w]) 1 =
  SOME (Push 1 [10w])
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_jumpdest_tail, opcode_def] >>
  irule parse_code_entry >> simp[parse_push1_tail]
QED

Theorem jumpdest_first_step_probe:
  es.contexts = [(ctxt,rb)] /\ ctxt.pc = 0 /\ ctxt.jumpDest = NONE /\
  0 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed 0 = SOME JumpDest ==>
  (ISR (FST (step es)) \/
   (?ctxt'. (SND (step es)).contexts = [(ctxt',rb)] /\ ctxt'.pc = 1 /\
      ctxt'.stack = ctxt.stack /\ ctxt'.jumpDest = NONE /\
      ctxt'.msgParams = ctxt.msgParams))
Proof
  strip_tac >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def, static_gas_def] >>
  drule consume_gas_cases >> disch_then (qspec_then `1` mp_tac) >>
  strip_tac
  >- simp[inc_pc_or_jump_def, is_call_def, opcode_def, bind_def,
          get_current_context_def, return_def, set_current_context_def] >>
  mp_tac (Q.SPECL [`OutOfGas`, `es`] handle_step_single_context) >>
  simp[vfm_abort_def] >> strip_tac >> simp[]
QED

Theorem jumpdest_no_observation:
  es.contexts = [(ctxt,rb)] /\ ctxt.pc = 0 /\
  0 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed 0 = SOME JumpDest /\ obs.pending = NONE ==>
  (observe 1 es (r,es') obs).entries = obs.entries /\
  (observe 1 es (r,es') obs).pending = NONE
Proof
  strip_tac >> irule observe_no_root_call >>
  simp[observable_call_def, next_opcode_def] >>
  Cases_on `ctxt.msgParams.code = []` >> simp[]
QED

Theorem pass_candidate_first_step:
  deploy_state_rel tops
    [91w;96w;10w;95w;144w;129w;97w;0w;19w;144w;57w;
     96w;10w;144w;243w;91w;95w;128w;253w;
     0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w]
    am tx es /\ constructor_args_encode tops tx [] /\ obs.pending = NONE ==>
  (ISR (FST (step es)) \/
   (?ctxt' rb'. (SND (step es)).contexts = [(ctxt',rb')] /\ ctxt'.pc = 1)) /\
  (observe 1 es (step es) obs).entries = obs.entries /\
  (observe 1 es (step es) obs).pending = NONE
Proof
  strip_tac >> drule_all pass_candidate_entry >> strip_tac >>
  conj_tac
  >- (`0 < LENGTH ctxt.msgParams.code /\
       FLOOKUP ctxt.msgParams.parsed 0 = SOME JumpDest` by
        simp[pass_candidate_lookup0] >>
      drule_all jumpdest_first_step_probe >> metis_tac[]) >>
  Cases_on `step es` >> irule jumpdest_no_observation >>
  simp[pass_candidate_lookup0] >> metis_tac[]
QED

Theorem handle_step_root_terminal[local]:
  LENGTH es.contexts = 1 ==> ISR (FST (handle_step e es))
Proof
  strip_tac >> Cases_on `handle_step e es` >> Cases_on `q` >> simp[] >>
  drule handle_step_preserves_length_1 >> simp[] >> strip_tac >>
  `es.contexts <> []` by (strip_tac >> gvs[]) >>
  drule_all handle_step_inl_pops >> simp[]
QED

Theorem return_step_terminal_probe:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [0w;10w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME Return ==>
  ISR (FST (step es))
Proof
  strip_tac >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def, static_gas_def] >>
  simp[step_return_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  simp[pop_stack_def, assert_def, set_current_context_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       memory_expansion_info_def] >>
  simp[consume_gas_def, expand_memory_def, read_memory_def,
       set_return_data_def, finish_def, bind_def, ignore_bind_def,
       get_current_context_def, set_current_context_def, return_def] >>
  simp[assert_def, return_def, fail_def] >>
  IF_CASES_TAC >> simp[get_current_context_def, set_current_context_def] >>
  irule handle_step_root_terminal >> simp[]
QED

Theorem terminal_no_call_observer[local]:
  ISR (FST (step es)) /\ obs.pending = NONE /\
  (LENGTH es.contexts = d ==> ~observable_call (FST (HD es.contexts))) ==>
  (frame_obs_tr d obs es (step es)).entries = obs.entries /\
  (frame_obs_tr d obs es (step es)).pending = NONE
Proof
  strip_tac >> Cases_on `step es` >> gvs[] >>
  `((observe d es (q,r) obs).entries = obs.entries) /\
   ((observe d es (q,r) obs).pending = NONE)` by
    (irule observe_no_root_call >> simp[]) >>
  simp[Ntimes frame_obs_tr_def 2]
QED

Theorem return_suffix_no_observation[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [0w;10w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule terminal_no_call_observer >> simp[] >>
  conj_tac
  >- (irule return_step_terminal_probe >> simp[]) >>
  simp[observable_call_def, next_opcode_def] >>
  Cases_on `ctxt.msgParams.code = []` >> simp[]
QED

Theorem swap_last_step[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = a :: b :: tail /\
  ctxt.jumpDest = NONE /\ ctxt.pc < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Swap 0) ==>
  ISR (FST (step es)) \/
  ?ctxt'. (SND (step es)).contexts = [(ctxt',rb)] /\
    ctxt'.pc = ctxt.pc + 1 /\ ctxt'.stack = b :: a :: tail /\
    ctxt'.jumpDest = NONE /\ ctxt'.msgParams = ctxt.msgParams
Proof
  strip_tac >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def, static_gas_def] >>
  simp[step_swap_def, consume_gas_def, assert_def, return_def, fail_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def] >>
  IF_CASES_TAC >> simp[]
  >- (simp[inc_pc_or_jump_def, is_call_def, opcode_def, bind_def,
            get_current_context_def, return_def, set_current_context_def]) >>
  disj1_tac >> irule handle_step_root_terminal >> simp[]
QED

Theorem no_call_backward[local]:
  obs.pending = NONE /\
  (LENGTH es.contexts = d ==> ~observable_call (FST (HD es.contexts))) /\
  (ISL (FST (step es)) ==> !obs'. obs'.pending = NONE ==>
    (frame_obs_tr d obs' (SND (step es)) (step (SND (step es)))).entries = obs'.entries /\
    (frame_obs_tr d obs' (SND (step es)) (step (SND (step es)))).pending = NONE) ==>
  (frame_obs_tr d obs es (step es)).entries = obs.entries /\
  (frame_obs_tr d obs es (step es)).pending = NONE
Proof
  strip_tac >> Cases_on `step es` >> gvs[] >>
  `(observe d es (q,r) obs).entries = obs.entries /\
   (observe d es (q,r) obs).pending = NONE` by
    (irule observe_no_root_call >> simp[]) >>
  simp[Ntimes frame_obs_tr_def 2] >>
  Cases_on `ISR q \/ LENGTH r.contexts < d` >> simp[] >>
  Cases_on `q` >> gvs[] >>
  first_x_assum (qspec_then `observe d es (INL x,r) obs` mp_tac) >> simp[]
QED

Theorem swap_return_suffix[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [10w;0w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc + 1 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 1) = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule no_call_backward >> simp[] >>
  reverse conj_tac
  >- (simp[observable_call_def, next_opcode_def] >>
      Cases_on `ctxt.msgParams.code = []` >> simp[]) >>
  strip_tac >> `ctxt.pc < LENGTH ctxt.msgParams.code` by simp[] >>
  drule_all swap_last_step >> strip_tac
  >- (Cases_on `step es` >> gvs[] >> Cases_on `q` >> gvs[]) >>
  gen_tac >> disch_tac >> irule return_suffix_no_observation >> simp[]
QED

Theorem push_step_boundary[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.jumpDest = NONE /\
  ctxt.pc < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Push n bytes) ==>
  ISR (FST (step es)) \/
  ?ctxt'. (SND (step es)).contexts = [(ctxt',rb)] /\
    ctxt'.pc = ctxt.pc + LENGTH (opcode (Push n bytes)) /\
    ctxt'.stack = word_of_bytes F 0w (REVERSE bytes) :: ctxt.stack /\
    ctxt'.jumpDest = NONE /\ ctxt'.msgParams = ctxt.msgParams
Proof
  strip_tac >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def, static_gas_def,
       step_push_def] >>
  qmatch_goalsub_abbrev_tac `consume_gas cost` >>
  simp[consume_gas_def, assert_def, return_def, fail_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def] >>
  IF_CASES_TAC >> simp[]
  >- (simp[push_stack_def, assert_def, return_def, fail_def,
           bind_def, ignore_bind_def, get_current_context_def,
           set_current_context_def] >>
      IF_CASES_TAC >> simp[]
      >- simp[inc_pc_or_jump_def, is_call_def, opcode_def, bind_def,
              get_current_context_def, return_def, set_current_context_def] >>
      disj1_tac >> irule handle_step_root_terminal >> simp[]) >>
  disj1_tac >> irule handle_step_root_terminal >> simp[]
QED

Theorem push10_step[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.jumpDest = NONE /\
  ctxt.pc < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Push 1 [10w]) ==>
  ISR (FST (step es)) \/
  ?ctxt'. (SND (step es)).contexts = [(ctxt',rb)] /\
    ctxt'.pc = ctxt.pc + 2 /\ ctxt'.stack = 10w :: ctxt.stack /\
    ctxt'.jumpDest = NONE /\ ctxt'.msgParams = ctxt.msgParams
Proof
  strip_tac >>
  `word_of_bytes F 0w [10w] = (10w:256 word)` by
    (simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
          byteTheory.word_slice_alt_zero] >> EVAL_TAC) >>
  drule_all push_step_boundary >> simp[opcode_def]
QED

Theorem codecopy_step_boundary[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [0w;19w;10w;0w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME CodeCopy ==>
  ISR (FST (step es)) \/
  ?ctxt'. (SND (step es)).contexts = [(ctxt',rb)] /\
    ctxt'.pc = ctxt.pc + 1 /\ ctxt'.stack = [0w] /\
    ctxt'.jumpDest = NONE /\ ctxt'.msgParams = ctxt.msgParams
Proof
  strip_tac >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def, static_gas_def] >>
  simp[step_copy_to_memory_def, pop_stack_def, assert_def,
       get_current_context_def, get_current_code_def, return_def,
       set_current_context_def, bind_def, ignore_bind_def,
       memory_expansion_info_def] >>
  simp[copy_to_memory_def, memory_expansion_info_def,
       get_current_context_def, return_def, bind_def, ignore_bind_def] >>
  qmatch_goalsub_abbrev_tac `consume_gas cost` >>
  simp[consume_gas_def, assert_def, return_def, fail_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def] >>
  IF_CASES_TAC >> simp[]
  >- (simp[expand_memory_def, write_memory_def, get_current_context_def,
           set_current_context_def, bind_def, ignore_bind_def, return_def] >>
      simp[inc_pc_or_jump_def, is_call_def, opcode_def, bind_def,
           get_current_context_def, return_def, set_current_context_def]) >>
  disj1_tac >> irule handle_step_root_terminal >> simp[]
QED

Theorem push_swap_return_suffix[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [0w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc + 3 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 2) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 3) = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule no_call_backward >> simp[] >> reverse conj_tac
  >- (simp[observable_call_def, next_opcode_def] >>
      Cases_on `ctxt.msgParams.code = []` >> simp[]) >>
  strip_tac >> `ctxt.pc < LENGTH ctxt.msgParams.code` by simp[] >>
  drule_all push10_step >> strip_tac
  >- (Cases_on `step es` >> gvs[] >> Cases_on `q` >> gvs[]) >>
  gen_tac >> disch_tac >> irule swap_return_suffix >> simp[]
QED

Theorem copy_return_suffix[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [0w;19w;10w;0w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc + 4 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME CodeCopy /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 1) = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 3) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 4) = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule no_call_backward >> simp[] >> reverse conj_tac
  >- (simp[observable_call_def, next_opcode_def] >>
      Cases_on `ctxt.msgParams.code = []` >> simp[]) >>
  strip_tac >> `ctxt.pc < LENGTH ctxt.msgParams.code` by simp[] >>
  drule_all codecopy_step_boundary >> strip_tac
  >- (Cases_on `step es` >> gvs[] >> Cases_on `q` >> gvs[]) >>
  gen_tac >> disch_tac >> irule push_swap_return_suffix >> simp[]
QED

Theorem dup_second_step[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [10w;0w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Dup 1) ==>
  ISR (FST (step es)) \/
  ?ctxt'. (SND (step es)).contexts = [(ctxt',rb)] /\
    ctxt'.pc = ctxt.pc + 1 /\ ctxt'.stack = [0w;10w;0w] /\
    ctxt'.jumpDest = NONE /\ ctxt'.msgParams = ctxt.msgParams
Proof
  strip_tac >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def, static_gas_def,
       step_dup_def] >>
  simp[consume_gas_def, assert_def, return_def, fail_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def] >>
  IF_CASES_TAC >> simp[]
  >- (simp[push_stack_def, assert_def, return_def, fail_def,
           bind_def, ignore_bind_def, get_current_context_def,
           set_current_context_def] >>
      simp[inc_pc_or_jump_def, is_call_def, opcode_def, bind_def,
           get_current_context_def, return_def, set_current_context_def]) >>
  disj1_tac >> irule handle_step_root_terminal >> simp[]
QED

Theorem parse_prefix_atoms[local]:
  parse_opcode (95w :: rest) = SOME (Push 0 []) /\
  parse_opcode (144w :: rest) = SOME (Swap 0) /\
  parse_opcode (129w :: rest) = SOME (Dup 1) /\
  parse_opcode (57w :: rest) = SOME CodeCopy /\
  parse_opcode (243w :: rest) = SOME Return /\
  parse_opcode (97w :: 0w :: 19w :: rest) = SOME (Push 2 [0w;19w])
Proof
  simp[parse_opcode_cond_thm, wordsTheory.dimword_8,
       vfmTypesTheory.take_pad_0_def, listTheory.PAD_RIGHT]
QED

Theorem parse_candidate_prefix[local]:
  parse_code 0 m
    ([91w;96w;10w;95w;144w;129w;97w;0w;19w;144w;57w;
      96w;10w;144w;243w] ++ rest) =
  parse_code 15
    (m |+ (0,JumpDest) |+ (1,Push 1 [10w]) |+ (3,Push 0 []) |+
       (4,Swap 0) |+ (5,Dup 1) |+ (6,Push 2 [0w;19w]) |+
       (9,Swap 0) |+ (10,CodeCopy) |+ (11,Push 1 [10w]) |+
       (13,Swap 0) |+ (14,Return)) rest
Proof
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_jumpdest_tail, opcode_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_push1_tail, opcode_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_prefix_atoms, opcode_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_prefix_atoms, opcode_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_prefix_atoms, opcode_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_prefix_atoms, opcode_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_prefix_atoms, opcode_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_prefix_atoms, opcode_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_push1_tail, opcode_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_prefix_atoms, opcode_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  simp[parse_prefix_atoms, opcode_def]
QED

Theorem candidate_prefix_lookups[local]:
  MEM (pc,op)
    [(0,JumpDest);(1,Push 1 [10w]);(3,Push 0 []);(4,Swap 0);
     (5,Dup 1);(6,Push 2 [0w;19w]);(9,Swap 0);(10,CodeCopy);
     (11,Push 1 [10w]);(13,Swap 0);(14,Return)] ==>
  FLOOKUP (parse_code 0 m
    ([91w;96w;10w;95w;144w;129w;97w;0w;19w;144w;57w;
      96w;10w;144w;243w] ++ rest)) pc = SOME op
Proof
  rewrite_tac[parse_candidate_prefix] >> strip_tac >>
  irule parse_code_preserves_below >>
  gvs[listTheory.MEM, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem push19_step[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.jumpDest = NONE /\
  ctxt.pc < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Push 2 [0w;19w]) ==>
  ISR (FST (step es)) \/
  ?ctxt'. (SND (step es)).contexts = [(ctxt',rb)] /\
    ctxt'.pc = ctxt.pc + 3 /\ ctxt'.stack = 19w :: ctxt.stack /\
    ctxt'.jumpDest = NONE /\ ctxt'.msgParams = ctxt.msgParams
Proof
  strip_tac >>
  `word_of_bytes F 0w [19w;0w] = (19w:256 word)` by
    (simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
          byteTheory.word_slice_alt_zero] >> EVAL_TAC) >>
  drule_all push_step_boundary >> simp[opcode_def]
QED

Theorem push0_step[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.jumpDest = NONE /\
  ctxt.pc < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Push 0 []) ==>
  ISR (FST (step es)) \/
  ?ctxt'. (SND (step es)).contexts = [(ctxt',rb)] /\
    ctxt'.pc = ctxt.pc + 1 /\ ctxt'.stack = 0w :: ctxt.stack /\
    ctxt'.jumpDest = NONE /\ ctxt'.msgParams = ctxt.msgParams
Proof
  strip_tac >> drule_all push_step_boundary >>
  simp[opcode_def, byteTheory.word_of_bytes_def]
QED

Theorem swap_copy_return_suffix[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [19w;0w;10w;0w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc + 5 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 1) = SOME CodeCopy /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 2) = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 4) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 5) = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule no_call_backward >> simp[] >> reverse conj_tac
  >- (simp[observable_call_def, next_opcode_def] >>
      Cases_on `ctxt.msgParams.code = []` >> simp[]) >>
  strip_tac >> `ctxt.pc < LENGTH ctxt.msgParams.code` by simp[] >>
  drule_all swap_last_step >> strip_tac
  >- (Cases_on `step es` >> gvs[] >> Cases_on `q` >> gvs[]) >>
  gen_tac >> disch_tac >> irule copy_return_suffix >> simp[]
QED

Theorem push19_return_suffix[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [0w;10w;0w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc + 8 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Push 2 [0w;19w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 3) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 4) = SOME CodeCopy /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 5) = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 7) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 8) = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule no_call_backward >> simp[] >> reverse conj_tac
  >- (simp[observable_call_def, next_opcode_def] >>
      Cases_on `ctxt.msgParams.code = []` >> simp[]) >>
  strip_tac >> `ctxt.pc < LENGTH ctxt.msgParams.code` by simp[] >>
  drule_all push19_step >> strip_tac
  >- (Cases_on `step es` >> gvs[] >> Cases_on `q` >> gvs[]) >>
  gen_tac >> disch_tac >> irule swap_copy_return_suffix >> simp[]
QED

Theorem dup_return_suffix[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [10w;0w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc + 9 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Dup 1) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 1) = SOME (Push 2 [0w;19w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 4) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 5) = SOME CodeCopy /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 6) = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 8) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 9) = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule no_call_backward >> simp[] >> reverse conj_tac
  >- (simp[observable_call_def, next_opcode_def] >>
      Cases_on `ctxt.msgParams.code = []` >> simp[]) >>
  strip_tac >> `ctxt.pc < LENGTH ctxt.msgParams.code` by simp[] >>
  drule_all dup_second_step >> strip_tac
  >- (Cases_on `step es` >> gvs[] >> Cases_on `q` >> gvs[]) >>
  gen_tac >> disch_tac >> irule push19_return_suffix >> simp[]
QED

Theorem swap_dup_return_suffix[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [0w;10w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc + 10 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 1) = SOME (Dup 1) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 2) = SOME (Push 2 [0w;19w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 5) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 6) = SOME CodeCopy /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 7) = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 9) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 10) = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule no_call_backward >> simp[] >> reverse conj_tac
  >- (simp[observable_call_def, next_opcode_def] >>
      Cases_on `ctxt.msgParams.code = []` >> simp[]) >>
  strip_tac >> `ctxt.pc < LENGTH ctxt.msgParams.code` by simp[] >>
  drule_all swap_last_step >> strip_tac
  >- (Cases_on `step es` >> gvs[] >> Cases_on `q` >> gvs[]) >>
  gen_tac >> disch_tac >> irule dup_return_suffix >> simp[]
QED

Theorem push0_return_suffix[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [10w] /\
  ctxt.jumpDest = NONE /\ ctxt.pc + 11 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Push 0 []) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 1) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 2) = SOME (Dup 1) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 3) = SOME (Push 2 [0w;19w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 6) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 7) = SOME CodeCopy /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 8) = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 10) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 11) = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule no_call_backward >> simp[] >> reverse conj_tac
  >- (simp[observable_call_def, next_opcode_def] >>
      Cases_on `ctxt.msgParams.code = []` >> simp[]) >>
  strip_tac >> `ctxt.pc < LENGTH ctxt.msgParams.code` by simp[] >>
  drule_all push0_step >> strip_tac
  >- (Cases_on `step es` >> gvs[] >> Cases_on `q` >> gvs[]) >>
  gen_tac >> disch_tac >> irule swap_dup_return_suffix >> simp[]
QED

Theorem push10_return_suffix[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.stack = [] /\
  ctxt.jumpDest = NONE /\ ctxt.pc + 13 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 2) = SOME (Push 0 []) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 3) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 4) = SOME (Dup 1) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 5) = SOME (Push 2 [0w;19w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 8) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 9) = SOME CodeCopy /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 10) = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 12) = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed (ctxt.pc + 13) = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule no_call_backward >> simp[] >> reverse conj_tac
  >- (simp[observable_call_def, next_opcode_def] >>
      Cases_on `ctxt.msgParams.code = []` >> simp[]) >>
  strip_tac >> `ctxt.pc < LENGTH ctxt.msgParams.code` by simp[] >>
  drule_all push10_step >> strip_tac
  >- (Cases_on `step es` >> gvs[] >> Cases_on `q` >> gvs[]) >>
  gen_tac >> disch_tac >> irule push0_return_suffix >> simp[]
QED

Theorem jumpdest_return_suffix[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.pc = 0 /\ ctxt.stack = [] /\
  ctxt.jumpDest = NONE /\ 14 < LENGTH ctxt.msgParams.code /\
  FLOOKUP ctxt.msgParams.parsed 0 = SOME JumpDest /\
  FLOOKUP ctxt.msgParams.parsed 1 = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed 3 = SOME (Push 0 []) /\
  FLOOKUP ctxt.msgParams.parsed 4 = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed 5 = SOME (Dup 1) /\
  FLOOKUP ctxt.msgParams.parsed 6 = SOME (Push 2 [0w;19w]) /\
  FLOOKUP ctxt.msgParams.parsed 9 = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed 10 = SOME CodeCopy /\
  FLOOKUP ctxt.msgParams.parsed 11 = SOME (Push 1 [10w]) /\
  FLOOKUP ctxt.msgParams.parsed 13 = SOME (Swap 0) /\
  FLOOKUP ctxt.msgParams.parsed 14 = SOME Return /\ obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule no_call_backward >> simp[] >> reverse conj_tac
  >- (simp[observable_call_def, next_opcode_def] >>
      Cases_on `ctxt.msgParams.code = []` >> simp[]) >>
  strip_tac >> `0 < LENGTH ctxt.msgParams.code` by simp[] >>
  drule_all jumpdest_first_step_probe >> strip_tac
  >- (Cases_on `step es` >> gvs[] >> Cases_on `q` >> gvs[]) >>
  gen_tac >> disch_tac >> irule push10_return_suffix >> simp[]
QED

Theorem candidate_prefix_no_observation[local]:
  es.contexts = [(ctxt,rb)] /\ ctxt.pc = 0 /\ ctxt.stack = [] /\
  ctxt.jumpDest = NONE /\
  ctxt.msgParams.code =
    [91w;96w;10w;95w;144w;129w;97w;0w;19w;144w;57w;
     96w;10w;144w;243w] ++ rest /\
  ctxt.msgParams.parsed = parse_code 0 FEMPTY ctxt.msgParams.code /\
  obs.pending = NONE ==>
  (frame_obs_tr 1 obs es (step es)).entries = obs.entries /\
  (frame_obs_tr 1 obs es (step es)).pending = NONE
Proof
  strip_tac >> irule jumpdest_return_suffix >> simp[] >>
  rpt conj_tac >>
  irule (SRULE [listTheory.APPEND] candidate_prefix_lookups) >> simp[]
QED

Theorem pass_candidate_trace_empty:
  deploy_state_rel tops
    [91w;96w;10w;95w;144w;129w;97w;0w;19w;144w;57w;
     96w;10w;144w;243w;91w;95w;128w;253w;
     0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w]
    am tx es /\ constructor_args_encode tops tx [] ==>
  call_trace es = []
Proof
  strip_tac >> drule_all pass_candidate_entry >> strip_tac >>
  simp[call_trace_def, frame_obs_def] >>
  irule (SRULE [] (Q.INST
    [`obs` |-> `<|entries := []; readings := []; pending := NONE|>`]
    (cj 1 candidate_prefix_no_observation))) >>
  qexistsl [`ctxt`, `rb`,
    `[91w;95w;128w;253w;
      0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w]`] >>
  simp[]
QED
