(*
 * LowerDload against the O1 pass contract: the output's taint reaches only
 * the dead bytes D.
 * Kept in its own theory so its proof can be worked on apart from the
 * other rows; o1ContractLowerDloadStage assembles them.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_taint
 *)
Theory o1ContractLowerDloadTaint
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list

(* A complete untainted overwrite clears a word, even if the step also
   introduces fresh-site taint. *)
Theorem mem_word_taint_overwrite:
  written_taint tn inst s = {} /\
  (!k. k < 32 ==> off + k IN range_bytes (step_writes inst s s')) ==>
  mem_word_taint (mem_taint tn inst s s') off = {}
Proof
  rw[mem_word_taint_def, mem_taint_def, pred_setTheory.EXTENSION] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem codecopy_word_taint:
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; len] /\
  eval_operand dst s = SOME dstw /\ eval_operand src s = SOME source /\
  eval_operand len s = SOME 32w ==>
  mem_word_taint (mem_taint tn inst s s') (w2n dstw) = {}
Proof
  strip_tac >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  irule mem_word_taint_overwrite >>
  simp[written_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.sized_source_write_range_def,
       range_bytes_def, wordsTheory.dimword_def] >> rpt strip_tac >> simp[]
QED

Theorem mload_out_taint:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [addr] /\
  eval_operand addr s = SOME w ==>
  out_taint tn inst s = mem_word_taint tn.t_mem (w2n w)
Proof
  simp[out_taint_def]
QED

Theorem step_taint_nonmemory:
  inst.inst_opcode <> SSTORE /\ inst.inst_opcode <> TSTORE /\
  inst.inst_opcode <> ISTORE /\ inst.inst_opcode <> CALL /\
  inst.inst_opcode <> STATICCALL ==>
  (step_taint inst s s' tn).t_stor = tn.t_stor /\
  (step_taint inst s s' tn).t_trans = tn.t_trans /\
  (step_taint inst s s' tn).t_imm = tn.t_imm
Proof
  simp[step_taint_def, adopt_reset_def, store_taint_def, imm_taint_def]
QED

Theorem exec_alloca_repeated:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (off,sz) ==>
  exec_alloca inst s n = OK (update_var out (n2w off) s)
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem exec_alloca_fresh:
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  exec_alloca inst s n =
    OK (update_var out (n2w s.vs_alloca_next)
      (s with <| vs_allocas := s.vs_allocas |+
                   (inst.inst_id,(s.vs_alloca_next,w2n n));
                 vs_alloca_next := s.vs_alloca_next + w2n n |>))
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem data_copy_taint:
  (inst.inst_opcode = DLOADBYTES \/ inst.inst_opcode = CODECOPY) /\
  inst.inst_operands = [dst; src; len] /\
  eval_operand dst s = SOME dstw /\ eval_operand src s = SOME srcw /\
  eval_operand len s = SOME lenw ==>
  mem_taint tn inst s s' =
    (tn.t_mem UNION new_site_bytes s s') DIFF
      {i | w2n dstw <= i /\ i < w2n dstw + w2n lenw}
Proof
  strip_tac >>
  simp[mem_taint_def, written_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.sized_source_write_range_def, range_bytes_def] >>
  fs[]
QED

Theorem codecopy_success_operands:
  inst.inst_opcode = CODECOPY /\ step_inst fuel ctx inst s = OK s' ==>
  ?dst src len dstw srcw lenw.
    inst.inst_operands = [dst; src; len] /\
    eval_operand dst s = SOME dstw /\ eval_operand src s = SOME srcw /\
    eval_operand len s = SOME lenw
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by fs[] >>
  drule venomExecSemanticsTheory.step_inst_non_invoke >>
  disch_then (qspecl_then [`fuel`,`ctx`,`s`] assume_tac) >>
  gvs[venomExecSemanticsTheory.step_inst_base_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem merge_callee_alloca_frontier:
  (merge_callee_state caller callee).vs_allocas = caller.vs_allocas /\
  (merge_callee_state caller callee).vs_alloca_next = caller.vs_alloca_next
Proof
  simp[venomExecSemanticsTheory.merge_callee_state_def]
QED

Theorem dead_stor_taint_transport:
  dead_wf D /\ storage_agree_except (D.d_stor a st) st st' /\
  X SUBSET D.d_stor a st /\ Y SUBSET X ==>
  Y SUBSET D.d_stor a st'
Proof
  rw[dead_wf_def] >> metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem dead_trans_taint_transport:
  dead_wf D /\ storage_agree_except (D.d_trans a st) st st' /\
  X SUBSET D.d_trans a st /\ Y SUBSET X ==>
  Y SUBSET D.d_trans a st'
Proof
  rw[dead_wf_def] >> metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem dead_imm_taint_transport:
  dead_wf D /\ imms_agree_except D im im' /\
  X SUBSET D.d_imm im /\ Y SUBSET X ==>
  Y SUBSET D.d_imm im'
Proof
  rw[dead_wf_def] >> metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem dead_ret_taint_transport:
  dead_wf D /\ LENGTH r = LENGTH r' /\
  (!i. i < LENGTH r /\ i NOTIN D.d_ret r ==> EL i r = EL i r') /\
  X SUBSET D.d_ret r /\ Y SUBSET X ==>
  Y SUBSET D.d_ret r'
Proof
  rw[dead_wf_def] >> metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem request_taint_transport:
  dead_wf D /\ taint_within D C vs /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' /\
  LENGTH s.vs_requests < LENGTH s'.vs_requests /\
  t.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  storage_agree_except
    (D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage)
    (s.vs_accounts s.vs_call_ctx.cc_address).storage
    (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
  storage_agree_except
    (D.d_trans s.vs_call_ctx.cc_address (s.vs_transient s.vs_call_ctx.cc_address))
    (s.vs_transient s.vs_call_ctx.cc_address)
    (t.vs_transient t.vs_call_ctx.cc_address) /\
  tt.t_stor SUBSET tn.t_stor /\ tt.t_trans SUBSET tn.t_trans ==>
  tt.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
    (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
  tt.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
    (t.vs_transient t.vs_call_ctx.cc_address)
Proof
  strip_tac >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
     (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
     (s.vs_transient s.vs_call_ctx.cc_address)` by
    (fs[taint_within_def] >> first_x_assum drule_all >> simp[]) >>
  conj_tac
  >- (irule dead_stor_taint_transport >> goal_assum drule >> simp[] >>
      metis_tac[]) >>
  irule dead_trans_taint_transport >> goal_assum drule >> simp[] >>
  metis_tac[]
QED

Theorem final_taint_transport:
  dead_wf D /\ taint_within D C vs /\ final_taint vs C s tn R /\
  t.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  storage_agree_except
    (D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage)
    (s.vs_accounts s.vs_call_ctx.cc_address).storage
    (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
  storage_agree_except
    (D.d_trans s.vs_call_ctx.cc_address (s.vs_transient s.vs_call_ctx.cc_address))
    (s.vs_transient s.vs_call_ctx.cc_address)
    (t.vs_transient t.vs_call_ctx.cc_address) /\
  imms_agree_except D s.vs_immutables t.vs_immutables /\
  LENGTH s.vs_returndata = LENGTH t.vs_returndata /\
  (!i. i < LENGTH s.vs_returndata /\ i NOTIN D.d_ret s.vs_returndata ==>
       EL i s.vs_returndata = EL i t.vs_returndata) /\
  tt.t_stor SUBSET tn.t_stor /\ tt.t_trans SUBSET tn.t_trans /\
  tt.t_imm SUBSET tn.t_imm /\ Rt SUBSET R ==>
  tt.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
    (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
  tt.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
    (t.vs_transient t.vs_call_ctx.cc_address) /\
  tt.t_imm SUBSET D.d_imm t.vs_immutables /\ Rt SUBSET D.d_ret t.vs_returndata
Proof
  strip_tac >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
     (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
     (s.vs_transient s.vs_call_ctx.cc_address) /\
   tn.t_imm SUBSET D.d_imm s.vs_immutables /\ R SUBSET D.d_ret s.vs_returndata` by
    (fs[taint_within_def] >> first_x_assum drule >> simp[]) >>
  conj_tac
  >- (irule dead_stor_taint_transport >> goal_assum drule >> simp[] >>
      metis_tac[]) >>
  conj_tac
  >- (irule dead_trans_taint_transport >> goal_assum drule >> simp[] >>
      metis_tac[]) >>
  conj_tac
  >- (irule dead_imm_taint_transport >> goal_assum drule >> metis_tac[]) >>
  irule dead_ret_taint_transport >> goal_assum drule >> metis_tac[]
QED

(* The output's taint reaches only the dead bytes D. *)
Theorem lower_dload_stage_taint:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    taint_within D C' vs
Proof
  cheat
QED
