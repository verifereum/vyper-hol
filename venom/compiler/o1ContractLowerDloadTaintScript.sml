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
  lowerDloadDefs venomPassSchedule list calleeTransport lowerDloadRequestObservation
  lowerDloadTerminalObservation lowerDloadRecursiveInterface lowerDloadReachableFloor
  lowerDloadNormalData lowerDloadReachableDiscipline unitShapeDefs pred_set
  contextCodegenRel venomInst lowerDloadSourceInterface

(* Agreement of the complete step_taint adoption guard; request streams
   themselves may differ, only their change indicators must agree. *)
Theorem ld_adoption_guard_agreement:
  !s s' t t'.
    s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
    s.vs_outcomes = t.vs_outcomes /\
    s'.vs_outcomes = t'.vs_outcomes /\
    ((s'.vs_requests <> s.vs_requests) <=>
     (t'.vs_requests <> t.vs_requests)) ==>
    ((~s.vs_call_ctx.cc_static /\
      s'.vs_requests <> s.vs_requests /\
      s'.vs_outcomes <> s.vs_outcomes /\
      (HD s.vs_outcomes).co_success) <=>
     (~t.vs_call_ctx.cc_static /\
      t'.vs_requests <> t.vs_requests /\
      t'.vs_outcomes <> t.vs_outcomes /\
      (HD t.vs_outcomes).co_success))
Proof
  rpt strip_tac >> simp[]
QED

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

Theorem related_taint_overwrite:
  (!x y. R x y /\ y IN Mt ==> x IN Ms) /\
  (!x y. R x y /\ y IN Nt ==> x IN Ns) /\
  (!x y. R x y /\ x IN Ws ==> y IN Wt) ==>
  !x y. R x y /\ y IN ((Mt UNION Nt) DIFF Wt) ==>
        x IN ((Ms UNION Ns) DIFF Ws)
Proof
  simp[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF] >> metis_tac[]
QED

Theorem translated_range_member:
  (b + k IN {i:num | b + off <= i /\ i < b + off + len}) <=>
  (b' + k IN {i:num | b' + off <= i /\ i < b' + off + len})
Proof
  simp_tac std_ss [pred_setTheory.GSPECIFICATION] >> decide_tac
QED

(* Word operands denote natural site-relative ranges when they do not wrap. *)
Theorem translated_word_range_member:
  b + off < dimword (:256) /\ b' + off < dimword (:256) /\
  len < dimword (:256) ==>
  ((b + k IN {i:num | w2n (n2w (b + off):bytes32) <= i /\
                     i < w2n (n2w (b + off):bytes32) +
                         w2n (n2w len:bytes32)}) <=>
   (b' + k IN {i:num | w2n (n2w (b' + off):bytes32) <= i /\
                      i < w2n (n2w (b' + off):bytes32) +
                          w2n (n2w len:bytes32)}))
Proof
  strip_tac >> simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
                    translated_range_member]
QED

Theorem data_copy_taint_related:
  si.inst_opcode = DLOADBYTES /\ ti.inst_opcode = CODECOPY /\
  si.inst_operands = [sd; ss; sn] /\ ti.inst_operands = [td; ts; tnop] /\
  eval_operand sd s = SOME sw /\ eval_operand ss s = SOME sr /\
  eval_operand sn s = SOME nw /\
  eval_operand td t = SOME tw /\ eval_operand ts t = SOME tr /\
  eval_operand tnop t = SOME nw /\
  (!x y. Rel x y /\ y IN tt.t_mem ==> x IN st.t_mem) /\
  (!x y. Rel x y /\ y IN new_site_bytes t t' ==> x IN new_site_bytes s s') /\
  (!x y. Rel x y /\ w2n sw <= x /\ x < w2n sw + w2n nw ==>
         w2n tw <= y /\ y < w2n tw + w2n nw) ==>
  !x y. Rel x y /\ y IN mem_taint tt ti t t' ==> x IN mem_taint st si s s'
Proof
  strip_tac >>
  `mem_taint st si s s' =
     (st.t_mem UNION new_site_bytes s s') DIFF
       {i | w2n sw <= i /\ i < w2n sw + w2n nw}` by
    (irule data_copy_taint >> metis_tac[]) >>
  `mem_taint tt ti t t' =
     (tt.t_mem UNION new_site_bytes t t') DIFF
       {i | w2n tw <= i /\ i < w2n tw + w2n nw}` by
    (irule data_copy_taint >> metis_tac[]) >>
  asm_rewrite_tac[] >> ho_match_mp_tac related_taint_overwrite >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

(* A successful scratch copy clears the following load independently of
   earlier allocation visits and the incoming taint. *)
Theorem codecopy_mload_cleared:
  ci.inst_opcode = CODECOPY /\ ci.inst_operands = [Var a; src; Lit 32w] /\
  li.inst_opcode = MLOAD /\ li.inst_operands = [Var a] /\
  step_inst k C ci s = OK s' ==>
  out_taint (step_taint ci s s' tn) li s' = {}
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once venomExecSemanticsTheory.step_inst_def] >>
  simp[venomExecSemanticsTheory.step_inst_base_def] >>
  simp[venomStateTheory.eval_operand_def, AllCaseEqs()] >> strip_tac >>
  simp[out_taint_def, step_taint_def,
       venomStateTheory.eval_operand_def,
       venomStateTheory.write_memory_with_expansion_def] >>
  `lookup_var a s' = SOME dst` by
    (fs[venomStateTheory.lookup_var_def] >>
     qpat_x_assum `write_memory_with_expansion _ _ _ = _` (mp_tac o SYM) >>
     simp[venomStateTheory.write_memory_with_expansion_def,
          venomStateTheory.lookup_var_def]) >>
  simp[] >> irule codecopy_word_taint >>
  simp[venomStateTheory.eval_operand_def] >> metis_tac[]
QED

Theorem lower_dload_supply_scratch_cleared:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  lower_dload_inst_supply supply inst = ([ai;bi;ci;li],supply') /\
  step_inst k C ci t2 = OK t3 ==>
  out_taint (step_taint ci t2 t3 tn) li t3 = {}
Proof
  strip_tac >>
  gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
  irule codecopy_mload_cleared >> simp[] >> metis_tac[]
QED

Theorem lower_dload_supply_external_taint:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  lower_dload_inst_supply supply inst = ([ai;bi;ci;li],supply') ==>
  let tn1 = step_taint ai t0 t1 tn0;
      tn2 = step_taint bi t1 t2 tn1;
      tn3 = step_taint ci t2 t3 tn2;
      tn4 = step_taint li t3 t4 tn3
  in tn4.t_stor = tn0.t_stor /\ tn4.t_trans = tn0.t_trans /\
     tn4.t_imm = tn0.t_imm
Proof
  strip_tac >>
  gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
  simp[step_taint_nonmemory]
QED

Theorem lower_dload_inst_supply_interval:
  lower_dload_inst_supply s i = (outs,s') ==>
  s.irs_next_inst <= s'.irs_next_inst /\
  EVERY (\j. j = i \/
    (s.irs_next_inst <= j.inst_id /\ j.inst_id < s'.irs_next_inst)) outs
Proof
  gvs[lower_dload_inst_supply_def, AllCaseEqs(),
      irSupplyTheory.fresh_inst_id_def] >>
  rpt strip_tac >>
  imp_res_tac irSupplyTheory.fresh_ir_var_contract >> gvs[]
QED

Theorem lower_dload_insts_supply_interval:
  !s outs s'. lower_dload_insts_supply s insts = (outs,s') ==>
  s.irs_next_inst <= s'.irs_next_inst /\
  EVERY (\j. MEM j insts \/
    (s.irs_next_inst <= j.inst_id /\ j.inst_id < s'.irs_next_inst)) outs
Proof
  Induct_on `insts`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >>
  drule lower_dload_inst_supply_interval >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[] >> decide_tac
QED

Theorem lower_dload_blocks_supply_interval:
  !s bs s'. lower_dload_blocks_supply s bbs = (bs,s') ==>
  s.irs_next_inst <= s'.irs_next_inst /\
  EVERY (\j. MEM j (fn_insts_blocks bbs) \/
    (s.irs_next_inst <= j.inst_id /\ j.inst_id < s'.irs_next_inst))
    (fn_insts_blocks bs)
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def, venomInstTheory.fn_insts_blocks_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt strip_tac >>
  drule lower_dload_insts_supply_interval >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[venomInstTheory.fn_insts_blocks_def, EVERY_MEM] >>
  rpt strip_tac >> res_tac >> gvs[] >> decide_tac
QED

Theorem lower_dload_function_supply_interval:
  lower_dload_function_supply s f = (g,s') ==>
  s.irs_next_inst <= s'.irs_next_inst /\
  EVERY (\j. MEM j (fn_insts f) \/
    (s.irs_next_inst <= j.inst_id /\ j.inst_id < s'.irs_next_inst))
    (fn_insts g)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >>
  drule lower_dload_blocks_supply_interval >>
  gvs[venomInstTheory.fn_insts_def]
QED

Theorem lower_dload_function_supply_old_id:
  lower_dload_function_supply s f = (g,s') /\
  MEM j (fn_insts g) /\ j.inst_id < s.irs_next_inst ==>
  MEM j (fn_insts f)
Proof
  strip_tac >> drule lower_dload_function_supply_interval >>
  simp[EVERY_MEM] >> strip_tac >> first_x_assum drule >> simp[]
QED

(* Scratch IDs are counted as sites, not dynamic executions. *)
Theorem lower_dload_inst_supply_scratch:
  lower_dload_inst_supply s i = (outs,s') /\
  i.inst_id < lo /\ lo <= s.irs_next_inst ==>
  ALL_DISTINCT (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA /\ lo <= j.inst_id) outs)) /\
  LENGTH (FILTER (\j. j.inst_opcode = ALLOCA /\ lo <= j.inst_id) outs) <=
    (if i.inst_opcode = DLOAD then 1 else 0) /\
  EVERY (\j. j.inst_opcode = ALLOCA /\ lo <= j.inst_id ==>
    s.irs_next_inst <= j.inst_id /\ j.inst_id < s'.irs_next_inst /\
    j.inst_operands = [Lit 32w] /\ LENGTH j.inst_outputs = 1) outs
Proof
  gvs[lower_dload_inst_supply_def, AllCaseEqs(),
      irSupplyTheory.fresh_inst_id_def] >>
  rpt strip_tac >>
  imp_res_tac irSupplyTheory.fresh_ir_var_contract >> gvs[]
QED

Theorem lower_dload_insts_supply_scratch:
  !s outs s' lo. lower_dload_insts_supply s insts = (outs,s') /\
  EVERY (\i. i.inst_id < lo) insts /\ lo <= s.irs_next_inst ==>
  ALL_DISTINCT (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA /\ lo <= j.inst_id) outs)) /\
  LENGTH (FILTER (\j. j.inst_opcode = ALLOCA /\ lo <= j.inst_id) outs) <=
    LENGTH (FILTER (\i. i.inst_opcode = DLOAD) insts) /\
  EVERY (\j. j.inst_opcode = ALLOCA /\ lo <= j.inst_id ==>
    s.irs_next_inst <= j.inst_id /\ j.inst_id < s'.irs_next_inst /\
    j.inst_operands = [Lit 32w] /\ LENGTH j.inst_outputs = 1) outs
Proof
  Induct_on `insts`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >>
  drule_all lower_dload_inst_supply_scratch >> strip_tac >>
  drule lower_dload_inst_supply_interval >> strip_tac >>
  first_x_assum drule >> disch_then (qspec_then `lo` mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> strip_tac >>
  drule lower_dload_insts_supply_interval >> strip_tac >>
  gvs[FILTER_APPEND_DISTRIB, MAP_APPEND, ALL_DISTINCT_APPEND] >>
  conj_tac
  >- (gvs[EVERY_MEM, MEM_MAP, MEM_FILTER] >> rpt strip_tac >>
      res_tac >> gvs[] >> strip_tac >>
      `lo <= j'.inst_id` by decide_tac >>
      res_tac >> gvs[] >> decide_tac) >>
  conj_tac
  >- (Cases_on `h.inst_opcode = DLOAD` >> gvs[] >> decide_tac) >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
            arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem lower_dload_blocks_supply_scratch:
  !s bs s' lo. lower_dload_blocks_supply s bbs = (bs,s') /\
  EVERY (\i. i.inst_id < lo) (fn_insts_blocks bbs) /\
  lo <= s.irs_next_inst ==>
  ALL_DISTINCT (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA /\ lo <= j.inst_id)
      (fn_insts_blocks bs))) /\
  LENGTH (FILTER (\j. j.inst_opcode = ALLOCA /\ lo <= j.inst_id)
      (fn_insts_blocks bs)) <=
    LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts_blocks bbs)) /\
  EVERY (\j. j.inst_opcode = ALLOCA /\ lo <= j.inst_id ==>
    s.irs_next_inst <= j.inst_id /\ j.inst_id < s'.irs_next_inst /\
    j.inst_operands = [Lit 32w] /\ LENGTH j.inst_outputs = 1)
    (fn_insts_blocks bs)
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def, venomInstTheory.fn_insts_blocks_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs(), venomInstTheory.fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all lower_dload_insts_supply_scratch >> strip_tac >>
  drule lower_dload_insts_supply_interval >> strip_tac >>
  first_x_assum drule >> disch_then (qspec_then `lo` mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> strip_tac >>
  drule lower_dload_blocks_supply_interval >> strip_tac >>
  gvs[venomInstTheory.fn_insts_blocks_def, FILTER_APPEND_DISTRIB,
      MAP_APPEND, ALL_DISTINCT_APPEND] >>
  conj_tac
  >- (gvs[EVERY_MEM, MEM_MAP, MEM_FILTER] >> rpt strip_tac >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS,
                arithmeticTheory.LESS_LESS_EQ_TRANS,
                prim_recTheory.LESS_REFL]) >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
            arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem lower_dload_function_supply_scratch:
  lower_dload_function_supply s f = (g,s') /\
  EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts f) ==>
  ALL_DISTINCT (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA /\ s.irs_next_inst <= j.inst_id)
      (fn_insts g))) /\
  LENGTH (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA /\ s.irs_next_inst <= j.inst_id)
      (fn_insts g))) <=
    LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts f)) /\
  EVERY (\j. j.inst_opcode = ALLOCA /\ s.irs_next_inst <= j.inst_id ==>
    j.inst_operands = [Lit 32w] /\ LENGTH j.inst_outputs = 1) (fn_insts g)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >>
  drule lower_dload_blocks_supply_scratch >>
  disch_then (qspec_then `s.irs_next_inst` mp_tac) >>
  gvs[venomInstTheory.fn_insts_def, EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_function_supply_scratch_separation:
  lower_dload_function_supply s f = (g,s') /\
  EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts f) /\
  MEM i (fn_insts f) ==>
  ~MEM i.inst_id (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA /\ s.irs_next_inst <= j.inst_id)
      (fn_insts g)))
Proof
  simp[EVERY_MEM, MEM_MAP, MEM_FILTER] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> decide_tac
QED

Theorem lower_dload_function_supply_alloca_origin:
  lower_dload_function_supply s f = (g,s') /\
  MEM j (fn_insts g) /\ j.inst_opcode = ALLOCA ==>
  MEM j (fn_insts f) \/
  MEM j.inst_id (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = ALLOCA /\ s.irs_next_inst <= i.inst_id)
      (fn_insts g)))
Proof
  strip_tac >> drule lower_dload_function_supply_interval >>
  simp[EVERY_MEM] >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

Theorem exec_alloca_fresh_projections:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s n = OK s' ==>
  s'.vs_alloca_next = s.vs_alloca_next + w2n n /\
  FLOOKUP s'.vs_allocas inst.inst_id =
    SOME (s.vs_alloca_next,w2n n) /\
  (!id. id <> inst.inst_id ==>
    FLOOKUP s'.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  lookup_var out s' = SOME (n2w s.vs_alloca_next)
Proof
  strip_tac >> drule_all exec_alloca_fresh >>
  disch_then (qspec_then `n` assume_tac) >>
  gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem exec_alloca_fresh_displacement:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s n = OK s' /\ exec_alloca inst t n = OK t' /\
  t.vs_alloca_next = s.vs_alloca_next + d ==>
  t'.vs_alloca_next = s'.vs_alloca_next + d
Proof
  strip_tac >>
  drule_all exec_alloca_fresh_projections >> strip_tac >>
  qpat_x_assum `exec_alloca inst t n = _` kall_tac >>
  drule_all exec_alloca_fresh_projections >> strip_tac >>
  gvs[]
QED

Theorem exec_alloca_repeated_projections:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  exec_alloca inst s n = OK s' ==>
  s'.vs_allocas = s.vs_allocas /\
  s'.vs_alloca_next = s.vs_alloca_next /\
  lookup_var out s' = SOME (n2w b)
Proof
  strip_tac >> drule_all exec_alloca_repeated >>
  disch_then (qspec_then `n` assume_tac) >>
  gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Inherited memory/frontier and return memory projections are already
   supplied by calleeTransport's setup_callee_shared_fields and
   merge_callee_shared_fields. Only the empty callee site map is missing. *)
Theorem setup_callee_allocas:
  setup_callee fn args s = SOME u ==> u.vs_allocas = FEMPTY
Proof
  simp[venomExecSemanticsTheory.setup_callee_def] >>
  strip_tac >> gvs[]
QED

(* Coverage is deliberately explicit: this consumer does not produce source
   witnesses for target observations. *)
Theorem taint_within_observation_transport:
  dead_wf D /\ taint_within D C vs /\
  (!stk PG G tt fn j t fuel t'.
    frame_reachable vs C' stk PG G tt fn j t /\ active_inst fn j t /\
    j.inst_opcode <> INVOKE /\ step_inst fuel C' j t = OK t' /\
    LENGTH t.vs_requests < LENGTH t'.vs_requests ==>
    ?stk0 PG0 G0 tn fn0 inst s s' fuel0.
      frame_reachable vs C stk0 PG0 G0 tn fn0 inst s /\
      active_inst fn0 inst s /\ inst.inst_opcode <> INVOKE /\
      step_inst fuel0 C inst s = OK s' /\
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
      tt.t_stor SUBSET tn.t_stor /\ tt.t_trans SUBSET tn.t_trans) /\
  (!t tt Rt. final_taint vs C' t tt Rt ==>
    ?s tn R. final_taint vs C s tn R /\
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
      tt.t_imm SUBSET tn.t_imm /\ Rt SUBSET R) ==>
  taint_within D C' vs
Proof
  strip_tac >> rewrite_tac[taint_within_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!stk PG G tt fn j t fuel t'. _` drule_all >>
      strip_tac >> drule_all request_taint_transport >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!t tt Rt. _` drule >> strip_tac >>
  drule_all final_taint_transport >> simp[]
QED

(* Reuse the authoritative candidate quotation from the selector's premise. *)
val ld_final_candidate = fst (dest_conj (fst (dest_imp
  (concl lowerDloadRecursiveInterfaceTheory.ld_recursive_combined_halt_anchor))));

Theorem ld_candidate_final_observation:
  dead_wf D /\ taint_within D CS vs0 /\ ptr_discipline lo CS vs0 /\
  o1_ctx_shape CS /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\
  (^ld_final_candidate) /\
  j.inst_opcode <> INVOKE /\ step_inst fuel CT j t = Halt th ==>
  (step_taint j t th un).t_stor SUBSET D.d_stor th.vs_call_ctx.cc_address
    (th.vs_accounts th.vs_call_ctx.cc_address).storage /\
  (step_taint j t th un).t_trans SUBSET D.d_trans th.vs_call_ctx.cc_address
    (th.vs_transient th.vs_call_ctx.cc_address) /\
  (step_taint j t th un).t_imm SUBSET D.d_imm th.vs_immutables /\
  ret_taint un j t SUBSET D.d_ret th.vs_returndata
Proof
  strip_tac >> drule_all ld_recursive_combined_halt_anchor >>
  qpat_x_assum `(^ld_final_candidate)` kall_tac >>
  BETA_TAC >> strip_tac >>
  qpat_x_assum `!q. q < LENGTH astk ==> _` kall_tac >>
  qpat_x_assum `code = [i]` SUBST_ALL_TAC >>
  fs[] >>
  `opaque_use_ok fn` by
    (qpat_assum `o1_ctx_shape CS` mp_tac >>
     qpat_assum `CS.ctx_functions = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, fn_shape_ok_def]) >>
  `MEM i (fn_insts fn)` by
    (qpat_assum `active_inst fn i s` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==> MEM v (fn_ir_vars fn)` by
    metis_tac[ld_original_operand_support] >>
  gvs[] >>
  drule ld_normal_halt_observation >>
  disch_then drule >>
  disch_then drule >>
  disch_then (qspecl_then [`th`, `fuel`, `P`, `CT`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> simp[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> suspend "dead_masks"
QED

Resume ld_candidate_final_observation[dead_masks]:
  `sn.t_stor SUBSET D.d_stor sh.vs_call_ctx.cc_address
     (sh.vs_accounts sh.vs_call_ctx.cc_address).storage /\
   sn.t_trans SUBSET D.d_trans sh.vs_call_ctx.cc_address
     (sh.vs_transient sh.vs_call_ctx.cc_address) /\
   sn.t_imm SUBSET D.d_imm sh.vs_immutables /\
   Rs SUBSET D.d_ret sh.vs_returndata` by
    (qpat_assum `taint_within D CS vs0` mp_tac >>
     qpat_assum `final_taint vs0 CS sh sn Rs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[taint_within_def] >> metis_tac[]) >>
  irule final_taint_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`CS`, `Rs`, `sh`, `sn`, `vs0`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `!q. q < LENGTH sh.vs_returndata /\ _ ==> _` mp_tac >>
      qpat_assum `Rs SUBSET _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rw[SUBSET_DEF] >> metis_tac[])
  >- (qpat_assum `!q. q IN FDOM sh.vs_immutables ==> _` mp_tac >>
      qpat_assum `FDOM sh.vs_immutables = _` mp_tac >>
      qpat_assum `sn.t_imm SUBSET _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      rw[imms_agree_except_def, word_agree_except_def, SUBSET_DEF] >> metis_tac[])
  >- (qpat_assum `storage_agree_except sn.t_stor _ _` mp_tac >>
      qpat_assum `sn.t_stor SUBSET _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      rw[storage_agree_except_def, word_agree_except_def, key_taint_def, SUBSET_DEF] >> metis_tac[]) >>
  qpat_assum `storage_agree_except sn.t_trans _ _` mp_tac >>
  qpat_assum `sn.t_trans SUBSET _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  rw[storage_agree_except_def, word_agree_except_def, key_taint_def, SUBSET_DEF] >> metis_tac[]
QED

Finalise ld_candidate_final_observation

Theorem ld_reachable_final_observation:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view CS CT /\
  dead_wf D /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  o1_src_inv D CS vs0 /\ callee_first names CS.ctx_functions ==>
  !t_h un R.
    final_taint vs0 CT t_h un R ==>
    un.t_stor SUBSET D.d_stor t_h.vs_call_ctx.cc_address
      (t_h.vs_accounts t_h.vs_call_ctx.cc_address).storage /\
    un.t_trans SUBSET D.d_trans t_h.vs_call_ctx.cc_address
      (t_h.vs_transient t_h.vs_call_ctx.cc_address) /\
    un.t_imm SUBSET D.d_imm t_h.vs_immutables /\
    R SUBSET D.d_ret t_h.vs_returndata
Proof
  strip_tac >>
  `ptr_discipline vs0.vs_alloca_next CS vs0` by
    metis_tac[ld_o1_src_inv_frontier_discipline] >>
  `?P. !g. MEM g CS.ctx_functions ==> fn_ptr_ok P g` by
    (qpat_assum `ptr_discipline _ CS vs0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ptr_discipline_def, EVERY_MEM] >>
     metis_tac[]) >>
  `taint_within D CS vs0` by
    (qpat_assum `o1_src_inv D CS vs0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[o1_src_inv_def]) >>
  rpt gen_tac >> simp[final_taint_def] >> strip_tac >>
  mp_tac (Q.INST [`lo` |-> `vs0.vs_alloca_next`] ld_recursive_combined_coverage) >>
  (impl_tac >- (rpt conj_tac >> simp[])) >>
  disch_then (qspecl_then [`stk`, `PG`, `G`, `T0`, `fn`, `inst`, `s`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
  qpat_x_assum `un = _` SUBST_ALL_TAC >>
  qpat_x_assum `R = _` SUBST_ALL_TAC >>
  irule ld_candidate_final_observation >>
  rpt conj_tac >> goal_assum (drule_at Any) >>
  qexistsl [`P`, `fuel`] >> rpt conj_tac >> first_assum ACCEPT_TAC
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
