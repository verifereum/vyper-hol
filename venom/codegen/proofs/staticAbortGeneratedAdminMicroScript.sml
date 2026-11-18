(* Shared, value-independent heights at every administrative microinstruction. *)
Theory staticAbortGeneratedAdminMicro
Ancestors
  staticAbortStack staticAbortTrace prefixExec planWf planExec stackOpSim
  asmSem asmIR stackOpAsmSim list rich_list arithmetic

Theorem generated_admin_op_heights[local]:
  !op fmp lo o2pc h.
    FST (stack_op_wf lo op h) ==>
    ?H. H 0 = h /\
      H (LENGTH (exec_stack_op fmp op)) = SND (stack_op_wf lo op h) /\
      !k extra t.
        k < LENGTH (exec_stack_op fmp op) /\
        LENGTH t.as_stack = H k + extra ==>
        ?u. asm_step lo o2pc (EL k (exec_stack_op fmp op)) t = AsmOK u /\
          LENGTH u.as_stack = H (SUC k) + extra
Proof
  Cases_on `op` >> simp[stack_op_wf_def, exec_stack_op_def] >>
  rpt strip_tac
  >- (Cases_on `o'` >> gvs[stack_op_wf_def, exec_stack_op_def]
      >- (qexists `\k. if k = 0 then h else h+1` >>
          simp[asm_step_push_ok, asm_next_def])
      >- (qexists `\k. h` >> simp[]) >>
      Cases_on `FLOOKUP lo s` >> gvs[] >>
      qexists `\k. if k = 0 then h else h+1` >>
      simp[asm_step_def, asm_next_def])
  >- (qexists `\k. h-k` >> simp[] >> rpt strip_tac >>
      `t.as_stack <> []` by (Cases_on `t.as_stack` >> gvs[]) >>
      drule asm_step_pop_ok >>
      disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
      simp[EL_REPLICATE] >>
      simp[asm_next_def] >> decide_tac)
  >- (qexists `\k. h` >> simp[] >> rpt strip_tac >>
      simp[asm_step_swap_ok, asm_next_def, LENGTH_LUPDATE])
  >- (qexists `\k. if k = 0 then h else h+1` >> simp[] >>
      rpt strip_tac >>
      `n-1 < 16 /\ n-1 < LENGTH t.as_stack /\ n-1+1 = n` by decide_tac >>
      drule_all asm_step_dup_ok >>
      disch_then (qspecl_then [`lo`, `o2pc`] mp_tac) >>
      simp[asm_next_def])
  >- (qexists `\k. h` >> simp[])
  >- (qexists `\k. if k = 0 then h else if k = 1 then h+1 else h-1` >>
      simp[] >> rpt strip_tac >>
      `k = 0 \/ k = 1` by decide_tac >> gvs[]
      >- simp[asm_step_push_ok, asm_next_def] >>
      `LENGTH t.as_stack >= 2` by decide_tac >>
      drule asm_step_mstore_ok >>
      disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
      goal_assum (drule_at Any) >> decide_tac)
  >- (qexists `\k. if k = 0 then h else h+1` >>
      simp[] >> rpt strip_tac >>
      `k = 0 \/ k = 1` by decide_tac >> gvs[]
      >- simp[asm_step_push_ok, asm_next_def] >>
      `t.as_stack <> []` by (Cases_on `t.as_stack` >> gvs[]) >>
      drule asm_step_mload_ok >>
      disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
      goal_assum (drule_at Any) >> simp[])
  >- (qexists `\k. if k = 0 then h else h+1` >>
      simp[asm_step_push_ok, asm_next_def])
  >- (qexists `\k. h` >> simp[asm_step_label_ok, asm_next_def])
  >- (Cases_on `FLOOKUP lo s` >> gvs[] >>
      qexists `\k. if k = 0 then h else h+1` >>
      simp[asm_step_def, asm_next_def]) >>
  Cases_on `FLOOKUP lo s` >> gvs[] >>
  qexists `\k. if k = 0 then h else h+1` >>
  simp[asm_step_def, asm_next_def]
QED

Theorem generated_admin_prefix_heights[local]:
  !ops fmp lo o2pc h.
    prefix_wf lo h ops ==>
    ?H. H 0 = h /\
      H (LENGTH (execute_plan fmp ops)) = prefix_end_len lo h ops /\
      !k extra t.
        k < LENGTH (execute_plan fmp ops) /\
        LENGTH t.as_stack = H k + extra ==>
        ?u. asm_step lo o2pc (EL k (execute_plan fmp ops)) t = AsmOK u /\
          LENGTH u.as_stack = H (SUC k) + extra
Proof
  Induct_on `ops`
  >- (simp[prefix_wf_def, execute_plan_def, prefix_end_len_def] >>
      rpt gen_tac >> qexists `\k. h` >> simp[]) >>
  rpt gen_tac >> simp[prefix_wf_def, prefix_end_len_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `stack_op_wf lo op n = (T,m)` >>
  `FST (stack_op_wf lo op n)` by simp[] >>
  drule generated_admin_op_heights >>
  disch_then (qspecl_then [`fmp`, `o2pc`] strip_assume_tac) >>
  first_x_assum (qspecl_then [`fmp`, `lo`, `o2pc`, `m`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `J` strip_assume_tac) >>
  qexists `\k. if k <= LENGTH (exec_stack_op fmp op) then H k
               else J (k - LENGTH (exec_stack_op fmp op))` >>
  simp[execute_plan_def] >> rewrite_tac[GSYM execute_plan_def] >>
  conj_tac
  >- (IF_CASES_TAC
      >- (`LENGTH (execute_plan fmp ops) = 0` by decide_tac >> gvs[]) >>
      simp[]) >>
  rpt strip_tac >>
  Cases_on `k < LENGTH (exec_stack_op fmp op)`
  >- (`k <= LENGTH (exec_stack_op fmp op) /\
       SUC k <= LENGTH (exec_stack_op fmp op)` by decide_tac >>
      gvs[EL_APPEND1] >> first_x_assum irule >> simp[ADD_COMM]) >>
  `LENGTH (exec_stack_op fmp op) <= k /\
   ~(SUC k <= LENGTH (exec_stack_op fmp op)) /\
   SUC k - LENGTH (exec_stack_op fmp op) =
     SUC (k - LENGTH (exec_stack_op fmp op))` by decide_tac >>
  `LENGTH t.as_stack = extra + J (k - LENGTH (exec_stack_op fmp op))` by
    (Cases_on `k = LENGTH (exec_stack_op fmp op)` >> gvs[]) >>
  gvs[EL_APPEND2] >> first_x_assum irule >> simp[]
QED

(* Offset word bounds are unnecessary here: only height and progress, not the
   value of a spill address, are observed. *)
Theorem generated_admin_micro_coverage:
  !p pc fmp ops h.
    let lo = SND (compute_label_offsets p);
        o2pc = build_offset_to_pc p;
        code = execute_plan fmp ops
    in
      prefix_wf lo h ops /\ asm_block_at p pc code ==>
      ?H. H 0 = h /\ H (LENGTH code) = prefix_end_len lo h ops /\
        (!inst. MEM inst code ==>
          inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI") /\
        !k extra t.
          k < LENGTH code /\ t.as_pc = pc + k /\
          LENGTH t.as_stack = H k + extra ==>
          ?u. static_abort_normal lo o2pc p 1 t u /\
            u.as_pc = pc + k + 1 /\
            LENGTH u.as_stack = H (SUC k) + extra /\
            u.as_call_ctx = t.as_call_ctx /\ u.as_requests = t.as_requests
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  drule generated_admin_prefix_heights >>
  disch_then (qspecl_then [`fmp`, `build_offset_to_pc p`] strip_assume_tac) >>
  `EVERY static_abort_admin (execute_plan fmp ops)` by
    metis_tac[prefix_static_abort_admin] >>
  qexists `H` >> simp[] >> conj_tac
  >- metis_tac[EVERY_MEM, static_abort_admin_safe] >>
  rpt strip_tac >>
  `static_abort_admin (EL k (execute_plan fmp ops))` by
    metis_tac[EVERY_EL] >>
  `?u. asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
         (EL k (execute_plan fmp ops)) t = AsmOK u /\
       LENGTH u.as_stack = H (SUC k) + extra` by
    (first_x_assum irule >> simp[]) >>
  `t.as_pc < LENGTH p /\ EL t.as_pc p = EL k (execute_plan fmp ops)` by
    (gvs[asm_block_at_def] >> first_x_assum (qspec_then `k` mp_tac) >>
     simp[]) >>
  `u.as_pc = t.as_pc + 1` by
    metis_tac[asm_step_pc_advance, static_abort_admin_safe] >>
  `u.as_requests = t.as_requests /\ u.as_call_ctx = t.as_call_ctx` by
    metis_tac[static_abort_admin_step_observers] >>
  `static_abort_safe_at p t` by metis_tac[static_abort_admin_safe] >>
  qexists `u` >> simp[static_abort_normal_def, static_abort_trace_def] >>
  rewrite_tac[numLib.num_CONV ``1:num``] >> simp[asm_steps_def]
QED
