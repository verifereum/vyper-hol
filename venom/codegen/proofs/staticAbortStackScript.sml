(* Height-only administrative plan execution and strict-prefix observations. *)
Theory staticAbortStack
Ancestors
  staticAbortTrace prefixExec prefixSim planExec symbolResolve asmSem asmIR
  stackOpSim stackPlanTypes planWf asmFrame list rich_list arithmetic

Definition static_abort_admin_def:
  static_abort_admin inst <=>
    case inst of
      AsmOp name => MEM name
        (["POP"; "MSTORE"; "MLOAD"] ++
         MAP dup_name (GENLIST SUC 16) ++ MAP swap_name (GENLIST SUC 16))
    | AsmPush _ => T
    | AsmLabel _ => T
    | AsmPushLabel _ => T
    | AsmPushOfst _ _ => T
    | _ => F
End

Theorem static_abort_admin_safe:
  static_abort_admin inst ==>
  inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI" /\
  (!prog s. s.as_pc < LENGTH prog /\ EL s.as_pc prog = inst ==>
    static_abort_safe_at prog s)
Proof
  Cases_on `inst` >>
  simp[static_abort_admin_def, static_abort_safe_at_def,
       GENLIST_CONS, dup_name_def, swap_name_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  EVAL_TAC >> simp[]
QED

Theorem static_abort_admin_step_observers:
  static_abort_admin inst /\ asm_step lo o2pc inst s = AsmOK t ==>
  t.as_requests = s.as_requests /\ t.as_call_ctx = s.as_call_ctx
Proof
  Cases_on `inst` >>
  simp[static_abort_admin_def, GENLIST_CONS, dup_name_def, swap_name_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `asm_step _ _ _ _ = _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV (computeLib.RESTR_EVAL_CONV
    [``asm_pop``, ``asm_mstore``, ``asm_mload``, ``asm_dup``, ``asm_swap``,
     ``asm_next``, ``FLOOKUP``]))) >>
  simp[asm_pop_def, asm_mstore_def, asm_mload_def, asm_dup_def, asm_swap_def,
       asm_next_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem static_abort_admin_run:
  !insts lo o2pc prog s t.
    EVERY static_abort_admin insts /\
    asm_block_at prog s.as_pc insts /\
    asm_steps lo o2pc prog (LENGTH insts) s = AsmOK t ==>
    static_abort_normal lo o2pc prog (LENGTH insts) s t /\
    t.as_call_ctx = s.as_call_ctx
Proof
  Induct >- simp[static_abort_normal_def, asm_steps_def] >>
  rpt gen_tac >> strip_tac >>
  fs[asm_block_at_cons, EVERY_DEF] >>
  qpat_x_assum `asm_steps _ _ _ _ _ = _` mp_tac >>
  simp[Once asm_steps_def] >>
  Cases_on `asm_step lo o2pc h s` >> simp[] >> strip_tac >>
  rename1 `asm_step lo o2pc h s = AsmOK u` >>
  `u.as_pc = s.as_pc + 1` by
    metis_tac[static_abort_admin_safe, asm_step_pc_advance] >>
  `u.as_requests = s.as_requests /\ u.as_call_ctx = s.as_call_ctx` by
    metis_tac[static_abort_admin_step_observers] >>
  `static_abort_normal lo o2pc prog (LENGTH insts) u t /\
   t.as_call_ctx = u.as_call_ctx` by
    (first_x_assum irule >> gvs[]) >>
  `static_abort_normal lo o2pc prog 1 s u` by
    (simp[static_abort_normal_def, static_abort_trace_def] >>
     conj_tac >- (rewrite_tac[numLib.num_CONV ``1:num``] >>
       simp[asm_steps_def]) >>
     simp[asm_steps_def] >> metis_tac[static_abort_admin_safe]) >>
  conj_tac >- (
    `SUC (LENGTH insts) = 1 + LENGTH insts` by simp[] >>
    pop_assum SUBST1_TAC >> irule static_abort_normal_append >>
    qexists `u` >> simp[]) >>
  metis_tac[]
QED

Theorem stack_op_static_abort_admin:
  is_prefix_op op /\ FST (stack_op_wf lo op n) ==>
  EVERY static_abort_admin (exec_stack_op fmp op)
Proof
  Cases_on `op` >>
  simp[is_prefix_op_def, stack_op_wf_def, exec_stack_op_def,
       static_abort_admin_def, EVERY_REPLICATE] >>
  rpt strip_tac
  >- (Cases_on `o'` >> simp[exec_stack_op_def, static_abort_admin_def])
  >> `n' < SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC
       (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))))))))`
       by decide_tac
  >> pop_assum mp_tac
  >> pure_rewrite_tac[prim_recTheory.LESS_THM, prim_recTheory.NOT_LESS_0]
  >> strip_tac >> gvs[]
QED

Theorem prefix_static_abort_admin:
  !ops lo n fmp.
    prefix_wf lo n ops ==>
    EVERY static_abort_admin (execute_plan fmp ops)
Proof
  Induct >> simp[prefix_wf_def, execute_plan_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >>
  conj_tac
  >- (irule stack_op_static_abort_admin >>
      conj_tac >- (qexistsl [`lo`, `n`] >> simp[]) >>
      Cases_on `h` >> fs[stack_op_wf_def, is_prefix_op_def]) >>
  rewrite_tac[GSYM execute_plan_def] >> first_x_assum irule >>
  qexistsl [`lo`, `n'`] >> simp[]
QED

Theorem prefix_static_abort_sim:
  !ops fmp lo o2pc prog s top rest n.
    prefix_wf lo n ops /\ s.as_stack = top ++ rest /\ LENGTH top = n /\
    asm_block_at prog s.as_pc (execute_plan fmp ops) ==>
    ?t top'.
      static_abort_normal lo o2pc prog (LENGTH (execute_plan fmp ops)) s t /\
      t.as_stack = top' ++ rest /\ LENGTH top' = prefix_end_len lo n ops /\
      t.as_pc = s.as_pc + LENGTH (execute_plan fmp ops) /\
      t.as_call_ctx = s.as_call_ctx
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY is_prefix_op ops` by metis_tac[planWfTheory.prefix_wf_every_prefix_op] >>
  drule prefixExecTheory.prefix_sim >>
  disch_then (qspecl_then [`fmp`, `o2pc`, `prog`,
    `s with as_stack := top`] mp_tac) >>
  simp[GSYM execute_plan_def] >> strip_tac >>
  `asm_steps lo o2pc prog (LENGTH (execute_plan fmp ops)) s =
     AsmOK (st' with as_stack := st'.as_stack ++ rest)` by
    (drule asmFrameTheory.asm_steps_frame >>
     disch_then (qspec_then `rest` mp_tac) >>
     `s with as_stack := top ++ rest = s` by
       simp[asm_state_component_equality] >> simp[]) >>
  qexistsl [`st' with as_stack := st'.as_stack ++ rest`, `st'.as_stack`] >>
  `EVERY static_abort_admin (execute_plan fmp ops)` by
    metis_tac[prefix_static_abort_admin] >>
  qpat_x_assum `asm_steps _ _ _ _ (s with as_stack := top) = _` kall_tac >>
  drule_all_then strip_assume_tac static_abort_admin_run >> simp[]
QED
