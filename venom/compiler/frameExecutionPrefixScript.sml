Theory frameExecutionPrefix
Ancestors frameInvokeReturn contextCodegenRel crossBlockSimProofs
  venomExecSemantics venomExecProofs venomState venomWf venomInst venomInstProofs passSimulationDefs arithmetic

(* A finite local prefix. Completed calls are supplied as successful steps;
   unfinished calls belong to the parallel activation stack, not this relation. *)
Inductive execution_prefix:
[~entry:]
  (!ctx fn entry inst s.
    enters_block fn entry s /\ active_inst fn inst s ==>
    execution_prefix ctx fn entry inst s)
[~next:]
  (!ctx fn entry inst s inst' post fuel.
    execution_prefix ctx fn entry inst s /\ active_inst fn inst s /\
    ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK post /\
    active_inst fn inst' (post with vs_inst_idx := SUC s.vs_inst_idx) ==>
    execution_prefix ctx fn entry inst'
      (post with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!ctx fn entry inst s inst' post s1 fuel.
    execution_prefix ctx fn entry inst s /\ active_inst fn inst s /\
    is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK post /\
    ~post.vs_halted /\ enters_block fn post s1 /\ active_inst fn inst' s1 ==>
    execution_prefix ctx fn entry inst' s1)
End

Theorem prefix_step_fuel_mono:
  (!e. step_inst fuel ctx inst s <> Error e) ==>
  step_inst (fuel + k) ctx inst s = step_inst fuel ctx inst s
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst`
      >- fs[Once step_inst_def] >>
      PairCases_on `x` >>
      Cases_on `lookup_function x0 ctx.ctx_functions`
      >- fs[Once step_inst_def] >>
      rename1 `lookup_function x0 ctx.ctx_functions = SOME callee` >>
      Cases_on `eval_operands x1 s`
      >- fs[Once step_inst_def] >>
      rename1 `eval_operands x1 s = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- fs[Once step_inst_def] >>
      rename1 `setup_callee callee args s = SOME cs` >>
      `terminates (run_blocks fuel ctx callee cs)` by
        (Cases_on `run_blocks fuel ctx callee cs` >>
         fs[Once step_inst_def, terminates_def]) >>
      drule run_blocks_fuel_mono >>
      disch_then (qspec_then `k` assume_tac) >>
      simp[step_inst_def]) >>
  simp[step_inst_def]
QED

Theorem prefix_exec_fuel_mono:
  !n ctx bb s fuel.
  n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
  (!e. exec_block fuel ctx bb s <> Error e) ==>
  !k. exec_block (fuel + k) ctx bb s = exec_block fuel ctx bb s
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- fs[Once exec_block_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `!e. step_inst fuel ctx inst s <> Error e` by
    (spose_not_then strip_assume_tac >> fs[Once exec_block_def]) >>
  drule prefix_step_fuel_mono >>
  disch_then (qspec_then `k` assume_tac) >>
  CONV_TAC (BINOP_CONV (REWR_CONV exec_block_def)) >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  rename1 `step_inst fuel ctx inst s = OK post` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  `!e. exec_block fuel ctx bb
    (post with vs_inst_idx := SUC s.vs_inst_idx) <> Error e` by
    (qpat_x_assum `!e. exec_block fuel ctx bb s <> Error e` mp_tac >>
     simp[Once exec_block_def]) >>
  first_x_assum irule >>
  gvs[get_instruction_def] >> decide_tac
QED

(* A successful continuation from an active instruction, without re-running
   its block's PHIs. The disjunction separates block return and block exit. *)
Definition local_return_suffix_def:
  local_return_suffix ctx fn s ret send <=>
  ?fuel bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (exec_block fuel ctx bb s = IntRet ret send \/
     ?post. exec_block fuel ctx bb s = OK post /\ ~post.vs_halted /\
       run_blocks fuel ctx fn post = IntRet ret send)
End

Theorem prefix_active_lookup[local]:
  wf_function fn /\ active_inst fn inst s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[active_inst_def] >> qexists `bb` >> simp[get_instruction_def] >>
  irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]
QED

Theorem local_return_suffix_mono:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (exec_block fuel ctx bb s = IntRet ret send \/
   ?post. exec_block fuel ctx bb s = OK post /\ ~post.vs_halted /\
     run_blocks fuel ctx fn post = IntRet ret send) ==>
  exec_block (fuel + k) ctx bb s = IntRet ret send \/
  ?post. exec_block (fuel + k) ctx bb s = OK post /\ ~post.vs_halted /\
    run_blocks (fuel + k) ctx fn post = IntRet ret send
Proof
  strip_tac >>
  `!e. exec_block fuel ctx bb s <> Error e` by simp[] >>
  `exec_block (fuel + k) ctx bb s = exec_block fuel ctx bb s` by
    (irule prefix_exec_fuel_mono >> simp[]) >>
  simp[] >>
  `terminates (run_blocks fuel ctx fn post)` by simp[terminates_def] >>
  drule run_blocks_fuel_mono >> simp[]
QED

Theorem local_return_suffix_entry:
  enters_block fn entry s /\ local_return_suffix ctx fn s ret send ==>
  ?fuel. run_blocks fuel ctx fn entry = IntRet ret send
Proof
  rw[enters_block_def, local_return_suffix_def] >>
  `s_phi.vs_current_bb = entry.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  gvs[] >> qexists `SUC fuel` >> simp[Once run_blocks_def]
QED

Theorem local_return_suffix_terminal:
  wf_function fn /\ active_inst fn inst s /\
  step_inst fuel ctx inst s = IntRet ret send ==>
  local_return_suffix ctx fn s ret send
Proof
  strip_tac >> drule_all prefix_active_lookup >> strip_tac >>
  simp[local_return_suffix_def] >> qexists `fuel` >>
  disj1_tac >> simp[Once exec_block_def]
QED

Theorem local_return_suffix_next:
  wf_function fn /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ step_inst f ctx inst s = OK post /\
  local_return_suffix ctx fn
    (post with vs_inst_idx := SUC s.vs_inst_idx) ret send ==>
  local_return_suffix ctx fn s ret send
Proof
  strip_tac >>
  `post.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  drule_all prefix_active_lookup >> strip_tac >>
  qpat_x_assum `local_return_suffix _ _ _ _ _` mp_tac >>
  simp[local_return_suffix_def] >>
  disch_then (qx_choose_then `n` strip_assume_tac) >>
  `step_inst (n + f) ctx inst s = OK post` by
    (simp[ADD_COMM] >>
     `!e. step_inst f ctx inst s <> Error e` by simp[] >>
     drule prefix_step_fuel_mono >> simp[]) >>
  fs[ADD_COMM] >>
  `exec_block (n + f) ctx bb s =
   exec_block (n + f) ctx bb (post with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once exec_block_def] >>
  qexists `n + f` >> simp[] >>
  `!e. exec_block n ctx bb
    (post with vs_inst_idx := SUC s.vs_inst_idx) <> Error e` by simp[] >>
  `exec_block (n + f) ctx bb (post with vs_inst_idx := SUC s.vs_inst_idx) =
   exec_block n ctx bb (post with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule prefix_exec_fuel_mono >> simp[]) >>
  gvs[ADD_COMM] >>
  `terminates (run_blocks n ctx fn post')` by simp[terminates_def] >>
  drule run_blocks_fuel_mono >> simp[]
QED

Theorem local_return_suffix_block:
  wf_function fn /\ active_inst fn inst s /\
  is_terminator inst.inst_opcode /\ step_inst f ctx inst s = OK post /\
  ~post.vs_halted /\ enters_block fn post s1 /\
  local_return_suffix ctx fn s1 ret send ==>
  local_return_suffix ctx fn s ret send
Proof
  strip_tac >> drule_all prefix_active_lookup >> strip_tac >>
  drule_all local_return_suffix_entry >> strip_tac >>
  rename1 `run_blocks n ctx fn post = IntRet ret send` >>
  `step_inst (f + n) ctx inst s = OK post` by
    (`!e. step_inst f ctx inst s <> Error e` by simp[] >>
     drule prefix_step_fuel_mono >> simp[]) >>
  `terminates (run_blocks n ctx fn post)` by simp[terminates_def] >>
  `run_blocks (n + f) ctx fn post = IntRet ret send` by
    (drule run_blocks_fuel_mono >> simp[]) >>
  fs[ADD_COMM] >> simp[local_return_suffix_def] >> qexists `f + n` >>
  disj2_tac >> qexists `post` >> simp[Once exec_block_def]
QED

Theorem execution_prefix_continuation:
  !ctx fn entry inst s.
  execution_prefix ctx fn entry inst s ==>
  wf_function fn ==>
  !ret send. local_return_suffix ctx fn s ret send ==>
  ?fuel. run_blocks fuel ctx fn entry = IntRet ret send
Proof
  ho_match_mp_tac execution_prefix_ind >> rpt strip_tac
  >- metis_tac[local_return_suffix_entry]
  >- (first_x_assum irule >> simp[] >>
      irule local_return_suffix_next >> metis_tac[]) >>
  first_x_assum irule >> simp[] >>
  irule local_return_suffix_block >> metis_tac[]
QED

Theorem execution_prefix_active:
  !ctx fn entry inst s.
  execution_prefix ctx fn entry inst s ==> active_inst fn inst s
Proof
  ho_match_mp_tac execution_prefix_ind >> simp[]
QED

Theorem execution_prefix_return:
  wf_function fn /\ execution_prefix ctx fn entry inst s /\
  step_inst fuel ctx inst s = IntRet ret send ==>
  ?n. run_blocks n ctx fn entry = IntRet ret send
Proof
  strip_tac >> drule execution_prefix_continuation >> simp[] >>
  disch_then irule >> irule local_return_suffix_terminal >>
  metis_tac[execution_prefix_active]
QED
