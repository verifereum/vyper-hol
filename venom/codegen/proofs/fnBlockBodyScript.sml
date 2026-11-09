(*
 * The rest of a function's run from inside one of its blocks, simulated by
 * the block's DFS code from fn_frame_inv.  Shared by the two steps of the
 * fuel induction behind venomToAsmProps (fnEntryStep, fnBlockStep): each
 * simulates its block's prefix (entry parameters; cleanup and PHIs) and
 * hands the rest of the run to block_body_frame_sim.
 *
 * TOP-LEVEL:
 *   block_rest            - the run_blocks result from inside a block
 *   block_body_frame_sim  - the rest of the run, simulated
 *)

Theory fnBlockBody
Ancestors
  fnBlockPlanStatic fnAliasStep fnFrameStepsRevertForwardDeep
  fnFrameDeep fnLineageStatic fnPlanPrefix fnSimSpec fnFrameSteps fnFrameBoundary fnFrameTerminal gasFrameSim
  genFrameSim fnPlanPlace fnPlanCover fnAliasInv fnPlanLineage frameRel
  venomExecSemantics fnBlockBodyClasses fnBlockBodySteps fnBlockBodyHelpers
  unitShapeDefs rich_list

(* What run_blocks (SUC fuel) returns once its block has reached state vs:
   the rest of the block, then the rest of the function from its successor
   (run_blocks_unfold, run_block_def). *)
Definition block_rest_def:
  block_rest fuel ctx fn bb vs =
    case exec_block fuel ctx bb vs of
      OK vs' => if vs'.vs_halted then Halt vs' else run_blocks fuel ctx fn vs'
    | res => res
End

(* ===== Facts from the codegen preconditions ===== *)

Theorem codegen_ready_fn_inst[local]:
  !fn inst.
    codegen_ready_fn fn /\ MEM inst (fn_insts fn) ==> codegen_ready_inst inst
Proof
  simp[stackPlanGenTheory.codegen_ready_fn_def, venomInstTheory.fn_insts_def] >>
  rpt strip_tac >>
  qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
  qpat_x_assum `MEM _ _` mp_tac >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[venomInstTheory.fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[listTheory.EVERY_MEM]
QED

(* DUP and SWAP reach 16 slots. *)
Theorem body_operands_le_16:
  !fn inst.
    codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode <> PHI ==>
    LENGTH (compute_operands inst) <= 16
Proof
  rpt strip_tac >>
  `codegen_ready_inst inst` by metis_tac[codegen_ready_fn_inst] >>
  gvs[stackPlanGenTheory.codegen_ready_inst_def]
QED

(* The EVM has LOG0 to LOG4. *)
Theorem body_log_topics:
  !fn inst.
    codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode <> PHI ==>
    (inst.inst_opcode = LOG ==>
     case inst.inst_operands of Lit tc :: _ => w2n tc <= 4 | _ => F)
Proof
  rpt strip_tac >>
  `codegen_ready_inst inst` by metis_tac[codegen_ready_fn_inst] >>
  gvs[stackPlanGenTheory.codegen_ready_inst_def]
QED

(* A revert forwarding's code neither spills nor restores:
   block_plan_state_static's last conjunct. *)
Theorem body_revert_no_spill:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb
   ps_l ps_dfs ps_dfs_after h promised block_ops ps_after k ps inst next_live
   next_is_term.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      k ps /\
    phi_prefix_length bb.bb_instructions <= k /\
    k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst /\
    next_live = live_vars_at liveness bb.bb_label (k + 1) /\
    next_is_term =
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
    ==>
    !j. revert_forward_pair bb k j ==>
    !ops ps_end.
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (k - LENGTH (get_params bb.bb_instructions))
        (DROP k bb.bb_instructions) ps = SOME (ops, ps_end) ==>
      !off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops
Proof
  rpt gen_tac >>
  disch_then (fn th => ACCEPT_TAC (last (CONJUNCTS
    (MATCH_MP (SPEC_ALL block_plan_state_static) th))))
QED

Theorem log_case_topics:
  !ops. (case ops of Lit tc :: _ => w2n tc <= 4 | _ => F) ==>
        ?tc args. ops = Lit tc :: args /\ w2n tc <= 4
Proof
  Cases >> simp[] >> Cases_on `h` >> simp[]
QED

(* ===== block_rest, one instruction at a time ===== *)

Theorem block_rest_advance:
  get_instruction bb vs.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst vs = OK vs1 /\ ~is_terminator inst.inst_opcode ==>
  block_rest fuel ctx fn bb vs =
  block_rest fuel ctx fn bb (vs1 with vs_inst_idx := SUC vs.vs_inst_idx)
Proof
  strip_tac >> PURE_REWRITE_TAC [block_rest_def] >>
  drule exec_block_step >> disch_then (fn th => REWRITE_TAC [th]) >>
  simp[]
QED

Theorem block_rest_jump:
  get_instruction bb vs.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst vs = OK vs1 /\ is_terminator inst.inst_opcode /\
  ~vs1.vs_halted ==>
  block_rest fuel ctx fn bb vs = run_blocks fuel ctx fn vs1
Proof
  strip_tac >> PURE_REWRITE_TAC [block_rest_def] >>
  drule exec_block_step >> disch_then (fn th => REWRITE_TAC [th]) >>
  simp[]
QED

Theorem block_rest_other:
  get_instruction bb vs.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst vs = res /\ (!s. res <> OK s) ==>
  block_rest fuel ctx fn bb vs = res
Proof
  strip_tac >> PURE_REWRITE_TAC [block_rest_def] >>
  drule exec_block_step >> disch_then (fn th => REWRITE_TAC [th]) >>
  Cases_on `res` >> gvs[] >> metis_tac[]
QED

Theorem block_rest_error:
  exec_block fuel ctx bb vs = Error e ==>
  block_rest fuel ctx fn bb vs = Error e
Proof
  simp[block_rest_def]
QED

Theorem block_rest_exec[local]:
  (!t. exec_block fuel ctx bb vs <> OK t) /\
  body_result lo o2pc prog cpl ctx fn mem0 pc_ret rest as
    (exec_block fuel ctx bb vs) ==>
  body_result lo o2pc prog cpl ctx fn mem0 pc_ret rest as
    (block_rest fuel ctx fn bb vs)
Proof
  rw[block_rest_def] >> Cases_on `exec_block fuel ctx bb vs` >> fs[]
QED

(* ===== The induction on the instructions left ===== *)

fun is_body_inv th =
  (fst (dest_const (fst (strip_comb (concl th)))) = "body_inv")
  handle HOL_ERR _ => false;

val unpack_inv =
  first_assum (strip_assume_tac o REWRITE_RULE [body_inv_def] o
               assert is_body_inv);

(* Rewrites block_rest at vs to the instruction's result res. *)
fun other_tac res =
  `!s. ^res <> OK s` by simp[] >>
  drule_all block_rest_other >> disch_then (fn th => REWRITE_TAC [th]);

Theorem body_run[local]:
  !d k prefix_ops rest_ops ps vs as.
    d = LENGTH bb.bb_instructions - k /\
    gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 ==>
    body_result lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (block_rest fuel ctx fn bb vs)
Proof
  completeInduct_on `d` >> rpt gen_tac >> strip_tac >>
  drule body_inv_facts >> strip_tac >> unpack_inv >>
  reverse (Cases_on `k < LENGTH bb.bb_instructions`)
  >- (qspecl_then [`fuel`, `ctx`, `bb`, `vs`] mp_tac exec_block_out_of_range >>
      impl_tac
      >- (qpat_x_assum `vs.vs_inst_idx = k` SUBST1_TAC >>
          qpat_x_assum `~(k < _)` mp_tac >> rpt (pop_assum kall_tac) >>
          decide_tac) >>
      strip_tac >> drule block_rest_error >>
      disch_then (fn th => REWRITE_TAC [th]) >>
      MATCH_ACCEPT_TAC body_result_error) >>
  `?inst. EL k bb.bb_instructions = inst` by
    (qexists_tac `EL k bb.bb_instructions` >> REWRITE_TAC []) >>
  drule_all body_inv_inst >> strip_tac >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by
    (qpat_assum `vs.vs_inst_idx = k` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qspecl_then [`fn`, `inst`] mp_tac body_operands_le_16 >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `inst.inst_opcode = LOG ==>
   ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4` by
    (strip_tac >> irule log_case_topics >>
     qspecl_then [`fn`, `inst`] mp_tac body_log_topics >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  Cases_on `?j. revert_forward_pair bb k j`
  >- (pop_assum strip_assume_tac >>
      qspecl_then [`liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`,
                   `lbl_ctr`, `fn`, `fn_ops`, `ps_end`, `bb.bb_label`, `bb`,
                   `ps_l`, `ps_dfs`, `ps_dfs_after`, `h`, `promised`,
                   `block_ops`, `ps_after`, `k`, `ps`, `inst`,
                   `live_vars_at liveness bb.bb_label (k + 1)`,
                   `k + 1 < LENGTH bb.bb_instructions /\
                    is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`]
        mp_tac body_revert_no_spill >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
          metis_tac[codegen_ready_fn_no_marker]) >>
      disch_then (qspec_then `j` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      disch_then (qspecl_then [`rest_ops`, `ps_after`] mp_tac) >>
      impl_tac
      >- (`k - LENGTH (get_params bb.bb_instructions) +
           LENGTH (get_params bb.bb_instructions) = k` by
            (qpat_x_assum `LENGTH (get_params _) <= k` mp_tac >>
             rpt (pop_assum kall_tac) >> decide_tac) >>
          `DROP (k - LENGTH (get_params bb.bb_instructions))
             (non_param_insts bb) = DROP k bb.bb_instructions` by
            (qpat_x_assum `non_param_insts bb = _` SUBST1_TAC >>
             REWRITE_TAC [DROP_DROP_T] >>
             qpat_x_assum `_ + _ = k` (fn th => REWRITE_TAC [th])) >>
          qpat_x_assum `DROP (k - _) (non_param_insts bb) = _`
            (fn th => REWRITE_TAC [GSYM th]) >>
          first_assum ACCEPT_TAC) >>
      strip_tac >>
      mp_tac (SPEC_ALL body_revert_step) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >> irule block_rest_exec >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (assume_tac o REWRITE_RULE [NOT_EXISTS_THM]) >>
  `?res. step_inst fuel ctx inst vs = res` by simp[] >>
  Cases_on `res`
  >~ [`step_inst fuel ctx inst vs = OK _`]
  >- (rename1 `step_inst fuel ctx inst vs = OK vs1` >>
      Cases_on `is_terminator inst.inst_opcode`
      >- (qspecl_then [`fuel`, `ctx`, `inst`, `vs`, `vs1`] mp_tac
            step_ok_terminator_jump >>
          impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac
          >~ [`inst.inst_opcode = DJMP`]
          >- (qpat_x_assum `inst_shape_ok inst` mp_tac >>
              qpat_x_assum `inst.inst_opcode = DJMP` mp_tac >>
              rpt (pop_assum kall_tac) >> simp[inst_shape_ok_def])
          >~ [`inst.inst_opcode = JMP`]
          >- (mp_tac (SPEC_ALL body_jmp_step) >>
              impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
              strip_tac >>
              mp_tac (SPEC_ALL block_rest_jump) >>
              impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
              disch_then (fn th => REWRITE_TAC [th]) >>
              first_assum ACCEPT_TAC)
          >~ [`inst.inst_opcode = JNZ`]
          >- (mp_tac (SPEC_ALL body_jnz_step) >>
              impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
              strip_tac >>
              mp_tac (SPEC_ALL block_rest_jump) >>
              impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
              disch_then (fn th => REWRITE_TAC [th]) >>
              first_assum ACCEPT_TAC)) >>
      `?ops ps' rest' n as1.
         generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
         asm_steps lo o2pc prog n as = AsmOK as1 /\
         fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
         as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)` by
        (Cases_on `inst.inst_opcode = INVOKE`
         >- (mp_tac (SPEC_ALL body_invoke_step) >>
             impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
             disch_then (fn th => irule (CONJUNCT1 th)) >>
             first_assum ACCEPT_TAC) >>
         Cases_on `inst.inst_opcode = GAS`
         >- (mp_tac (SPEC_ALL body_gas_ok) >>
             impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
             disch_then ACCEPT_TAC) >>
         mp_tac (SPEC_ALL body_ordinary_ok) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then ACCEPT_TAC) >>
      mp_tac (SPEC_ALL body_inv_advance) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
      qpat_x_assum `!m. m < d ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC k` mp_tac) >>
      impl_tac
      >- (qpat_x_assum `d = _` SUBST1_TAC >>
          qpat_x_assum `k < LENGTH _` mp_tac >> rpt (pop_assum kall_tac) >>
          decide_tac) >>
      disch_then (qspecl_then [`SUC k`, `prefix_ops ++ ops`, `rest'`, `ps'`,
                               `vs1 with vs_inst_idx := SUC k`, `as1`]
                    mp_tac) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                   REWRITE_TAC []) >>
      strip_tac >>
      mp_tac (SPEC_ALL block_rest_advance) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_assum `vs.vs_inst_idx = k` (fn th => REWRITE_TAC [th]) >>
      disch_then (fn th => REWRITE_TAC [th]) >>
      qspecl_then [`lo`, `o2pc`, `prog`, `cpl`, `ctx`, `fn`, `mem0`, `pc_ret`,
                   `rest`, `as`, `as1`, `n`,
                   `block_rest fuel ctx fn bb (vs1 with vs_inst_idx := SUC k)`]
        mp_tac body_result_prefix >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
  >~ [`step_inst fuel ctx inst vs = IntRet _ _`]
  >- (rename1 `step_inst fuel ctx inst vs = IntRet ret vs1` >>
      other_tac ``IntRet ret vs1`` >>
      mp_tac (SPEC_ALL body_ret_step) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
  >~ [`step_inst fuel ctx inst vs = Halt _`]
  >- (rename1 `step_inst fuel ctx inst vs = Halt vs1` >>
      other_tac ``Halt vs1`` >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (mp_tac (SPEC_ALL body_invoke_step) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
          disch_then (fn th => irule (CONJUNCT1 (CONJUNCT2 th))) >>
          first_assum ACCEPT_TAC) >>
      mp_tac (SPEC_ALL body_halt_step) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
  >~ [`step_inst fuel ctx inst vs = Abort _ _`]
  >- (rename1 `step_inst fuel ctx inst vs = Abort a vs1` >>
      other_tac ``Abort a vs1`` >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (mp_tac (SPEC_ALL body_invoke_step) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
          disch_then (fn th => irule (CONJUNCT2 (CONJUNCT2 th))) >>
          first_assum ACCEPT_TAC) >>
      mp_tac (SPEC_ALL body_abort_step) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
  >~ [`step_inst fuel ctx inst vs = Error _`]
  >- (rename1 `step_inst fuel ctx inst vs = Error e` >>
      other_tac ``Error e`` >>
      MATCH_ACCEPT_TAC body_result_error)
QED

(* ===== The theorem ===== *)

(* vs is at instruction k of block bb, past its PHIs, and fn_frame_inv
   holds with ps, the planner's state at k when bb is planned from its
   lineage state ps_l (with the cleanup fields h, promised that
   lineage_state_block_plan picks, which also gives the alloc equation).
   k is not inside a revert forwarding (its instructions run as one
   step, revert_forward_frame_sim_deep, from its RETURNDATACOPY).
   That plan is the block's DFS code block_ops, placed at pc0, and as is
   at its rest_ops, the code of the instructions from k on.  The entry
   step starts here after the parameters (entry_params_frame_sim), the
   block step after the cleanup and the PHI prefix.

   Why it should hold: by induction on the instructions from k.  Each runs
   by its instruction lemma, in the fnFrameDeep form (operands at any
   depth, repeated dead_stack_marker slots): gen_inst_frame_sim_deep,
   gas_inst_frame_sim_owned_deep, gen_invoke_frame_sim_deep with
   gen_fn_sim_at fuel for the callee, the halt, abort and return steps,
   revert_forward_frame_sim_deep.  Their static premises at the planner
   state ps come from fnBlockPlanStatic$block_plan_state_static, the slot
   alias is carried through each step by fnAliasStep$alias_step_preserve,
   and their
   memory premises come from Inv (codegen_memory_obligations,
   reachability_closed).  A JMP or JNZ ends the block at a successor
   whose code is placed (dfs_block_code_placed), entered with the
   lineage entry from this block, so gen_fn_frame_sim_at fuel finishes
   the run and its assembly steps are added to the block's. *)
Theorem block_body_frame_sim:
  !fuel rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv ra pc_ret
   rest mem0.
    gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    ~vs.vs_call_ctx.cc_static /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\
    (!inst. active_inst fn inst vs ==> Inv ctx fn inst vs) /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    fn_reachable fn bb.bb_label /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
    ps_after.ps_spilled = ps_dfs_after.ps_spilled /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      k ps /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (k - LENGTH (get_params bb.bb_instructions))
      (DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps = SOME (rest_ops, ps_after) /\
    block_ops = SOLabel bb.bb_label :: prefix_ops ++ rest_ops /\
    phi_prefix_length bb.bb_instructions <= k /\
    (!i j. revert_forward_pair bb i j ==> k <= i \/ j < k) /\
    vs.vs_inst_idx = k /\
    asm_block_at prog pc0 (execute_plan cp.cp_initial_fmp block_ops) /\
    as.as_pc = pc0 + LENGTH (execute_plan cp.cp_initial_fmp
                                 (SOLabel bb.bb_label :: prefix_ops)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret)
    ==>
    (!vs'. block_rest fuel ctx fn bb vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. block_rest fuel ctx fn bb vs = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as') /\
    (!ret vs'. block_rest fuel ctx fn bb vs = IntRet ret vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE ret.iret_values ++ rest /\
               context_memory_rel cp vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cp b /\
                    ~closure_spill_byte ctx cp fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as')
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generate_context_plan _ = SOME cpl` >>
  `body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0` by
    (PURE_REWRITE_TAC [body_inv_def] >> rpt conj_tac >>
     first_assum ACCEPT_TAC) >>
  qspecl_then [`LENGTH bb.bb_instructions - k`, `k`, `prefix_ops`,
               `rest_ops`, `ps`, `vs`, `as`] mp_tac body_run >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
               REWRITE_TAC []) >>
  disch_then (ACCEPT_TAC o PURE_REWRITE_RULE [body_result_def])
QED
