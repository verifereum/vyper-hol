(* Straight-line code a compile step appends to the current block, run as
   one joint path when its memory and pointer checks hold along the run;
   and the ghost frames the forcing cases share. *)
Theory bodyFullUnwrapRun
Ancestors
  fragGasSeqPtr fragGasOriginPtr fragExecMem fragExec exprLoweringProps
  allocaHistoryFragment allocaHistory bodyPtrDefs compileEnv venomInst
  list rich_list pred_set

Theorem emitted_origin_ptr_path:
  !code sb sc s t G tn G' tn'.
    fn_has_code sb sc func /\
    sc.cs_current_bb = sb.cs_current_bb /\
    sc.cs_current_insts = sb.cs_current_insts ++ code /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) code /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    run_inst_seq_mem_ok code s /\
    inst_seq_ptr D lo ctx func PG G tn code s G' tn' /\
    run_inst_seq code s = OK t ==>
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
      (OK (t with vs_inst_idx := LENGTH sc.cs_current_insts), G', tn')
Proof
  rpt gen_tac >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def] >> fs[IS_PREFIX_APPEND] >>
     qexists_tac `l` >> simp[DROP_APPEND, DROP_LENGTH_NIL] >>
     `LENGTH sb.cs_current_insts - (LENGTH code + LENGTH sb.cs_current_insts) = 0`
       by decide_tac >> simp[]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    fs[FILTER_EQ_NIL, EVERY_MEM] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    fs[EVERY_MEM] >>
  qspecl_then [`code`, `s`, `t`, `G`, `tn`, `G'`, `tn'`, `ctx`, `func`, `bb`]
    mp_tac run_inst_seq_gas_origin_ptr_path >>
  simp[]
QED

Theorem emitted_alloca_history:
  !code sb sc s t.
    fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
    sc.cs_current_bb = sb.cs_current_bb /\
    sc.cs_current_insts = sb.cs_current_insts ++ code /\
    EVERY (\i. ~is_terminator i.inst_opcode) code /\
    alloca_history func s /\ alloca_inv s /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    run_inst_seq code s = OK t ==>
    alloca_history func (t with vs_inst_idx := LENGTH sc.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
             DROP s.vs_inst_idx bb.bb_instructions = code ++ rest` by
    (fs[fn_has_code_def] >> fs[IS_PREFIX_APPEND] >>
     qexists_tac `l` >> simp[DROP_APPEND, DROP_LENGTH_NIL] >>
     `LENGTH sb.cs_current_insts - (LENGTH code + LENGTH sb.cs_current_insts) = 0`
       by decide_tac >> simp[]) >>
  qspecl_then [`func`, `bb`, `s`, `code`, `rest`, `t`] mp_tac
    alloca_history_run_inst_seq >>
  simp[]
QED

Theorem ghost_kept_at_clean_suffix:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  rw[ghost_kept_at_def, SUBSET_DEF] >> metis_tac[]
QED
