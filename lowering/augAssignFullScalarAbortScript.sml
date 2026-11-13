(* An abort cursor is operational: choose it before the pointer certificate. *)
Theory augAssignFullScalarAbort
Ancestors
  augAssignFullScalar fragGasSeqPtr fragGasSeqAbort fragGasOriginPtrExec
  fragGasOriginPtr fragGasMode fragGasPathMem fragExec fragExecMem
  venomExecSemantics venomInstProofs venomState instIdxIndep
  augAssignPtrScalarRun instSeqPtrLo fragGasFresh freshWrites varsExt
  ptrDiscipline exprLoweringProps list rich_list

Theorem run_inst_seq_abort_origin_ptr_uniform:
  !code s t a ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    run_inst_seq code s = Abort a t ==>
    ?j. !D lo PG G tn G' tn' explicit.
      inst_seq_ptr D lo ctx func PG G tn code s G' tn' ==>
      gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
        (Abort a (t with vs_inst_idx := j), G', tn')
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, run_inst_seq_mem_ok_def]
  >~ [`step_inst_base h s = OK u`]
  >- (`step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`, `a`, `ctx`, `func`, `bb`]
        mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
      qexists_tac `j` >> rpt gen_tac >> strip_tac >>
      gvs[inst_seq_ptr_def] >>
      `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
         (u with vs_inst_idx := SUC s.vs_inst_idx,
          step_prov PG G h u, step_taint h s u tn) []
         (Abort a (t with vs_inst_idx := j), G', tn')` by metis_tac[] >>
      `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG) (s, G, tn) []
         (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
          step_prov PG G h u, step_taint h s u tn)` by
        (drule_all straight_line_origin_ptr_edge >> simp[]) >>
      metis_tac[cj 2 gas_origin_ptr_path_rules, APPEND]) >>
  qexists_tac `t.vs_inst_idx` >> rpt gen_tac >> strip_tac >>
  gvs[inst_seq_ptr_def] >>
  `gas_path_mem ctx func s 0 (Abort a t)` by
    (qspecl_then [`T`, `ctx`, `func`, `s`, `bb`, `h`, `a`, `t`] mp_tac
      gas_marked_path_abort >> simp[gas_marked_path_def]) >>
  `gas_path_ptr D lo ctx func PG G tn s 0 G tn (Abort a t)` by
    (drule_all gas_path_ptr_abort >> simp[]) >>
  irule gas_zero_paths_joint >> simp[exit_result_def]
QED

Theorem scalar_code_origin_ptr_abort:
  !code A s t a G tn ctx func PG explicit bb.
    scalar_code A code /\
    (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq code s = Abort a t ==>
    ?j G' tn'.
      !D lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
        gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
          (Abort a (t with vs_inst_idx := j), G', tn')
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`code`, `A`, `s`] mp_tac scalar_code_memory_checks >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`code`, `s`, `t`, `a`, `ctx`, `func`, `bb`] mp_tac
    run_inst_seq_abort_origin_ptr_uniform >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
                     d_imm := K {}; d_ret := K {}|>` >>
  `?G' tn'. inst_seq_ptr D0 0 ctx func PG G tn code s G' tn'` by
    metis_tac[scalar_code_inst_seq_ptr] >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`j`, `G'`, `tn'`] >> rpt gen_tac >> strip_tac >>
  `inst_seq_ptr D lo ctx func PG G tn code s G' tn'` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D0` >>
     simp[Abbr `D0`]) >>
  metis_tac[]
QED

Theorem straight_fresh_scalar_origin_ptr_abort:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  scalar_code A (emitted_insts sa sb) /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = Abort a t0 ==>
  ?t j G' tn'.
    run_inst_seq (emitted_insts sa sb) s = Abort a t /\ vars_ext t0 t /\
    (!D lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
      gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
        (Abort a (t with vs_inst_idx := j), G', tn'))
Proof
  strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = Abort a t` >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  qspecl_then [`emitted_insts sa sb`, `A`, `s`, `t`, `a`, `G`, `tn`,
              `ctx`, `func`, `PG`, `explicit`, `bb`] mp_tac
    scalar_code_origin_ptr_abort >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`j`, `G'`, `tn'`] >> simp[]
QED
