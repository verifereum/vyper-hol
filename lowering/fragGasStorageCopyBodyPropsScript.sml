(* The straight-line body of a counted storage or transient copy. *)
Theory fragGasStorageCopyBodyProps
Ancestors
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy bodyStorageCopyMemory
  fragGasSeqPtrContext ptrDiscipline fragExecMem fragExec
  contextCodegenRel venomState venomInst venomExecSemantics
  venomExecProofs arithmetic words list

Theorem storage_copy_body_ptr_run:
  (loc = LocStorage \/ loc = LocTransient) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  code =
      [mk_inst id ADD [src;Var cv] [sv];
       mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
       mk_inst (id+3) ADD [Var dst;Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv;Var vv] [];
       mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]] ==>
  !func PG D. ?r Gf tnf.
    run_inst_seq code s = OK r /\
    inst_seq_ptr D 0 ctx func PG G tn code s Gf tnf /\
    run_inst_seq_mem_ok code s /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code /\
    toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 (k+1) Gf tnf r /\
    r.vs_halted = s.vs_halted /\ r.vs_current_bb = s.vs_current_bb /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp r)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  drule toplevel_copy_inv_source >> strip_tac >>
  drule toplevel_copy_inv_destination >> strip_tac >>
  drule toplevel_copy_inv_counter_value >> strip_tac >>
  drule toplevel_copy_inv_bounds >> strip_tac >>
  `eval_operand (Var dst) s = SOME (n2w b) /\
   eval_operand (Var cv) s = SOME (n2w k)` by simp[eval_operand_def] >>
  qspecl_then [`if loc = LocStorage then SLOAD else TLOAD`, `src`, `Var dst`,
    `a`, `n2w b`, `cv`, `sv`, `vv`, `mv`, `dv`, `nv`, `id`, `s`, `n2w k`]
    mp_tac storage_copy_body_run >>
  (impl_tac >- (Cases_on `loc = LocStorage` >> gvs[MEM] >> metis_tac[])) >>
  disch_then (qx_choose_then `r` strip_assume_tac) >>
  `run_inst_seq code s = OK r` by
    (qpat_assum `code = _` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  drule_all toplevel_copy_body_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_alloca_op i.inst_opcode /\ i.inst_opcode <> SETFMP /\
      i.inst_opcode <> DALLOCA) code` by
    (qpat_x_assum `code = _` SUBST1_TAC >>
     Cases_on `loc = LocStorage` >> simp[mk_inst_def, is_terminator_def, is_alloca_op_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
    metis_tac[run_inst_seq_allocas_below_fmp] >>
  `run_inst_seq_mem_ok code s` by
    (qpat_x_assum `code = _` SUBST1_TAC >>
     irule body_storage_iteration_mem_ok >> rpt conj_tac
     >- (rpt strip_tac >> gvs[] >> metis_tac[])
     >- gvs[]
     >- (qexistsl_tac [`b`, `k`] >> gvs[eval_operand_def, dimword_def]) >>
     gvs[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code` by
    (qpat_x_assum `code = _` SUBST1_TAC >>
     Cases_on `loc = LocStorage` >> simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`r`, `Gf`, `tnf`] >> simp[]
QED
