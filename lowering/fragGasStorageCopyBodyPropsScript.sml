(* The straight-line body of a counted storage or transient copy. *)
Theory fragGasStorageCopyBodyProps
Ancestors
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy bodyStorageCopyMemory
  fragGasCopySeqLiftProps fragGasOriginPtrLoop exprLoweringProps rich_list
  fragGasSeqPtrContext ptrDiscipline memSafeRun unitTransformDefs fragExecMem fragExec
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
    (ctx_has_dalloca ctx ==>
      !pre i post v. code = pre ++ i::post /\
        run_inst_seq pre s = OK v ==> dalloca_no_wrap i v) /\
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
  `(ctx_has_dalloca ctx ==>
     !pre i post v. code = pre ++ i::post /\
       run_inst_seq pre s = OK v ==> dalloca_no_wrap i v)` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `code = pre ++ i::post` SUBST_ALL_TAC >> fs[EVERY_APPEND]) >>
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
  qexistsl_tac [`r`, `Gf`, `tnf`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The counted path through the body and its jump back to the header. *)
Theorem storage_copy_body_origin_path:
  (loc = LocStorage \/ loc = LocTransient) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME
    <|bb_label := s.vs_current_bb; bb_instructions :=
      [mk_inst id ADD [src;Var cv] [sv];
       mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
       mk_inst (id+3) ADD [Var dst;Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv;Var vv] [];
       mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv];
       mk_inst (id+7) JMP [Label hdr] []]|> ==>
  !D explicit PG. ?r G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK r,G1,tn1) /\
    (toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 (k+1) G1 tn1 r /\
     allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r)) /\
    ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0 /\
    ?code u t bb.
      lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
      EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
      EVERY (\i. id <= i.inst_id /\ i.inst_id < id+7) code /\
      run_inst_seq code s = OK u /\
      t = u with vs_inst_idx := s.vs_inst_idx + LENGTH code /\
      t.vs_current_bb = s.vs_current_bb /\
      get_instruction bb t.vs_inst_idx = SOME (mk_inst (id+7) JMP [Label hdr] []) /\
      r = jump_to hdr t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  qabbrev_tac `code =
      [mk_inst id ADD [src;Var cv] [sv];
       mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
       mk_inst (id+3) ADD [Var dst;Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv;Var vv] [];
       mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]]` >>
  RULE_ASSUM_TAC (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all storage_copy_body_ptr_run >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  qabbrev_tac `bb = <|bb_label := s.vs_current_bb;
                       bb_instructions := code ++ [mk_inst (id+7) JMP [Label hdr] []]|>` >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by
    (simp[Abbr `bb`] >> fs[]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by simp[Abbr `bb`] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (r with vs_inst_idx := s.vs_inst_idx + LENGTH code),Gf,tnf) /\
   allocas_from lo r` by
    (irule run_inst_seq_origin_ptr_lift >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexists_tac `bb` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `t = r with vs_inst_idx := s.vs_inst_idx + LENGTH code` >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 7 /\
   allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (simp[Abbr `t`] >> gvs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `get_instruction bb t.vs_inst_idx = SOME (mk_inst (id+7) JMP [Label hdr] [])` by
    (simp[Abbr `bb`, get_instruction_def] >> fs[]) >>
  qexistsl_tac [`jump_to hdr t`, `Gf`, `tnf`] >>
  conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gf`, `t`, `tnf`] >>
      simp[] >>
      irule (Q.INST [`bb` |-> `bb`, `iid` |-> `id+7`] jmp_origin_ptr_path) >>
      simp[] >> qexists_tac `id` >> fs[get_instruction_def]) >>
  conj_tac
  >- (gvs[Abbr `t`, jump_to_def, allocas_from_def, allocas_below_fmp_def] >>
      metis_tac[]) >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac >- simp[jump_to_def] >>
  qexistsl_tac [`code`, `r`, `t`, `bb`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    fs[EVERY_MEM] >>
  `EVERY (\i. id <= i.inst_id /\ i.inst_id < id+7) code` by
    (qpat_x_assum `code = _` SUBST1_TAC >>
     Cases_on `loc = LocStorage` >> simp[mk_inst_def] >> decide_tac) >>
  asm_rewrite_tac[] >> simp[Abbr `t`]
QED
