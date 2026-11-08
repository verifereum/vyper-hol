Theory bodyPtrIfExpStorageLoop
Ancestors
  slotCopyExecution copyExecution bodyPtrIfExpMaterializeWord
  stmtAppendStorageRunPtr typedCopyLoopHeaderPtr bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  finite_map words fragGasSeqPtr

(* Unlike literal_add_ptr_covers this boundary accepts the computed offset
   operand emitted by the slot-copy loop. The first operand owns the site. *)
Theorem ifexp_dynamic_add_ghost:
  op_prov G bop = SOME site ==>
  step_prov PG G (mk_inst id ADD [bop;off] [out])
    (update_var out w s) = G |+ (out,site) /\
  step_taint (mk_inst id ADD [bop;off] [out]) s
    (update_var out w s) tn = tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >> conj_tac
  >- simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
          mk_inst_def] >>
  irule scalar_add_taint >> simp[update_var_def]
QED

Theorem ifexp_dynamic_add_covers:
  op_prov G bop = SOME (b,n) /\
  b <= w2n w /\ w2n w + sz <= b+n ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [bop;off] [out]) (update_var out w s))
    (step_taint (mk_inst id ADD [bop;off] [out]) s (update_var out w s) tn)
    out (update_var out w s) sz
Proof
  strip_tac >> drule ifexp_dynamic_add_ghost >> strip_tac >>
  simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE]
QED

(* The loaded word must survive the two arithmetic instructions between the
   storage read and MSTORE. Neither temporary is assumed fresh on reentry. *)
Theorem ifexp_copy_address_ghost:
  op_prov G bop = SOME (b,n) /\ bop <> Var scaled /\
  loaded <> scaled /\ loaded <> addr /\
  b <= w2n w /\ w2n w + sz <= b+n /\
  s1 = update_var scaled off s /\
  s2 = update_var addr w s1 /\
  G1 = step_prov PG G (mk_inst mid MUL [counter;Lit 32w] [scaled]) s1 /\
  tn1 = step_taint (mk_inst mid MUL [counter;Lit 32w] [scaled]) s s1 tn /\
  G2 = step_prov PG G1 (mk_inst aid ADD [bop;Var scaled] [addr]) s2 /\
  tn2 = step_taint (mk_inst aid ADD [bop;Var scaled] [addr]) s1 s2 tn1 ==>
  ptr_covers G2 tn2 addr s2 sz /\
  op_taint tn2 (Var loaded) = op_taint tn (Var loaded) /\
  lookup_var loaded s2 = lookup_var loaded s
Proof
  strip_tac >>
  `op_prov G1 bop = SOME (b,n)` by
    (gvs[step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
     Cases_on `bop` >> gvs[op_prov_def, FLOOKUP_DRESTRICT]) >>
  conj_tac
  >- (gvs[] >> irule ifexp_dynamic_add_covers >> simp[]) >>
  conj_tac
  >- (gvs[] >>
      simp[scalar_step_old_taint]) >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ifexp_copy_address_checks:
  ~ctx_has_dalloca ctx /\
  op_taint tn counter = {} /\ op_taint tn bop = {} /\ bop <> Var scaled /\
  step_inst_base (mk_inst mid MUL [counter;Lit 32w] [scaled]) s =
    OK (update_var scaled off s) /\
  s1 = (update_var scaled off s with vs_inst_idx := SUC s.vs_inst_idx) /\
  step_inst_base (mk_inst aid ADD [bop;Var scaled] [addr]) s1 =
    OK (update_var addr w s1) /\
  G1 = step_prov PG G (mk_inst mid MUL [counter;Lit 32w] [scaled])
    (update_var scaled off s) /\
  tn1 = step_taint (mk_inst mid MUL [counter;Lit 32w] [scaled]) s
    (update_var scaled off s) tn ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst mid MUL [counter;Lit 32w] [scaled];
     mk_inst aid ADD [bop;Var scaled] [addr]] s
    (step_prov PG G1 (mk_inst aid ADD [bop;Var scaled] [addr])
      (update_var addr w s1))
    (step_taint (mk_inst aid ADD [bop;Var scaled] [addr]) s1
      (update_var addr w s1) tn1)
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst mid MUL [counter;Lit 32w] [scaled]) s` by
    (irule typed_copy_loop_test_check >> simp[update_var_def] >>
     rpt strip_tac >> gvs[op_taint_def]) >>
  `tn1 = tn with t_var := tn.t_var |+ (scaled,{})` by
    (gvs[] >> irule (cj 2 typed_copy_loop_arith_ghost_clean) >>
     gvs[update_var_def, DISJ_IMP_THM, op_taint_def]) >>
  qpat_x_assum `tn1 = step_taint _ _ _ _` kall_tac >>
  `op_taint tn1 bop = {} /\ op_taint tn1 (Var scaled) = {}` by
    (Cases_on `bop` >> gvs[op_taint_def, FLOOKUP_UPDATE]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1
     (mk_inst aid ADD [bop;Var scaled] [addr]) s1` by
    (irule append_scalar_inst_check >> simp[update_var_def] >> metis_tac[]) >>
  `out_taint tn (mk_inst mid MUL [counter;Lit 32w] [scaled]) s = {}` by
    (simp[ptrDisciplineTheory.out_taint_def, mk_inst_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> gvs[op_taint_def])) >>
  simp[inst_seq_ptr_def] >>
  gvs[typed_copy_loop_arith_ghost, update_var_def]
QED

Theorem ifexp_copy_read_checks:
  MEM load [SLOAD;TLOAD] /\ ~ctx_has_dalloca ctx /\
  op_taint tn src = {} /\ op_taint tn counter = {} /\
  step_inst_base (mk_inst aid ADD [src;counter] [key]) s =
    OK (update_var key a s) /\
  s1 = (update_var key a s with vs_inst_idx := SUC s.vs_inst_idx) /\
  step_inst_base (mk_inst lid load [Var key] [loaded]) s1 =
    OK (update_var loaded w s1) /\
  G1 = step_prov PG G (mk_inst aid ADD [src;counter] [key])
    (update_var key a s) /\
  tn1 = step_taint (mk_inst aid ADD [src;counter] [key]) s
    (update_var key a s) tn ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst aid ADD [src;counter] [key];
     mk_inst lid load [Var key] [loaded]] s
    (step_prov PG G1 (mk_inst lid load [Var key] [loaded])
      (update_var loaded w s1))
    (step_taint (mk_inst lid load [Var key] [loaded]) s1
      (update_var loaded w s1) tn1)
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst aid ADD [src;counter] [key]) s` by
    (irule append_scalar_inst_check >> simp[update_var_def] >> metis_tac[]) >>
  `step_taint (mk_inst aid ADD [src;counter] [key]) s
     (update_var key a s) tn = tn with t_var := tn.t_var |+ (key,{})` by
    (irule scalar_add_taint >> simp[update_var_def]) >>
  `op_taint tn1 (Var key) = {}` by
    (simp[] >> gvs[op_taint_def, FLOOKUP_UPDATE]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1
     (mk_inst lid load [Var key] [loaded]) s1` by
    (irule bodyPtrIfExpScalarLoadTheory.ifexp_scalar_load_check >>
     simp[] >> conj_tac >- (qexists_tac `w` >> simp[]) >> fs[]) >>
  simp[inst_seq_ptr_def] >> gvs[]
QED

Theorem ifexp_copy_assign_check:
  ~ctx_has_dalloca ctx /\ eval_operand arg s = SOME w ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ASSIGN [arg] [out]) s
Proof
  strip_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def, allocas_from_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure1_def, update_var_def]
QED

Theorem ifexp_copy_increment_checks:
  ~ctx_has_dalloca ctx /\ op_taint tn (Var ctr) = {} /\
  step_inst_base (mk_inst aid ADD [Var ctr;Lit 1w] [next]) s =
    OK (update_var next w s) /\
  s1 = (update_var next w s with vs_inst_idx := SUC s.vs_inst_idx) /\
  G1 = step_prov PG G (mk_inst aid ADD [Var ctr;Lit 1w] [next])
    (update_var next w s) /\
  tn1 = step_taint (mk_inst aid ADD [Var ctr;Lit 1w] [next]) s
    (update_var next w s) tn ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst aid ADD [Var ctr;Lit 1w] [next];
     mk_inst sid ASSIGN [Var next] [ctr]] s
    (step_prov PG G1 (mk_inst sid ASSIGN [Var next] [ctr])
      (update_var ctr w s1))
    (step_taint (mk_inst sid ASSIGN [Var next] [ctr]) s1
      (update_var ctr w s1) tn1)
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst aid ADD [Var ctr;Lit 1w] [next]) s` by
    (irule append_scalar_inst_check >> simp[update_var_def] >>
     rpt strip_tac >> gvs[op_taint_def]) >>
  `eval_operand (Var next) s1 = SOME w` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1
     (mk_inst sid ASSIGN [Var next] [ctr]) s1` by
    (irule ifexp_copy_assign_check >> simp[] >> metis_tac[]) >>
  `step_inst_base (mk_inst sid ASSIGN [Var next] [ctr]) s1 =
     OK (update_var ctr w s1)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  simp[inst_seq_ptr_def] >> gvs[]
QED
