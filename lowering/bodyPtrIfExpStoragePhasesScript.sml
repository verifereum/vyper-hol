Theory bodyPtrIfExpStoragePhases
Ancestors
  bodyPtrIfExpStorageLoop bodyPtrIfExpMaterializeWord bodyPtrIfExpScalarLoad
  slotCopyExecution stmtAppendStorageRunPtr fragGasSeqPtr exprLoweringProps
  venomExecSemantics venomState venomInst ptrDiscipline finite_map
  typedCopyLoopHeaderPtr bodyPtrDefs bodyPtrIfExpAssignFrame
  instSeqComposePtr ghostPcTransportPtr instIdxIndep fragExec

(* Semantic inputs, rather than supplied per-instruction outcomes, form the
   public phase interface. The runtime cursor is advanced only by the path. *)
Theorem ifexp_copy_read_phase:
  MEM load [SLOAD;TLOAD] /\ ~ctx_has_dalloca ctx /\
  eval_operand src s = SOME p /\ eval_operand counter s = SOME q /\
  op_taint tn src = {} /\ op_taint tn counter = {} ==>
  ?t G' tn'.
    run_inst_seq [mk_inst aid ADD [src;counter] [key];
      mk_inst lid load [Var key] [loaded]] s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst aid ADD [src;counter] [key];
       mk_inst lid load [Var key] [loaded]] s G' tn' /\
    t = update_var loaded (slot_copy_word load s (p+q))
          (update_var key (p+q) s) /\
    op_prov G' (Var loaded) = NONE /\
    op_taint tn' (Var loaded) =
      (if load = SLOAD then key_taint tn.t_stor (p+q)
       else key_taint tn.t_trans (p+q)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> key /\ x <> loaded ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `r = update_var key (p+q) s` >>
  qabbrev_tac `s1 = r with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = slot_copy_word load s (p+q)` >>
  `step_inst_base (mk_inst aid ADD [src;counter] [key]) s = OK r` by
    simp[Abbr `r`, step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  `step_inst_base (mk_inst lid load [Var key] [loaded]) s1 =
     OK (update_var loaded v s1)` by
    (gvs[] >> simp[Abbr `s1`, Abbr `r`, Abbr `v`, step_inst_base_def,
      mk_inst_def, exec_read1_def, eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE, slot_copy_word_def, sload_def,
      tload_def, contract_storage_def, contract_transient_def]) >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst aid ADD [src;counter] [key]) r` >>
  qabbrev_tac `tn1 = step_taint (mk_inst aid ADD [src;counter] [key]) s r tn` >>
  qexistsl_tac [`update_var loaded v r`,
    `step_prov PG G1 (mk_inst lid load [Var key] [loaded]) (update_var loaded v s1)`,
    `step_taint (mk_inst lid load [Var key] [loaded]) s1 (update_var loaded v s1) tn1`] >>
  reverse conj_tac
  >- (conj_tac
      >- (irule ifexp_copy_read_checks >> simp[Abbr `G1`, Abbr `tn1`] >>
          qexists_tac `p+q` >> simp[Abbr `r`, Abbr `s1`]) >>
      simp[Abbr `r`, Abbr `v`] >>
      `tn1 = tn with t_var := tn.t_var |+ (key,{})` by
        (simp[Abbr `tn1`] >> irule scalar_add_taint >> simp[update_var_def]) >>
      `eval_operand (Var key) s1 = SOME (p+q)` by
        simp[Abbr `s1`, eval_operand_def, lookup_var_def,
             update_var_def, FLOOKUP_UPDATE] >>
      `step_taint (mk_inst lid load [Var key] [loaded]) s1
         (update_var loaded (slot_copy_word load s (p+q)) s1) tn1 =
         tn1 with t_var := tn1.t_var |+ (loaded,
           if load = SLOAD then key_taint tn1.t_stor (p+q)
           else if load = TLOAD then key_taint tn1.t_trans (p+q) else {})` by
        (irule ifexp_materialize_load_taint >> simp[] >> fs[]) >>
      simp[op_prov_def, step_prov_def, out_prov_def,
        set_prov_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE,
        FLOOKUP_DRESTRICT, lookup_var_def, update_var_def] >>
      rpt strip_tac >> simp[Abbr `G1`, scalar_step_old_prov] >>
      gvs[FLOOKUP_DRESTRICT, scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE]) >>
  gvs[] >> simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
    exec_read1_def, Abbr `r`, Abbr `v`, slot_copy_word_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    sload_def, tload_def, contract_storage_def, contract_transient_def]
QED

Theorem ifexp_copy_address_phase:
  ~ctx_has_dalloca ctx /\
  eval_operand counter s = SOME q /\ eval_operand bop s = SOME d /\
  op_taint tn counter = {} /\ op_taint tn bop = {} /\
  op_prov G bop = SOME (b,n) /\ bop <> Var scaled /\
  b <= w2n (d+q*32w) /\ w2n (d+q*32w) + sz <= b+n ==>
  ?t G' tn'.
    run_inst_seq [mk_inst mid MUL [counter;Lit 32w] [scaled];
      mk_inst aid ADD [bop;Var scaled] [addr]] s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst mid MUL [counter;Lit 32w] [scaled];
       mk_inst aid ADD [bop;Var scaled] [addr]] s G' tn' /\
    t = update_var addr (d+q*32w) (update_var scaled (q*32w) s) /\
    ptr_covers G' tn' addr t sz /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> scaled /\ x <> addr ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `r = update_var scaled (q*32w) s` >>
  qabbrev_tac `s1 = r with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base (mk_inst mid MUL [counter;Lit 32w] [scaled]) s = OK r` by
    simp[Abbr `r`, step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def] >>
  `step_inst_base (mk_inst aid ADD [bop;Var scaled] [addr]) s1 =
     OK (update_var addr (d+q*32w) s1)` by
    simp[Abbr `s1`, Abbr `r`, step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE, slot_copy_operand_update] >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst mid MUL [counter;Lit 32w] [scaled]) r` >>
  qabbrev_tac `tn1 = step_taint (mk_inst mid MUL [counter;Lit 32w] [scaled]) s r tn` >>
  qexistsl_tac [`update_var addr (d+q*32w) r`,
    `step_prov PG G1 (mk_inst aid ADD [bop;Var scaled] [addr]) (update_var addr (d+q*32w) s1)`,
    `step_taint (mk_inst aid ADD [bop;Var scaled] [addr]) s1 (update_var addr (d+q*32w) s1) tn1`] >>
  reverse conj_tac
  >- (conj_tac
      >- (irule ifexp_copy_address_checks >> simp[Abbr `G1`, Abbr `tn1`] >>
          qexists_tac `q*32w` >> simp[Abbr `r`, Abbr `s1`]) >>
      simp[Abbr `r`] >>
      `G1 = DRESTRICT G (COMPL {scaled}) /\
       tn1 = tn with t_var := tn.t_var |+ (scaled,{})` by
        (simp[Abbr `G1`, Abbr `tn1`] >> conj_tac
         >- simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
         irule (cj 2 typed_copy_loop_arith_ghost) >> simp[update_var_def]) >>
      `op_prov G1 bop = SOME (b,n)` by
        (Cases_on `bop` >> gvs[op_prov_def, FLOOKUP_DRESTRICT]) >>
      `step_prov PG G1 (mk_inst aid ADD [bop;Var scaled] [addr])
         (update_var addr (d+q*32w) s1) = G1 |+ (addr,(b,n))` by
        (irule (cj 1 ifexp_dynamic_add_ghost) >> simp[]) >>
      `step_taint (mk_inst aid ADD [bop;Var scaled] [addr]) s1
         (update_var addr (d+q*32w) s1) tn1 =
         tn1 with t_var := tn1.t_var |+ (addr,{})` by
        (irule scalar_add_taint >> simp[update_var_def]) >>
      simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
        FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  simp[run_inst_seq_def] >>
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def, Abbr `r`,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    slot_copy_operand_update]
QED

Theorem ifexp_copy_increment_phase:
  ~ctx_has_dalloca ctx /\ lookup_var ctr s = SOME w /\
  op_taint tn (Var ctr) = {} /\ op_prov G (Var ctr) = NONE ==>
  ?t G' tn'.
    run_inst_seq [mk_inst aid ADD [Var ctr;Lit 1w] [next];
      mk_inst sid ASSIGN [Var next] [ctr]] s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst aid ADD [Var ctr;Lit 1w] [next];
       mk_inst sid ASSIGN [Var next] [ctr]] s G' tn' /\
    t = update_var ctr (w+1w) (update_var next (w+1w) s) /\
    lookup_var ctr t = SOME (w+1w) /\
    op_prov G' (Var ctr) = NONE /\ op_taint tn' (Var ctr) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> next /\ x <> ctr ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `r = update_var next (w+1w) s` >>
  qabbrev_tac `s1 = r with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base (mk_inst aid ADD [Var ctr;Lit 1w] [next]) s = OK r` by
    simp[Abbr `r`, step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def] >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst aid ADD [Var ctr;Lit 1w] [next]) r` >>
  qabbrev_tac `tn1 = step_taint (mk_inst aid ADD [Var ctr;Lit 1w] [next]) s r tn` >>
  qexistsl_tac [`update_var ctr (w+1w) r`,
    `step_prov PG G1 (mk_inst sid ASSIGN [Var next] [ctr]) (update_var ctr (w+1w) s1)`,
    `step_taint (mk_inst sid ASSIGN [Var next] [ctr]) s1 (update_var ctr (w+1w) s1) tn1`] >>
  reverse conj_tac
  >- (conj_tac
      >- (irule ifexp_copy_increment_checks >> simp[Abbr `G1`, Abbr `tn1`] >>
          qexists_tac `w+1w` >> simp[Abbr `r`, Abbr `s1`]) >>
      simp[Abbr `r`] >>
      `G1 = DRESTRICT G (COMPL {next})` by
        simp[Abbr `G1`, step_prov_def, out_prov_def, first_prov_def,
             set_prov_def, mk_inst_def, op_prov_def] >>
      `tn1 = tn with t_var := tn.t_var |+ (next,{})` by
        (simp[Abbr `tn1`] >> irule scalar_add_taint >> simp[update_var_def]) >>
      `eval_operand (Var next) s1 = SOME (w+1w)` by
        simp[Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      `step_taint (mk_inst sid ASSIGN [Var next] [ctr]) s1
         (update_var ctr (w+1w) s1) tn1 =
         tn1 with t_var := tn1.t_var |+ (ctr, op_taint tn1 (Var next))` by
        (irule assign_taint >> simp[]) >>
      simp[assign_result_prov, scalar_step_old_prov, op_prov_def,
        step_prov_def, out_prov_def, first_prov_def, set_prov_def, mk_inst_def,
        op_taint_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, Abbr `r`,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ifexp_copy_store_phase:
  ~ctx_has_dalloca ctx /\ ptr_covers G tn addr s 32 /\
  eval_operand (Var addr) s = SOME d /\ eval_operand value s = SOME w ==>
  ?t tn'.
    run_inst_seq [mk_inst id MSTORE [Var addr;value] []] s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id MSTORE [Var addr;value] []]
      s G tn' /\
    t = mstore (w2n d) w s /\
    tn'.t_mem = (tn.t_mem DIFF {i | w2n d <= i /\ i < w2n d + 32}) UNION
      {w2n d + k | k IN op_taint tn value} /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var addr;value] []) s =
     OK (mstore (w2n d) w s)` by
    simp[step_inst_base_def, mk_inst_def, exec_write2_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MSTORE [Var addr;value] []) s` by
    (irule ifexp_materialize_mstore_check >> simp[]) >>
  qexistsl_tac [`mstore (w2n d) w s`,
    `step_taint (mk_inst id MSTORE [Var addr;value] []) s (mstore (w2n d) w s) tn`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, scalar_void_prov] >>
  conj_tac >- simp[ifexp_materialize_mstore_taint] >>
  simp[ifexp_materialize_mstore_ghost]
QED

(* The uniform append interface is stronger than the phase consumer needs:
   the suffix is checked at the one cursor actually reached by the prefix. *)
Theorem ifexp_inst_seq_ptr_append_at:
  !xs s t G tn G1 tn1 G2 tn2 ys.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn xs s G1 tn1 /\
    inst_seq_ptr D lo ctx fn PG G1 tn1 ys
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH xs) G2 tn2 ==>
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s G2 tn2
Proof
  Induct_on `xs`
  >- (simp[run_inst_seq_def, inst_seq_ptr_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> simp[run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[inst_seq_ptr_def] >>
  first_x_assum irule >>
  qexistsl_tac [`G1`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `tn1`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, arithmeticTheory.ADD_CLAUSES,
       arithmeticTheory.ADD1] >>
  `SUC (LENGTH xs) + s.vs_inst_idx = LENGTH xs + (s.vs_inst_idx + 1)` by decide_tac >>
  metis_tac[]
QED
