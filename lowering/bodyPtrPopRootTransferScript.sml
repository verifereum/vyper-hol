Theory bodyPtrPopRootTransfer
Ancestors
  bodyPtrPopRootEntry exprSimPop appendStorageGhostPtr stmtAppendStorageRunPtr
  typedCopyLoopHeaderPtr exprSendPtr fragGasSeqPtr ptrSafeRun ptrDiscipline
  venomExecSemantics venomInstProofs venomInst venomState
  codegenRel contextCodegenRel finite_map pred_set

(* The literal root load cannot consume a pointer-valued operand.  Its
   result is a clean word even for an arbitrary initial provenance map. *)
Theorem pop_root_header_transfer:
  ~ctx_has_dalloca ctx /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]] s
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `mk_inst id opc ops outs` >>
  qabbrev_tac `u = update_var out (if tr then tload slot s else sload slot s) s` >>
  `step_inst_base (mk_inst id opc ops outs) s = OK u` by
    (map_every qunabbrev_tac [`opc`,`ops`,`outs`,`u`] >>
     Cases_on `tr` >> simp[step_inst_base_def, mk_inst_def, eval_operand_def,
       eval_operands_def, update_var_def, exec_read1_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops outs) s` by
    (irule append_scalar_inst_check >> simp[Abbr `opc`, Abbr `ops`,
      op_taint_def, Abbr `u`, update_var_def] >> Cases_on `tr` >> simp[]) >>
  simp[inst_seq_ptr_def] >>
  conj_tac
  >- (simp[Abbr `opc`, Abbr `ops`, Abbr `outs`, step_prov_def,
       out_prov_def, set_prov_def, mk_inst_def] >> Cases_on `tr` >> simp[]) >>
  sym_tac >> simp[Abbr `opc`, Abbr `ops`, Abbr `outs`] >>
  irule scalar_storage_load_taint >>
  simp[eval_operand_def, Abbr `u`, update_var_def]
QED

Theorem pop_root_iszero_transfer:
  ~ctx_has_dalloca ctx /\ op_taint tn op = {} /\
  eval_operand op s = SOME w ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ISZERO [op] [out]) s /\
  step_inst_base (mk_inst id ISZERO [op] [out]) s =
    OK (update_var out (bool_to_word (w = 0w)) s) /\
  step_prov PG G (mk_inst id ISZERO [op] [out])
    (update_var out (bool_to_word (w = 0w)) s) = DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id ISZERO [op] [out]) s
    (update_var out (bool_to_word (w = 0w)) s) tn =
      tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ISZERO [op] [out]) s =
    OK (update_var out (bool_to_word (w = 0w)) s)` by
    simp[step_inst_base_def, exec_pure1_def, mk_inst_def, eval_operands_def] >>
  conj_tac
  >- (irule typed_copy_loop_test_check >> simp[update_var_def] >> metis_tac[]) >>
  simp[] >> irule typed_copy_loop_arith_ghost >> simp[update_var_def]
QED

(* The guard stops on either branch with the same ghost. No inequality
   between the temporary names is needed for this short slice. *)
Theorem pop_root_guard_transfer:
  ~ctx_has_dalloca ctx /\ op_taint tn (Var x0) = {} /\
  lookup_var x0 s = SOME w ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ISZERO [Var x0] [x1];
     mk_inst (id+1) ISZERO [Var x1] [x2];
     mk_inst (id+2) ASSERT [Var x2] []] s
    (DRESTRICT (DRESTRICT G (COMPL {x1})) (COMPL {x2}))
    (tn with t_var := tn.t_var |+ (x1,{}) |+ (x2,{}))
Proof
  strip_tac >>
  `eval_operand (Var x0) s = SOME w` by simp[eval_operand_def] >>
  drule_all pop_root_iszero_transfer >> strip_tac >> fs[] >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr D 0 ctx fn PG G1 tn1 _ u1 _ _` >>
  `op_taint tn1 (Var x1) = {} /\
   eval_operand (Var x1) u1 = SOME (bool_to_word (w = 0w))` by
    simp[Abbr `tn1`, Abbr `u1`, op_taint_def,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  drule_all pop_root_iszero_transfer >> strip_tac >> fs[] >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr D 0 ctx fn PG G2 tn2 _ u2 _ _` >>
  `op_taint tn2 (Var x2) = {} /\
   eval_operand (Var x2) u2 = SOME (bool_to_word (bool_to_word (w = 0w) = 0w))` by
    simp[Abbr `tn2`, Abbr `u2`, op_taint_def,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[Once inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_assert >> metis_tac[]) >>
  simp[pop_step_ASSERT, lookup_var_def, Abbr `u2`, update_var_def,
       FLOOKUP_UPDATE] >>
  Cases_on `w = 0w` >>
  simp[bool_to_word_def, inst_seq_ptr_def, scalar_void_prov,
       scalar_assert_taint, Abbr `tn2`, Abbr `tn1`, Abbr `G2`, Abbr `G1`]
QED


(* Schematic final ghosts and instruction ids keep matching independent of
   the simplifier's normal form for nested map deletions and updates. *)
Theorem pop_root_guard_transfer_at:
  ~ctx_has_dalloca ctx /\ op_taint tn (Var x0) = {} /\
  lookup_var x0 s = SOME w /\ id1 = id+1 /\ id2 = id+2 /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {x1})) (COMPL {x2}) /\
  tnf = (tn with t_var := tn.t_var |+ (x1,{}) |+ (x2,{})) ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ISZERO [Var x0] [x1];
     mk_inst id1 ISZERO [Var x1] [x2];
     mk_inst id2 ASSERT [Var x2] []] s Gf tnf
Proof
  strip_tac >> gvs[] >> irule (SRULE [] pop_root_guard_transfer) >> metis_tac[]
QED

Theorem pop_root_prefix_transfer:
  ~ctx_has_dalloca ctx /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  Gf = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x0})) (COMPL {x1})) (COMPL {x2}) /\
  tnf = (tn with t_var := tn.t_var |+ (x0,{}) |+ (x1,{}) |+ (x2,{})) ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] []] s Gf tnf
Proof
  strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0]] s
    (DRESTRICT G (COMPL {x0})) (tn with t_var := tn.t_var |+ (x0,{}))` by
    (irule pop_root_header_transfer >> simp[]) >>
  pop_assum mp_tac >> simp[Once inst_seq_ptr_def] >>
  Cases_on `tr` >>
  simp[step_inst_base_def, exec_read1_def, mk_inst_def,
       eval_operands_def, eval_operand_def] >> strip_tac >>
  simp[Once inst_seq_ptr_def] >>
  simp[step_inst_base_def, exec_read1_def, mk_inst_def,
       eval_operands_def, eval_operand_def] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [] _ _ _`
    (strip_assume_tac o SRULE [inst_seq_ptr_def]) >>
  qpat_x_assum `DRESTRICT _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `(_ with t_var := _) = _` (fn th => rewrite_tac[GSYM th]) >>
  rewrite_tac[GSYM mk_inst_def] >>
  irule pop_root_guard_transfer_at >>
  simp[lookup_var_def, update_var_def, op_taint_def, FLOOKUP_UPDATE] >>
  goal_assum (drule_at Any) >> simp[]
QED
