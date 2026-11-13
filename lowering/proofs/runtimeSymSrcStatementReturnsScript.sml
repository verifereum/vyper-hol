Theory runtimeSymSrcStatementReturns
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission stmtLowering compileEnv
  context venomInst stackPlanTypes list supportedStmts supportedStmtTraverse exprLowering

Theorem runtime_sym_load_tuple_elements:
  !tys ce base off s ops s'. ~is_label_operand base /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_load_tuple_elements ce base tys off s = (ops,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\op. ~is_label_operand op) ops
Proof
  Induct >> simp[compile_load_tuple_elements_def, comp_return_def] >>
  rpt gen_tac >> simp[comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[comp_return_def] >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[] >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_mk_dret_operands:
  EVERY (\op. ~is_label_operand op) ordinary /\
  EVERY (\p. ~is_label_operand (FST p) /\ ~is_label_operand (SND p)) dynamic /\
  ~is_label_operand pc /\ mk_dret_operands ordinary dynamic pc = SOME ops ==>
  EVERY (\op. ~is_label_operand op) ops
Proof
  simp[mk_dret_operands_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[is_label_operand_def, EVERY_FLAT, EVERY_MAP, EVERY_MEM] >>
  gvs[EVERY_MEM]
QED

Theorem runtime_sym_return_emit:
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) /\
  emit_inst opc ops [] s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  rpt strip_tac >> irule runtime_sym_emit_inst >>
  goal_assum (drule_at (Pat `emit_inst _ _ _ _ = _`)) >> qexists `s.cs_next_id` >>
  simp[runtime_sym_ordinary_inst]
QED

Theorem runtime_sym_mcopy_guard:
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\ supported s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !ce s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_mcopy_guard ce supported s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >> Cases_on `ce.ce_target CapMcopy` >>
  simp[compile_mcopy_guard_def] >> rpt strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  irule runtime_sym_return_emit >> goal_assum (drule_at (Pat `emit_inst _ _ _ _ = _`)) >> simp[]
QED

(* Optional steps below are guarded by their computation equations or constructor
   shapes. TRY only skips absent deterministic cases; it never wraps proof search. *)

(* External boundary ledger: store_memory, allocation and typed stores are
   owned by C1.1.3.2; ABI encoding by C1.1.3; unlock by C1.1.3.1.
   Literal hypotheses remain visible for discharge at C1.1.7. *)
Theorem runtime_sym_internal_return:
  (!v b dt st s u s'. ~is_label_operand v /\ ~is_label_operand b /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce v b dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !rv pc rc rt st tys rb s u s'.
    (!v. rv = SOME v ==> ~is_label_operand v) /\
    (!b. rb = SOME b ==> ~is_label_operand b) /\ ~is_label_operand pc /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_return ce rv pc rc rt st tys rb s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >>
  rename1 `compile_internal_return ce rv pc n rt st tys rb s = (u,s')` >>
  Cases_on `n > 0` >>
  Cases_on `rv` >> Cases_on `rb` >> Cases_on `tys = []` >>
  simp[compile_internal_return_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
  TRY (qpat_assum `compile_load_tuple_elements _ _ _ _ _ = _` kall_tac >>
       drule_all runtime_sym_load_tuple_elements >> strip_tac) >>
  TRY (qpat_assum `compile_store_memory _ _ _ _ _ _ = _` kall_tac >>
       first_assum drule_all >> strip_tac) >>
  irule runtime_sym_return_emit >> goal_assum (drule_at (Pat `emit_inst _ _ _ _ = _`)) >> simp[]
QED

Theorem runtime_sym_return_unlock:
  (!k t v s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_nonreentrant_unlock k t v s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !ce s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_return_unlock ce s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >>
  simp[compile_return_unlock_def] >> rpt (pairarg_tac >> simp[]) >>
  rename1 `if nr then _ else _` >> Cases_on `nr` >> simp[comp_return_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_external_return:
  (!k t v s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_nonreentrant_unlock k t v s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !rv prim raw info sz nr key trans view s u s'.
    (!v. rv = SOME v ==> ~is_label_operand v) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_external_return rv prim raw info sz nr key trans view s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "unlock")
    (CONJUNCTS_THEN2 (mk_asm "alloc") (mk_asm "abi"))) >>
  rpt gen_tac >> Cases_on `rv` >> Cases_on `nr` >>
  Cases_on `raw` >> Cases_on `prim` >>
  simp[compile_external_return_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
  TRY (qpat_assum `compile_nonreentrant_unlock _ _ _ _ = _` kall_tac >>
       asm "unlock" drule_all >> strip_tac) >>
  TRY (qpat_assum `compile_alloc_buffer _ _ = _` kall_tac >>
       asm "alloc" drule_all >> strip_tac) >>
  TRY (qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
       simp[] >> strip_tac >>
       qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
       simp[is_label_operand_def] >> strip_tac) >>
  TRY (qpat_assum `emit_void _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
       simp[] >> strip_tac) >>
  TRY (qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` kall_tac >>
       asm "abi" drule_all >> strip_tac) >>
  irule runtime_sym_return_emit >>
  goal_assum (drule_at (Pat `emit_inst _ _ _ _ = _`)) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_internal_return_from_env:
  (!v b dt st s u s'. ~is_label_operand v /\ ~is_label_operand b /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce v b dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!k t v s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_nonreentrant_unlock k t v s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !ty st v pc s u s'. runtime_sym_env ce /\
    ~is_label_operand v /\ ~is_label_operand pc /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_return_from_env ce ty st v pc s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "store") (mk_asm "unlock")) >>
  rpt gen_tac >> Cases_on `ce.ce_return_buf` >>
  TRY (rename1 `ce.ce_return_buf = SOME loc` >> Cases_on `loc`) >>
  simp[compile_internal_return_from_env_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> TRY (pairarg_tac >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  TRY (qpat_x_assum `(\(a,b). _) _ = _` mp_tac >>
       pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  `EVERY runtime_sym_inst (state_insts cs')` by
    (asm "unlock" (mp_then Any mp_tac runtime_sym_return_unlock) >>
     disch_then drule_all >> simp[]) >>
  TRY (qpat_assum `emit_op MLOAD _ _ = _`
         (mp_then Any mp_tac runtime_sym_emit_op) >>
       simp[is_label_operand_def] >> strip_tac) >>
  asm "store" (mp_then Any mp_tac runtime_sym_internal_return) >>
  disch_then (drule_at (Pat `compile_internal_return _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> gvs[runtime_sym_env_def, runtime_sym_loc_def]
QED

Theorem runtime_sym_return_none:
  (!k t v s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_nonreentrant_unlock k t v s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Return NONE)
Proof
  disch_then (mk_asm "unlock") >>
  simp[runtime_sym_stmt_contract_def] >> rpt gen_tac >>
  Cases_on `ce.ce_return_pc` >>
  TRY (rename1 `ce.ce_return_pc = SOME loc` >> Cases_on `loc`) >>
  simp[compile_stmt_def] >>
  TRY (Cases_on `ce.ce_ctor_exit_label` >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  TRY (rename1 `if nr then _ else _` >> Cases_on `nr`) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
  TRY (qpat_assum `compile_return_unlock _ _ = _` kall_tac >>
       asm "unlock" (mp_then Any mp_tac runtime_sym_return_unlock) >>
       disch_then drule_all >> strip_tac) >>
  TRY (qpat_assum `compile_nonreentrant_unlock _ _ _ _ = _` kall_tac >>
       asm "unlock" drule_all >> strip_tac) >>
  TRY (qpat_assum `emit_op MLOAD _ _ = _`
         (mp_then Any mp_tac runtime_sym_emit_op) >>
       simp[is_label_operand_def] >> strip_tac) >>
  (all_tac >>~- ([`emit_inst JMP _ _ _ = _`],
       irule runtime_sym_jump >>
       goal_assum (drule_at (Pat `emit_inst _ _ _ _ = _`)) >>
       gvs[runtime_sym_env_def])) >>
  irule runtime_sym_return_emit >>
  goal_assum (drule_at (Pat `emit_inst _ _ _ _ = _`)) >>
  gvs[runtime_sym_env_def, runtime_sym_loc_def]
QED

(* The two return-dispatch contracts below are local family boundaries proved
   above. The final exit join discharges them from the literal primitive
   contracts. unwrap_value is C1.1.3.2; the pointwise expression is C1.1.4. *)
Theorem runtime_sym_return_some:
  runtime_sym_expr_contract tops compile_expr ce ty e /\
  (!v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
    EVERY runtime_sym_inst (state_insts s) /\ unwrap_value ce v s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!dt st v pc s u s'. runtime_sym_env ce /\
    ~is_label_operand v /\ ~is_label_operand pc /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_return_from_env ce dt st v pc s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!rv prim raw info sz nr key trans view s u s'.
    (!v. rv = SOME v ==> ~is_label_operand v) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_external_return rv prim raw info sz nr key trans view s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!b dt v st s u s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory_typed ce b dt v st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!k t v s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_nonreentrant_unlock k t v s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Return (SOME e))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "expr") (CONJUNCTS_THEN2 (mk_asm "unwrap")
    (CONJUNCTS_THEN2 (mk_asm "internal") (CONJUNCTS_THEN2 (mk_asm "external_return")
    (CONJUNCTS_THEN2 (mk_asm "alloc")
    (CONJUNCTS_THEN2 (mk_asm "typed") (mk_asm "unlock"))))))) >>
  simp[runtime_sym_stmt_contract_def] >> rpt strip_tac >>
  fs[supported_stmt_def, supported_stmt_expr_exists_def,
     supportedExprTraverseTheory.supported_expr_exists_def] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `compile_expr ce ty e s = (vv,sa)` >>
  `EVERY runtime_sym_inst (state_insts sa) /\ runtime_sym_value vv` by
    (asm "expr" mp_tac >> simp[runtime_sym_expr_contract_def] >>
     disch_then drule_all >> simp[]) >>
  gvs[] >> rename1 `unwrap_value ce vv sa = (v,sb)` >>
  `EVERY runtime_sym_inst (state_insts sb) /\ ~is_label_operand v` by
    (asm "unwrap" drule_all >> simp[]) >>
  Cases_on `ce.ce_return_pc` >>
  TRY (rename1 `ce.ce_return_pc = SOME loc` >> Cases_on `loc`) >> simp[]
  >>~- ([`ce.ce_return_pc = SOME (PtrVar _ _)`],
          rpt strip_tac >>
          `!loc. ce.ce_return_pc = SOME loc ==> runtime_sym_loc loc` by
            gvs[runtime_sym_env_def] >>
          asm "internal" (drule_at (Pat `compile_internal_return_from_env _ _ _ _ _ _ = _`)) >>
          gvs[runtime_sym_loc_def])
  >>~- ([`ce.ce_return_pc = SOME (MemLoc _ _)`],
          simp[comp_bind_def] >> pairarg_tac >> simp[] >> rpt strip_tac >>
          qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
          simp[is_label_operand_def] >> strip_tac >>
          asm "internal" drule_all >> simp[])
  >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >>
  qmatch_asmsub_abbrev_tac `if norm then _ else _` >>
  `EVERY runtime_sym_inst (state_insts cs') /\ ~is_label_operand ret_op` by
    (Cases_on `norm` >>
     qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
     asm "alloc" drule_all >> strip_tac >> asm "typed" drule_all >> simp[]) >>
  Cases_on `ce.ce_raw_return` >> Cases_on `FST ce.ce_nonreentrant` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
  TRY (qpat_assum `compile_nonreentrant_unlock _ _ _ _ = _` kall_tac >>
       asm "unlock" drule_all >> strip_tac) >>
  TRY (qpat_assum `compile_alloc_buffer _ _ = _`
       (fn eq => asm "alloc" (fn th => mp_then Any mp_tac th eq)) >>
       simp[] >> strip_tac >> asm "typed" drule_all >> strip_tac) >>
  asm "external_return" (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]
QED

