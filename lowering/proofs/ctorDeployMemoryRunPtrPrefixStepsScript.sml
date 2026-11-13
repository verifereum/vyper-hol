(* Local instruction boundaries for the constructor prefix. *)
Theory ctorDeployMemoryRunPtrPrefixSteps
Ancestors
  venomExecProofs
  exprSimUnwrap slotCopyExecution
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst memLocDefs codegenRel contextCodegenRel




Theorem prefix_alloca_output_taint:
  !aid size x s t tn.
    op_taint (step_taint (mk_inst aid ALLOCA [Lit size] [x]) s t tn)
      (Var x) = {}
Proof
  simp[op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, eval_operand_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem prefix_alloca_inst_ok:
  !aid size x s lo ctx fn G tn D fuel.
    allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D lo fuel ctx fn G tn
      (mk_inst aid ALLOCA [Lit size] [x]) s
Proof
  simp[ptr_inst_ok_def, mk_inst_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       op_taint_def, step_inst_non_invoke, step_inst_base_def,
       exec_alloca_def] >>
  rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid` >> gvs[] >>
  PairCases_on `x'` >> gvs[update_var_def]
QED

Theorem prefix_alloca_ghost_step:
  !aid size x s ctx PG G tn fuel.
    FLOOKUP s.vs_allocas aid = NONE ==>
    let inst = mk_inst aid ALLOCA [Lit size] [x];
        t = update_var x (n2w s.vs_alloca_next)
          (s with <| vs_allocas := s.vs_allocas |+
                        (aid, (s.vs_alloca_next, w2n size));
                     vs_alloca_next := s.vs_alloca_next + w2n size |>)
    in ghost_step fuel ctx PG G tn inst s =
         (G |+ (x, (s.vs_alloca_next, w2n size)),
          step_taint inst s t tn)
Proof
  rpt strip_tac >> simp[] >>
  simp[ghost_step_def, mk_inst_def, step_inst_non_invoke,
       step_inst_base_def, exec_alloca_def, eval_operand_def,
       step_prov_def, set_prov_def, out_prov_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem prefix_alloca_ptr_step:
  !aid size x s lo ctx fn PG G tn D fuel.
    allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
    ptr_safe_step D lo fuel ctx fn PG G tn
      (mk_inst aid ALLOCA [Lit size] [x]) s
Proof
  rpt strip_tac >>
  simp[ptr_safe_step_def, prefix_alloca_inst_ok, mk_inst_def]
QED



Theorem prefix_dload_output_taint:
  !iid off x s t tn.
    op_taint (step_taint (mk_inst iid DLOAD [off] [x]) s t tn)
      (Var x) = {}
Proof
  simp[op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `eval_operand off s` >> simp[]
QED


Theorem prefix_dload_ptr_step:
  !iid off x s lo ctx fn PG G tn D fuel.
    op_taint tn off = {} /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    ptr_safe_step D lo fuel ctx fn PG G tn
      (mk_inst iid DLOAD [off] [x]) s
Proof
  simp[ptr_safe_step_def, ptr_inst_ok_def, mk_inst_def, access_ok_def,
       taint_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, step_inst_non_invoke,
       step_inst_base_def, exec_read1_def] >>
  rpt strip_tac >> Cases_on `eval_operand off s` >> gvs[update_var_def]
QED

Theorem prefix_assert_ptr_step:
  !iid cond s lo ctx fn PG G tn D fuel.
    op_taint tn cond = {} /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    ptr_safe_step D lo fuel ctx fn PG G tn
      (mk_inst iid ASSERT [cond] []) s
Proof
  simp[ptr_safe_step_def, ptr_inst_ok_def, mk_inst_def, access_ok_def,
       taint_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, step_inst_non_invoke,
       step_inst_base_def] >>
  rpt strip_tac >> Cases_on `eval_operand cond s` >> gvs[] >>
  Cases_on `x = 0w` >> gvs[]
QED


Theorem prefix_dload_ghost_step:
  !iid off x s w ctx PG G tn fuel.
    eval_operand off s = SOME w ==>
    let inst = mk_inst iid DLOAD [off] [x];
        t = update_var x
          (word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w))) s
    in ghost_step fuel ctx PG G tn inst s =
         (DRESTRICT G (COMPL {x}), step_taint inst s t tn)
Proof
  rpt strip_tac >> simp[] >>
  simp[ghost_step_def, step_inst_non_invoke, exprSimUnwrapTheory.step_DLOAD,
       mk_inst_def, step_prov_def, set_prov_def, out_prov_def,
       step_inst_base_def, exec_read1_def]
QED

Theorem prefix_assert_ghost_step:
  !iid cond s w ctx PG G tn fuel.
    eval_operand cond s = SOME w ==>
    ghost_step fuel ctx PG G tn (mk_inst iid ASSERT [cond] []) s = (G, tn)
Proof
  rpt strip_tac >>
  simp[ghost_step_def, step_inst_non_invoke, (REWRITE_RULE [GSYM venomInstTheory.mk_inst_def] venomExecProofsTheory.step_assert_behavior), mk_inst_def,
       step_inst_base_def] >>
  Cases_on `w = 0w` >> simp[] >>
  simp[step_prov_def, set_prov_def, step_taint_def, mem_taint_def,
       set_var_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
       finite_mapTheory.DRESTRICT_UNIV, new_site_bytes_def, step_writes_def,
       written_taint_def, range_bytes_def, source_memory_write_ranges_def,
       mk_inst_def, finite_mapTheory.FLOOKUP_DEF] >>
  simp[SF CONJ_ss, taint_component_equality]
QED


(* Clean taint alone does not license comparisons of provenance-bearing variables. *)

Theorem prefix_compare_access_ok:
  !opc iid a b x lo G fn s.
    opc IN {LT; GT; EQ} /\ op_prov G a = NONE /\ op_prov G b = NONE ==>
    access_ok lo G fn (mk_inst iid opc [a;b] [x]) s
Proof
  simp[] >> rpt strip_tac >> gvs[] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[op_prov_def, access_ok_def, mk_inst_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def,
      finite_mapTheory.FLOOKUP_DEF]
QED

Theorem prefix_lt_dispatch[local]:
  step_inst_base (mk_inst iid LT [a;b] [x]) s =
  exec_pure2 (\u v. bool_to_word (w2n u < w2n v))
    (mk_inst iid LT [a;b] [x]) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_gt_dispatch[local]:
  step_inst_base (mk_inst iid GT [a;b] [x]) s =
  exec_pure2 (\u v. bool_to_word (w2n u > w2n v))
    (mk_inst iid GT [a;b] [x]) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_eq_dispatch[local]:
  step_inst_base (mk_inst iid EQ [a;b] [x]) s =
  exec_pure2 (\u v. bool_to_word (u = v))
    (mk_inst iid EQ [a;b] [x]) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_iszero_dispatch[local]:
  step_inst_base (mk_inst iid ISZERO [a] [x]) s =
  exec_pure1 (\u. bool_to_word (u = 0w))
    (mk_inst iid ISZERO [a] [x]) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_compare_ptr_step:
  !opc iid a b x s lo ctx fn PG G tn D fuel.
    opc IN {LT; GT; EQ} /\ op_prov G a = NONE /\ op_prov G b = NONE /\
    op_taint tn a = {} /\ op_taint tn b = {} /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    ptr_safe_step D lo fuel ctx fn PG G tn
      (mk_inst iid opc [a;b] [x]) s
Proof
  rpt strip_tac >>
  `access_ok lo G fn (mk_inst iid opc [a;b] [x]) s` by
    (irule prefix_compare_access_ok >> simp[]) >>
  simp[ptr_safe_step_def, ptr_inst_ok_def] >> gvs[] >>
  simp[step_inst_non_invoke, prefix_lt_dispatch, prefix_gt_dispatch,
       prefix_eq_dispatch, mk_inst_def] >>
  simp[taint_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  (conj_tac >- metis_tac[]) >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand b s` >>
  simp[exec_pure2_def, mk_inst_def, update_var_def]
QED
Theorem prefix_iszero_ptr_step:
  !iid a x s lo ctx fn PG G tn D fuel.
    op_taint tn a = {} /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid ISZERO [a] [x]) s
Proof
  rpt strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
       step_inst_non_invoke, prefix_iszero_dispatch, mk_inst_def,
       taint_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  Cases_on `eval_operand a s` >> simp[exec_pure1_def, mk_inst_def, update_var_def]
QED



Theorem prefix_guard_prov:
  !opc iid ops x PG G t.
    opc IN {LT; GT; EQ; ISZERO} ==>
    step_prov PG G (mk_inst iid opc ops [x]) t = DRESTRICT G (COMPL {x})
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem prefix_guard_output_taint:
  !opc iid ops x s t tn.
    opc IN {LT; GT; EQ; ISZERO} /\ (LENGTH ops = 1 \/ LENGTH ops = 2) ==>
    op_taint (step_taint (mk_inst iid opc ops [x]) s t tn) (Var x) = {}
Proof
  rpt strip_tac >> gvs[] >>
  Cases_on `ops` >> gvs[] >>
  simp[op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `t'` >> gvs[]
QED


Theorem prefix_guard_taint_other:
  !opc iid ops x s t tn y.
    y <> x ==>
    op_taint (step_taint (mk_inst iid opc ops [x]) s t tn) (Var y) =
      op_taint tn (Var y)
Proof
  simp[op_taint_def, step_taint_def, set_var_taint_def, mk_inst_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem prefix_compare_ghost_step:
  !opc iid a b x s t ctx PG G tn fuel.
    opc IN {LT; GT; EQ} /\
    step_inst_base (mk_inst iid opc [a;b] [x]) s = OK t ==>
    ghost_step fuel ctx PG G tn (mk_inst iid opc [a;b] [x]) s =
      (DRESTRICT G (COMPL {x}),
       step_taint (mk_inst iid opc [a;b] [x]) s t tn)
Proof
  rpt strip_tac >>
  simp[ghost_step_def, step_inst_non_invoke, prefix_guard_prov] >>
  gvs[] >> simp[mk_inst_def, step_prov_def, set_prov_def, out_prov_def]
QED

Theorem prefix_iszero_ghost_step:
  !iid a x s t ctx PG G tn fuel.
    step_inst_base (mk_inst iid ISZERO [a] [x]) s = OK t ==>
    ghost_step fuel ctx PG G tn (mk_inst iid ISZERO [a] [x]) s =
      (DRESTRICT G (COMPL {x}),
       step_taint (mk_inst iid ISZERO [a] [x]) s t tn)
Proof
  rpt strip_tac >>
  simp[ghost_step_def, step_inst_non_invoke, prefix_guard_prov, mk_inst_def,
       step_prov_def, set_prov_def, out_prov_def]
QED

Theorem prefix_mstore_dispatch[local]:
  step_inst_base (mk_inst iid MSTORE [addr;value] []) s =
  exec_write2 (\a w s. mstore (w2n a) w s)
    (mk_inst iid MSTORE [addr;value] []) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED



Theorem prefix_mstore_ptr_step:
  !iid dst value s a w b sz lo ctx fn PG G tn D fuel.
    eval_operand (Var dst) s = SOME a /\ eval_operand value s = SOME w /\
    FLOOKUP G dst = SOME (b,sz) /\ b <= w2n a /\ w2n a + 32 <= b + sz /\
    op_taint tn (Var dst) = {} /\ op_taint tn value = {} /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
    ptr_safe_step D lo fuel ctx fn PG G tn
      (mk_inst iid MSTORE [Var dst;value] []) s
Proof
  rpt strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def,
       step_inst_non_invoke, slotCopyExecutionTheory.slot_copy_step_store] >>
  simp[access_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       mem_write_ops_def, mk_inst_def, taint_ok_def,
       REWRITE_RULE[mk_inst_def] prefix_mstore_dispatch, exec_write2_def,
       mstore_def, allocas_from_def] >> metis_tac[]
QED

Theorem prefix_mstore_ghost_step:
  !iid addr value s t fuel ctx PG G tn.
    step_inst fuel ctx (mk_inst iid MSTORE [addr;value] []) s = OK t ==>
    ghost_step fuel ctx PG G tn (mk_inst iid MSTORE [addr;value] []) s =
      (G, step_taint (mk_inst iid MSTORE [addr;value] []) s t tn)
Proof
  rpt strip_tac >>
  simp[ghost_step_def, mk_inst_def, step_prov_def, set_prov_def,
       finite_mapTheory.DRESTRICT_UNIV] >>
  gvs[step_inst_non_invoke, mk_inst_def]
QED

Theorem prefix_mstore_taint_frame:
  !iid addr value s t tn.
    let tn' = step_taint (mk_inst iid MSTORE [addr;value] []) s t tn in
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  simp[step_taint_def, mk_inst_def, set_var_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem prefix_mstore_mem_taint:
  !iid addr value s a w tn.
    eval_operand addr s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} ==>
    (step_taint (mk_inst iid MSTORE [addr;value] []) s
      (mstore (w2n a) w s) tn).t_mem =
      tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}
Proof
  rpt strip_tac >>
  simp[step_taint_def, mem_taint_def, mk_inst_def, new_site_bytes_def,
       mstore_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       range_bytes_def, finite_mapTheory.FLOOKUP_DEF] >>
  simp[SF CONJ_ss]
QED

Theorem prefix_mstore_endpoint:
  !iid addr value s a w fuel ctx.
    eval_operand addr s = SOME a /\ eval_operand value s = SOME w ==>
    step_inst fuel ctx (mk_inst iid MSTORE [addr;value] []) s =
      OK (mstore (w2n a) w s)
Proof
  rpt strip_tac >>
  simp[step_inst_non_invoke, prefix_mstore_dispatch, mk_inst_def,
       exec_write2_def]
QED
