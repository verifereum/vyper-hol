(* Pointer-checked allocation and selector initialization for custom errors. *)
Theory stmtSimCustomErrorPtrTailPrefix
Ancestors
  annAssignPtrSetup annAssignPtrStore
  exprSimPtrLiteralOps actualAllocExec loweringHalt exprLoweringProps
  bodyPtrDefs fragExec fragGasPathPtr emitHelperProps compileEnv emitHelper
  ptrDiscipline venomExecSemantics venomInst venomState
  loweringStateRelDefs finite_map words arithmetic

Theorem custom_error_selector_prefix_run_ptr:
  compile_alloc_buffer (B+32) st = (buf,mid) /\
  emit_void MSTORE [buf.buf_operand; Lit selector] mid = ((),en) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  stmt_state_rel ctx func cenv cx es s /\ B+32 < 2 ** 64 /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  !D PG G tn. ?u d G' tn'.
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = en.cs_current_bb /\
    u.vs_inst_idx = LENGTH en.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME (n2w d) /\
    (!p. buf.buf_operand = Var p ==>
      not_fresh_at en p /\ ptr_covers G' tn' p u (B+32)) /\
    d+B+32 < dimword (:256) /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (d,B+32)
Proof
  strip_tac >> rpt gen_tac >>
  `B+32 < dimword (:256)` by
    (fs[dimword_def] >> decide_tac) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule_all actual_alloc_buffer_site >> strip_tac >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  `?raw. step_inst_base
    (mk_inst st.cs_next_id ALLOCA [Lit (n2w (B+32))] [p]) s = OK raw` by
    (simp[step_inst_base_def, mk_inst_def, eval_operand_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >> simp[] >>
     PairCases_on `x` >> simp[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH st.cs_current_insts) =
    SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w (B+32))] [p])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `p`]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (B+32))] [p])
    (fn_insts func)` by simp[Abbr `p`] >>
  `?G1 tn1 v d.
    gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK v) /\
    v = (raw with vs_inst_idx := SUC s.vs_inst_idx) /\
    G1 = step_prov PG G
      (mk_inst st.cs_next_id ALLOCA [Lit (n2w (B+32))] [p]) raw /\
    tn1 = step_taint
      (mk_inst st.cs_next_id ALLOCA [Lit (n2w (B+32))] [p]) s raw tn /\
    ptr_covers G1 tn1 p v (B+32) /\
    FLOOKUP v.vs_allocas st.cs_next_id = SOME (d,B+32) /\
    d+B+32 < dimword (:256) /\ eval_operand (Var p) v = SOME (n2w d)` by
    (mp_tac (Q.INST [`id` |-> `st.cs_next_id`, `n` |-> `B+32`,
      `u` |-> `raw`] (SPEC_ALL annassign_alloca_path_ptr)) >>
     (impl_tac >- simp[]) >> strip_tac >>
     rpt (irule_at Any EQ_REFL) >> simp[] >> metis_tac[]) >>
  `~v.vs_halted /\ v.vs_current_bb = mid.cs_current_bb /\
    v.vs_inst_idx = LENGTH mid.cs_current_insts` by
    (qpat_x_assum `step_inst_base _ s = OK raw` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >> simp[] >>
     TRY (PairCases_on `x`) >> strip_tac >> gvs[update_var_def]) >>
  `ptr_covers G1 tn1 p v 32` by
    (gvs[ptr_covers_def] >> decide_tac) >>
  `emit_inst MSTORE [Var p; Lit selector] [] mid = ((),en)` by
    gvs[emit_void_def, emit_inst_def, Abbr `p`] >>
  drule_all annassign_emit_instruction_ptr >> strip_tac >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >>
  `lookup_var p v = SOME (n2w d)` by gvs[eval_operand_def] >>
  mp_tac (Q.INST [`s` |-> `v`, `id` |-> `mid.cs_next_id`,
    `G` |-> `G1`, `tn` |-> `tn1`, `value` |-> `Lit selector`,
    `a` |-> `n2w d`, `w` |-> `selector`] (SPEC_ALL annassign_mstore_path_ptr)) >>
  (impl_tac >- (simp[eval_operand_def, op_taint_def] >>
    qpat_x_assum `get_instruction _ (LENGTH mid.cs_current_insts) = _` mp_tac >>
    simp[])) >> strip_tac >>
  `d < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`dst` |-> `p`, `s` |-> `v`, `a` |-> `n2w d`,
    `G` |-> `G1`, `tn` |-> `tn1`, `id` |-> `mid.cs_next_id`,
    `w` |-> `selector`] (SPEC_ALL literal_mstore_ghost)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  `en.cs_current_bb = mid.cs_current_bb /\
    en.cs_next_var = mid.cs_next_var /\
    LENGTH en.cs_current_insts = SUC (LENGTH mid.cs_current_insts)` by
    (qpat_x_assum `emit_inst MSTORE _ _ mid = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `w2n (n2w d : bytes32) = d` by simp[w2n_n2w] >>
  `not_fresh_at en p` by fs[not_fresh_at_def] >>
  `ptr_covers G1
    (tn1 with t_mem := tn1.t_mem DIFF {i | d <= i /\ i < d+32})
    p (mstore d selector v with vs_inst_idx := SUC v.vs_inst_idx) (B+32)` by
    (qpat_x_assum `ptr_covers G1 tn1 p v (B+32)` mp_tac >>
     simp_tac (srw_ss()) [ptr_covers_def, op_taint_def, mstore_def,
       lookup_var_def]) >>
  qexistsl_tac [`mstore d selector v with vs_inst_idx := SUC v.vs_inst_idx`,
    `d`, `G1`, `tn1 with t_mem := tn1.t_mem DIFF {i | d <= i /\ i < d+32}`] >>
  conj_tac
  >- (irule (Q.INST [`n` |-> `0`, `m` |-> `0`]
        (SPEC_ALL gas_path_ptr_then) |> SRULE [ADD_0]) >>
      qexistsl_tac [`G1`, `v`, `tn1`] >> conj_tac
      >- first_assum ACCEPT_TAC >>
      qpat_x_assum `gas_path_ptr D 0 ctx func PG G1 tn1 v 0 _ _ _`
        (fn path_th =>
          qpat_assum `step_prov PG G1 _ _ = G1` (fn prov_th =>
            qpat_assum `step_taint _ v _ tn1 = _` (fn taint_th =>
              qpat_assum `w2n (n2w d : bytes32) = d` (fn d_th =>
                ACCEPT_TAC (REWRITE_RULE [prov_th,taint_th,d_th] path_th)))))) >>
  conj_tac >- (simp_tac (srw_ss()) [mstore_def, LET_THM] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (simp_tac (srw_ss()) [mstore_def, LET_THM] >> metis_tac[]) >>
  conj_tac >- (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `buf.buf_operand = _` SUBST1_TAC >>
      qpat_assum `lookup_var p v = SOME (n2w d)` mp_tac >>
      simp_tac (srw_ss()) [eval_operand_def, lookup_var_def, mstore_def, LET_THM]) >>
  conj_tac
  >- metis_tac[operand_11] >>
  conj_tac >- decide_tac >>
  simp_tac (srw_ss()) [mstore_def, LET_THM] >> first_assum ACCEPT_TAC
QED
