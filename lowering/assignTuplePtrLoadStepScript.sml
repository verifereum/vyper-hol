(* Safe tuple member loads: robust representations justify clean scalar reads. *)
Theory assignTuplePtrLoadStep
Ancestors
  assignTuplePtrBoundary assignTuplePtrPrefix representationCleanPtr bodyPtrDefs compileEnv
  tupleTypedLoad tupleMemoryLayout words arithmetic list rich_list valueEncoding valueEncodingProofs
  typedCopyPtr ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState emitHelperProps

Theorem tuple_word_member_clean:
  !tys tvs vs tenv cenv a mem tn i.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    values_have_types tvs vs /\
    (!m. mem_agree_outside tn.t_mem mem m ==> tuple_in_memory vs tvs a m) /\
    a + type_memory_size_list tvs < dimword (:256) /\
    i < LENGTH tys /\ is_word_type (EL i tys) ==>
    !j. a + SUM (MAP type_memory_size (TAKE i tvs)) <= j /\
        j < a + SUM (MAP type_memory_size (TAKE i tvs)) + 32 ==>
        j NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >> rename1 `a + type_memory_size_list tvs < _` >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) =
   SUM (MAP type_memory_size (TAKE i tvs))` by
    (irule tuple_prefix_sizes >> simp[]) >>
  `a + SUM (MAP type_memory_size (TAKE i tvs)) < dimword (:256)` by
    (`i < LENGTH tvs` by metis_tac[] >>
     drule tuple_element_interval >> fs[type_memory_size_list_sum] >> decide_tac) >>
  `!m. mem_agree_outside tn.t_mem mem m ==>
    mem_word_at (a + SUM (MAP type_memory_size (TAKE i tvs))) m =
      typed_val_to_w256 (EL i tvs) (EL i vs)` by
    (rpt strip_tac >>
     qspecl_then [`tys`, `tvs`, `vs`, `tenv`, `cenv`, `n2w a`, `m`, `i`]
       mp_tac tuple_typed_load_value >>
     simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     disch_then irule >> simp[]) >>
  drule robust_mem_word_at_clean >> simp[]
QED

(* Fresh variable writes preserve the ghost at an unchanged source scope. *)
Theorem ghost_inv_old_vars_frame_ptr:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  ghost_inv d cenv cx es G' tn' t
Proof
  strip_tac >>
  fs[ghost_inv_def, local_ptrs_reserved_def, ptr_covers_def,
     stor_taint_ok_def] >>
  conj_tac >- metis_tac[] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]
QED

Theorem emit_add_zero_path_ptr:
  emit_inst ADD [left; right] [tmp] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ADD [left;right] [tmp])
      (update_var tmp (a+b) s))
    (step_taint (mk_inst sa.cs_next_id ADD [left;right] [tmp]) s
      (update_var tmp (a+b) s) tn)
    (OK (update_var tmp (a+b) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule emit_inst_zero_path_ptr >> simp[is_terminator_def] >>
  conj_tac
  >- simp[step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  irule ptr_inst_ok_copy_len_binop >> simp[]
QED

Theorem add_source_site_ptr:
  FLOOKUP G src = SOME site ==>
  FLOOKUP (step_prov PG G (mk_inst id ADD [Var src; Lit off] [dst]) u) dst =
    SOME site
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE]
QED
