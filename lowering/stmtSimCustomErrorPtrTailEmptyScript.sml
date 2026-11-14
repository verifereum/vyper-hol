(* The zero-argument custom-error tail has no encoder invocation. *)
Theory stmtSimCustomErrorPtrTailEmpty
Ancestors
  stmtSimCustomErrorPtrTailPrefix stmtSimCustomErrorPtrTail stmtSimCustomErrorRevert
  loweringHalt fragExec fragGasPathPtr emitHelperProps compileEnv emitHelper
  venomState venomInst venomExecSemantics bodyPtrDefs words arithmetic

Theorem custom_error_revert_empty_tail_run_ptr:
  custom_error_revert_tail cenv id tys args_buf T st = ((),en) /\
  fn_has_code st en func /\
  abi_size_bound cenv.ce_struct_fields (TupleT tys)+32 < 2 ** 64 /\
  stmt_state_rel ctx func cenv cx es s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  !D PG G tn. ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (Abort Revert_abort t)
Proof
  strip_tac >> rpt gen_tac >>
  qabbrev_tac `B = abi_size_bound cenv.ce_struct_fields (TupleT tys)` >>
  `B = abi_size_bound cenv.ce_struct_fields (TupleT tys)` by simp[Abbr `B`] >>
  Cases_on `compile_alloc_buffer (B+32) st` >>
  rename1 `_ = (buf,sa)` >>
  Cases_on `emit_void MSTORE
    [buf.buf_operand; Lit (n2w (cenv.ce_method_id (SND id) tys))] sa` >>
  rename1 `_ = (unit,sc)` >> Cases_on `unit` >>
  Cases_on `emit_op ADD [buf.buf_operand;Lit 28w] sc` >>
  rename1 `_ = (offset,sn)` >>
  qpat_x_assum `custom_error_revert_tail _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `B = abi_size_bound _ _` (fn bth =>
    qpat_assum `compile_alloc_buffer (B+32) st = _` (fn alloc_th =>
      qpat_assum `emit_void MSTORE _ sa = _` (fn store_th =>
        qpat_assum `emit_op ADD _ sc = _` (fn add_th =>
          simp_tac (srw_ss()) [custom_error_revert_tail_def, comp_bind_def,
            comp_ignore_bind_def, comp_return_def, LET_THM, GSYM bth,
            alloc_th, store_th, add_th])))) >>
  strip_tac >>
  `cs_extends st sa /\ cs_extends sa sc /\ cs_extends sc sn /\
    cs_extends sn en` by
    metis_tac[compile_alloc_buffer_extends, cs_appends_emit_helpers,
      cs_appends_def, cs_extends_emit_inst] >>
  `cs_extends sa en /\ cs_extends sc en` by metis_tac[cs_extends_trans] >>
  `fn_has_code st sa func /\ fn_has_code sa sc func /\
    fn_has_code sc sn func /\ fn_has_code sn en func` by
    metis_tac[fn_has_code_split] >>
  mp_tac (Q.INST [`mid` |-> `sa`, `en` |-> `sc`,
    `selector` |-> `n2w (cenv.ce_method_id (SND id) tys)`]
    (SPEC_ALL custom_error_selector_prefix_run_ptr)) >>
  (impl_tac >- simp[Abbr `B`]) >>
  disch_then (qspecl_then [`D`,`PG`,`G`,`tn`]
    (qx_choose_then `u` (qx_choose_then `d`
      (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))))) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  `lookup_var p u = SOME (n2w d) /\
    not_fresh_at sc p /\ ptr_covers G1 tn1 p u (B+32)` by
    (conj_tac
     >- (qpat_x_assum `buf.buf_operand = Var p` (fn bth =>
           qpat_x_assum `eval_operand buf.buf_operand u = _`
             (ACCEPT_TAC o REWRITE_RULE [bth, eval_operand_def]))) >>
     qpat_x_assum `!p. buf.buf_operand = Var p ==> _`
       (qspec_then `p` mp_tac) >>
     qpat_x_assum `buf.buf_operand = Var p`
       (fn bth => simp_tac (srw_ss()) [bth])) >>
  `fn_has_code sn sn func` by
    (mp_tac (Q.SPECL [`sn`,`sn`,`en`,`func`] fn_has_code_split) >>
     simp[cs_extends_refl]) >>
  mp_tac (Q.INST [`st` |-> `sc`, `sr` |-> `sn`,
    `x` |-> `p`, `s` |-> `u`, `G` |-> `G1`, `tn` |-> `tn1`,
    `no_args` |-> `T`, `len` |-> `Lit 4w`, `k` |-> `0`,
    `encoded_len` |-> `Lit 0w`] (SPEC_ALL custom_error_revert_suffix_run_ptr)) >>
  (impl_tac >-
    (qpat_x_assum `buf.buf_operand = Var p` (fn bth =>
       qpat_x_assum `emit_op ADD [buf.buf_operand;Lit 28w] sc = _`
         (assume_tac o REWRITE_RULE [bth])) >>
     simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  metis_tac[gas_path_ptr_then, ADD_0]
QED
