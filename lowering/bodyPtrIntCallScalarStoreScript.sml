Theory bodyPtrIntCallScalarStore
Ancestors
  bodyPtrDefs fragExecPtr typedCopyPtr robustCopyTransportPtr
  ptrDiscipline venomInst venomExecSemantics venomState venomMemProps
  valueEncoding valueEncodingProps valueEncodingProofs venomMemProofs
  emitHelperProps list pred_set

Theorem intcall_scalar_mstore_robust:
  eval_operand a s = SOME aw /\ eval_operand v s = SOME word /\
  op_taint tn v = {} /\
  (!b m. mem_word_at b m = word ==> val_in_memory ty value b m) ==>
  !m. mem_agree_outside
        (step_taint (mk_inst id MSTORE [a;v] []) s
          (mstore (w2n aw) word s) tn).t_mem
        (mstore (w2n aw) word s).vs_memory m ==>
      val_in_memory ty value (w2n aw) m
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  `mem_bytes_at (w2n aw) 32 m =
   mem_bytes_at (w2n aw) 32 (mstore (w2n aw) word s).vs_memory` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >> rename1 `j < 32` >>
     `w2n aw+j NOTIN
       (step_taint (mk_inst id MSTORE [a;v] []) s
         (mstore (w2n aw) word s) tn).t_mem` by
       (irule mstore_word_clean >> simp[] >> metis_tac[]) >>
     `mem_bytes_at (w2n aw+j) 1 (mstore (w2n aw) word s).vs_memory =
      mem_bytes_at (w2n aw+j) 1 m` by
       (fs[mem_agree_outside_def] >> metis_tac[]) >>
     pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  `mem_word_at (w2n aw) m =
   mem_word_at (w2n aw) (mstore (w2n aw) word s).vs_memory` by
    asm_simp_tac bool_ss [mem_word_at_def, GSYM mem_bytes_at_def] >>
  first_x_assum irule >> metis_tac[mstore_mem_word_at_same]
QED

Theorem intcall_scalar_mstore_preserves_robust:
  lookup_var dst s = SOME aw /\ eval_operand v s = SOME word /\
  op_taint tn v = {} /\ val_wf ty value /\
  (!i. p <= i /\ i < p + val_footprint ty value ==>
       i < w2n aw \/ w2n aw + 32 <= i) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory ty value p m) ==>
  !m. mem_agree_outside
        (step_taint (mk_inst id MSTORE [Var dst;v] []) s
          (mstore (w2n aw) word s) tn).t_mem
        (mstore (w2n aw) word s).vs_memory m ==>
      val_in_memory ty value p m
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mstore_ghost_frame >> strip_tac >>
  match_mp_tac robust_val_in_memory_exterior_frame >>
  simp[] >>
  qexistsl_tac [`tn.t_mem`, `s.vs_memory`,
               `{i | w2n aw <= i /\ i < w2n aw + 32}`] >>
  simp[] >>
  mp_tac (Q.SPECL [`s`, `w2n (aw:bytes32)`, `word`] mstore_memory_frame) >>
  simp[mem_agree_outside_def] >> strip_tac >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  first_x_assum ACCEPT_TAC
QED

Theorem intcall_scalar_mstore_ok_robust:
  eval_operand a s = SOME aw /\ eval_operand v s = SOME word /\
  op_taint tn v = {} /\
  step_inst fuel ctx (mk_inst id MSTORE [a;v] []) s = OK s' /\
  (!b m. mem_word_at b m = word ==> val_in_memory ty value b m) ==>
  !m. mem_agree_outside
        (step_taint (mk_inst id MSTORE [a;v] []) s s' tn).t_mem
        s'.vs_memory m ==> val_in_memory ty value (w2n aw) m
Proof
  rpt gen_tac >> strip_tac >>
  `s' = mstore (w2n aw) word s` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, mk_inst_def] >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     simp[exec_write2_def]) >>
  gvs[] >> match_mp_tac intcall_scalar_mstore_robust >> metis_tac[]
QED
