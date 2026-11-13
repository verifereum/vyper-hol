Theory frameRelocationTaintOrder
Ancestors frameRelocationCopyTaint frameRelocationLoadSteps frameRelocationMemory
  frameRelocationTaintBounds ptrDiscipline
  codegenRel venomState venomExecSemantics finite_map pred_set words list

Definition relocation_taint_le_def:
  relocation_taint_le R tn un <=>
    demand_taint R tn.t_mem un.t_mem /\
    (!v. op_taint un (Var v) SUBSET op_taint tn (Var v)) /\
    un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
    un.t_imm SUBSET tn.t_imm
End

Theorem set_var_taint_subset:
  (!v. (case FLOOKUP uv v of NONE => {} | SOME m => m) SUBSET
       (case FLOOKUP tv v of NONE => {} | SOME m => m)) /\ n SUBSET m ==>
  !v. (case FLOOKUP (set_var_taint uv outs n) v of
         NONE => {} | SOME m => m) SUBSET
      (case FLOOKUP (set_var_taint tv outs m) v of
         NONE => {} | SOME m => m)
Proof
  strip_tac >> Cases_on `outs`
  >- simp[set_var_taint_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t`
  >- (simp[set_var_taint_def, FLOOKUP_UPDATE] >>
      rpt gen_tac >> IF_CASES_TAC >> simp[]) >>
  simp[set_var_taint_def, FLOOKUP_DRESTRICT] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem mem_word_taint_subset:
  demand_taint R M N /\ (!k. k < 32 ==> R (src+k) (dst+k)) ==>
  mem_word_taint N dst SUBSET mem_word_taint M src
Proof
  simp[demand_taint_def, mem_word_taint_def, SUBSET_DEF] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem relocation_taint_le_mcopy:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  eval_operand opd t = SOME dstT /\ eval_operand ops t = SOME srcT /\
  eval_operand opn t = SOME sz /\
  s' = mcopy (w2n dst) (w2n src) (w2n sz) s /\
  t' = mcopy (w2n dstT) (w2n srcT) (w2n sz) t /\
  relocation_taint_le R tn un /\
  (!a b. next a b /\ w2n dst <= a /\ a < w2n dst+w2n sz ==>
    w2n dstT <= b /\ b < w2n dstT+w2n sz /\
    R (w2n src+(a-w2n dst)) (w2n srcT+(b-w2n dstT))) /\
  (!a b. next a b /\ ~(w2n dst <= a /\ a < w2n dst+w2n sz) ==>
    R a b /\ ~(w2n dstT <= b /\ b < w2n dstT+w2n sz)) ==>
  relocation_taint_le next (step_taint inst s s' tn)
    (step_taint inst t t' un)
Proof
  strip_tac >>
  `demand_taint next (step_taint inst s s' tn).t_mem
     (step_taint inst t t' un).t_mem` by
    (irule demand_taint_mcopy >>
     gvs[relocation_taint_le_def] >> metis_tac[]) >>
  gvs[relocation_taint_le_def] >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       op_taint_def, out_taint_def] >>
  irule set_var_taint_subset >> simp[] >>
  gvs[op_taint_def]
QED

Theorem relocation_taint_le_mload:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [opa] /\
  inst.inst_outputs = [v] /\
  eval_operand opa s = SOME src /\ eval_operand opa t = SOME dst /\
  s' = update_var v (mload (w2n src) s) s /\
  t' = update_var v (mload (w2n dst) t) t /\
  relocation_taint_le R tn un /\
  (!a b. next a b ==> R a b) /\
  (!k. k < 32 ==> R (w2n src+k) (w2n dst+k)) ==>
  relocation_taint_le next (step_taint inst s s' tn)
    (step_taint inst t t' un)
Proof
  strip_tac >>
  `mem_word_taint un.t_mem (w2n dst) SUBSET
   mem_word_taint tn.t_mem (w2n src)` by
    (irule mem_word_taint_subset >>
     gvs[relocation_taint_le_def] >> metis_tac[]) >>
  `new_site_bytes s s' = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  `new_site_bytes t t' = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  gvs[relocation_taint_le_def] >>
  simp[relocation_taint_le_def, step_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       out_taint_def, op_taint_def] >>
  conj_tac
  >- (gvs[demand_taint_def] >> metis_tac[]) >>
  irule set_var_taint_subset >> simp[] >> gvs[op_taint_def]
QED

Theorem relocation_reachable_operand_taint_bounded:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  relocation_taint_le R tn un ==>
  op_taint un op SUBSET {k:num | k < 32}
Proof
  strip_tac >>
  `op_taint tn op SUBSET {k:num | k < 32}` by
    (irule frame_reachable_operand_taint_bounded >> metis_tac[]) >>
  `op_taint un op SUBSET op_taint tn op` by
    (Cases_on `op` >> gvs[relocation_taint_le_def, op_taint_def]) >>
  metis_tac[SUBSET_TRANS]
QED
