Theory bodyPtrPopTargetSimArrayEndpoint
Ancestors
  exprSimArrayIndex freshWrites exprSimCopy exprSimStorageCopy
  compileEnv exprLoweringProps emitHelperProps venomState list

Theorem target_array_suffix_writes_fresh:
  array_bounds_check idx len sgn sa = ((),sm) /\
  array_elem_ptr bop idx dyn ws esz sm = (dst,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  writes_fresh sa (emitted_insts sa sb) /\
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  `comp_ignore_bind (array_bounds_check idx len sgn)
      (array_elem_ptr bop idx dyn ws esz) sa = (dst,sb)` by
    simp[comp_ignore_bind_def, comp_bind_def] >>
  drule_at (Pat `comp_ignore_bind _ _ _ = _`)
    (SRULE [straight_fresh_def] straight_fresh_array_check_ptr) >>
  simp[same_blocks_def]
QED

Theorem target_array_suffix_runtime:
  array_bounds_check idx len sgn sa = ((),sm) /\
  array_elem_ptr bop idx dyn ws esz sm = (dst,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  eval_operand len s = SOME n /\ fresh_vars_wrt sa s /\ idx_in_range sgn i n ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    fresh_vars_wrt sb t /\ copy_old_operand sb dst /\
    eval_operand dst t = SOME ((if dyn then b+n2w ws else b)+i*n2w esz) /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all array_bounds_check_ok >> strip_tac >>
  `eval_operand bop ss' = SOME b /\ eval_operand idx ss' = SOME i` by metis_tac[] >>
  drule_all array_elem_ptr_run >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK ss''` by
    metis_tac[run_inst_seq_append] >>
  drule_all target_array_suffix_writes_fresh >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  qexists_tac `ss''` >> simp[lookup_var_def, copy_old_operand_def] >>
  metis_tac[exprSimWordBuiltinsTheory.fresh_vars_wrt_not_fresh_at]
QED
