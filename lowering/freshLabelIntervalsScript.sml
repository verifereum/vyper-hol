(* Numeric fresh-label intervals, independent of compiler label suffixes. *)
Theory freshLabelIntervals
Ancestors
  exprSimAbiEncodeObliviousLabels exprSimAbiEncodeObliviousContext
  exprSimAbiEncodeObliviousCode
  emitHelper emitHelperProps fragExec compileEnv list rich_list arithmetic

Definition fresh_label_between_def:
  fresh_label_between lo hi l <=>
    ?s k. lo <= k /\ k < hi /\ l = fresh_label_output s k
End
Theorem fresh_label_between_output:
  lo <= k /\ k < hi ==> fresh_label_between lo hi (fresh_label_output s k)
Proof
  simp[fresh_label_between_def] >> metis_tac[]
QED


Definition fresh_label_step_def:
  fresh_label_step a b <=>
    entry_shape a b /\ a.cs_next_label <= b.cs_next_label /\
    ALL_DISTINCT (opened_labels a b) /\
    EVERY (fresh_label_between a.cs_next_label b.cs_next_label)
          (opened_labels a b)
End

Theorem fresh_label_between_mono:
  lo' <= lo /\ hi <= hi' /\ fresh_label_between lo hi l ==>
  fresh_label_between lo' hi' l
Proof
  simp[fresh_label_between_def] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem fresh_label_between_not_mem:
  fresh_label_between lo mid l /\ EVERY (fresh_label_between mid hi) xs ==>
  ~MEM l xs
Proof
  simp[fresh_label_between_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule fresh_label_output_inj >> simp[]
QED

Theorem fresh_label_step_refl:
  fresh_label_step a a
Proof
  simp[fresh_label_step_def, entry_shape_refl, opened_labels_open]
QED

Theorem fresh_label_step_trans:
  fresh_label_step a b /\ fresh_label_step b c ==> fresh_label_step a c
Proof
  rw[fresh_label_step_def]
  >- metis_tac[entry_shape_trans]
  >- (drule_all opened_labels_compose >> disch_then SUBST1_TAC
      >> simp[ALL_DISTINCT_APPEND]
      >> gvs[EVERY_MEM, fresh_label_between_def]
      >> rpt strip_tac >> res_tac >> gvs[]
      >> imp_res_tac fresh_label_output_inj >> gvs[])
  >> drule_all opened_labels_compose >> disch_then SUBST1_TAC
  >> simp[EVERY_APPEND, EVERY_MEM]
  >> gvs[EVERY_MEM]
  >> conj_tac >> rpt strip_tac
  >- (irule fresh_label_between_mono
      >> qexistsl_tac [`b.cs_next_label`, `a.cs_next_label`] >> simp[])
  >> irule fresh_label_between_mono
  >> qexistsl_tac [`c.cs_next_label`, `b.cs_next_label`] >> simp[]
QED

Theorem fresh_label_step_current_excluded:
  fresh_label_step a b ==>
  ~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks a b)))
Proof
  rw[fresh_label_step_def]
  >> Cases_on `NULL (emitted_blocks a b)`
  >- gvs[NULL_EQ]
  >> gvs[opened_labels_def, ALL_DISTINCT_APPEND, MEM_MAP]
  >> metis_tac[MEM_REVERSE]
QED

Theorem fresh_label_step_reserved_close:
  fresh_label_step a m /\ fresh_label_step m b /\ entry_shape b c /\
  c.cs_next_label = b.cs_next_label /\ opened_labels b c = [l] /\
  fresh_label_between a.cs_next_label m.cs_next_label l /\
  ~MEM l (opened_labels a m) ==>
  fresh_label_step a c
Proof
  rpt strip_tac
  >> `fresh_label_step a b` by metis_tac[fresh_label_step_trans]
  >> `~MEM l (opened_labels m b)` by
       (irule fresh_label_between_not_mem
        >> qexistsl_tac [`b.cs_next_label`, `a.cs_next_label`, `m.cs_next_label`]
        >> gvs[fresh_label_step_def])
  >> `opened_labels a b = opened_labels a m ++ opened_labels m b` by
       (irule opened_labels_compose >> gvs[fresh_label_step_def])
  >> `opened_labels a c = opened_labels a b ++ [l]` by
       (gvs[fresh_label_step_def] >> drule_all opened_labels_compose >> simp[])
  >> gvs[fresh_label_step_def]
  >> simp[ALL_DISTINCT_APPEND, EVERY_APPEND]
  >> conj_tac >- metis_tac[entry_shape_trans]
  >> irule fresh_label_between_mono
  >> qexistsl_tac [`m.cs_next_label`, `a.cs_next_label`] >> simp[]
QED

Definition fresh_label_action_def:
  fresh_label_action m <=> !a x b. m a = (x,b) ==> fresh_label_step a b
End

Theorem fresh_label_action_return:
  fresh_label_action (comp_return x)
Proof
  simp[fresh_label_action_def, comp_return_def, fresh_label_step_refl]
QED

Theorem fresh_label_action_bind:
  fresh_label_action m /\ (!x. fresh_label_action (f x)) ==>
  fresh_label_action (comp_bind m f)
Proof
  rw[fresh_label_action_def, comp_bind_def]
  >> Cases_on `m a` >> gvs[] >> metis_tac[fresh_label_step_trans]
QED

Theorem fresh_label_action_ignore_bind:
  fresh_label_action m /\ fresh_label_action n ==>
  fresh_label_action (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def, fresh_label_action_bind]
QED

Theorem fresh_label_action_emit:
  (!opc ops. fresh_label_action (emit_op opc ops)) /\
  (!opc ops. fresh_label_action (emit_void opc ops)) /\
  (!opc ops outs. fresh_label_action (emit_inst opc ops outs))
Proof
  simp[fresh_label_action_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  simp[fresh_label_step_def, opened_labels_open, entry_shape_def] >>
  metis_tac[APPEND_ASSOC]
QED
