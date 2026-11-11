Theory frameRelocationGhostCopy
Ancestors frameRelocationLocalSteps frameResolvedOrigins frameOriginUpdates
  ptrDiscipline venomState venomInst finite_map words pred_set

Definition copy_ptr_def:
  copy_ptr L rv v (x:bytes32) y <=>
  !tok b sz. FLOOKUP rv v = SOME (tok,(b,sz)) ==>
    x - n2w b = y - n2w (L tok)
End

Definition copy_bytes_def:
  copy_bytes rv tn v x y <=>
  FLOOKUP rv v = NONE ==> word_agree_except (op_taint tn (Var v)) x y
End

Theorem assign_prov_erasure:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var w] /\
  inst.inst_outputs = [v] ==>
  step_prov PG (SND o_f rv) inst s' =
    SND o_f (origin_set rv [v] (FLOOKUP rv w))
Proof
  strip_tac >> Cases_on `FLOOKUP rv w` >>
  simp[step_prov_def, out_prov_def, first_prov_def, op_prov_def,
       FLOOKUP_o_f, origin_set_def, set_prov_def, fmap_eq_flookup,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  qx_gen_tac `u` >> Cases_on `u = v` >> simp[]
QED

Theorem assign_taint_copy:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var w] /\
  inst.inst_outputs = [v] /\ lookup_var w s = SOME x ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := tn.t_var |+ (v,op_taint tn (Var w))
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, update_var_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, out_taint_def, eval_operand_def,
       set_var_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
       FLOOKUP_DEF, EXTENSION] >>
  `{i | ?aid b sz. aid NOTIN FDOM s.vs_allocas /\
       (aid IN FDOM s.vs_allocas /\ s.vs_allocas ' aid = (b,sz)) /\
       b <= i /\ i < b + sz} = {}` by (simp[EXTENSION] >> metis_tac[]) >>
  simp[] >> simp[taint_component_equality]
QED

Theorem copy_ptr_output:
  copy_ptr L rv w x y ==>
  copy_ptr L (origin_set rv [v] (FLOOKUP rv w)) v x y
Proof
  simp[copy_ptr_def, origin_set_lookup]
QED

Theorem copy_ptr_other:
  u <> v ==>
  (copy_ptr L (origin_set rv [v] p) u x y <=> copy_ptr L rv u x y)
Proof
  simp[copy_ptr_def, origin_set_lookup]
QED

Theorem copy_bytes_output:
  copy_bytes rv tn w x y ==>
  copy_bytes (origin_set rv [v] (FLOOKUP rv w))
    (tn with t_var := tn.t_var |+ (v,op_taint tn (Var w))) v x y
Proof
  simp[copy_bytes_def, origin_set_lookup, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem copy_bytes_other:
  u <> v ==>
  (copy_bytes (origin_set rv [v] p)
    (tn with t_var := tn.t_var |+ (v,m)) u x y <=> copy_bytes rv tn u x y)
Proof
  simp[copy_bytes_def, origin_set_lookup, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem resolved_assign_step:
  local_rel (\u. F) (copy_ptr L rv) (copy_bytes rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [Var w] /\ inst.inst_outputs = [v] /\
  lookup_var w s = SOME x /\
  (!a b x y. Obs a b ==> Obs (update_var v x a) (update_var v y b)) ==>
  ?y. eval_operand (Var w) t = SOME y /\
    step_inst_base inst s = OK (update_var v x s) /\
    step_inst_base inst t = OK (update_var v y t) /\
    local_rel (\u. F) (copy_ptr L (origin_set rv [v] (FLOOKUP rv w)))
      (copy_bytes (origin_set rv [v] (FLOOKUP rv w))
        (step_taint inst s (update_var v x s) tn)) R Obs
      (update_var v x s) (update_var v y t) /\
    step_prov PG (SND o_f rv) inst (update_var v x s) =
      SND o_f (origin_set rv [v] (FLOOKUP rv w))
Proof
  strip_tac >>
  `step_prov PG (SND o_f rv) inst (update_var v x s) =
     SND o_f (origin_set rv [v] (FLOOKUP rv w))` by
    (irule assign_prov_erasure >> simp[]) >>
  `step_taint inst s (update_var v x s) tn =
     tn with t_var := tn.t_var |+ (v,op_taint tn (Var w))` by
    (irule assign_taint_copy >> simp[]) >>
  simp[] >> irule local_rel_assign_copy >> simp[] >>
  qexistsl_tac [`copy_bytes rv tn`, `\u. F`, `copy_ptr L rv`] >>
  simp[copy_ptr_other, copy_bytes_other, copy_ptr_output, copy_bytes_output]
QED
