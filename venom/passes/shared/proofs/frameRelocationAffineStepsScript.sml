Theory frameRelocationAffineSteps
Ancestors frameRelocationScalarSteps frameRelocationGuardedValues
  frameRelocationGhostCopy frameRelocationLocal frameRelocationValues
  frameOriginUpdates venomExecSemantics venomState venomInst ptrDiscipline
  finite_map words

Theorem guarded_pointer_write:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  x - n2w b = y - n2w (L tok) /\
  (!a b x y. Obs a b ==> Obs (update_var v x a) (update_var v y b)) ==>
  local_rel (\u. F)
    (guarded_ptr Opaque L (origin_set rv [v] (SOME (tok,(b,sz)))))
    (guarded_bytes Opaque (origin_set rv [v] (SOME (tok,(b,sz))))
      (tn with t_var := tn.t_var |+ (v,{}))) R Obs
    (update_var v x s) (update_var v y t)
Proof
  strip_tac >> irule local_rel_update_observation_invariant >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
       origin_set_lookup] >>
  qexistsl_tac [`guarded_bytes Opaque rv tn`, `\u. F`, `guarded_ptr Opaque L rv`] >>
  simp[guarded_ptr_other, guarded_bytes_other] >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
       origin_set_lookup, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem affine_prov_erasure:
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  (inst.inst_operands = [Var w;a] \/ inst.inst_operands = [a;Var w]) /\
  inst.inst_outputs = [v] /\ FLOOKUP rv w = SOME (tok,(b,sz)) /\
  (!u. a = Var u ==> FLOOKUP rv u = NONE) ==>
  step_prov PG (SND o_f rv) inst s' =
    SND o_f (origin_set rv [v] (SOME (tok,(b,sz))))
Proof
  strip_tac >>
  `op_prov (SND o_f rv) a = NONE` by
    (Cases_on `a` >> simp[op_prov_def, FLOOKUP_o_f] >> metis_tac[]) >>
  gvs[] >>
  simp[step_prov_def, out_prov_def, first_prov_def, op_prov_def,
       FLOOKUP_o_f, set_prov_def, origin_set_def, fmap_eq_flookup,
       FLOOKUP_UPDATE] >> qx_gen_tac `u` >> Cases_on `u = v` >> simp[]
QED

Theorem guarded_pointer_pure2:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  ~Opaque w /\ FLOOKUP rv w = SOME (tok,(b,sz)) /\
  inst.inst_operands = [Var w;a] /\ inst.inst_outputs = [v] /\
  s.vs_labels = t.vs_labels /\
  (!u. a = Var u ==> clean_scalar Opaque rv tn u) /\
  (!x y c. x - n2w b = y - n2w (L tok) ==>
     f x c - n2w b = f y c - n2w (L tok)) /\
  (!s t x y. Obs s t ==> Obs (update_var v x s) (update_var v y t)) /\
  exec_pure2 f inst s = OK s' ==>
  ?x y c. lookup_var w s = SOME x /\ lookup_var w t = SOME y /\
    eval_operand a s = SOME c /\ eval_operand a t = SOME c /\
    s' = update_var v (f x c) s /\
    exec_pure2 f inst t = OK (update_var v (f y c) t) /\
    local_rel (\u. F)
      (guarded_ptr Opaque L (origin_set rv [v] (SOME (tok,(b,sz)))))
      (guarded_bytes Opaque (origin_set rv [v] (SOME (tok,(b,sz))))
        (tn with t_var := tn.t_var |+ (v,{}))) R Obs
      s' (update_var v (f y c) t)
Proof
  strip_tac >>
  `eval_operand a s = eval_operand a t` by
    (irule guarded_scalar_operand >> simp[] >>
     metis_tac[]) >>
  gvs[exec_pure2_def, eval_operand_def, AllCaseEqs()] >>
  drule local_rel_domains >>
  simp[variable_domains_def] >>
  disch_then (qspec_then `w` mp_tac) >>
  Cases_on `lookup_var w t` >> simp[] >>
  rename1 `lookup_var w t = SOME y` >>
  rename1 `lookup_var w s = SOME x` >>
  `guarded_ptr Opaque L rv w x y` by
    (metis_tac[local_rel_pointer]) >>
  gvs[guarded_ptr_def, copy_ptr_def] >>
  irule guarded_pointer_write >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem guarded_pointer_binary_step:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  ~Opaque w /\ FLOOKUP rv w = SOME (tok,(b,sz)) /\
  inst.inst_operands = [Var w;a] /\ inst.inst_outputs = [v] /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  s.vs_labels = t.vs_labels /\
  (!u. a = Var u ==> clean_scalar Opaque rv tn u) /\
  (!s t x y. Obs s t ==> Obs (update_var v x s) (update_var v y t)) /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
    local_rel (\u. F)
      (guarded_ptr Opaque L (origin_set rv [v] (SOME (tok,(b,sz)))))
      (guarded_bytes Opaque (origin_set rv [v] (SOME (tok,(b,sz))))
        (step_taint inst s s' tn)) R Obs s' t' /\
    step_prov PG (SND o_f rv) inst s' =
      SND o_f (origin_set rv [v] (SOME (tok,(b,sz)))) /\
    step_taint inst s s' tn = tn with t_var := tn.t_var |+ (v,{}) /\
    step_taint inst t t' tn = tn with t_var := tn.t_var |+ (v,{})
Proof
  strip_tac >>
  `step_prov PG (SND o_f rv) inst s' =
     SND o_f (origin_set rv [v] (SOME (tok,(b,sz))))` by
    (irule affine_prov_erasure >> simp[] >>
     metis_tac[clean_scalar_def]) >>
  `?f. (!u. step_inst_base inst u = exec_pure2 f inst u) /\
       (!x y c. x - n2w b = y - n2w (L tok) ==>
          f x c - n2w b = f y c - n2w (L tok))` by
    (Cases_on `inst.inst_opcode = ADD`
     >- (qexists_tac `word_add` >> simp[step_inst_base_def] >>
         metis_tac[word_displacement_affine]) >>
     qexists_tac `word_sub` >> simp[step_inst_base_def] >>
     metis_tac[word_displacement_sub_scalar]) >>
  `exec_pure2 f inst s = OK s'` by metis_tac[] >>
  drule_all guarded_pointer_pure2 >> strip_tac >>
  `scalar_binary_opcode inst.inst_opcode` by
    (gvs[scalar_binary_opcode_def]) >>
  qexists_tac `update_var v (f y c) t` >>
  gvs[] >>
  `step_taint inst s (update_var v (f x c) s) tn =
     tn with t_var := tn.t_var |+ (v,{})` by
    (irule scalar_binary_taint >> simp[]) >>
  `step_taint inst t (update_var v (f y c) t) tn =
     tn with t_var := tn.t_var |+ (v,{})` by
    (irule scalar_binary_taint >> simp[]) >> simp[]
QED

Theorem add_operand_swap:
  inst.inst_opcode = ADD /\ inst.inst_operands = [a;b] ==>
  step_inst_base (inst with inst_operands := [b;a]) s = step_inst_base inst s
Proof
  strip_tac >> simp[step_inst_base_def, exec_pure2_def] >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand b s` >>
  simp[WORD_ADD_COMM]
QED

Theorem scalar_binary_taint_operands:
  scalar_binary_opcode inst.inst_opcode /\ inst.inst_opcode <> MUL /\
  inst.inst_operands = [a;b] ==>
  step_taint (inst with inst_operands := [c;d]) s s' tn =
    step_taint inst s s' tn
Proof
  strip_tac >> gvs[scalar_binary_opcode_def] >>
  simp[step_taint_def, mem_taint_def, step_writes_def, written_taint_def,
       range_bytes_def, codegenRelTheory.source_memory_write_ranges_def, out_taint_def,
       adopt_reset_def, store_taint_def, imm_taint_def] >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand c s` >> simp[]
QED

Theorem guarded_scalar_add_pointer_step:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  ~Opaque w /\ FLOOKUP rv w = SOME (tok,(b,sz)) /\
  inst.inst_opcode = ADD /\ inst.inst_operands = [a;Var w] /\
  inst.inst_outputs = [v] /\ s.vs_labels = t.vs_labels /\
  (!u. a = Var u ==> clean_scalar Opaque rv tn u) /\
  (!s t x y. Obs s t ==> Obs (update_var v x s) (update_var v y t)) /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
    local_rel (\u. F)
      (guarded_ptr Opaque L (origin_set rv [v] (SOME (tok,(b,sz)))))
      (guarded_bytes Opaque (origin_set rv [v] (SOME (tok,(b,sz))))
        (step_taint inst s s' tn)) R Obs s' t' /\
    step_prov PG (SND o_f rv) inst s' =
      SND o_f (origin_set rv [v] (SOME (tok,(b,sz)))) /\
    step_taint inst s s' tn = tn with t_var := tn.t_var |+ (v,{}) /\
    step_taint inst t t' tn = tn with t_var := tn.t_var |+ (v,{})
Proof
  strip_tac >>
  `!u. step_inst_base (inst with inst_operands := [Var w;a]) u =
       step_inst_base inst u` by (irule add_operand_swap >> simp[]) >>
  `!u u' tn. step_taint (inst with inst_operands := [Var w;a]) u u' tn =
       step_taint inst u u' tn` by
    (rpt gen_tac >> irule scalar_binary_taint_operands >>
     simp[scalar_binary_opcode_def]) >>
  `step_prov PG (SND o_f rv) inst s' =
     SND o_f (origin_set rv [v] (SOME (tok,(b,sz))))` by
    (irule affine_prov_erasure >> simp[] >> metis_tac[clean_scalar_def]) >>
  mp_tac (Q.INST [`inst` |-> `inst with inst_operands := [Var w;a]`]
    guarded_pointer_binary_step) >>
  simp[] >> strip_tac >> goal_assum (drule_at Any) >> simp[]
QED
