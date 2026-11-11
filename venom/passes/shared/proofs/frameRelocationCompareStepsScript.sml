Theory frameRelocationCompareSteps
Ancestors frameRelocationAffineSteps frameRelocationScalarSteps
  frameRelocationGuardedValues frameRelocationGhostCopy frameRelocationLocal
  frameRelocationValues
  frameOriginUpdates venomExecSemantics venomState venomInst ptrDiscipline
  finite_map words

(* Inclusive bounds admit one-past pointers, but not a wrapped endpoint. *)
Theorem displacement_natural_address:
  b <= w2n (x:'a word) /\ w2n x <= b+sz /\
  b+sz < dimword (:'a) /\ d+sz < dimword (:'a) /\
  x - n2w b = y - n2w d ==>
  w2n y = d + (w2n x - b)
Proof
  strip_tac >>
  `b < dimword (:'a) /\ d < dimword (:'a)` by decide_tac >>
  `w2n (x - n2w b) = w2n x - b` by
    (mp_tac (Q.SPECL [`x`, `n2w b`] word_sub_w2n) >>
     simp[WORD_LS, w2n_n2w]) >>
  `y = x - n2w b + n2w d` by metis_tac[WORD_SUB_ADD] >>
  `w2n (x - n2w b) + d < dimword (:'a)` by decide_tac >>
  qpat_x_assum `y = _` SUBST1_TAC >>
  simp[word_add_def, w2n_n2w, arithmeticTheory.ADD_COMM]
QED

Theorem displacement_same_site_comparisons:
  b <= w2n (x:'a word) /\ w2n x <= b+sz /\
  b <= w2n (z:'a word) /\ w2n z <= b+sz /\
  b+sz < dimword (:'a) /\ d+sz < dimword (:'a) /\
  x - n2w b = y - n2w d /\ z - n2w b = w - n2w d ==>
  (x = z <=> y = w) /\ (x <+ z <=> y <+ w) /\
  (z <+ x <=> w <+ y)
Proof
  strip_tac >>
  `w2n y = d + (w2n x - b)` by
    (irule displacement_natural_address >> metis_tac[]) >>
  `w2n w = d + (w2n z - b)` by
    (irule displacement_natural_address >> metis_tac[]) >>
  pure_rewrite_tac[GSYM w2n_11, WORD_LO] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem compare_prov_erasure:
  (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
  inst.inst_outputs = [v] ==>
  step_prov PG (SND o_f rv) inst s' = SND o_f (origin_set rv [v] NONE)
Proof
  strip_tac >> gvs[] >>
  simp[step_prov_def, out_prov_def, set_prov_def, origin_set_def,
       fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
  qx_gen_tac `u` >> Cases_on `u = v` >> simp[]
QED

Theorem compare_dispatch:
  (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/ inst.inst_opcode = GT) ==>
  ?f. (!s. step_inst_base inst s = exec_pure2 f inst s) /\
    (!x z y w. (x = z <=> y = w) /\ (x <+ z <=> y <+ w) /\
       (z <+ x <=> w <+ y) ==> f x z = f y w)
Proof
  strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  FIRST [qexists_tac `\x y. bool_to_word (x = y)` >> simp[] >> NO_TAC,
         qexists_tac `\x y. bool_to_word (w2n x < w2n y)` >> simp[GSYM WORD_LO] >> NO_TAC,
         qexists_tac `\x y. bool_to_word (w2n x > w2n y)` >> simp[arithmeticTheory.GREATER_DEF, GSYM WORD_LO] >> NO_TAC]
QED

Theorem guarded_pointer_compare_step:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  ~Opaque u /\ ~Opaque w /\
  FLOOKUP rv u = SOME (tok,(b,sz)) /\
  FLOOKUP rv w = SOME (tok,(b,sz)) /\
  inst.inst_operands = [Var u;Var w] /\ inst.inst_outputs = [v] /\
  (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
  lookup_var u s = SOME x /\ lookup_var w s = SOME z /\
  b <= w2n x /\ w2n x <= b+sz /\
  b <= w2n z /\ w2n z <= b+sz /\
  b+sz < dimword (:256) /\ L tok+sz < dimword (:256) /\
  (!s t x. Obs s t ==> Obs (update_var v x s) (update_var v x t)) /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
      (guarded_bytes Opaque (origin_set rv [v] NONE)
        (step_taint inst s s' tn)) R Obs s' t' /\
    step_prov PG (SND o_f rv) inst s' = SND o_f (origin_set rv [v] NONE) /\
    step_taint inst s s' tn = tn with t_var := tn.t_var |+ (v,{}) /\
    step_taint inst t t' tn = tn with t_var := tn.t_var |+ (v,{})
Proof
  strip_tac >> (
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  `?y. lookup_var u t = SOME y` by
    (Cases_on `lookup_var u t` >> gvs[variable_domains_def] >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  `?q. lookup_var w t = SOME q` by
    (Cases_on `lookup_var w t` >> gvs[variable_domains_def] >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  `guarded_ptr Opaque L rv u x y /\ guarded_ptr Opaque L rv w z q` by
    (metis_tac[local_rel_pointer]) >>
  `x - n2w b = y - n2w (L tok) /\
   z - n2w b = q - n2w (L tok)` by
    (gvs[guarded_ptr_def, copy_ptr_def]) >>
  ` (x = z <=> y = q) /\ (x <+ z <=> y <+ q) /\ (z <+ x <=> q <+ y)` by
    (irule displacement_same_site_comparisons >> metis_tac[]) >>
  `?f. (!s. step_inst_base inst s = exec_pure2 f inst s) /\
    (!x z y w. (x = z <=> y = w) /\ (x <+ z <=> y <+ w) /\
       (z <+ x <=> w <+ y) ==> f x z = f y w)` by
    (irule compare_dispatch >> simp[]) >>
  `f x z = f y q` by metis_tac[] >>
  `exec_pure2 f inst s = OK s'` by metis_tac[] >>
  `s' = update_var v (f x z) s` by
    (gvs[exec_pure2_def, eval_operand_def]) >>
  `exec_pure2 f inst t = OK (update_var v (f x z) t)` by
    (simp[exec_pure2_def, eval_operand_def]) >>
  `scalar_binary_opcode inst.inst_opcode` by
    (gvs[scalar_binary_opcode_def]) >>
  `step_taint inst s s' tn = tn with t_var := tn.t_var |+ (v,{})` by
    (gvs[] >> irule scalar_binary_taint >> simp[]) >>
  qexists_tac `update_var v (f x z) t` >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (gvs[] >> irule guarded_equal_write >> metis_tac[]) >>
  conj_tac >- (irule compare_prov_erasure >> simp[]) >>
  simp[] >> irule scalar_binary_taint >> simp[])
QED
