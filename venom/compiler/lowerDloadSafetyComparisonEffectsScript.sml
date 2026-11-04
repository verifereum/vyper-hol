(* Unsigned comparisons observe translated positive allocation sites. *)
Theory lowerDloadSafetyComparisonEffects
Ancestors
  lowerDloadSafetyValues lowerDloadSafetyRelation lowerDloadSafetyKernel
  pointerConfinedDefs memLocDefs ptrDiscipline venomState venomInst irSupply unitLabelMapIdentity
  finite_map pred_set list arithmetic words

Theorem ld_comparison_pointer_syntax[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [LT;GT;EQ] /\
  MEM (Var v) inst.inst_operands /\ v IN fn_pv P fn ==>
  ?u w. inst.inst_operands = [Var u;Var w]
Proof
  simp[fn_ptr_ok_def, ptr_use_ok_def] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i (fn_insts fn) ==> _`
    (qspec_then `inst` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!v. MEM (Var v) inst.inst_operands /\ _ ==> _`
    (qspec_then `v` mp_tac) >>
  gvs[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
  metis_tac[]
QED

Theorem ld_selected_erased_site[local]:
  ld_vars P A f /\ ~retpc_var f.lf_fn v /\
  eval_operand (Var v) f.lf_src = SOME x /\
  eval_operand (Var v) f.lf_tgt = SOME y /\
  FLOOKUP (ld_erase A o_f f.lf_H) v = SOME (b,n) /\ 0 < n ==>
  ?a c. FLOOKUP f.lf_H v = SOME a /\
    FLOOKUP A a = SOME (b,c,n) /\ ld_wordrel A (SOME a) x y
Proof
  simp[FLOOKUP_o_f] >> strip_tac >>
  Cases_on `FLOOKUP f.lf_H v` >> gvs[] >> rename1 `ld_erase A a = (b,n)` >>
  `ld_wordrel A (SOME a) x y` by
    (irule ld_vars_operand_selected >> qexistsl_tac [`P`, `f`, `Var v`] >>
     simp[op_prov_def]) >>
  gvs[ld_wordrel_SOME, ld_erase_def] >> metis_tac[]
QED

Theorem ld_comparison_selected[local]:
  ld_vars P A f /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [Var u;Var w] /\
  (u IN FDOM f.lf_H \/ w IN FDOM f.lf_H) /\
  ~retpc_var f.lf_fn u /\ ~retpc_var f.lf_fn w /\
  eval_operand (Var u) f.lf_tgt = SOME y1 /\
  eval_operand (Var w) f.lf_tgt = SOME y2 /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  (!a b c n. FLOOKUP A a = SOME (b,c,n) ==> c+n < dimword (:256)) ==>
  ?x1 x2. eval_operand (Var u) f.lf_src = SOME x1 /\
    eval_operand (Var w) f.lf_src = SOME x2 /\
    ((y1=y2) <=> (x1=x2)) /\
    ((w2n y1 < w2n y2) <=> (w2n x1 < w2n x2)) /\
    ((w2n y2 < w2n y1) <=> (w2n x2 < w2n x1))
Proof
  strip_tac >>
  `?b n x1 x2.
    FLOOKUP (ld_erase A o_f f.lf_H) u = SOME (b,n) /\
    FLOOKUP (ld_erase A o_f f.lf_H) w = SOME (b,n) /\ 0 < n /\
    eval_operand (Var u) f.lf_src = SOME x1 /\
    eval_operand (Var w) f.lf_src = SOME x2 /\
    b <= w2n x1 /\ w2n x1 <= b+n /\
    b <= w2n x2 /\ w2n x2 <= b+n` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     simp[access_ok_def] >> strip_tac >>
     gvs[] >> metis_tac[]) >>
  `?a c. FLOOKUP f.lf_H u = SOME a /\ FLOOKUP A a = SOME (b,c,n) /\
    ld_wordrel A (SOME a) x1 y1` by
    (irule ld_selected_erased_site >> metis_tac[]) >>
  `?a' c'. FLOOKUP f.lf_H w = SOME a' /\ FLOOKUP A a' = SOME (b,c',n) /\
    ld_wordrel A (SOME a') x2 y2` by
    (irule ld_selected_erased_site >> metis_tac[]) >>
  `a = a'` by (irule ld_positive_source_identity >> metis_tac[]) >> gvs[] >>
  irule ld_wordrel_site_comparisons >> metis_tac[]
QED

Theorem ld_comparison_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [op1;op2] /\
  eval_operand op1 f.lf_tgt = SOME y1 /\
  eval_operand op2 f.lf_tgt = SOME y2 /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  (!a b c n. FLOOKUP A a = SOME (b,c,n) ==> c+n < dimword (:256)) ==>
  ?x1 x2. eval_operand op1 f.lf_src = SOME x1 /\
    eval_operand op2 f.lf_src = SOME x2 /\
    ((y1=y2) <=> (x1=x2)) /\
    ((w2n y1 < w2n y2) <=> (w2n x1 < w2n x2)) /\
    ((w2n y2 < w2n y1) <=> (w2n x2 < w2n x1))
Proof
  strip_tac >>
  `!op v. MEM op inst.inst_operands /\ op = Var v ==>
    MEM v (fn_ir_vars f.lf_fn) /\ ~retpc_var f.lf_fn v /\
    (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) = {}` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- metis_tac[ld_inst_input_ir] >> conj_tac
     >- (irule ld_numeric_operand_nonopaque >> simp[] >> qexists_tac `inst` >> gvs[])
     >> `op_taint tn (Var v) = {}` by
       (irule ld_numeric_operand_untainted >>
        qexistsl_tac [`f.lf_fn`, `inst`, `f.lf_src`] >> gvs[]) >>
     gvs[op_taint_def]) >>
  Cases_on `op_prov f.lf_H op1 = NONE /\ op_prov f.lf_H op2 = NONE`
  >- (`eval_operand op1 f.lf_src = eval_operand op1 f.lf_tgt` by
        (irule ld_vars_operand_equal >> metis_tac[listTheory.MEM]) >>
      `eval_operand op2 f.lf_src = eval_operand op2 f.lf_tgt` by
        (irule ld_vars_operand_equal >> metis_tac[listTheory.MEM]) >>
      metis_tac[]) >>
  `?v. MEM (Var v) inst.inst_operands /\ v IN FDOM f.lf_H` by
    (Cases_on `op1` >> Cases_on `op2` >>
     gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]) >>
  `v IN fn_pv P f.lf_fn` by (gvs[ld_vars_def, SUBSET_DEF] >> metis_tac[]) >>
  `?u w. inst.inst_operands = [Var u;Var w]` by
    (irule ld_comparison_pointer_syntax >> metis_tac[]) >>
  `op1 = Var u /\ op2 = Var w` by metis_tac[listTheory.CONS_11] >> gvs[] >>
  irule ld_comparison_selected >> simp[] >> metis_tac[]
QED
