Theory o1LabelFlowRetention
Ancestors
  codegenSymRel

(* Negative uses transport against instruction inclusion. *)
Theorem code_end_var_instruction_subset:
  !f x. code_end_var f x ==>
    !g. (!i. MEM i (fn_insts f) ==> MEM i (fn_insts g)) ==>
        code_end_var g x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  metis_tac[code_end_var_rules]
QED

(* A retained reader forces retention of each definition on its seed/copy
   chain.  No SSA or arbitrary-deletion monotonicity is assumed. *)
Theorem code_end_var_closed_retention:
  !f x. code_end_var f x ==>
    !g. (!i d y. MEM i (fn_insts g) /\
                  MEM (Var y) i.inst_operands /\
                  MEM d (fn_insts f) /\ MEM y d.inst_outputs ==>
                  MEM d (fn_insts g)) ==>
        !i. MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands ==>
            code_end_var g x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  metis_tac[code_end_var_rules, listTheory.MEM]
QED

Theorem label_flow_ok_closed_retention:
  (!i. MEM i (fn_insts g) ==> MEM i (fn_insts f)) /\
  (!i d x. MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands /\
           MEM d (fn_insts f) /\ MEM x d.inst_outputs ==>
           MEM d (fn_insts g)) ==>
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [g])
Proof
  simp[label_flow_ok_def] >> strip_tac >> strip_tac >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!inst. MEM inst (fn_insts f) ==> _`
    (qspec_then `inst` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `code_end_var f x` by
        metis_tac[code_end_var_instruction_subset] >>
      metis_tac[]) >>
  strip_tac >> gvs[] >>
  irule code_end_var_closed_retention >>
  metis_tac[listTheory.MEM]
QED
