(* The typed return stack depends only on stack concretization. *)
Theory symControlRetStackOwn
Ancestors codegenSymRel symFrameControlFacts

Theorem sym_kinds_ret_stack_concretization:
  !cp fn ret srest ps ss.
  sym_kinds_ok cp fn ret srest ps ss ==>
  !front x lo ra values rest.
    ps.ps_stack = front ++ [Var x] /\ retpc_var fn x /\
    Var x <> dead_stack_marker /\
    (!op sv. MEM op front /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w)
      ss.sym_stack (ra :: values ++ rest) /\
    LENGTH values = LENGTH front ==>
    ss.sym_stack = Lab ret 0 :: MAP Val values ++ srest
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[sym_kinds_ok_def] >>
  gvs[listTheory.REVERSE_APPEND, listTheory.LIST_REL_CONS1] >>
  qpat_x_assum `op_kind_ok fn ret (Var x) _` mp_tac >>
  simp[op_kind_ok_def] >> strip_tac >> gvs[] >>
  rename1 `LIST_REL (op_kind_ok fn ret) (REVERSE front) payload` >>
  `payload = MAP Val values` by
    (irule word_kind_prefix_concretization >>
     metis_tac[listTheory.MEM_REVERSE, listTheory.LENGTH_REVERSE]) >> simp[]
QED
