(* Standalone unwrap boundaries at the actual intermediate compiler cursor.
   No expression compilation is replayed across the destination ADD. *)
Theory bodyPtrStructLitUnwrap
Ancestors
  bodyPtrDefs gasSummaryComposePtr fragGasPathPtr exprLowering
  exprSimMemorySource emitHelper vyperInterpreter compileEnv

Theorem stack_unwrap_counted:
  !D ctx fn PG G tn s cenv ty op sa out sb cx t tv ee.
    unwrap_value cenv (StackValue ty op) sa = (out,sb) /\
    ptr_vv_ok cx t tv (StackValue ty op) ee G tn s /\
    ~s.vs_halted ==>
    out = op /\ sb = sa /\
    ?v. gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
          (ee,s,G,tn) [] (INL v) ee G tn (OK s) /\
        ptr_val_ok cx t v op G tn s
Proof
  rpt gen_tac >>
  simp[unwrap_value_def, comp_return_def, ptr_vv_ok_def] >>
  strip_tac >> qexists_tac `v` >> simp[] >>
  simp[gas_marked_exec_ptr_def, gas_path_ptr_rules] >>
  metis_tac[read_result_gas_obs]
QED

Theorem memory_nonword_unwrap_counted:
  !D ctx fn PG G tn s cenv ty p sa out sb cx t tv ee.
    ~is_word_type ty /\ p.ptr_location = LocMemory /\
    unwrap_value cenv (LocatedValue ty p) sa = (out,sb) /\
    ptr_vv_ok cx t tv (LocatedValue ty p) ee G tn s /\
    (is_word_type t ==> op_prov G p.ptr_operand = NONE) /\
    ~s.vs_halted ==>
    out = p.ptr_operand /\ sb = sa /\
    ?v. gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
          (ee,s,G,tn) [] (INL v) ee G tn (OK s) /\
        ptr_val_ok cx t v out G tn s
Proof
  rpt gen_tac >>
  simp[unwrap_value_def, comp_return_def, ptr_vv_ok_def] >>
  strip_tac >> gvs[comp_return_def] >> qexists_tac `v` >>
  simp[ptr_val_ok_def, gas_marked_exec_ptr_def, gas_path_ptr_rules] >>
  metis_tac[read_result_gas_obs]
QED
