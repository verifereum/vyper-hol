(*
 * The conversion of an internal call whose type widens its callee's
 * return type.
 *
 * body_convert_widened_call_arg, the case bodySimExprCases'
 * body_type_builtin_case splits off for compile_type_builtin_case.
 *)

Theory bodySimConvertWidened
Ancestors
  exprSimSource bodySimConvertWidenedFacts bodySimConvertWidenedBytes
  exprSimHypsDefs bodySimConvertWidenedFromBytes exprSimConvert exprSimStack
  staticTypeFitsPtr
  list bodySim  exprSimHyps exprSimOperators exprSimAttribute
  exprSimPlaces exprSimPopNested targetPlaceSim exprSimAggregates exprSimSend exprSimMain exprSimECArith vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph

(* A conversion whose operand is an internal call whose type widens its
   callee's return type: the conversion's lowering sizes the operand by the
   callee's return type, so, as for body_struct_lit_widened_call_elem,
   describing the operand's value at that type is the internal-call
   simulation's work (body_intcall_case). *)
Theorem body_convert_widened_call_arg:
  !cx v11 typ e1.
    body_exprs_ok cx [e1] ==>
    !tops ctx func cenv env ty st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (TypeBuiltin v11 Convert typ [e1]) st /\
      (?a f cargs d. e1 = Call a (IntCall f) cargs d) /\
      lowered_value_type cenv e1 <> expr_type e1 ==>
      expr_sim ctx func cenv cx ty (TypeBuiltin v11 Convert typ [e1]) st /\
      expr_vv_sim ctx func cenv cx ty (TypeBuiltin v11 Convert typ [e1]) st
Proof
  rpt gen_tac >> simp[body_exprs_ok_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  rename1 `Call a (IntCall fid) args drv` >>
  `expr_sim ctx func cenv cx a (Call a (IntCall fid) args drv) st` by
    (gvs[body_expr_ok_def] >> metis_tac[]) >>
  `expr_sim ctx func cenv cx ty
     (TypeBuiltin typ Convert typ [Call a (IntCall fid) args drv]) st` by
    (Cases_on `is_bytestring_type typ`
     >- (irule intcall_convert_bytestring_sim >> metis_tac[]) >>
     Cases_on `is_bytestring_type a`
     >- (irule intcall_convert_from_bytestring_sim >> metis_tac[]) >>
     suspend "scalar") >>
  simp[] >> irule expr_vv_sim_stack >> simp[] >> conj_tac
  >- (gen_tac >> irule compile_convert_stack) >>
  metis_tac[eval_expr_type_builtin_value]
QED

Resume body_convert_widened_call_arg[scalar]:
  drule ifexp_body_pre_intcall_physical >> strip_tac >>
  `~is_abi_dynamic cenv.ce_struct_fields a` by
    (Cases_on `a` >> Cases_on `typ` >>
     gvs[vyperASTTheory.expr_type_def, vyperTypeSystemTheory.valid_conversion_def,
         compileEnvTheory.is_abi_dynamic_def] >>
     Cases_on `b` >>
     gvs[compileEnvTheory.is_abi_dynamic_def, compileEnvTheory.is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[compileEnvTheory.is_abi_dynamic_def, compileEnvTheory.is_bytestring_type_def]) >>
  drule (INST_TYPE [alpha |-> ``:string``, beta |-> ``:num``]
          (cj 1 static_arg_type_fits)) >>
  disch_then (qspec_then `cenv.ce_struct_fields` mp_tac) >>
  gvs[vyperASTTheory.expr_type_def]
QED
Finalise body_convert_widened_call_arg
