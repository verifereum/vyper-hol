(* Static metadata boundary only: no assertion about INVOKE execution. *)
Theory augAssignPtrCallWordBoundary
Ancestors
  bodySim memoryLocalRhsProps compileEnv vyperTypeSystem exprSimHypsDefs

Theorem internal_call_word_return_metadata:
  !tops ctx cenv cx env es ann id args drv mut nr rr params dflts ret body.
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  well_typed_expr env (Call ann (IntCall id) args drv) /\
  is_word_type ann /\
  supported_function_decl tops id Internal =
    SOME (mut,nr,rr,params,dflts,ret,body) ==>
  cenv.ce_func_return_type (nsid_to_string id) = ann
Proof
  rpt gen_tac >> PairCases_on `id` >> strip_tac >>
  `?sig. FLOOKUP env.fn_sigs (id0,id1) = SOME sig /\
     type_widens_to env.type_defs sig.ret_ty ann` by
    gvs[well_typed_expr_def] >>
  `sig.ret_ty = ann` by metis_tac[type_widens_to_word] >>
  `supported_program tops /\
   cenv.ce_func_return_type = build_func_return_type tops /\
   get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
  drule_all supported_internal_signature_return >> simp[]
QED
