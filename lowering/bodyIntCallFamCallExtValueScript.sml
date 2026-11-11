(* Value authorization uses the shared positive supported-type slot interface.
   Supported tuples/fixed arrays and structs are nonempty; dynamic arrays have
   a length header, so no zero-footprint escape remains for these return types. *)
Theory bodyIntCallFamCallExtValue
Ancestors
  bodyIntCallJointPureSlot exprExtRequestShape supportedExprForms
  supportedExprs loweringPosts
  bodyIntCallFamCallExtSource

Theorem extcall_result_slot:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_res fp ce env ee sc s /\
  supported_expr fp.jc_tops (Call ann (ExtCall stat skip sig opts) args dflt) /\
  well_typed_expr env (Call ann (ExtCall stat skip sig opts) args dflt) /\
  vv_holds ce fp.jc_cx ann r vv ee s /\
  vv_at ce fp.jc_cx ann sa sb ee r vv s /\
  ann <> NoneT /\ ~is_word_type ann /\ ~is_bytestring_type ann /\
  (case vv of StackValue _ _ => T
            | LocatedValue _ p => p.ptr_location = LocMemory) /\
  evaluate_type (get_tenv fp.jc_cx) ann = SOME tv ==>
  ?w a k. eval_operand (vv_operand vv) s = SOME w /\
    a <= w2n w /\ w2n w + type_memory_size tv <= a + k /\
    a + k < dimword (:256) /\
    (fp.jc_lo <= a \/
     ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)
Proof
  strip_tac >>
  `supported_value_type fp.jc_tops ann` by
    (PairCases_on `sig` >>
     drule extrequest_typed_nonempty >> strip_tac >>
     gvs[supported_expr_def, supported_pure_expr_def] >>
     gvs[supported_effect_expr_def, supported_external_return_type_def]) >>
  `?v. read_result fp.jc_cx r ee = (INL v,ee)` by
    (Cases_on `vv` >> gvs[vv_holds_def] >>
     rename1 `p.ptr_location = LocMemory` >> gvs[]) >>
  drule_all joint_supported_result_slot >> simp[]
QED
