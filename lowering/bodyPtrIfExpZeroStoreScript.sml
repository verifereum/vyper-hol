Theory bodyPtrIfExpZeroStore
Ancestors bodyPtrIfExpResidual bodyPtrIfExpReturnMetadata bodyPtrIfExpLayoutRefl
  bodyPtrIfExpEndpointTyping vyperTypeSystem vyperTypeArgFits
  exprLowering context exprSimHypsDefs vyperTyping vyperAST

Theorem ifexp_selected_zero_call:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args dret) es_arm /\
  compile_expr ce ret_ty (Call ann (IntCall fid) args dret) sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,0,pvs) ==>
  vv = StackValue (ce.ce_func_return_type (nsid_to_string fid)) (Lit 0w) /\
  (ce.ce_func_return_type (nsid_to_string fid) = NoneT \/
   type_memory_bytes ce (ce.ce_func_return_type (nsid_to_string fid)) = 0)
Proof
  strip_tac >> conj_tac
  >- metis_tac[ifexp_zero_call_result] >>
  drule_all ifexp_internal_call_zero_extent >> simp[]
QED

Theorem ifexp_residual_store_dispatch:
  ~is_word_type ty /\ ~same_memory_layout ce sty ty ==>
  compile_store_memory ce (Lit 0w) dst ty sty =
    if is_bytestring_type ty then compile_store_bytestring (Lit 0w) dst
    else compile_store_memory_typed ce dst ty (Lit 0w) sty
Proof
  strip_tac >>
  `ty <> sty` by metis_tac[same_memory_layout_reflexive] >>
  simp[compile_store_memory_def]
QED

Theorem ifexp_call_annotation_widens:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args dret) es ==>
  type_widens_to env.type_defs
    (ce.ce_func_return_type (nsid_to_string fid)) ann
Proof
  strip_tac >>
  `?sig. FLOOKUP env.fn_sigs fid = SOME sig /\
     type_widens_to env.type_defs sig.ret_ty ann` by
    (Cases_on `fid` >> gvs[expr_body_pre_def, well_typed_expr_def] >> metis_tac[]) >>
  drule_all ifexp_internal_call_return_bridge >> simp[]
QED

Theorem ifexp_none_call_not_allocating:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args dret) es /\
  ce.ce_func_return_type (nsid_to_string fid) = NoneT ==>
  same_memory_layout ce (lowered_value_type ce (Call ann (IntCall fid) args dret)) ann
Proof
  strip_tac >> drule_all ifexp_call_annotation_widens >>
  simp[vyperTypeArgFitsTheory.type_widens_to_NoneT] >> strip_tac >>
  gvs[lowered_value_type_def, same_memory_layout_reflexive]
QED

Theorem ifexp_residual_zero_call_extent:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args dret) es /\
  ce.ce_func_info (nsid_to_string fid) = (0,0,pvs) /\
  ~same_memory_layout ce (lowered_value_type ce (Call ann (IntCall fid) args dret)) ann ==>
  ce.ce_func_return_type (nsid_to_string fid) <> NoneT /\
  type_memory_bytes ce (ce.ce_func_return_type (nsid_to_string fid)) = 0 /\
  type_widens_to env.type_defs (ce.ce_func_return_type (nsid_to_string fid)) ann
Proof
  strip_tac >>
  `ce.ce_func_return_type (nsid_to_string fid) <> NoneT` by
    metis_tac[ifexp_none_call_not_allocating] >>
  drule_all ifexp_internal_call_zero_extent >> strip_tac >> gvs[] >>
  drule_all ifexp_call_annotation_widens >> simp[]
QED

(* The checked residual has zero physical extent, but its annotation is
   connected only by type_widens_to. A zero-extent widening/layout boundary
   is still needed before reducing the nonbytes typed-store dispatch. No
   positive-length read from Lit 0w is justified by these facts. *)
