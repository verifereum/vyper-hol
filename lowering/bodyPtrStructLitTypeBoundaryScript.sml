(* Live representations ignore dynamic bounds; capacity and source typing
   remain separate obligations.  No new representation definitions.

   val_in_memory_def tests neither StringT bounds nor dynamic BytesT bounds,
   so the transfer lemmas below require NO length inequality.  For a string
   literal instantiate ty1 at its annotation, ty2 at StringT (LENGTH s).
   For a dynamic bytes literal instantiate n at its annotation, k at LENGTH bs.
   For AbiEncode with dynamic-bytes annotation, instantiate k at the bound
   computed by lowered_value_type_def; the same lemma applies to every output
   payload, independently of whether its length fits either capacity.

   These are representation transfers, not pointer simulations.  The S1
   expr_post carries expr_val_rel and expr_val_at at the annotation.
   structlit_abi_encode_annotation below proves that current source typing
   restricts AbiEncode annotations to dynamic bytes. Its successful source
   result is BytesV; the transfer corollary concerns that constructor only.
   Literal forms in the exhaustive split already have the required types.
   Evaluated types must exist: evaluate_type also checks size bounds. *)
Theory bodyPtrStructLitTypeBoundary
Ancestors exprLowering valueEncoding bodyPtrDefs vyperAST vyperTypeSystem vyperValue

Theorem robust_string_memory_type_irrelevant:
  !tn mem s a ty1 ty2.
    (!m. mem_agree_outside tn.t_mem mem m ==>
         val_in_memory ty1 (StringV s) a m) <=>
    (!m. mem_agree_outside tn.t_mem mem m ==>
         val_in_memory ty2 (StringV s) a m)
Proof
  simp[val_in_memory_def]
QED

Theorem robust_dynamic_bytes_memory_bound_irrelevant:
  !tn mem bs a n k.
    (!m. mem_agree_outside tn.t_mem mem m ==>
         val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) a m) <=>
    (!m. mem_agree_outside tn.t_mem mem m ==>
         val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) a m)
Proof
  simp[val_in_memory_def]
QED

Theorem lowered_value_type_exceptional:
  !cenv e.
    lowered_value_type cenv e <> expr_type e ==>
    (?n s. e = Literal (BaseT (StringT n)) (StringL s)) \/
    (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) \/
    (?ty ensure method_id tys args.
       e = TypeBuiltin ty (AbiEncode ensure method_id) tys args) \/
    (?ty fid args d. e = Call ty (IntCall fid) args d)
Proof
  Cases_on `e` >> simp[lowered_value_type_def]
  >~ [`Literal t l`]
  >- (Cases_on `t` >> simp[lowered_value_type_def, expr_type_def] >>
      rename1 `BaseT b` >> Cases_on `b` >>
      simp[lowered_value_type_def, expr_type_def] >>
      Cases_on `l` >> simp[lowered_value_type_def, expr_type_def] >>
      Cases_on `b'` >> simp[lowered_value_type_def, expr_type_def])
  >~ [`TypeBuiltin t1 t0 t l`]
  >- (Cases_on `t0` >> simp[lowered_value_type_def, expr_type_def]) >>
  Cases_on `c` >> simp[lowered_value_type_def, expr_type_def]
QED

Theorem structlit_abi_encode_annotation:
  well_typed_expr env (TypeBuiltin ty (AbiEncode ensure mid) target args) ==>
  ?n. ty = BaseT (BytesT (Dynamic n))
Proof
  simp[well_typed_expr_def, type_builtin_result_ok_def] >> metis_tac[]
QED

(* Type evaluation is partial (including slot-size bounds). Transfer claims
   representation equality when both evaluated types exist, not capacity. *)
Theorem structlit_abi_encode_representation:
  well_typed_expr env (TypeBuiltin ty (AbiEncode ensure mid) target args) /\
  evaluate_type tenv ty = SOME source_ty /\
  evaluate_type tenv
    (lowered_value_type cenv (TypeBuiltin ty (AbiEncode ensure mid) target args)) =
    SOME lowered_ty ==>
  ((!m. mem_agree_outside tn.t_mem mem m ==>
       val_in_memory source_ty (BytesV bs) a m) <=>
   (!m. mem_agree_outside tn.t_mem mem m ==>
       val_in_memory lowered_ty (BytesV bs) a m))
Proof
  strip_tac >> drule structlit_abi_encode_annotation >> strip_tac >>
  gvs[lowered_value_type_def, evaluate_type_def, AllCaseEqs()] >>
  simp[robust_dynamic_bytes_memory_bound_irrelevant]
QED
