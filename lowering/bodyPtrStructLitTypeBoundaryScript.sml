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
   expr_post carries expr_val_rel and expr_val_at at the annotation, not a
   guarantee that an arbitrary AbiEncode annotation IS dynamic bytes.
   evaluate_type_builtin's successful AbiEncode returns BytesV, whereas
   compile_abi_encode_case alone does not state that annotation restriction.
   This remaining annotation/typing interface must not be silently assumed.
   Literal forms in the exhaustive split already have the required types. *)
Theory bodyPtrStructLitTypeBoundary
Ancestors exprLowering valueEncoding bodyPtrDefs vyperAST

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
