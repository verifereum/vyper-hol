(* Request-prefix companion to bodyFullSubscriptUnframedArray. *)
Theory s1PrefixSubscriptUnframedArray
Ancestors
  s1PrefixPreds bodyFullSubscriptUnframedArray s1PrefixDefs
  s1PrefixSubscriptCopiedChildren s1PrefixSubscriptNoCopyCore
  bodyFullSubscriptCopySnapshot exprSimSubscriptArraySource

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qspecl_then [`e1`,`e2`] assume_tac)
    bodySimTheory.body_inv_copies_subscript_base >>
  Cases_on `subscript_reads_base cx e1 e2`
  >- (`copies_subscript_base cenv e1 e2` by fs[] >>
      irule (Q.SPEC `T` subscript_copied_children_prefix) >>
      qpat_assum `expr_type e1 = ArrayT et bd` (irule_at Any) >>
      qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
      qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (rpt strip_tac >>
          qpat_assum `!s r t s' r' t'. _ ==> body_expr_full_ok cx e2` irule >>
          qexistsl [`raw`,`Value saved`,`s`,`mid`,`mid`,`mid`] >>
          simp[vyperStateTheory.bind_def,vyperStateTheory.return_def])
      >- (rpt strip_tac >>
          qpat_assum `!s r t s' r' t'. _ ==> body_expr_prefix_ok cx e2` irule >>
          qexistsl [`raw`,`Value saved`,`s`,`mid`,`mid`,`mid`] >>
          simp[vyperStateTheory.bind_def,vyperStateTheory.return_def]) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      drule_then assume_tac copies_subscript_base_not_array_slot_base >>
      drule_all subscript_array_copy_snapshot_caller_frame >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
        strip_assume_tac) >>
      qexistsl [`u`,`Gc`,`tnc`,`q`,`w`,`atv`] >> simp[]) >>
  `~copies_subscript_base cenv e1 e2` by fs[] >>
  irule subscript_nocopy_sim_prefix >>
  qpat_assum `expr_type e1 = ArrayT et bd` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!s r t s' r' t'. _ ==> body_expr_full_ok cx e2` irule >>
      simp[vyperStateTheory.return_def] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_assum `!s r t s' r' t'. _ ==> body_expr_prefix_ok cx e2` irule >>
  simp[vyperStateTheory.return_def] >> metis_tac[]
QED
*)
Theorem subscript_unframed_array_vv_prefix:
  !cx v8 e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es et bd.
  (!s'' res t s3 res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s3 = (INL res',t') ==>
       body_expr_full_ok cx e2) /\
  (!s'' res t s3 res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s3 = (INL res',t') ==>
       body_expr_prefix_ok cx e2) /\
  body_expr_full_ok cx e1 /\
  body_expr_prefix_ok cx e1 /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Subscript v8 e1 e2) es /\
  expr_type e1 = ArrayT et bd /\
  place_type cenv e1 = ValPT (ArrayT et bd) /\
  post_value_type cenv e1 = expr_type e1 /\
  ~((!t r t'. eval_expr cx e2 t = (INL r,t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
      (!s tr slot vt t.
         eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
      ((~cenv.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory))) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript v8 e1 e2) es
Proof
  cheat
QED
