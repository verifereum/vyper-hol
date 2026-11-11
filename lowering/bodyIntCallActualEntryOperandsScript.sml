(* Old operands survive actual internal entry independently of live scopes. *)
Theory bodyIntCallActualEntryOperands
Ancestors
  bodyIntCallActualEntrySemantic bodyIntCallBodyTrace bodyIntCallActualEntryResource
  intCallCallee moduleLowering context emitHelper compileEnv loweringStateRelDefs exprLoweringProps
  finite_map list pair rich_list

Theorem materialize_internal_params_excludes_old:
  !caps ce st ce' st' x.
    materialize_internal_params ce caps st = (ce',st') /\
    not_fresh_at st x /\
    EVERY (\c. SND (SND c) <> Var x) caps /\
    (!n sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar (Var x) sz)) ==>
    !n sz. FLOOKUP ce'.ce_vars n <> SOME (PtrVar (Var x) sz)
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> strip_tac >>
  Cases_on `h1` >>
  namedCases_on `FLOOKUP ce.ce_vars h0` ["", "loc"] >>
  TRY (Cases_on `loc`) >>
  gvs[materialize_internal_params_def, AllCaseEqs(),
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  qpat_x_assum `!ce st ce' st' x. _` irule >>
  simp[] >>
  qpat_assum `materialize_internal_params _ _ _ = _`
    (irule_at (Pat `materialize_internal_params _ _ _ = _`)) >>
  gvs[not_fresh_at_def, FLOOKUP_UPDATE] >>
  rw[] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED
