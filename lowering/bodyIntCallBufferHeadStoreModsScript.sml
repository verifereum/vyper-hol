(* Execute the store on the reached unwrap cut, at the actual allocated row. *)
Theory bodyIntCallBufferHeadStoreMods
Ancestors
  bodyIntCallBufferHeadCutsMods bodyIntCallBufferHeadSpecMods
  bodyIntCallBufferStoreCutMods bodyIntCallArgWordStoreMods
  bodyIntCallArgBytesStoreMods bodyIntCallArgAggregateStoreMods
  exprSimFullBundleProps exprSimConvertBytes exprLoweringProps
  exprLowering context compileEnv emitHelper vyperValue vyperTypeSystem
  bodyFullPredsMods vyperAST venomInst words arithmetic

Theorem store_bytes_classification[local]:
  (case ty of BaseT (BytesT (Dynamic _)) => T
            | BaseT (StringT _) => T | _ => F) = is_bytestring_type ty
Proof
  Cases_on `ty` >> simp[bytestring_type_cases] >>
  rename1 `(?n. bt = BytesT (Dynamic n)) \/ _` >>
  Cases_on `bt` >> simp[] >> Cases_on `b` >> simp[]
QED

Theorem classified_store_growth[local]:
  (if is_word_type ty then emit_void MSTORE [dst;opn]
   else if is_bytestring_type ty then
     (do compile_store_bytestring opn dst; return () od)
   else compile_store_memory ce opn dst ty sty) cu = ((),cs) ==>
  cu.cs_next_id <= cs.cs_next_id /\ cu.cs_next_var <= cs.cs_next_var
Proof
  qsuff_tac `ci_mono cu (SND ((if is_word_type ty then emit_void MSTORE [dst;opn]
      else if is_bytestring_type ty then
        (do compile_store_bytestring opn dst; return () od)
      else compile_store_memory ce opn dst ty sty) cu))`
  >- (strip_tac >> strip_tac >> fs[ci_mono_def]) >>
  Cases_on `is_word_type ty` >- simp[ci_mono_emit_void] >>
  Cases_on `is_bytestring_type ty` >-
    (mp_tac (Q.SPECL [`opn`,`dst`,`cu`] ci_mono_compile_store_bytestring) >>
     Cases_on `compile_store_bytestring opn dst cu` >>
     simp[comp_ignore_bind_def,comp_bind_def,comp_return_def]) >>
  simp[ci_mono_compile_store_memory]
QED

(* Only an aggregate store uses the two ambient source invariants. *)
Theorem store_branch_context[local]:
  (if w then p else if b then q else a1 /\ a2 /\ r1 /\ r2) <=>
  ((~w /\ ~b ==> a1 /\ a2) /\ (if w then p else if b then q else r1 /\ r2))
Proof
  Cases_on `w` >> Cases_on `b` >> simp[CONJ_ASSOC]
QED

(* The buffer equality and reached source invariant are projections of A. *)
Theorem intcall_buffer_head_store_mods:
  intcall_buffer_head_input_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods exps src tops cenv cx env st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn)
    pin (ops,ws,vals,ptys,pflags) e dty (shi,vv,ci,shci,buf,ca,opn,cu,cs) /\
  intcall_buffer_head_unwrap_post_mods (DF,lo,d,ctx,shadow_ctx,PG,func) cenv cx st0
    (si,esi,s,G,tn) (ca,mid,a,Ga,ta) (cu,mid,z,Gz,tz)
    e dty raw vv ci.cs_next_id dst addr cap v opn /\
  buf.buf_operand = Var dst /\ expr_sim_inv_mods mods cenv cx env mid ==>
  ?t Gf tf nw.
    intcall_buffer_head_store_post_mods (lo,ctx,shadow_ctx,PG,func) cenv cx
      (cu,mid,z,Gz,tz) (cs,mid,t,Gf,tf) ci.cs_next_id dst addr cap v dty nw
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (CONJUNCTS_THEN2 kall_tac
    (qx_choosel_then [`stv`,`dtv`] assume_tac)) intcall_buffer_head_store_input_mods >>
  qhdtm_x_assum `intcall_buffer_head_input_mods`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [intcall_buffer_head_input_mods_def,expr_sim_full_code_def,store_bytes_classification]) >>
  qhdtm_x_assum `intcall_buffer_head_unwrap_post_mods`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [intcall_buffer_head_unwrap_post_mods_def,REFL_CLAUSE]) >>
  qpat_x_assum `?stv dtv. _` kall_tac >>
  drule_then strip_assume_tac classified_store_growth >>
  `w2n (n2w addr : bytes32) = addr` by
    (simp[w2n_n2w_compute] >> decide_tac) >>
  qpat_x_assum `(if is_word_type _ then _ else _) cu = _`
    (fn th => qpat_assum `buf.buf_operand = Var dst`
      (assume_tac o (fn eq => PURE_REWRITE_RULE [eq] th))) >>
  drule_at (Pat `(if is_word_type _ then _ else _) _ = _`)
    (MATCH_MP intcall_buffer_store_cut_mods
      (LIST_CONJ [GEN_ALL intcall_arg_word_store_mods,
                  GEN_ALL intcall_arg_bytes_store_mods,
                  GEN_ALL intcall_arg_aggregate_store_mods])) >>
  disch_then (drule_at (Pat `if is_word_type _ then _ else _`) o
    PURE_REWRITE_RULE [store_branch_context]) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  `~is_word_type dty /\ ~is_bytestring_type dty ==>
   contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env mid`
    by simp[] >>
  disch_then (drule_at (Pat `~is_word_type _ /\ ~is_bytestring_type _ ==> _`)) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn th => qpat_assum `w2n (n2w addr : bytes32) = addr`
    (strip_assume_tac o (fn eq => PURE_REWRITE_RULE [eq] th))) >>
  map_every qexists_tac [`t`, `Gf`, `tf`, `nw`] >>
  simp[intcall_buffer_head_store_post_mods_def] >>
  fs[]
QED
