(* Source-facing length interfaces; operand admissibility is already exported
   as expr_body_pre_vv_gas_admissible by exprSimHyps. *)
Theory bodyPtrEnvBuiltinsLenSource
Ancestors
  exprSimHypsDefs exprSimHyps exprSimLen exprSimSource exprSimDefs exprLowering
  vyperInterpreter vyperTypeSystem vyperAST vyperState builtinSimple
  builtinProps vyperTyping compileEnv vyperContext exprLoweringProps
  emitHelperProps fragExec exprSimCopy gasExemptCert gasSummaryCompose
  context exprSimUnwrap

Theorem len_builtin_pre_shape:
  !cenv cx env ann args es.
    expr_body_pre cenv cx env (Builtin ann Len args) es ==>
    ?e. args = [e] /\ ann = BaseT (UintT 256) /\
        is_sized_type (expr_type e)
Proof
  rpt gen_tac >>
  simp[expr_body_pre_def, well_typed_expr_def,
       well_typed_builtin_app_def] >> strip_tac >>
  Cases_on `args` >> gvs[] >>
  rename1 `LENGTH rest = 0` >>
  Cases_on `rest` >> gvs[]
QED

Theorem len_builtin_eval:
  !cx ann e es.
    eval_expr cx (Builtin ann Len [e]) es =
    (do tv <- eval_expr cx e;
        n <- result_array_length cx tv;
        return (Value (IntV (&n))) od) es
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, builtin_args_length_ok_def, type_check_def,
       assert_def, bind_def, ignore_bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >>
  rename1 `(res, es1)` >> Cases_on `res` >> simp[bind_def] >>
  rename1 `result_array_length cx tv es1` >>
  Cases_on `result_array_length cx tv es1` >>
  rename1 `(res, es2)` >> Cases_on `res` >> simp[bind_def, return_def]
QED

Theorem len_builtin_source:
  !cx ann e.
    eval_expr cx (Builtin ann Len [e]) =
    bind (eval_expr cx e)
      (\tv. bind (result_array_length cx tv) (\n. return (Value (IntV (&n)))))
Proof
  rpt gen_tac >> simp[FUN_EQ_THM, len_builtin_eval]
QED

Theorem len_names_excluded[local]:
  !args. ~names_builtin Len args
Proof
  `!bt args. names_builtin bt args ==> bt <> Len` suffices_by
    metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem len_compile_split:
  !cenv ty ann e st.
    compile_expr cenv ty (Builtin ann Len [e]) st =
    UNCURRY (\vv st1. as_stack_val ann
      (compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
        (case vv_location vv of SOME l => l | NONE => LocMemory) st1))
      (compile_expr cenv ty e st)
Proof
  rpt gen_tac >>
  simp[compile_expr_builtin_dispatch, len_names_excluded] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[]
QED

Theorem len_read_place_obs[local]:
  !cx p st g.
    read_place cx p (st with gas_obs := g) =
    (FST (read_place cx p st), SND (read_place cx p st) with gas_obs := g)
Proof
  Cases_on `p`
  >- simp[read_place_def, len_rss_obs]
  >- (rpt gen_tac >>
      simp[read_place_def, bind_def, get_scopes_def, lift_option_type_def,
           lift_sum_def, return_def, raise_def] >>
      Cases_on `lookup_scopes s st.scopes` >> simp[raise_def] >>
      Cases_on `read_memory_path x l` >> simp[return_def, raise_def])
  >- (rpt gen_tac >>
      simp[read_place_def, bind_def, get_immutables_def, get_address_immutables_def,
           lift_option_type_def, lift_sum_def, return_def, raise_def] >>
      Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[raise_def] >>
      Cases_on `FLOOKUP (get_source_immutables o' x) s` >> simp[raise_def] >>
      Cases_on `evaluate_subscripts (FST x') (SND x') l` >> simp[return_def, raise_def])
QED

Theorem len_bind_observation:
  !m f.
    (!st g. m (st with gas_obs := g) = (FST (m st), SND (m st) with gas_obs := g)) /\
    (!v st g. f v (st with gas_obs := g) = (FST (f v st), SND (f v st) with gas_obs := g)) ==>
    !st g. bind m f (st with gas_obs := g) =
           (FST (bind m f st), SND (bind m f st) with gas_obs := g)
Proof
  rpt strip_tac >> simp[bind_def] >>
  Cases_on `m st` >> Cases_on `q` >> simp[]
QED

Theorem len_read_result_obs[local]:
  !cx res st g.
    read_result cx res (st with gas_obs := g) =
    (FST (read_result cx res st), SND (read_result cx res st) with gas_obs := g)
Proof
  Cases_on `res` >> simp[read_result_def, len_read_place_obs, return_def, raise_def]
QED

Theorem len_value_tail_obs[local]:
  !v st g.
    (case v of
       ArrayV (DynArrayV vs) => return (LENGTH vs)
     | ArrayV (SArrayV vs) => return (LENGTH vs)
     | ArrayV (TupleV vs) => return (LENGTH vs)
     | BytesV bs => return (LENGTH bs)
     | StringV bs => return (STRLEN bs)
     | _ => raise (Error (TypeError "result_array_length"))) (st with gas_obs := g) =
    (FST ((case v of
       ArrayV (DynArrayV vs) => return (LENGTH vs)
     | ArrayV (SArrayV vs) => return (LENGTH vs)
     | ArrayV (TupleV vs) => return (LENGTH vs)
     | BytesV bs => return (LENGTH bs)
     | StringV bs => return (STRLEN bs)
     | _ => raise (Error (TypeError "result_array_length"))) st),
     SND ((case v of
       ArrayV (DynArrayV vs) => return (LENGTH vs)
     | ArrayV (SArrayV vs) => return (LENGTH vs)
     | ArrayV (TupleV vs) => return (LENGTH vs)
     | BytesV bs => return (LENGTH bs)
     | StringV bs => return (STRLEN bs)
     | _ => raise (Error (TypeError "result_array_length"))) st) with gas_obs := g)
Proof
  Cases >> TRY (rename1 `ArrayV a` >> Cases_on `a`) >>
  simp[return_def, raise_def]
QED

Theorem len_result_length_observation:
  !cx tv st g.
    result_array_length cx tv (st with gas_obs := g) =
    (FST (result_array_length cx tv st),
     SND (result_array_length cx tv st) with gas_obs := g)
Proof
  gen_tac >> gen_tac >>
  Cases_on `tv` >> TRY (rename1 `PlaceR p` >> Cases_on `p`) >>
  TRY (rename1 `StoragePlace tr sl tvv` >> Cases_on `tvv` >>
       TRY (rename1 `ArrayTV tv0 bd` >> Cases_on `bd`)) >>
  simp[result_array_length_def, return_def] >>
  TRY (irule len_bind_observation >>
       simp[len_read_result_obs, len_value_tail_obs, return_def, raise_def] >> NO_TAC) >>
  rpt gen_tac >> simp[bind_def, len_gsb_obs] >>
  Cases_on `get_storage_backend cx tr st` >> Cases_on `q` >> simp[return_def]
QED

Theorem len_builtin_load_extends:
  !ctor imm pop loc sa op sb.
    compile_builtin_len ctor imm pop loc sa = (op,sb) ==> cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc = LocCode /\ ctor`
  >- (gvs[compile_builtin_len_def, compile_ptr_load_def] >>
      metis_tac[compile_imm_load_word_appends, cs_appends_def]) >>
  Cases_on `loc` >>
  gvs[compile_builtin_len_def, compile_ptr_load_def,
      compile_imm_load_word_runtime] >>
  drule emitted_insts_emit_op >> drule emit_op_extends >> rpt strip_tac >>
  irule cs_extends_same_block >> gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem len_builtin_exempt_cert:
  !memory tops p cx ann e start marks out endpoint.
    gas_exempt_cert memory tops p (ignore_bind (eval_expr cx e) (return ()))
      start marks out endpoint ==>
    gas_exempt_cert memory tops p
      (ignore_bind (eval_expr cx (Builtin ann Len [e])) (return ()))
      start marks out endpoint
Proof
  rpt strip_tac >> simp[len_builtin_source] >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  `ignore_bind
    (bind (eval_expr cx e)
      (\tv. bind (result_array_length cx tv) (\n. return (Value (IntV (&n))))))
    (return ()) =
   bind (eval_expr cx e)
     (\tv. ignore_bind (bind (result_array_length cx tv)
              (\n. return (Value (IntV (&n))))) (return ()))` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[] >>
     Cases_on `bind (result_array_length cx x') (\n. return (Value (IntV (&n)))) r` >>
     simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_result >> simp[]
QED
