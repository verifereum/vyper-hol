(* Static origins of staged memory arguments, independent of execution. *)
Theory bodyIntCallStageOrigin
Ancestors
  bodyIntCallStageCompile exprLowering exprLoweringProps loweringHalt context
  compileEnv
  list arithmetic
Libs
  monadsyntax

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem stage_intcall_args_length:
  !es flags tys a ops b.
    compile_stage_intcall_args cfn ce es flags tys a = (ops,b) ==>
    LENGTH ops = LENGTH es
Proof
  Induct_on `es` >> rpt gen_tac
  >- simp[compile_stage_intcall_args_def, comp_return_def] >>
  namedCases_on `flags` ["", "flag fs"] >>
  namedCases_on `tys` ["", "ty ts"] >>
  TRY (Cases_on `flag`) >>
  simp[Once compile_stage_intcall_args_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem stage_intcall_memory_origin:
  !es flags tys a ops b i.
    (!ce' ty' e' s'. ci_mono s' (SND (cfn ce' ty' e' s'))) /\
    LENGTH es <= LENGTH flags /\ LENGTH es <= LENGTH tys /\
    compile_stage_intcall_args cfn ce es flags tys a = (ops,b) /\
    i < LENGTH es /\ ~EL i flags ==>
    ?pre post buf.
      compile_alloc_buffer (MAX 32 (type_memory_bytes ce (EL i tys))) pre =
        (buf,post) /\
      EL i ops = buf.buf_operand /\
      a.cs_next_id <= pre.cs_next_id /\ pre.cs_next_id < b.cs_next_id
Proof
  Induct_on `es` >> rpt gen_tac >- simp[] >>
  namedCases_on `flags` ["", "flag fs"] >>
  namedCases_on `tys` ["", "ty ts"] >> simp[] >> strip_tac >>
  Cases_on `flag`
  >- (drule intcall_stage_word_parts >> strip_tac >> gvs[] >>
      Cases_on `i` >> gvs[] >> rename1 `n < LENGTH es` >>
      `ci_mono a s1` by
        (first_assum (qspecl_then [`ce`,`expr_type h`,`h`,`a`] mp_tac) >>
         simp[]) >>
      `ci_mono s1 sm` by
        (qspecl_then [`ce`,`vv`,`s1`] mp_tac ci_mono_unwrap_value >> simp[]) >>
      last_x_assum (qspecl_then [`fs`,`ts`,`sm`,`rest`,`b`,`n`] mp_tac) >>
      simp[] >> strip_tac >> gvs[ci_mono_def] >>
      qexistsl_tac [`pre`,`post`,`buf`] >> simp[]) >>
  drule intcall_stage_memory_parts >> strip_tac >> gvs[] >>
  `ci_mono a s1` by
    (first_assum (qspecl_then [`ce`,`expr_type h`,`h`,`a`] mp_tac) >> simp[]) >>
  `ci_mono s2 s3` by
    (qspecl_then [`ce`,`vv`,`s2`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `ci_mono s3 s4` by
    (qspecl_then [`ce`,`op`,`buf.buf_operand`,`ty`,`vv_type vv`,`s3`] mp_tac
       ci_mono_compile_store_memory >> simp[]) >>
  `ci_mono s4 b` by
    (qspecl_then [`cfn`,`ce`,`es`,`fs`,`ts`,`s4`] mp_tac
       ci_mono_compile_stage_intcall_args >> simp[]) >>
  `s2.cs_next_id = s1.cs_next_id + 1` by metis_tac[compile_alloc_buffer_parts] >>
  Cases_on `i` >> gvs[]
  >- (gvs[ci_mono_def] >> qexistsl_tac [`s1`,`s2`,`buf`] >> simp[]) >>
  rename1 `n < LENGTH es` >>
  last_x_assum (qspecl_then [`fs`,`ts`,`s4`,`rest`,`b`,`n`] mp_tac) >>
  simp[] >> strip_tac >> gvs[ci_mono_def] >>
  qexistsl_tac [`pre`,`post`,`buf'`] >> simp[]
QED
