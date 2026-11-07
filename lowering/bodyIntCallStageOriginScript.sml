(* Static origins of staged memory arguments, independent of execution. *)
Theory bodyIntCallStageOrigin
Ancestors
  exprLowering exprLoweringProps loweringHalt context compileEnv
  list arithmetic
Libs
  monadsyntax

Theorem stage_intcall_args_length:
  !vals flags tys a ops b.
    LENGTH vals = LENGTH flags /\ LENGTH vals = LENGTH tys /\
    compile_stage_intcall_args ce vals flags tys a = (ops,b) ==>
    LENGTH ops = LENGTH vals
Proof
  Induct_on `vals` >> rpt gen_tac
  >- simp[compile_stage_intcall_args_def, comp_return_def] >>
  Cases_on `flags` >> Cases_on `tys` >> simp[] >>
  rename1 `compile_stage_intcall_args ce (h::vals) (flag::flags) (ty::tys)` >>
  Cases_on `flag` >>
  simp[Once compile_stage_intcall_args_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem stage_intcall_memory_origin:
  !vals flags tys a ops b i.
    LENGTH vals = LENGTH flags /\ LENGTH vals = LENGTH tys /\
    compile_stage_intcall_args ce vals flags tys a = (ops,b) /\
    i < LENGTH vals /\ ~EL i flags ==>
    ?pre post buf.
      compile_alloc_buffer (MAX 32 (type_memory_bytes ce (EL i tys))) pre =
        (buf,post) /\
      EL i ops = buf.buf_operand /\
      a.cs_next_id <= pre.cs_next_id /\ pre.cs_next_id < b.cs_next_id
Proof
  Induct_on `vals` >> rpt gen_tac >- simp[] >>
  Cases_on `flags` >> Cases_on `tys` >> simp[] >>
  rename1 `compile_stage_intcall_args ce (h::vals) (flag::flags) (ty::tys)` >>
  Cases_on `flag` >>
  simp[Once compile_stage_intcall_args_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> rpt strip_tac >> gvs[]
  >- (Cases_on `i` >> gvs[] >>
      qspecl_then [`ce`, `h`, `a`] mp_tac ci_mono_unwrap_value >>
      simp[ci_mono_def] >> strip_tac >>
      first_x_assum (drule_at (Pat `compile_stage_intcall_args _ _ _ _ _ = _`)) >>
      simp[] >> disch_then drule_all >> strip_tac >>
      goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  rename1 `compile_alloc_buffer _ pre = (buf,post)` >>
  rename1 `compile_stage_intcall_args ce vals flags tys tail = (rest,b)` >>
  `a.cs_next_id <= pre.cs_next_id` by
    (qspecl_then [`ce`, `h`, `a`] mp_tac ci_mono_unwrap_value >>
     simp[ci_mono_def]) >>
  `post.cs_next_id = pre.cs_next_id + 1` by
    metis_tac[compile_alloc_buffer_parts] >>
  `tail.cs_next_id <= b.cs_next_id` by
    (qspecl_then [`ce`, `vals`, `flags`, `tys`, `tail`] mp_tac
       ci_mono_compile_stage_intcall_args >> simp[ci_mono_def]) >>
  `post.cs_next_id <= tail.cs_next_id` by suspend "store_mono" >>
  Cases_on `i` >> gvs[]
  >- (goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  first_x_assum (drule_at (Pat `compile_stage_intcall_args _ _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Resume stage_intcall_memory_origin[store_mono]:
  Cases_on `is_word_type ty` >> fs[]
  >- (qspecl_then [`MSTORE`, `[buf.buf_operand; val_op]`, `post`]
        mp_tac ci_mono_emit_void >> simp[ci_mono_def]) >>
  qpat_x_assum `(if _ then _ else _) post = _` mp_tac >>
  IF_CASES_TAC >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
  >- (rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
      qspecl_then [`val_op`, `buf.buf_operand`, `post`]
        mp_tac ci_mono_compile_store_bytestring >> simp[ci_mono_def]) >>
  strip_tac >> metis_tac[ci_mono_compile_store_memory, ci_mono_def, pairTheory.SND]
QED

Finalise stage_intcall_memory_origin
