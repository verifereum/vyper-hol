(* Multi-block code boundary for the memory-to-memory assignment path. *)
Theory annassignRelayoutCode
Ancestors
  stmtLowering exprLowering exprLoweringProps fragExec context compileEnv
Libs monadsyntax

Theorem assign_memory_relayout_code:
  !cenv dst src dty sty n sa sb func.
    compile_assign_value cenv dst LocMemory src F (SOME LocMemory)
      dty sty n sa = ((),sb) /\ fn_has_code sa sb func ==>
    ?buf sm sc.
      compile_alloc_buffer (type_memory_bytes cenv sty) sa = (buf,sm) /\
      compile_copy_memory buf.buf_operand src (type_memory_bytes cenv sty) sm = ((),sc) /\
      compile_store_memory cenv buf.buf_operand dst dty sty sc = ((),sb) /\
      ci_mono sa sm /\ ci_mono sm sc /\ ci_mono sc sb /\
      fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc sb func
Proof
  rpt strip_tac >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv sty) sa` >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  Cases_on `compile_copy_memory buf.buf_operand src (type_memory_bytes cenv sty) sm` >>
  rename1 `compile_copy_memory _ _ _ sm = (u,sc)` >> Cases_on `u` >>
  gvs[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sc` by metis_tac[ci_mono_compile_copy_memory, pairTheory.SND] >>
  `ci_mono sc sb` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  simp[] >> fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]
QED

(* Even an absent return buffer is representable: the non-staging branch
   must remain available until call metadata proves a buffer was allocated. *)
Theorem internal_call_location_cases:
  !cfn cenv ret_ty ty fid args drv sa vv sb.
    compile_call cfn cenv ret_ty ty (IntCall fid) args drv sa = (vv,sb) ==>
    vv_location vv = NONE \/ vv_location vv = SOME LocMemory
Proof
  rpt gen_tac >>
  Cases_on `cenv.ce_func_info (nsid_to_string fid)` >>
  rename1 `cenv.ce_func_info _ = (nret,metadata)` >> Cases_on `metadata` >>
  simp[Once compile_call_def, LET_THM, pairTheory.UNCURRY] >>
  rpt IF_CASES_TAC >>
  simp[LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >> gvs[AllCaseEqs(), vv_location_def, base_ptr_def]
QED
