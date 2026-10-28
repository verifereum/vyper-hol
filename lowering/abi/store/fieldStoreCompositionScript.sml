(* TOP-LEVEL: a Log field is its real address instruction followed by its
   typed memory store. Containment and execution contracts compose even
   when the store emits additional control-flow blocks. *)
Theory fieldStoreComposition
Ancestors
  compileAppendProps typedCopyAppend copyAppend stmtLowering context compileEnv
  emitHelper fragExec list pair

Theorem compile_log_store_field:
  !cenv src aty fty buf offset.
    compile_log_store_data cenv [(src,aty)] [fty] buf offset =
    comp_bind (emit_op ADD [buf; Lit (n2w offset)])
      (\dst. compile_store_memory cenv src dst fty aty)
Proof
  rpt gen_tac >>
  simp[compile_log_store_data_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, FUN_EQ_THM, LET_THM, pairTheory.UNCURRY] >> gen_tac >>
  Cases_on `compile_store_memory cenv src (FST (emit_op ADD [buf; Lit (n2w offset)] x))
    fty aty (SND (emit_op ADD [buf; Lit (n2w offset)] x))` >>
  rename1 `_ = (unit_result,next)` >> Cases_on `unit_result` >> simp[]
QED

Theorem compile_log_store_field_split:
  !cenv src aty fty buf offset cs ret cs'.
    compile_log_store_data cenv [(src,aty)] [fty] buf offset cs = (ret,cs') <=>
    ?dst mid. emit_op ADD [buf; Lit (n2w offset)] cs = (dst,mid) /\
      compile_store_memory cenv src dst fty aty mid = (ret,cs')
Proof
  rpt gen_tac >> rewrite_tac [compile_log_store_field] >>
  Cases_on `emit_op ADD [buf; Lit (n2w offset)] cs` >> simp[comp_bind_def]
QED

Theorem compile_log_store_field_contains:
  !cenv src aty fty buf offset cs ret cs' func.
    compile_log_store_data cenv [(src,aty)] [fty] buf offset cs = (ret,cs') /\
    fn_has_code cs cs' func ==>
    ?dst mid. emit_op ADD [buf; Lit (n2w offset)] cs = (dst,mid) /\
      compile_store_memory cenv src dst fty aty mid = (ret,cs') /\
      fn_has_code cs mid func /\ fn_has_code mid cs' func
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_log_store_data _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_log_store_field]) >> strip_tac >>
  mp_tac (Q.ISPECL [`emit_op ADD [buf; Lit (n2w offset)]`,
    `\dst. compile_store_memory cenv src dst fty aty`] compile_bind_contains) >>
  disch_then (qspecl_then [`cs`, `ret`, `cs'`, `func`] mp_tac) >>
  simp[cs_appends_emit_helpers, cs_appends_compile_store_memory]
QED

Theorem compile_log_store_field_frag_seq:
  !ctx cenv src aty fty buf offset dst cs mid cs' P Q Q' R.
    emit_op ADD [buf; Lit (n2w offset)] cs = (dst,mid) /\
    compile_store_memory cenv src dst fty aty mid = ((),cs') /\
    frag_exec ctx cs mid P Q R /\ frag_exec ctx mid cs' Q Q' R ==>
    compile_log_store_data cenv [(src,aty)] [fty] buf offset cs = ((),cs') /\
    frag_exec ctx cs cs' P Q' R
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rewrite_tac [compile_log_store_field_split] >> qexistsl_tac [`dst`, `mid`] >> simp[]) >>
  `cs_appends (emit_op ADD [buf; Lit (n2w offset)])` by simp[cs_appends_emit_helpers] >>
  `cs_extends cs mid` by (drule_all cs_appends_result_extends >> simp[]) >>
  `cs_extends mid cs'` by
    (mp_tac (Q.SPECL [`cenv`, `src`, `dst`, `fty`, `aty`] cs_appends_compile_store_memory) >>
     simp_tac bool_ss [cs_appends_def] >>
     disch_then (qspecl_then [`mid`, `()`, `cs'`] mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `cs`, `mid`, `cs'`, `P`, `Q`, `Q'`, `R`] frag_exec_seq) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed Log field-store composition theorem: " ^ name)
  end) (DB.thms "fieldStoreComposition")
