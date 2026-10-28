(* TOP-LEVEL: actual Log data stores compose in a containing function.
   Prefix offsets use the declared field footprints, including zero sizes.
   Helpers expose append structure and the code of each constituent store. *)
Theory logStoreComposition
Ancestors
  typedCopyAppend copyAppend eventLoweringStructure stmtLowering compileEnv context
  fragExec fragBlockPath emitHelper list rich_list pair arithmetic

val log_append_rules =
  [cs_appends_return, cs_appends_emit_helpers, cs_appends_compile_store_memory];

fun log_append_tac () = rpt (FIRST
  [CHANGED_TAC (asm_simp_tac (srw_ss()) log_append_rules),
   irule cs_appends_bind >> conj_tac >> rpt gen_tac,
   irule cs_appends_ignore_bind >> conj_tac]);

Theorem cs_appends_compile_log_store_data:
  !cenv ops types buf offset.
    cs_appends (compile_log_store_data cenv ops types buf offset)
Proof
  Induct_on `ops` >> Cases_on `types` >> rpt gen_tac >>
  simp_tac bool_ss [Once compile_log_store_data_def, LET_THM] >> log_append_tac ()
QED

Theorem compile_log_store_data_extends:
  !cenv ops types buf offset cs ret cs'.
    compile_log_store_data cenv ops types buf offset cs = (ret,cs') ==> cs_extends cs cs'
Proof
  rpt strip_tac >>
  `cs_appends (compile_log_store_data cenv ops types buf offset)` by
    simp[cs_appends_compile_log_store_data] >> fs[cs_appends_def]
QED

Theorem compile_log_store_data_split_code:
  !cenv x xs ty tys buf offset cs ret cs' func.
    compile_log_store_data cenv (x::xs) (ty::tys) buf offset cs = (ret,cs') /\
    fn_has_code cs cs' func ==>
    ?mid. compile_log_store_data cenv [x] [ty] buf offset cs = ((),mid) /\
      compile_log_store_data cenv xs tys buf
        (offset + type_memory_bytes cenv ty) mid = (ret,cs') /\
      fn_has_code cs mid func /\ fn_has_code mid cs' func
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_log_store_data _ _ _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [compile_log_store_data_split]) >> strip_tac >>
  `cs_extends cs mid` by
    (mp_tac (Q.SPECL [`cenv`, `[x]`, `[ty]`, `buf`, `offset`, `cs`, `()`, `mid`]
      compile_log_store_data_extends) >> simp[]) >>
  `cs_extends mid cs'` by
    (mp_tac (Q.SPECL [`cenv`, `xs`, `tys`, `buf`, `offset + type_memory_bytes cenv ty`,
      `mid`, `ret`, `cs'`] compile_log_store_data_extends) >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >> qexists_tac `mid` >> simp[]
QED

Theorem compile_log_store_data_frag_seq:
  !ctx cenv x xs ty tys buf offset cs mid cs' P Q Q' R.
    compile_log_store_data cenv [x] [ty] buf offset cs = ((),mid) /\
    compile_log_store_data cenv xs tys buf
      (offset + type_memory_bytes cenv ty) mid = ((),cs') /\
    frag_exec ctx cs mid P Q R /\ frag_exec ctx mid cs' Q Q' R ==>
    compile_log_store_data cenv (x::xs) (ty::tys) buf offset cs = ((),cs') /\
    frag_exec ctx cs cs' P Q' R
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (CONV_TAC (ONCE_REWRITE_CONV [compile_log_store_data_split]) >>
      qexists_tac `mid` >> simp[]) >>
  `cs_extends cs mid` by
    (mp_tac (Q.SPECL [`cenv`, `[x]`, `[ty]`, `buf`, `offset`, `cs`, `()`, `mid`]
      compile_log_store_data_extends) >> simp[]) >>
  `cs_extends mid cs'` by
    (mp_tac (Q.SPECL [`cenv`, `xs`, `tys`, `buf`, `offset + type_memory_bytes cenv ty`,
      `mid`, `()`, `cs'`] compile_log_store_data_extends) >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `cs`, `mid`, `cs'`, `P`, `Q`, `Q'`, `R`] frag_exec_seq) >> simp[]
QED

Theorem compile_log_store_data_append:
  !cenv prefix ftypes suffix stypes buf offset.
    LENGTH prefix = LENGTH ftypes ==>
    compile_log_store_data cenv (prefix ++ suffix) (ftypes ++ stypes) buf offset =
      comp_ignore_bind (compile_log_store_data cenv prefix ftypes buf offset)
        (compile_log_store_data cenv suffix stypes buf
          (offset + SUM (MAP (type_memory_bytes cenv) ftypes)))
Proof
  Induct_on `prefix` >> Cases_on `ftypes` >> rpt gen_tac >> simp[] >> rpt strip_tac >>
  simp[compile_log_store_data_def, comp_ignore_bind_def, comp_bind_def,
    comp_return_def, FUN_EQ_THM, LET_THM, pairTheory.UNCURRY]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed Log store-composition theorem: " ^ name)
  end) (DB.thms "logStoreComposition")
