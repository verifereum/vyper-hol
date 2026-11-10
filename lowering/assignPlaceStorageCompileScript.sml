Theory assignPlaceStorageCompile
Ancestors
  placeStoreDynPrepare placeStoreStorage exprLoweringProps stmtLoweringMono
  entryArgPtrs compileEnv stmtLowering loweringPosts
  loweringHalt exprSimTypedAlloc fragExec
Libs monadsyntax

Theorem assign_place_storage_normalize_compile:
  compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
     | _ => NONE) (type_memory_bytes cenv dty) sa = ((),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  type_memory_bytes cenv dty = type_memory_size dtv /\ fn_has_code sa sb func ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes cenv dty) sa = (buf,sm) /\
    compile_store_memory_typed cenv buf.buf_operand dty op sty sm = ((),sn) /\
    (case dty of ArrayT et (Dynamic n) =>
       compile_dynarray_to_storage buf.buf_operand dst
         ((type_memory_bytes cenv et + 31) DIV 32) (type_memory_bytes cenv et)
         (loc = LocTransient) sn = ((),sb)
     | _ => if type_memory_size dtv <= 32 then
         ?loaded sd. emit_op MLOAD [buf.buf_operand] sn = (loaded,sd) /\
           emit_void (if loc = LocTransient then TSTORE else SSTORE)
             [dst;loaded] sd = ((),sb)
       else ?r. (if loc = LocTransient then compile_memory_to_transient
                 else compile_memory_to_storage)
         buf.buf_operand dst (type_memory_size dtv DIV 32) sn = (r,sb)) /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\
    fn_has_code sa sn func /\ fn_has_code sn sb func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv dty))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qsuff_tac `?buf sm sn.
    compile_alloc_buffer (type_memory_bytes cenv dty) sa = (buf,sm) /\
    compile_store_memory_typed cenv buf.buf_operand dty op sty sm = ((),sn) /\
    ((?et n. dty = ArrayT et (Dynamic n) /\
       compile_dynarray_to_storage buf.buf_operand dst
         ((type_memory_bytes cenv et + 31) DIV 32) (type_memory_bytes cenv et)
         (loc = LocTransient) sn = ((),sb)) \/
     ((!et n. dty <> ArrayT et (Dynamic n)) /\
      (if type_memory_size dtv <= 32 then
        ?loaded sd. emit_op MLOAD [buf.buf_operand] sn = (loaded,sd) /\
          emit_void (if loc = LocTransient then TSTORE else SSTORE) [dst;loaded] sd = ((),sb)
       else ?r. (if loc = LocTransient then compile_memory_to_transient else compile_memory_to_storage)
         buf.buf_operand dst (type_memory_size dtv DIV 32) sn = (r,sb))))`
  >- suspend "intervals" >>
  suspend "cut"
QED

Resume assign_place_storage_normalize_compile[cut]:
  Cases_on `?et n. dty = ArrayT et (Dynamic n)`
  >- (pop_assum strip_assume_tac >> gvs[is_word_type_def] >>
      drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)
        place_dyn_assign_compile_cut >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
      simp[comp_bind_def, comp_return_def] >>
      Cases_on `compile_alloc_buffer (type_memory_size dtv) sa` >>
      rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
      Cases_on `compile_store_memory_typed cenv buf.buf_operand (ArrayT et (Dynamic n)) op sty sm` >>
      rename1 `compile_store_memory_typed _ _ _ _ _ _ = (unitv,sn)` >>
      Cases_on `unitv` >> simp[] >> strip_tac >> gvs[] >>
      qexistsl_tac [`buf`, `sm`, `sn`] >> simp[]) >>
  `!et n. dty <> ArrayT et (Dynamic n)` by metis_tac[] >>
  `loc = slot_loc (loc = LocTransient)` by (Cases_on `loc` >> gvs[slot_loc_def]) >>
  mp_tac (Q.INST [`tr` |-> `loc = LocTransient`, `src` |-> `op`]
    (SPEC_ALL place_store_storage_compile)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  qexistsl_tac [`a`, `sm`, `sc'`] >> simp[]
QED

Resume assign_place_storage_normalize_compile[intervals]:
  disch_then (qx_choosel_then [`buf`, `sm`, `sn`] (map_every assume_tac o CONJUNCTS)) >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by (drule typed_return_store_mono >> simp[ci_mono_def]) >>
  `cs_extends sn sb` by
    (qpat_x_assum `(?et n. _ /\ _) \/ _` strip_assume_tac
     >- (mp_tac (cj 7 ci_mono_context_helpers) >>
         disch_then (qspecl_then [`buf.buf_operand`, `dst`,
           `(type_memory_bytes cenv et + 31) DIV 32`, `type_memory_bytes cenv et`,
           `loc = LocTransient`, `sn`] mp_tac) >> simp[ci_mono_def]) >>
     Cases_on `type_memory_size dtv <= 32`
     >- (qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
         `cs_extends sn sd /\ cs_extends sd sb` by
           metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
         irule cs_extends_trans >> qexists_tac `sd` >> simp[]) >>
     qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
     Cases_on `loc = LocTransient` >> gvs[] >>
     mp_tac (cj 1 ci_mono_context_helpers) >> mp_tac (cj 2 ci_mono_context_helpers) >>
     disch_then (qspecl_then [`buf.buf_operand`, `dst`, `type_memory_size dtv DIV 32`, `sn`] mp_tac) >>
     simp[ci_mono_def] >> disch_then kall_tac >>
     disch_then (qspecl_then [`buf.buf_operand`, `dst`, `type_memory_size dtv DIV 32`, `sn`] mp_tac) >>
     simp[ci_mono_def]) >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func /\
   fn_has_code sa sm func /\ fn_has_code sm sn func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv dty))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule entry_alloc_buffer_inst >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`buf`, `sm`, `sn`] >> simp[] >>
  qpat_x_assum `(?et n. _ /\ _) \/ _` strip_assume_tac
  >- (gvs[]) >>
  Cases_on `dty` >> gvs[] >> rename1 `ArrayT et bd` >>
  Cases_on `bd` >> gvs[]
QED

Finalise assign_place_storage_normalize_compile
