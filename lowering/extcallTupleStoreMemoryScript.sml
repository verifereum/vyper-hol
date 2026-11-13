(* Compose the actual extcall cell stores in compiler order. *)
Theory extcallTupleStoreMemory
Ancestors
  extcallStoreMemory externalEntryShape exprLowering compileEnv fragExec
  fragGasPathMem venomState list

Theorem extcall_tuple_store_mem_cps:
  !vals sa sb off prefix s.
    compile_extcall_store_values ce vals buf off sa = ((),sb) /\
    fn_has_code sa sb func /\ P prefix off s sa vals /\
    (!pre k t sc remaining. P pre k t sc remaining ==> ~t.vs_halted) /\
    (!vv ty tail pre k t sc sn.
       MEM (vv,ty) vals /\ P pre k t sc ((vv,ty)::tail) /\
       compile_extcall_store_values ce [(vv,ty)] buf k sc = ((),sn) /\
       fn_has_code sc sn func ==>
       ?u. gas_path_mem ctx func t 0 (OK u) /\
           P (pre ++ [(vv,ty)]) (k + type_memory_bytes ce ty) u sn tail) ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        P (prefix ++ vals)
          (off + SUM (MAP (type_memory_bytes ce o SND) vals)) u sb []
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_extcall_store_values_def,comp_return_def] >>
      `~s.vs_halted` by metis_tac[] >>
      qexists_tac `s` >> simp[cj 1 gas_path_mem_rules]) >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  qpat_x_assum `compile_extcall_store_values _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_extcall_store_values_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_bind_def,comp_ignore_bind_def,comp_return_def]) >>
  strip_tac >> gvs[] >>
  rename1 `compile_extcall_store_values ce vals buf _ sn = ((),sb)` >>
  `compile_extcall_store_values ce [(h0,h1)] buf off sa = ((),sn)` by
    (simp[compile_extcall_store_values_def,comp_bind_def,
          comp_ignore_bind_def,comp_return_def] >>
     fs[]) >>
  `cs_extends sa sn /\ cs_extends sn sb` by
    (qspecl_then [`ce`,`[(h0,h1)]`,`buf`,`off`,`sa`]
       mp_tac compile_extcall_store_values_labels >>
     qspecl_then [`ce`,`vals`,`buf`,`off+type_memory_bytes ce h1`,`sn`]
       mp_tac compile_extcall_store_values_labels >> simp[]) >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_mid,cs_extends_refl] >>
  `?t. gas_path_mem ctx func s 0 (OK t) /\
       P (prefix ++ [(h0,h1)]) (off+type_memory_bytes ce h1) t sn vals` by
    (qpat_x_assum `!vv ty tail pre k t sc sn. _`
       (qspecl_then [`h0`,`h1`,`vals`,`prefix`,`off`,`s`,`sa`,`sn`] mp_tac) >> simp[]) >>
  suspend "tail"
QED
Resume extcall_tuple_store_mem_cps[tail]:
  qpat_x_assum `!sa sb off prefix s. _`
    (qspecl_then [`sn`,`sb`,`off+type_memory_bytes ce h1`,
                 `prefix ++ [(h0,h1)]`,`t`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[MEM])) >>
  strip_tac >> qexists_tac `u` >> conj_tac
  >- (drule_all gas_path_mem_then >> simp[]) >>
  `off + type_memory_bytes ce h1 + SUM (MAP (type_memory_bytes ce o SND) vals) =
   off + (SUM (MAP (type_memory_bytes ce o SND) vals) + type_memory_bytes ce h1)` by
    decide_tac >>
  qpat_x_assum `P (prefix ++ [(h0,h1)] ++ vals) _ u sb []` mp_tac >>
  qpat_x_assum `off + type_memory_bytes ce h1 + _ = _`
    (fn th => pure_once_rewrite_tac [th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
  simp_tac bool_ss []
QED
Finalise extcall_tuple_store_mem_cps
