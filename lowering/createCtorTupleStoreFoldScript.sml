Theory createCtorTupleStoreFold
Ancestors
  exprLowering context compileEnv emitHelper fragGasMode fragGasPath
  venomState arithmetic list

(* The invariant carries all semantic and resource facts; this rule exposes
   only the actual compiler traversal and zero-mark path composition. *)
Theorem ctor_delayed_stores_invariant:
  (!done vv ty rest off a a1 a2 a3 dst op u.
    invariant done ((vv,ty)::rest) off a u /\
    emit_op ADD [src; Lit (n2w off)] a = (dst,a1) /\
    unwrap_value ce vv a1 = (op,a2) /\
    (if is_word_type ty then emit_void MSTORE [dst; op]
     else if is_bytestring_type ty then compile_store_bytestring op dst
     else emit_void MCOPY [dst; op; Lit (n2w (type_memory_bytes ce ty))])
       a2 = ((),a3) ==>
    ?t. gas_marked_path F ctx func u 0 (OK t) /\
        invariant (done ++ [(vv,ty)]) rest
          (off + type_memory_bytes ce ty) a3 t) /\
  compile_extcall_store_values ce pairs src off ca = ((),cb) /\
  invariant done pairs off ca s /\ ~s.vs_halted ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      invariant (done ++ pairs) []
        (off + SUM (MAP (\p. type_memory_bytes ce (SND p)) pairs)) cb t
Proof
  map_every qid_spec_tac [`s`, `ca`, `off`, `done`] >>
  Induct_on `pairs`
  >- (simp[compile_extcall_store_values_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[gas_marked_path_def, gas_path_rules]) >>
  gen_tac >>
  qpat_x_assum `!done off ca s. _` (mk_asm "ih") >>
  PairCases_on `h` >> rpt gen_tac >>
  simp[Once compile_extcall_store_values_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >>
  rename1 `(if _ then _ else _) _ = (r,a3)` >> Cases_on `r` >>
  qpat_assum `!done vv ty rest off a a1 a2 a3 dst op u. _`
    (fn th => drule_all th) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `~u.vs_halted` by
    (drule gas_marked_path_exec >> metis_tac[gas_path_normal]) >>
  asm_x "ih" (fn th => drule_all th) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> conj_tac
  >- (drule_all gas_marked_path_then >> simp[]) >>
  qpat_x_assum `invariant _ [] _ _ _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  qmatch_goalsub_abbrev_tac `SUM sizes` >>
  `off + type_memory_bytes ce h1 + SUM sizes =
   off + (SUM sizes + type_memory_bytes ce h1)` by decide_tac >>
  asm_rewrite_tac[]
QED
