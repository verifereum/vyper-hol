(* Empty-safe counted execution of dynamic storage copies. *)
Theory placeStorageDynamicExecution
Ancestors
  placeStorageCompiledTraversal placeStorageTraversalCounted
  placeStorageControlCounted placeStorageLayoutCounted compileEnv emitHelperProps
  words list rich_list

Theorem dyn_storage_multi_empty_path[local]:
  compile_dynarray_to_storage src dst ew em tr sa = ((),sb) /\
  ew <> 1 /\ fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  ~s.vs_call_ctx.cc_static /\ w2n p + 32 <= s.vs_alloca_next /\
  mload (w2n p) s = 0w /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      store_copy_normalize s t = (if tr then tstore d 0w s else sstore d 0w s) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all dyn_storage_multi_split >> strip_tac >>
  `cs_extends sa sc` by
    (simp[compileEnvTheory.cs_extends_def] >> qexists_tac `TAKE 2 sc.cs_blocks` >>
     simp[IS_PREFIX_APPEND]) >>
  `cs_extends sc sd` by
    (drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
       bodyMemAssignTopCopyCompilerTheory.topcopy_compile_certificate >>
     (impl_tac >- (Cases_on `tr` >> simp[])) >> strip_tac >>
     metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `cs_extends sa sd` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `cs_extends sd sb` by metis_tac[dyn_storage_suffix_extends] >>
  drule_all dyn_storage_suffix_code >> strip_tac >>
  drule dyn_storage_suffix_layout >> strip_tac >>
  `!bb. MEM bb (TAKE 2 sc.cs_blocks) ==>
      lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (`fn_has_code sa sc fn` by metis_tac[fragExecTheory.fn_has_code_split] >>
     fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
     gvs[] >> metis_tac[]) >>
  gvs[TAKE, MEM, DISJ_IMP_THM, FORALL_AND_THM] >>
  suspend "entry"
QED

Resume dyn_storage_multi_empty_path[entry]:
  qmatch_asmsub_abbrev_tac `lookup_block sa.cs_current_bb fn.fn_blocks = SOME entry_bb` >>
  `entry_bb.bb_instructions = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id MLOAD [src] ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] ["%" ++ toString (sa.cs_next_var+1)];
     mk_inst (sa.cs_next_id+2) JMP [Label (fresh_label_output "dyn_cond" sa.cs_next_label)] []]`
    by simp[Abbr `entry_bb`] >>
  drule_at (Pat `bb.bb_instructions = _`) storage_traversal_entry >>
  disch_then (qspecl_then [`s`,`p`,`0`,`fn`,`ctx`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  suspend "exit"
QED

Resume dyn_storage_multi_empty_path[exit]:
  `u.vs_call_ctx = s.vs_call_ctx /\ u.vs_labels = s.vs_labels` by
    (qpat_assum `store_copy_normalize s u = s`
       (mp_tac o Q.AP_TERM `(\v. (v.vs_call_ctx,v.vs_labels))`) >>
     simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.LESS_EQ_REFL]) >>
  `eval_operand dst u = SOME d` by
    (Cases_on `dst` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `?v. gas_path_mem ctx fn u 0 (OK v) /\
       store_copy_normalize s v = (if tr then tstore d 0w s else sstore d 0w s) /\
       (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s) /\
       ~v.vs_halted /\ v.vs_current_bb = fresh_label_output "dyn_exit" (sa.cs_next_label+2) /\
       v.vs_inst_idx = 1` by
    (irule (REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
       (Q.INST [`hid` |-> `sa.cs_next_id+3`, `n` |-> `0`] storage_traversal_exit)) >>
     qpat_assum `lookup_block (fresh_label_output "dyn_cond" _) _ = SOME _` (irule_at Any) >>
     simp[venomInstTheory.mk_inst_def] >>
     qexistsl_tac [`sd.cs_next_id+3`, `dst`] >> fs[venomInstTheory.mk_inst_def] >>
     conj_tac
     >- (rpt strip_tac >> `not_fresh_at sa x` by metis_tac[] >>
         gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.LESS_EQ_REFL]) >>
     rpt strip_tac >> gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.LESS_EQ_REFL]) >>
  qexists_tac `v` >> simp[] >>
  metis_tac[SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
    fragGasPathMemTheory.gas_path_mem_then)]
QED
Finalise dyn_storage_multi_empty_path

Theorem dyn_storage_path_nonempty_bound:
  compile_dynarray_to_storage src dst ew em tr sa = ((),sb) /\
  (0 < n ==> ew < dimword(:256)) /\ fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  ~s.vs_call_ctx.cc_static /\ w2n p + 32 <= s.vs_alloca_next /\
  mload (w2n p) s = n2w n /\ n < dimword(:256) /\
  (!j. j < n ==>
       w2n (p + n2w (32+j*(if ew = 1 then 32 else em))) + 32*ew
         <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      store_copy_normalize s t =
        (if tr then tstore d (n2w n) else sstore d (n2w n))
          (FOLDL (\a j. store_copy_prefix
             (if tr then LocTransient else LocStorage)
             (p+n2w (32+j*(if ew = 1 then 32 else em)))
             (d+n2w (1+j*ew)) a ew) s (COUNT_LIST n)) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Cases_on `n = 0`
  >- (simp[COUNT_LIST_def] >> strip_tac >> Cases_on `ew = 1`
      >- (gvs[] >>
          drule_at (Pat `compile_dynarray_to_storage _ _ _ _ _ _ = _`) dyn_storage_word_path >>
          disch_then (qspec_then `s` mp_tac) >> simp[] >>
          disch_then (qspecl_then [`0`,`fn`,`ctx`] mp_tac) >>
          simp[COUNT_LIST_def] >> metis_tac[]) >>
      drule_all dyn_storage_multi_empty_path >>
      disch_then (qspec_then `ctx` mp_tac) >> Cases_on `tr` >> simp[]) >>
  strip_tac >> `ew < dimword(:256)` by (first_x_assum irule >> decide_tac) >>
  drule_all dyn_storage_path >> disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED
