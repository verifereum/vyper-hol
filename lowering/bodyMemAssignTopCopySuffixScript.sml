(* Counted memory-safe storage-copy suffix with the full semantic post. *)
Theory bodyMemAssignTopCopySuffix
Ancestors
  bodyMemAssignTopCopyPaths bodyMemAssignTopCopySem bodyMemAssignTopCopyCompiler
  allocaHistory allocaHistoryFragment bodyDeclMemoryCore bodyDeclMemoryCounted
  bodyMemAssignTopCopyLoop gasOutcome fragGasMode fragExec instMemFrontier emitHelper emitHelperProps context venomInst
  stmtSimStoreCopy stmtSimProps stmtSimDefs exprSimDefs exprSimMemDefs loweringPosts exprLoweringProps compileEnv loweringStateRelDefs
  exprSimProps exprOperandVar freshWrites vyperStorageBackend vyperStorage valueEncodingProps
  bodyMemAssignTopCopyFacts stmtLowering emitHelperProps
  venomState words arithmetic list rich_list

Theorem topcopy_normalize_allocations[local]:
  !s t loc b k n.
    store_copy_normalize s t = store_copy_prefix loc b k s n ==>
    t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `!s. (store_copy_prefix loc b k s n).vs_allocas = s.vs_allocas /\
        (store_copy_prefix loc b k s n).vs_alloca_next = s.vs_alloca_next`
    suffices_by
      (strip_tac >>
       qpat_x_assum `store_copy_normalize _ _ = _`
         (mp_tac o AP_TERM ``\u:venom_state. (u.vs_allocas,u.vs_alloca_next)``) >>
       simp[store_copy_normalize_def]) >>
  simp[store_copy_prefix_def] >>
  qid_spec_tac `n` >> Induct >> simp[COUNT_LIST_SNOC, FOLDL_SNOC] >>
  rpt gen_tac >> Cases_on `loc = LocStorage` >> fs[] >>
  simp[Once sstore_def, Once tstore_def]
QED

Theorem storage_copy_bulk_run_mem:
  !ctx func cenv cx es' tr src k n sa sb u s b.
    compile_word_copy_loop src (Lit k) n LocMemory
      (if tr then LocTransient else LocStorage) F sa = (u,sb) /\
    n < dimword (:256) /\ w2n b + 32*n <= s.vs_alloca_next /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME b /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es'
      (FOLDL (\t i. (if tr then tstore else sstore)
        (k+n2w i) (mload (w2n (b+n2w i*32w)) s) t) s (COUNT_LIST n)) ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t
Proof
  rpt gen_tac >> strip_tac >>
  `~s.vs_call_ctx.cc_static` by
    (Cases_on `tr` >>
     fs[stmt_state_rel_def, state_rel_def, topcopy_backend_fold]) >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    topcopy_compile_loop_path >>
  disch_then (qspecl_then [`ctx`, `func`, `s`, `b`, `k`] mp_tac) >>
  (impl_tac >- (Cases_on `tr` >> simp[eval_operand_def])) >>
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es' t` by
    (irule topcopy_normalized_state >> qexistsl_tac [`s`, `sa`] >>
     fs[store_copy_frame_def, store_copy_normalize_def, store_copy_prefix_def] >>
     Cases_on `tr` >> gvs[]) >>
  `t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next` by
    (fs[store_copy_frame_def] >>
     drule topcopy_normalize_allocations >> simp[]) >>
  `sb.cs_current_insts = []` by
    (drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
       topcopy_code_certificate >>
     disch_then (qspec_then `func` mp_tac) >>
     (impl_tac >- (Cases_on `tr` >> simp[])) >>
     strip_tac >> simp[]) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists_tac `s` >> simp[]) >>
  qexists_tac `t` >> fs[store_copy_frame_def]
QED

Theorem storage_copy_one_run_mem:
  !ctx func cenv cx es' tr src k sa sm sb op s b.
    emit_op MLOAD [src] sa = (op,sm) /\
    emit_void (if tr then TSTORE else SSTORE) [Lit k;op] sm = ((),sb) /\
    eval_operand src s = SOME b /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ alloca_inv s /\ w2n b + 32 <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es'
      ((if tr then tstore else sstore) k (mload (w2n b) s) s) ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  drule_all emitted_insts_append >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (fs[same_blocks_def, IS_PREFIX_APPEND3] >> simp[GSYM APPEND_ASSOC]) >>
  qmatch_asmsub_abbrev_tac `Var out` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> decide_tac) >>
  `~s.vs_call_ctx.cc_static` by
    (Cases_on `tr` >> fs[stmt_state_rel_def, state_rel_def, sstore_def, tstore_def]) >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
     store_copy_normalize s u = (if tr then tstore else sstore) k (mload (w2n b) s) s /\
     (!x. x <> out ==> lookup_var x u = lookup_var x s) /\
     u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx /\
     u.vs_halted = s.vs_halted` by
    (mp_tac (Q.INST [`loc` |-> `if tr then LocTransient else LocStorage`,
                    `dst` |-> `Lit k`, `v` |-> `out`, `id` |-> `sa.cs_next_id`]
       (SPEC_ALL topcopy_singleton_run)) >>
     simp[eval_operand_def] >>
     impl_tac >- (Cases_on `tr` >> simp[]) >>
     Cases_on `tr` >> gvs[]) >>
  suspend "post"
QED

Resume storage_copy_one_run_mem[post]:
  `same_blocks sa sb` by fs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (simp[] >>
     mp_tac (Q.INST [`loc` |-> `if tr then LocTransient else LocStorage`,
                     `dst` |-> `Lit k`, `v` |-> `out`, `id` |-> `sa.cs_next_id`]
        (SPEC_ALL body_mem_storage_singleton_mem_ok)) >>
     Cases_on `tr` >> simp[eval_operand_def]) >>
  `gas_path_mem ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule (cj 1 body_decl_cursor_path) >> simp[] >> qexists_tac `sa` >>
     simp[] >> Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl_tac [`s`, `sa`] >>
     simp[] >> Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  `stmt_state_rel ctx func cenv cx es' u` by
    (irule topcopy_normalized_state >> qexistsl_tac [`s`, `sa`] >>
     simp[GSYM store_copy_normalize_def] >> metis_tac[]) >>
  `store_copy_normalize s u =
     store_copy_prefix (if tr then LocTransient else LocStorage) b k s 1` by
    (`COUNT_LIST 1 = [0]` by EVAL_TAC >>
     simp[store_copy_prefix_def] >> Cases_on `tr` >>
     gvs[WORD_ADD_0, WORD_MULT_CLAUSES]) >>
  drule topcopy_normalize_allocations >> strip_tac >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx, lookup_var_def] >>
  metis_tac[lookup_var_def]
QED

Finalise storage_copy_one_run_mem

Theorem storage_copy_suffix_run_mem:
  !ctx func cenv cx es' tr src k n typ src_ty loc sa sb s b.
    compile_assign_value cenv (Lit k)
      (if tr then LocTransient else LocStorage) src F loc
      typ src_ty NONE (32 * n) sa = ((),sb) /\
    ~is_word_type typ /\ typ = src_ty /\ type_memory_bytes cenv typ = 32*n /\
    0 < n /\ n < dimword (:256) /\ w2n b + 32*n <= s.vs_alloca_next /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ eval_operand src s = SOME b /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ alloca_history func s /\ alloca_inv s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es'
      (FOLDL (\t i. (if tr then tstore else sstore)
        (k+n2w i) (mload (w2n (b+n2w i*32w)) s) t) s (COUNT_LIST n)) ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  dep_rewrite.DEP_REWRITE_TAC[topcopy_suffix] >> simp[] >>
  Cases_on `32*n <= 32`
  >- (`n = 1` by decide_tac >> gvs[] >>
      simp[comp_bind_def, AllCaseEqs()] >> strip_tac >>
      Cases_on `emit_op MLOAD [src] sa` >> gvs[] >>
      `COUNT_LIST 1 = [0]` by EVAL_TAC >>
      fs[WORD_ADD_0, WORD_MULT_CLAUSES] >>
      drule_all storage_copy_one_run_mem >> simp[]) >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
       comp_bind_def, comp_return_def, AllCaseEqs()] >> strip_tac >>
  fs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> rename1 `_ sa = (u,sf)` >>
  `compile_word_copy_loop src (Lit k) n LocMemory
     (if tr then LocTransient else LocStorage) F sa = (u,sf)` by
    (Cases_on `tr` >> gvs[]) >>
  `w2n b + 32*n <= s.vs_alloca_next` by decide_tac >>
  drule_all storage_copy_bulk_run_mem >> simp[]
QED

Theorem storage_copy_success_run_mem:
  !ctx func cenv cx e es es1 es' v tv tr mid id slot sa sm sf op loc s0 s1.
    expr_post ctx func cenv cx e es sa sm s0 es1 v op s1 /\
    expr_store_bound cx (expr_type e) v op s1 /\ alloca_history func s1 /\
    ~s1.vs_halted /\ s1.vs_current_bb = sm.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sm.cs_current_insts /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
    value_has_type tv v /\ lowered_value_type cenv e = expr_type e /\
    type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
    declared_storage_region cx mid id [] = SOME (tr,n2w slot,tv) /\
    0 < type_slot_size tv /\ slot + type_slot_size tv <= dimword (:256) /\
    (!mid' id' subs' k' tv'.
       declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (n2w slot,tv) ==>
       ranges_disjoint slot (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
    write_storage_slot cx tr (n2w slot) tv v es1 = (INL (),es') /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    compile_assign_value cenv (Lit (n2w slot))
      (if tr then LocTransient else LocStorage) op F loc
      (expr_type e) (expr_type e) NONE (type_memory_size tv) sm = ((),sf) /\
    fn_has_code sa sm func /\ fn_has_code sm sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
    ?t. gas_marked_path T ctx func s1 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
             lookup_var x t = SOME u) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
                  FLOOKUP t.vs_allocas aid = SOME ent) /\
      t.vs_allocas = s1.vs_allocas /\ t.vs_alloca_next = s1.vs_alloca_next /\
      alloca_history func t
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_lower_value_var >> simp[] >> disch_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all topcopy_post_region >> strip_tac >>
  `0 < type_memory_size tv` by simp[type_memory_size_slots] >>
  `w2n w + type_memory_size tv <= s1.vs_alloca_next` by
    (drule_all topcopy_source_bound >> simp[]) >>
  `alloca_inv s1` by fs[expr_post_def, stmt_state_rel_def] >>
  RULE_ASSUM_TAC (REWRITE_RULE [type_memory_size_slots]) >>
  `w2n w + 32 * type_slot_size tv <= s1.vs_alloca_next` by decide_tac >>
  drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)
    storage_copy_suffix_run_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es'`, `s1`, `w`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sa` >> simp[ci_mono_def]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  conj_tac >- metis_tac[] >> metis_tac[]
QED

(* Storage writes do not inspect or change the source gas observation tail. *)
Theorem topcopy_write_storage_gas_tail:
  !cx tr k tv v es es' tail.
    write_storage_slot cx tr k tv v es = (INL (),es') ==>
    write_storage_slot cx tr k tv v (es with gas_obs := tail) =
      (INL (),es' with gas_obs := tail)
Proof
  rpt gen_tac >>
  simp[write_storage_slot_eq, AllCaseEqs()] >> strip_tac >>
  gvs[] >> Cases_on `tr` >>
  simp[set_storage_def, get_storage_def]
QED

val () =
  List.app (fn (name,th) =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th)
       then print (name ^ " oracles: " ^ String.concatWith "," oracles ^ "\n")
       else raise Fail "topcopy suffix has axioms or hypotheses"
    end)
    [("bulk",storage_copy_bulk_run_mem), ("one",storage_copy_one_run_mem),
     ("suffix",storage_copy_suffix_run_mem), ("success",storage_copy_success_run_mem),
     ("gas_tail",topcopy_write_storage_gas_tail)];

val () = List.app (fn (name,th) =>
  let val (os,_) = Tag.dest_tag (Thm.tag th)
  in print (name ^ " dependency oracles: " ^ String.concatWith "," os ^ "\n") end)
  [("post_region",topcopy_post_region), ("source_bound",topcopy_source_bound),
   ("lower_value_var",compile_lower_value_var), ("expr_grows",cj 2 compile_expr_grows),
   ("reserved_next",local_ptrs_reserved_next_var), ("fresh_mono",not_fresh_at_mono)];
