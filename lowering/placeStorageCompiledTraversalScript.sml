(* Compiler-facing counted dynamic storage traversal. *)
Theory placeStorageCompiledTraversal
Ancestors
  placeStorageTraversalCounted placeStorageLayoutCounted placeStorageControlCounted
  compileEnv emitHelperProps words list rich_list

Theorem dyn_storage_word_header[local]:
  compile_dynarray_to_storage src dst 1 em tr sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  ~s.vs_call_ctx.cc_static /\ w2n p + 32 <= s.vs_alloca_next /\
  mload (w2n p) s = n2w n /\ n < dimword(:256) /\
  (!j. j < n ==> w2n (p + n2w (32+j*32)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
          (p+n2w (32+j*32)) (d+n2w (1+j)) a 1) s (COUNT_LIST n) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      lookup_var ("%" ++ toString (sa.cs_next_var+1)) t = SOME (n2w n) /\
      lookup_var ("%" ++ toString sa.cs_next_var) t = SOME (n2w n) /\
      ~t.vs_halted /\ t.vs_current_bb = fresh_label_output "dyn_cond" sa.cs_next_label /\
      t.vs_inst_idx = 0
Proof
  strip_tac >>
  drule dyn_storage_word_layout >> strip_tac >>
  drule dyn_storage_word_blocks >> strip_tac >>
  drule_all dyn_storage_word_code >>
  simp[TAKE, MEM, DISJ_IMP_THM, FORALL_AND_THM, IS_PREFIX_APPEND] >> strip_tac >>
  fs[] >>
  qmatch_asmsub_abbrev_tac `lookup_block sa.cs_current_bb fn.fn_blocks = SOME entry_bb` >>
  `entry_bb.bb_instructions = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id MLOAD [src] ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] ["%" ++ toString (sa.cs_next_var+1)];
     mk_inst (sa.cs_next_id+2) JMP [Label (fresh_label_output "dyn_cond" sa.cs_next_label)] []]`
    by simp[Abbr `entry_bb`] >>
  drule_at (Pat `bb.bb_instructions = _`) storage_traversal_entry >>
  disch_then (qspecl_then [`s`,`p`,`n`,`fn`,`ctx`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `lookup_block (fresh_label_output "dyn_cond" sa.cs_next_label) fn.fn_blocks = SOME hb` >>
  qmatch_asmsub_abbrev_tac `lookup_block (fresh_label_output "dyn_body" (sa.cs_next_label+1)) fn.fn_blocks = SOME wb` >>
  `hb.bb_instructions =
    [mk_inst (sa.cs_next_id+3) LT [Var ("%" ++ toString (sa.cs_next_var+1)); Var ("%" ++ toString sa.cs_next_var)] ["%" ++ toString (sa.cs_next_var+2)];
     mk_inst (sa.cs_next_id+4) ISZERO [Var ("%" ++ toString (sa.cs_next_var+2))] ["%" ++ toString (sa.cs_next_var+3)];
     mk_inst (sa.cs_next_id+5) JNZ [Var ("%" ++ toString (sa.cs_next_var+3)); Label (fresh_label_output "dyn_exit" (sa.cs_next_label+2)); Label (fresh_label_output "dyn_body" (sa.cs_next_label+1))] []]`
    by simp[Abbr `hb`] >>
  qabbrev_tac `H = \i. FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
           (p+n2w (32+j*32)) (d+n2w (1+j)) a 1) s (COUNT_LIST i)` >>
  `?v. gas_path_mem ctx fn u 0 (OK v) /\
       store_copy_normalize s v = H n /\
       (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s) /\
       lookup_var ("%" ++ toString (sa.cs_next_var+1)) v = SOME (n2w n) /\
       lookup_var ("%" ++ toString sa.cs_next_var) v = SOME (n2w n) /\
       ~v.vs_halted /\ v.vs_current_bb = fresh_label_output "dyn_cond" sa.cs_next_label /\
       v.vs_inst_idx = 0` by
    (irule (REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC] (Q.INST [`hid` |-> `sa.cs_next_id+3`,
       `id` |-> `sa.cs_next_id+6`, `tid` |-> `sa.cs_next_id+13`]
       storage_traversal_word_iteration)) >>
     (conj_tac >- (rpt strip_tac >> first_x_assum irule >>
       gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD])) >>
     simp[IgnAsm `hb.bb_instructions = _`, IgnAsm `store_copy_normalize s u = s`] >>
     reverse conj_tac >- simp[Abbr `H`, COUNT_LIST_def] >>
     qpat_assum `hb.bb_instructions = _` (irule_at Any o SRULE []) >>
     qpat_assum `lookup_block _ _ = SOME wb` (irule_at Any) >>
     simp[Abbr `wb`, typedArrayLoopControlMemTheory.typed_sa_backedge_insts_def, venomInstTheory.mk_inst_def] >>
     qexists_tac `tr` >>
     simp[Abbr `H`] >>
     rpt strip_tac >> gvs[not_fresh_at_def] >>
     first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
  qexists_tac `v` >> simp[] >>
  conj_tac >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] fragGasPathMemTheory.gas_path_mem_then)) >>
    qexists_tac `u` >> simp[]) >> gvs[Abbr `H`]
QED

Theorem dyn_storage_word_path:
  compile_dynarray_to_storage src dst 1 em tr sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  ~s.vs_call_ctx.cc_static /\ w2n p + 32 <= s.vs_alloca_next /\
  mload (w2n p) s = n2w n /\ n < dimword(:256) /\
  (!j. j < n ==> w2n (p + n2w (32+j*32)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      store_copy_normalize s t =
        (if tr then tstore d (n2w n) else sstore d (n2w n))
          (FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
             (p+n2w (32+j*32)) (d+n2w (1+j)) a 1) s (COUNT_LIST n)) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all dyn_storage_word_header >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule dyn_storage_word_layout >> strip_tac >>
  drule dyn_storage_word_blocks >> strip_tac >>
  drule_all dyn_storage_word_code >>
  simp[TAKE, MEM, DISJ_IMP_THM, FORALL_AND_THM, IS_PREFIX_APPEND] >> strip_tac >>
  fs[] >>
  qmatch_asmsub_abbrev_tac `store_copy_normalize s t = h` >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_labels = s.vs_labels` by
    (qpat_x_assum `store_copy_normalize s t = h`
       (mp_tac o Q.AP_TERM `(\u. (u.vs_call_ctx,u.vs_labels))`) >>
     `!ls a. (\u. (u.vs_call_ctx,u.vs_labels))
       (FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
        (p+n2w (32+j*32)) (d+n2w (1+j)) a 1) a ls) =
       (a.vs_call_ctx,a.vs_labels)` by
       (CONV_TAC (DEPTH_CONV BETA_CONV) >>
        Induct >> gvs[FOLDL, stmtSimStoreCopyTheory.store_copy_prefix_memory]) >>
     gvs[stmtSimStoreCopyTheory.store_copy_normalize_def, Abbr `h`]) >>
  `eval_operand dst t = SOME d` by
    (Cases_on `dst` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `?v. gas_path_mem ctx fn t 0 (OK v) /\
       store_copy_normalize s v = (if tr then tstore d (n2w n) h else sstore d (n2w n) h) /\
       (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s) /\
       ~v.vs_halted /\ v.vs_current_bb = fresh_label_output "dyn_exit" (sa.cs_next_label+2) /\
       v.vs_inst_idx = 1` by
    (irule (REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
       (Q.INST [`hid` |-> `sa.cs_next_id+3`] storage_traversal_exit)) >>
     qpat_assum `lookup_block (fresh_label_output "dyn_cond" _) _ = SOME _` (irule_at Any) >>
     simp[venomInstTheory.mk_inst_def] >>
     conj_tac
     >- (rpt strip_tac >> `not_fresh_at sa x` by metis_tac[] >>
         gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.LESS_EQ_REFL]) >>
     rpt strip_tac >> gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.LESS_EQ_REFL]) >>
  qexists_tac `v` >> simp[] >>
  metis_tac[SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
    fragGasPathMemTheory.gas_path_mem_then)]
QED
