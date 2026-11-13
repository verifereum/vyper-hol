(* One multiword element follows the compiler's two address prefixes. *)
Theory assignDynStorageDataPtr
Ancestors
  assignDynStorageAddressPtr assignStorageBlockFramePtr assignTupleStorageAddressPtr
  assignStorageExecFramePtr
  assignBasePtrStorageFrame assignBasePtrStorageLoop assignTuplePtrCopyLen placeStoreCopyPath
  typedMemoryCopy context compileEnv exprLoweringProps freshWrites
  bodyPtrDefs fragGasPathPtr fragExec ptrDiscipline venomState venomExecSemantics stateFrame
  words finite_map list arithmetic

Theorem dyn_storage_multi_data_counted:
  !sa sb sc sd se sf sg sh ctr root dst mul_m off_m sp mul_k off_k dp
   ew ems idx cap a k tr fn s G tn ctx D PG z.
    emit_op MUL [Var ctr;Lit (n2w ems)] sa = (mul_m,sb) /\
    emit_op ADD [Lit 32w;mul_m] sb = (off_m,sc) /\
    emit_op ADD [Var root;off_m] sc = (sp,sd) /\
    emit_op MUL [Var ctr;Lit (n2w ew)] sd = (mul_k,se) /\
    emit_op ADD [Lit 1w;mul_k] se = (off_k,sf) /\
    emit_op ADD [dst;off_k] sf = (dp,sg) /\
    compile_word_copy_loop sp dp ew LocMemory
      (if tr then LocTransient else LocStorage) F sg = (z,sh) /\
    fn_has_code sa sd fn /\ fn_has_code sd sg fn /\ fn_has_code sg sh fn /\
    ci_mono sa sd /\ ci_mono sd sg /\
    not_fresh_at sa ctr /\ not_fresh_at sa root /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    lookup_var ctr s = SOME (n2w idx) /\ op_taint tn (Var ctr) = {} /\
    lookup_var root s = SOME a /\ ptr_covers G tn root s cap /\
    op_taint tn (Var root) = {} /\ eval_operand dst s = SOME k /\
    op_taint tn dst = {} /\
    0 < ew /\ ew < dimword (:256) /\ ems = 32*ew /\
    32+idx*ems < cap /\ 32+idx*ems+32*ew <= cap /\
    w2n a+32+idx*ems+32*ew < dimword (:256) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?H tt u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK u) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage)
        (a+n2w (32+idx*ems)) (k+n2w (1+idx*ew)) s tn ew u tt /\
      execution_frame u = execution_frame (store_copy_prefix
        (if tr then LocTransient else LocStorage)
        (a+n2w (32+idx*ems)) (k+n2w (1+idx*ew)) s ew) /\
      u.vs_current_bb = sh.cs_current_bb /\
      u.vs_inst_idx = LENGTH sh.cs_current_insts /\ ~u.vs_halted /\
      u.vs_labels = s.vs_labels /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x /\ not_fresh_at sg x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def, LESS_EQ_TRANS] >>
  `emit_op ADD [Lit (n2w 32);mul_m] sb = (off_m,sc) /\
   (!x. Var root = Var x ==> not_fresh_at sa x) /\
   eval_operand (Var root) s = SOME a /\
   eval_operand (Var ctr) s = SOME (n2w idx)` by simp[eval_operand_def] >>
  `(0 < 32*ew ==> ?p total. Var root = Var p /\ ptr_covers G tn p s total /\
    32+idx*ems < total /\ 32+idx*ems+32*ew <= total /\
    w2n a+32+idx*ems < dimword (:256))` by
    (strip_tac >> qexistsl_tac [`root`,`cap`] >> rpt conj_tac
     >- REFL_TAC >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC >> decide_tac) >>
  mp_tac (Q.SPECL [`sa`,`sb`,`sc`,`sd`,`ctr`,`ems`,`32`,`Var root`,
    `mul_m`,`off_m`,`sp`,`fn`,`ctx`,`D`,`PG`,`G`,`tn`,`s`,`idx`,`a`,`32*ew`]
    dyn_storage_index_address_counted) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`sp_id`,`s1`,`G1`,`tn1`] strip_assume_tac) >>
  qpat_x_assum `s1 = s with <|vs_vars := _; vs_inst_idx := _|>`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `lookup_var ctr s1 = SOME (n2w idx) /\ op_taint tn1 (Var ctr) = {} /\
   eval_operand dst s1 = SOME k /\ op_taint tn1 dst = {}` by
    (Cases_on `dst` >> gnvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  suspend "destination"
QED

Resume dyn_storage_multi_data_counted[destination]:
  mp_tac (Q.SPECL [`sd`,`se`,`sf`,`sg`,`ctr`,`ew`,`1`,`dst`,
    `mul_k`,`off_k`,`dp`,`fn`,`ctx`,`D`,`PG`,`G1`,`tn1`,`s1`,`idx`,`k`,`0`]
    dyn_storage_index_address_counted) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`dp_id`,`s2`,`G2`,`tn2`] strip_assume_tac) >>
  qpat_x_assum `s2 = s1 with <|vs_vars := _; vs_inst_idx := _|>`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `0 < 32*ew` by decide_tac >>
  `ptr_covers G1 tn1 sp_id s1 (32*ew)` by metis_tac[] >>
  `lookup_var sp_id s2 = lookup_var sp_id s1 /\
   FLOOKUP G2 sp_id = FLOOKUP G1 sp_id /\
   op_taint tn2 (Var sp_id) = op_taint tn1 (Var sp_id)` by
    (qpat_assum `!x. not_fresh_at sd x ==>
       lookup_var x s2 = lookup_var x s1 /\ FLOOKUP G2 x = FLOOKUP G1 x /\
       op_taint tn2 (Var x) = op_taint tn1 (Var x)`
       (qspec_then `sp_id` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `lookup_var sp_id s2 = SOME (a+n2w (32+idx*ems)) /\
   ptr_covers G2 tn2 sp_id s2 (32*ew)` by
    (conj_tac
     >- (gnvs[eval_operand_def] >> metis_tac[]) >>
     mp_tac (Q.INST [`G` |-> `G1`, `tn` |-> `tn1`, `p` |-> `sp_id`,
       `s` |-> `s1`, `n` |-> `32*ew`, `G'` |-> `G2`, `tn'` |-> `tn2`,
       `t` |-> `s2`] (SPEC_ALL ptr_covers_lookup_frame)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `w2n ((a:bytes32)+n2w (32+idx*ems)) = w2n a+32+idx*ems` by
    (`(a:bytes32)+n2w (32+idx*ems) = n2w (w2n a+32+idx*ems)` by
       simp_tac bool_ss [GSYM word_add_n2w, n2w_w2n, WORD_ADD_ASSOC] >>
     qpat_x_assum `(a:bytes32)+n2w (32+idx*ems) = n2w (w2n a+32+idx*ems)`
       (fn th => once_rewrite_tac[th]) >> pure_rewrite_tac[w2n_n2w] >>
     irule LESS_MOD >> decide_tac) >>
  `w2n ((a:bytes32)+n2w (32+idx*ems))+32*(ew-1) < dimword (:256)` by decide_tac >>
  `compile_word_copy_loop (Var sp_id) dp ew LocMemory
      (if tr then LocTransient else LocStorage) F sg = (z,sh)` by metis_tac[] >>
  `not_fresh_at sg sp_id /\ ~s2.vs_call_ctx.cc_static` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  mp_tac (Q.SPECL [`tr`,`sp_id`,`dp`,`k+n2w (1+idx*ew)`,`ew`,`sg`,`z`,
    `sh`,`fn`,`s2`,`G2`,`tn2`,`ctx`,`D`,`PG`,
    `a+n2w (32+idx*ems)`,`32*ew`] tuple_storage_address_compiled_counted) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`H`,`tt`,`u`] strip_assume_tac) >>
  suspend "join"
QED

Resume dyn_storage_multi_data_counted[join]:
  `assign_base_store_frame (if tr then LocTransient else LocStorage)
      (a+n2w (32+idx*ems)) (k+n2w (1+idx*ew)) s tn 0 s2 tn2` by
    (simp[assign_base_store_frame_def, assign_base_store_prefix_zero,
      assign_base_store_taint_prefix_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`loc` |-> `if tr then LocTransient else LocStorage`,
    `b` |-> `(a:bytes32)+n2w (32+idx*ems)`,
    `k` |-> `(k:bytes32)+n2w (1+idx*ew)`, `s0` |-> `s`, `tn0` |-> `tn`,
    `i` |-> `0`, `s` |-> `s2`, `tn` |-> `tn2`, `j` |-> `ew`,
    `u` |-> `u`, `tf` |-> `tt`] (SPEC_ALL assign_base_store_frame_block)) >>
  (impl_tac >-
    (qpat_x_assum `assign_base_store_frame _ _ _ _ _ 0 _ _` mp_tac >>
     qpat_x_assum `assign_base_store_frame _ _ _ _ _ ew _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[WORD_MULT_CLAUSES, WORD_ADD_0, ADD_COMM, MULT_COMM])) >>
  simp[] >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK s2)` by
    (qpat_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK u)` by
    (qpat_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK s2)`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  `execution_frame s2 = execution_frame s` by
    (simp[execution_frame_def] >> metis_tac[]) >>
  `execution_frame u = execution_frame (store_copy_prefix
     (if tr then LocTransient else LocStorage)
     (a+n2w (32+idx*ems)) (k+n2w (1+idx*ew)) s ew)` by
    (qpat_assum `execution_frame u = execution_frame (store_copy_prefix _ _ _ s2 _)` mp_tac >>
     qpat_assum `execution_frame s2 = execution_frame s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >>
     mp_tac (Q.SPECL [`ew`,`if tr then LocTransient else LocStorage`,
       `(a:bytes32)+n2w (32+idx*ems)`,`(k:bytes32)+n2w (1+idx*ew)`,`s2`,`s`]
       store_copy_prefix_execution_frame) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (fn th => once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `execution_frame u = execution_frame (store_copy_prefix _ _ _ s _)`
       (mp_tac o Q.AP_TERM `\v. v.vs_labels`) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[execution_frame_def, place_store_prefix_fields]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x /\ not_fresh_at sg x` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x s1 = lookup_var x s /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x s2 = lookup_var x s1 /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sg x ==> lookup_var x u = lookup_var x s2 /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qexistsl_tac [`H`,`tt`,`u`] >> gvs[execution_frame_def]

QED

Finalise dyn_storage_multi_data_counted
