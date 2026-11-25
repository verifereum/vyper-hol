(* The ordinary Slice writes a length header and exactly the selected payload. *)
Theory bodySliceWindowValueMods
Ancestors
  bodyFullPostsMods exprSimSliceData exprSimHash exprSimProps
  reasonCodeResourcesPtr bodyPtrAttributeFields bodyPtrDefs exprSimMemDefs
  valueEncoding valueEncodingDefs vyperValue vyperState vyperAST
  loweringPosts loweringStateRelDefs compileEnv exprLowering
  context venomState vfmConstants words list

Triviality slice_window_encoding:
  mem_bytes_at (w2n p) (LENGTH bs) za.vs_memory = bs /\
  i + k <= LENGTH bs /\ k <= n /\
  ((a = BaseT (BytesT (Dynamic n)) /\ result = BytesV (TAKE k (DROP i bs))) \/
   (?str. a = BaseT (StringT n) /\ bs = MAP (n2w o ORD) str /\
          result = StringV (TAKE k (DROP i str)))) /\
  N = type_memory_bytes cenv a /\ 32 + n <= N /\ N < dimword (:256) /\
  target.vs_memory =
    (mstore (w2n w) (n2w k) (mcopy (w2n w + 32) (w2n p + i) k za)).vs_memory ==>
  ~is_word_type a /\
  ?vt. evaluate_type (get_tenv cx) a = SOME vt /\
       type_memory_size vt = N /\ val_wf vt result /\
       val_footprint vt result = 32 + k /\ val_store_size vt result <= N /\
       val_in_memory vt result (w2n w) target.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `word_size k <= word_size n` by (irule word_size_monotone >> simp[]) >>
  qpat_x_assum `(_ /\ _) \/ (?str. _)` (DISJ_CASES_THEN STRIP_ASSUME_TAC) >>
  gvs[is_word_type_def] >-
   (`LENGTH (TAKE k (DROP i bs)) = k` by (simp[LENGTH_TAKE,LENGTH_DROP] >> decide_tac) >>
    `val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE k (DROP i bs)))
        (w2n w) target.vs_memory` by
      (simp[] >> `i + w2n p = w2n p + i` by decide_tac >>
       pop_assum (fn th => pure_rewrite_tac[th]) >>
       irule slice_copy_store_encoding >> simp[]) >>
    pop_assum mp_tac >>
    fs[evaluate_type_def,type_memory_bytes_def,type_memory_size_def,type_slot_size_def,
       word_size_def,val_wf_def,val_footprint_def,val_store_size_def] >> decide_tac) >>
  `LENGTH (TAKE k (DROP i str)) = k` by (simp[LENGTH_TAKE,LENGTH_DROP] >> decide_tac) >>
  `val_in_memory (BaseTV (StringT n)) (StringV (TAKE k (DROP i str)))
      (w2n w) target.vs_memory` by
    (simp[] >> `i + w2n p = w2n p + i` by decide_tac >>
     pop_assum (fn th => pure_rewrite_tac[th]) >>
     irule slice_copy_store_string_encoding >> simp[]) >>
  pop_assum mp_tac >>
  fs[evaluate_type_def,type_memory_bytes_def,type_memory_size_def,type_slot_size_def,
     word_size_def,val_wf_def,val_footprint_def,val_store_size_def] >> decide_tac
QED

Theorem slice_window_value_mods:
  i + k <= LENGTH bs /\ i < dimword (:256) /\ k < dimword (:256) /\
  (i + k <= LENGTH bs ==> k <= n) /\
  ((a = BaseT (BytesT (Dynamic n)) /\ result = BytesV (TAKE k (DROP i bs))) \/
   (?str. a = BaseT (StringT n) /\ bs = MAP (n2w o ORD) str /\
          result = StringV (TAKE k (DROP i str)))) /\
  e = Builtin a (Slice n) args /\ N = type_memory_bytes cenv a /\
  32 + n <= N /\ N < dimword (:256) /\
  mem_bytes_at (w2n p) (LENGTH bs) za.vs_memory = bs /\
  target.vs_memory =
    (mstore (w2n w) (n2w k)
      (write_memory_with_expansion (w2n w + 32) (TAKE k (DROP i bs)) za)).vs_memory /\
  (!j. w2n w <= j /\ j < w2n w + 32 + k ==> j NOTIN tm.t_mem) /\
  out = Var root /\ lookup_var root target = SOME w /\ ptr_covers G3 tm root target N /\
  FLOOKUP target.vs_allocas aid = SOME (w2n w,N) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  w2n w + N <= target.vs_alloca_next /\
  (!name b len. local_region cenv es.scopes target name b len ==>
                regions_disjoint (w2n w) N b len) /\
  stmt_state_rel H ctx func cenv cx es target /\
  storage_well_formed_on cx es (FST H) /\
  immutable_frame_mods func cenv cx es target /\
  wb_frame cenv es es sa s target /\ pure_frame cenv func es sa s target ==>
  vv_post_mods H ctx func cenv cx e es sa sb s es (Value result)
    (LocatedValue a (mk_ptr out LocMemory)) target /\
  vv_store_bound cx a a es (Value result) (LocatedValue a (mk_ptr out LocMemory)) target /\
  ptr_vv_ok cx a (Value result) (LocatedValue a (mk_ptr out LocMemory)) es G3 tm target /\
  ptr_buf_ok cenv e out G3 target
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `k <= n` by simp[] >>
  `target.vs_memory =
    (mstore (w2n w) (n2w k) (mcopy (w2n w + 32) (w2n p + i) k za)).vs_memory` by
    (drule_all_then (qspec_then `w2n (w:bytes32) + 32` SUBST1_TAC) slice_mcopy_payload >> simp[]) >>
  drule_all_then (qspec_then `cx` strip_assume_tac) slice_window_encoding >>
  ntac 2 (qpat_x_assum `target.vs_memory = _` kall_tac) >>
  `32 + k <= N` by decide_tac >>
  `ptr_mem_ok cx a result (Var root) G3 tm target` by
    (irule clean_memory_representation_ptr >>
     qexistsl_tac [`w`,`N`,`vt`] >> simp[] >> gen_tac >> disch_tac >>
     qpat_assum `!j. w2n w <= j /\ _ ==> _` irule >> decide_tac) >>
  `vv_post H ctx func cenv cx e es sa sb s es (Value result)
    (LocatedValue a (mk_ptr out LocMemory)) target` by
    (qpat_x_assum `e = _` SUBST_ALL_TAC >> qpat_x_assum `out = _` SUBST_ALL_TAC >>
     irule (SIMP_RULE (srw_ss()) [expr_type_def]
       (Q.INST [`e` |-> `Builtin a (Slice n) args`] vv_post_allocated_memory_intro)) >>
     simp[post_value_type_def,mk_ptr_def,eval_operand_def] >>
     qexistsl_tac [`aid`,`w2n w`,`N`] >>
     simp[GSYM regions_disjoint_def] >> rpt strip_tac >>
     qpat_assum `!name b len. local_region _ _ _ name b len ==> _` (drule_then mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[NoAsms,vv_post_mods_def,vv_post_def,vv_holds_mods_def,vv_place_ptr_mods_def,mk_ptr_def] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp[vv_store_bound_def,mk_ptr_def,read_result_def,return_def,eval_operand_def] >>
      rpt strip_tac >> gvs[] >> decide_tac) >>
  qpat_x_assum `(_ /\ _) \/ (?str. _)` kall_tac >>
  conj_tac
  >- (`op_taint tm (Var root) = {}` by fs[ptr_covers_def] >>
      irule ptr_vv_ok_memory >> simp[mk_ptr_def,read_result_def,return_def]) >>
  qpat_x_assum `ptr_covers _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ptr_covers_def]) >>
  simp[ptr_buf_ok_def,eval_operand_def,lowered_value_type_def,expr_type_def] >>
  qexistsl_tac [`b`,`sz`] >> fs[]
QED
