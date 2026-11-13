(* Zero-byte snapshot copies need no source-pointer frontier bound. *)
Theory bodyMemSnapshotStoreRoom
Ancestors
  bodyMemSnapshotStore bodyMemSnapshotResult bodyMemSnapshotFrame
  exprSimBufferStore exprSimProps exprSimMemDefs loweringPosts
  exprLowering exprLoweringProps loweringSlice context compileEnv fragGasPathMem venomExecSemantics
  loweringStateRelDefs

Theorem snapshot_zero_store_identity[local]:
  compile_store_memory ce src dst ty ty sc = ((),sb) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv = 0 /\ eval_operand src s = SOME w /\
  eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sc x) ==>
  sb = sc /\ val_in_memory tv v (w2n d) s.vs_memory
Proof
  strip_tac >>
  `~is_bytestring_type ty` by
    (strip_tac >> drule_all buffer_typed_bytestring_header >> strip_tac >>
     `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
     gvs[]) >>
  `expr_val_rel cx ty v src s` by simp[expr_val_rel_def] >>
  `type_memory_size tv < dimword (:256)` by simp[] >>
  drule_all buffer_store_memory_encoding >> strip_tac >>
  gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def,
      emitted_insts_def, run_inst_seq_def]
QED

Theorem snapshot_store_result_room_mem:
  compile_store_memory ce src dst lt lt sc = ((),sb) /\
  post_value_type ce e = expr_type e /\
  (lt = expr_type e \/ is_bytestring_type (expr_type e) /\
    is_bytestring_type lt /\ arg_type_fits lt (expr_type e)) /\
  ~is_word_type (expr_type e) /\ ~is_word_type lt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) lt = SOME ltv /\
  value_has_type tv v /\ value_has_type ltv v /\ val_wf ltv v /\
  read_result cx raw ee = (INL v,ee) /\
  val_in_memory ltv v (w2n w) s.vs_memory /\
  type_memory_bytes ce lt = type_memory_size ltv /\
  type_memory_size ltv < dimword (:256) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  (type_memory_size ltv = 0 \/
   w2n w + type_memory_size ltv <= s.vs_alloca_next) /\
  w2n d + type_memory_size ltv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sc x) /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  expr_post ctx func ce cx e es sa sc s0 ee v src s /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= inst.inst_id /\
  inst.inst_id < sb.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size ltv) /\
  (!n b len. local_region ce ee.scopes s n b len ==>
    regions_disjoint (w2n d) (type_memory_size ltv) b len) /\
  (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id ==>
    regions_disjoint (w2n d) (type_memory_size ltv) off len) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    vv_post ctx func ce cx e es sa sb s0 ee raw
      (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
    vv_own ce cx (expr_type e) sm sb ee raw
      (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
    pure_frame ce func ee sm s z /\
    vv_store_bound cx (expr_type e) lt ee raw
      (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `type_memory_size ltv = 0`
  >- (drule_all snapshot_zero_store_identity >> strip_tac >>
      qpat_x_assum `sb = sc` SUBST_ALL_TAC >>
      `vv_holds ce cx (expr_type e) raw
         (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) ee s /\
       vv_at ce cx (expr_type e) sa sc ee raw
         (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) s /\
       vv_own ce cx (expr_type e) sm sc ee raw
         (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) s /\
       vv_store_bound cx (expr_type e) lt ee raw
         (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) s` by
        (irule snapshot_located_result_facts >> simp[] >>
         qexists_tac `inst.inst_id` >>
         simp[regions_disjoint_def] >> rpt strip_tac >>
         qpat_x_assum `!n b len. local_region _ _ _ _ _ _ ==> _` drule >>
         simp[regions_disjoint_def]) >>
      `vv_post ctx func ce cx e es sa sc s0 ee raw
         (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) s /\
       pure_frame ce func ee sm s s` by
        (irule snapshot_store_post_frame >> simp[] >>
         conj_tac
         >- (qexistsl_tac [`w2n d`, `inst`, `type_memory_size ltv`] >>
             simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
         metis_tac[]) >>
      qexists_tac `s` >> simp[cj 1 gas_path_mem_rules]) >>
  irule snapshot_store_result_mem >> simp[] >>
  qexistsl_tac [`inst`, `sc`, `src`, `w`] >>
  simp[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED
