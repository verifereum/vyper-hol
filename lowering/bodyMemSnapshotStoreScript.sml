(* Counted typed snapshot stores at the lowered annotation. *)
Theory bodyMemSnapshotStore
Ancestors
  bodyMemSnapshotResult bodyMemSnapshotFrame exprSimCopy exprSimStorageCopy
  bodyCopyMemory bodyMemAggregateStore exprSimBufferStore exprSimMemUnwrap
  valueCopyBytes exprSimProps exprSimMemDefs loweringPosts exprLoweringProps
  exprLowering context compileEnv freshWrites loweringStateRelDefs
  valueEncodingProps fragGasPathMem
  venomState venomInst venomExecSemantics

Theorem snapshot_nonword_store_mem_ok[local]:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `is_bytestring_type ty`
  >- (drule_all buffer_typed_bytestring_header >> strip_tac >>
      `val_store_size tv v <= type_memory_size tv` by
        metis_tac[val_store_size_le] >>
      gvs[compile_store_memory_def] >>
      irule compile_store_bytestring_body_mem_ok >>
      qexistsl_tac [`d`, `dst`, `len`, `src`, `w`] >> simp[] >>
      metis_tac[]) >>
  gvs[compile_store_memory_def] >>
  irule compile_copy_memory_body_mem_ok >>
  qexistsl_tac [`d`, `dst`, `type_memory_size tv`, `src`, `w`] >> simp[]
QED

Theorem snapshot_nonword_store_path_mem:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    val_in_memory tv v (w2n d) z.vs_memory /\
    (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
       mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    alloca_history func z /\ ~z.vs_halted /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `expr_val_rel cx ty v src s` by simp[expr_val_rel_def] >>
  drule_all snapshot_nonword_store_mem_ok >> strip_tac >>
  drule_all buffer_store_memory_encoding >> strip_tac >>
  drule_all buffer_store_memory_capacity >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  drule aggregate_store_memory_no_gas >> strip_tac >>
  drule_all straight_path_mem >> strip_tac >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[lookup_var_def] >>
  qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >>
  metis_tac[lookup_var_def, arithmeticTheory.ADD_COMM]
QED

Theorem snapshot_store_result_mem:
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
  w2n w + type_memory_size ltv <= s.vs_alloca_next /\
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
  drule_all snapshot_nonword_store_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `copy_static z = copy_static s` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
      mp_tac >> simp[copy_static_def, venom_state_component_equality] >>
     rpt strip_tac >> simp[]) >>
  drule copy_static_fields >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  `eval_operand dst z = SOME d` by
    (Cases_on `dst` >> gvs[eval_operand_def]) >>
  `!n b len. local_region ce ee.scopes z n b len ==>
    regions_disjoint (w2n d) (type_memory_size ltv) b len` by
    (rpt strip_tac >>
     `local_region ce ee.scopes s n b len` by
       metis_tac[copy_buffer_local_region_frame] >>
     metis_tac[]) >>
  `vv_holds ce cx (expr_type e) raw
     (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) ee z /\
   vv_at ce cx (expr_type e) sa sb ee raw
     (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
   vv_own ce cx (expr_type e) sm sb ee raw
     (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
   vv_store_bound cx (expr_type e) lt ee raw
     (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z` by
    (irule snapshot_located_result_facts >> simp[] >>
     qexists_tac `inst.inst_id` >>
     simp[regions_disjoint_def] >>
     metis_tac[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  `vv_post ctx func ce cx e es sa sb s0 ee raw
     (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
   pure_frame ce func ee sm s z` by
    (irule snapshot_store_post_frame >> simp[] >>
     conj_tac
     >- (qexistsl_tac [`w2n d`, `inst`, `type_memory_size ltv`] >>
         simp[arithmeticTheory.ADD_COMM] >>
         rpt conj_tac >- metis_tac[] >- metis_tac[] >>
         rpt strip_tac >>
         qpat_x_assum `!a k. _ ==> mem_bytes_at _ _ z.vs_memory = _` irule >>
         decide_tac) >>
     metis_tac[]) >>
  qexists_tac `z` >> simp[]
QED
