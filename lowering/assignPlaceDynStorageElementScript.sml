(* Exact storage folds for one element of a runtime-length copy. *)
Theory assignPlaceDynStorageElement
Ancestors
  assignPlaceDynStoragePaths stmtSimStoreCopy bodyMemAssignTopCopyPaths
  venomState words arithmetic list rich_list

Theorem dyn_storage_prefix_normalize:
  store_copy_normalize initial (store_copy_prefix loc a q s n) =
  store_copy_prefix loc a q (store_copy_normalize initial s) n
Proof
  Induct_on `n` >>
  simp[topcopy_prefix_suc, topcopy_normalize_store] >>
  simp[store_copy_normalize_def, mload_def]
QED

Theorem dyn_storage_normalize_compose:
  store_copy_normalize mid t = store_copy_prefix loc a q mid n ==>
  store_copy_normalize initial t =
    store_copy_prefix loc a q (store_copy_normalize initial mid) n
Proof
  strip_tac >>
  first_x_assum (mp_tac o Q.AP_TERM `store_copy_normalize initial`) >>
  simp[dyn_storage_prefix_normalize] >>
  simp[store_copy_normalize_def]
QED

Theorem dyn_storage_outer_fold_suc:
  FOLDL (\s j. store_copy_prefix loc
      (b + (32w + n2w j * n2w stride))
      (k + (1w + n2w j * n2w ew)) s ew) initial (COUNT_LIST (SUC n)) =
  store_copy_prefix loc (b + (32w + n2w n * n2w stride))
    (k + (1w + n2w n * n2w ew))
    (FOLDL (\s j. store_copy_prefix loc
       (b + (32w + n2w j * n2w stride))
       (k + (1w + n2w j * n2w ew)) s ew) initial (COUNT_LIST n)) ew
Proof
  simp[COUNT_LIST_SNOC, FOLDL_SNOC]
QED

Theorem dyn_storage_outer_fold_frame:
  (FOLDL (\s j. store_copy_prefix loc
      (b + (32w + n2w j * n2w stride))
      (k + (1w + n2w j * n2w ew)) s ew) initial (COUNT_LIST n)) with
    <|vs_accounts := initial.vs_accounts;
      vs_transient := initial.vs_transient|> = initial
Proof
  Induct_on `n` >- simp[COUNT_LIST_def] >>
  simp[dyn_storage_outer_fold_suc] >>
  qmatch_goalsub_abbrev_tac `store_copy_prefix loc a q ss ew` >>
  `!m. (store_copy_prefix loc a q ss m) with
     <|vs_accounts := initial.vs_accounts;
       vs_transient := initial.vs_transient|> = initial` suffices_by simp[] >>
  Induct >> simp[topcopy_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem dyn_storage_element_path_mem:
  emit_op MUL [Var cv;Lit (n2w (if ew = 1 then 32 else ems))] b1 = (scaled,b2) /\
  emit_op ADD [Lit 32w;scaled] b2 = (off,b3) /\
  emit_op ADD [src;off] b3 = (sp,b4) /\
  (if ew = 1 then
     emit_op MLOAD [sp] b4 = (value,b5) /\
     emit_op ADD [Var cv;Lit 1w] b5 = (slot_off,b6) /\
     emit_op ADD [dst;slot_off] b6 = (dp,b7) /\
     emit_void (if tr then TSTORE else SSTORE) [dp;value] b7 = ((),b8)
   else
     emit_op MUL [Var cv;Lit (n2w ew)] b4 = (slot_scaled,b5) /\
     emit_op ADD [Lit 1w;slot_scaled] b5 = (slot_off,b6) /\
     emit_op ADD [dst;slot_off] b6 = (dp,b7) /\
     compile_word_copy_loop sp dp ew LocMemory
       (if tr then LocTransient else LocStorage) F b7 = (u,b8)) /\
  fn_has_code b1 b4 func /\ fn_has_code b4 b8 func /\
  fn_has_code b4 b7 func /\ fn_has_code b7 b8 func /\
  b1.cs_next_var <= b4.cs_next_var /\ b4.cs_next_var <= b7.cs_next_var /\
  not_fresh_at b1 cv /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at b1 x) /\
  eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
  eval_operand (Var cv) s = SOME (n2w j) /\ ew < dimword (:256) /\
  w2n (b + (32w + n2w j * n2w (if ew = 1 then 32 else ems))) +
    32*ew <= s.vs_alloca_next /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = b1.cs_current_bb /\
  s.vs_inst_idx = LENGTH b1.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t = store_copy_prefix
      (if tr then LocTransient else LocStorage)
      (b + (32w + n2w j * n2w (if ew = 1 then 32 else ems)))
      (k + (1w + n2w j * n2w ew)) s ew /\
    (!x. not_fresh_at b1 x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = b8.cs_current_bb /\
    t.vs_inst_idx = LENGTH b8.cs_current_insts
Proof
  strip_tac >>
  `?mid. gas_marked_path T ctx func s 0 (OK mid) /\
    eval_operand sp mid = SOME (b + (32w + n2w j *
      n2w (if ew = 1 then 32 else ems))) /\
    (mid with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at b1 x ==> lookup_var x mid = lookup_var x s) /\
    ~mid.vs_halted /\ mid.vs_current_bb = b4.cs_current_bb /\
    mid.vs_inst_idx = LENGTH b4.cs_current_insts` by
    (irule dyn_storage_scaled_address_compile_path_mem >>
     metis_tac[]) >>
  Cases_on `ew = 1` >- suspend "singleton" >> suspend "nested"
QED

Resume dyn_storage_element_path_mem[singleton]:
  gvs[] >>
  `not_fresh_at b4 cv /\
   (!x. dst = Var x ==> not_fresh_at b4 x)` by
    (metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `mid.vs_alloca_next = s.vs_alloca_next /\
   mid.vs_call_ctx = s.vs_call_ctx /\ mid.vs_labels = s.vs_labels` by
    (qpat_assum `mid with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand dst mid = SOME k /\
   eval_operand (Var cv) mid = SOME (n2w j)` by
    (Cases_on `dst` >> gvs[eval_operand_def]) >>
  `~mid.vs_call_ctx.cc_static /\
   w2n (b + (32w + n2w j * 32w)) + 32 <= mid.vs_alloca_next` by simp[] >>
  drule_all dyn_storage_singleton_compile_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexists_tac `t` >> conj_tac
  >- (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  reverse conj_tac
  >- (simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `store_copy_normalize s mid = s` by
    gvs[store_copy_normalize_def, venom_state_component_equality] >>
  qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = _`
    (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >>
  Cases_on `tr` >>
  gvs[store_copy_normalize_def, store_copy_prefix_def,
       sstore_def, tstore_def, mload_def, WORD_ADD_COMM,
       venom_state_component_equality, WORD_ADD_0, WORD_MULT_CLAUSES]
QED

Resume dyn_storage_element_path_mem[nested]:
  gvs[] >>
  `!x. dst = Var x ==> not_fresh_at b4 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `mid.vs_labels = s.vs_labels` by
    (qpat_assum `mid with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand dst mid = SOME k /\
   eval_operand (Var cv) mid = SOME (n2w j)` by
    (Cases_on `dst` >> gvs[eval_operand_def]) >>
  `?next. gas_marked_path T ctx func mid 0 (OK next) /\
    eval_operand dp next = SOME (k + (1w + n2w j * n2w ew)) /\
    next with <|vs_vars := mid.vs_vars; vs_inst_idx := mid.vs_inst_idx|> = mid /\
    (!x. not_fresh_at b4 x ==> lookup_var x next = lookup_var x mid) /\
    ~next.vs_halted /\ next.vs_current_bb = b7.cs_current_bb /\
    next.vs_inst_idx = LENGTH b7.cs_current_insts` by
    (irule dyn_storage_scaled_address_compile_path_mem >> metis_tac[]) >>
  `(!x. sp = Var x ==> not_fresh_at b4 x) /\
   (!x. dp = Var x ==> not_fresh_at b7 x)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh] >>
  `eval_operand sp next = SOME (b + (32w + n2w j * n2w ems))` by
    (Cases_on `sp` >> gvs[eval_operand_def] >>
     qpat_assum `next with <|vs_vars := _; vs_inst_idx := _|> = mid` mp_tac >>
     simp[venom_state_component_equality]) >>
  `(!x. sp = Var x \/ dp = Var x ==> not_fresh_at b7 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `~next.vs_call_ctx.cc_static /\
   w2n (b + (32w + n2w j * n2w ems)) + 32*ew <= next.vs_alloca_next` by
    (gvs[venom_state_component_equality] >> decide_tac) >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    topcopy_compile_loop_path >>
  disch_then (qspecl_then [`ctx`, `func`, `next`,
    `b + (32w + n2w j * n2w ems)`, `k + (1w + n2w j * n2w ew)`] mp_tac) >>
  (impl_tac >- (simp[] >> Cases_on `tr` >> metis_tac[])) >> strip_tac >>
  gvs[store_copy_frame_def] >>
  qexists_tac `t` >> conj_tac
  >- (`gas_marked_path T ctx func mid 0 (OK t)` by
        (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
      qpat_x_assum `gas_marked_path T ctx func mid 0 (OK next)` kall_tac >>
      qpat_x_assum `gas_marked_path T ctx func next 0 (OK t)` kall_tac >>
      drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  reverse conj_tac
  >- (simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  drule dyn_storage_normalize_compose >>
  disch_then (qspec_then `s` mp_tac) >>
  `store_copy_normalize s next = s` by
    gvs[store_copy_normalize_def, venom_state_component_equality] >>
  simp[]
QED

Finalise dyn_storage_element_path_mem
