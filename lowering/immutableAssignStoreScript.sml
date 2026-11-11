(* Constructor immutable stores: execution and value representation boundary. *)
Theory immutableAssignStore
Ancestors
  immutableDeployOperandTransfer immutableDeployMeaningfulTransfer
  immutableDeployNormalize stmtSimDeclStore
  immutableBytestringRuntime immutableBytestringFootprint
  context immutableDeployAssignBytes immutableDeployAssignAdmissible
  vyperTypeValues exprLoweringProps venomInst compileEnv
Libs monadsyntax

Theorem immutable_assign_direct_store:
  compile_assign_value cenv dst LocCode src F src_loc dty sty mem_size sa = ((),sb) /\
  cenv.ce_imm_alloca = imm /\
  dty = sty /\ ~is_bytestring_type dty /\
  copy_size = mem_size /\
  n = (if copy_size <= 32 then 1 else (copy_size+31) DIV 32) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  k <= 32*n /\ a+k < dimword (:256) /\ b+32*n < dimword (:256) /\
  (a+k <= b \/ b+32*n <= a) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_in_memory stv v a s.vs_memory /\ val_footprint stv v <= k ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    gas_marked_path F ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    val_in_memory dtv v b u.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at b (type_memory_size dtv) u.vs_memory) /\
    (!p len. p+len <= b \/ b+32*n <= p ==>
      mem_bytes_at p len u.vs_memory = mem_bytes_at p len s.vs_memory) /\
    u.vs_immutables = (immutable_transfers T T (n2w a) (n2w b) n 0 s).vs_immutables
Proof
  strip_tac >> drule immutable_direct_composite_old_path >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >>
  disch_then (qspec_then `k` mp_tac) >>
  disch_then (qspecl_then [`func`,`ctx`,`b`,`a`] mp_tac) >>
  simp[GSYM arithmeticTheory.ADD_ASSOC] >>
  (impl_tac >- (simp[] >> gvs[] >> decide_tac)) >> strip_tac >>
  `val_in_memory dtv v b u.vs_memory /\
   immutable_value_bytes_rel dtv v (mem_bytes_at b (type_memory_size dtv) u.vs_memory)` by
    (irule immutable_direct_meaningful_transfer >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem immutable_assign_word_store:
  compile_assign_value cenv dst LocCode src T src_loc dty sty mem_size sa = ((),sb) /\
  (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME (n2w off) /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\
  off < dimword (:256) /\
  evaluate_type tenv dty = SOME tv /\ is_word_type dty /\ value_has_type tv v /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    gas_marked_path F ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    val_in_memory tv v off u.vs_memory /\
    immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) u.vs_memory) /\
    u.vs_memory = (mstore off (typed_val_to_w256 tv v) s).vs_memory /\
    u.vs_immutables = s.vs_immutables |+ (off,typed_val_to_w256 tv v)
Proof
  strip_tac >>
  `compile_imm_store_word cenv.ce_imm_alloca dst src sa = ((),sb)` by
    gvs[stmtLoweringTheory.compile_assign_value_def, comp_bind_def, comp_return_def] >>
  drule immutable_store_word_old_execution >>
  disch_then (qspecl_then [`typed_val_to_w256 tv v`,`s`,`n2w off`] mp_tac) >>
  simp[] >> strip_tac >>
  `val_in_memory tv v off (mstore off (typed_val_to_w256 tv v) s).vs_memory` by
    metis_tac[typed_word_store] >>
  `immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) t.vs_memory)` by
    (irule immutable_memory_bytes >> simp[] >>
     metis_tac[evaluated_immutable_admissible, evaluate_type_well_formed_type_value]) >>
  qexists_tac `t` >> simp[] >>
  irule placeTypedCopyPathTheory.place_copy_seq_path >> simp[] >>
  qexists_tac `sa` >>
  Cases_on `cenv.ce_imm_alloca` >>
  qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_store_word_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[same_blocks_def, emitted_insts_def,
    listTheory.DROP_APPEND, mk_inst_def, is_terminator_def,
    arithmeticTheory.SUB_PLUS]
QED

Theorem immutable_assign_normalized_compile:
  compile_assign_value cenv dst LocCode src F src_loc dty sty mem_size sa = ((),sb) /\
  dty <> sty /\ ~is_bytestring_type dty ==>
  ?buf mid sm.
    compile_alloc_buffer mem_size sa = (buf,mid) /\
    compile_store_memory_typed cenv buf.buf_operand dty src sty mid = ((),sm) /\
    (if (if is_bytestring_type dty then type_memory_bytes cenv sty else mem_size) <= 32 then
       (do loaded <- emit_op MLOAD [buf.buf_operand];
           compile_imm_store_word cenv.ce_imm_alloca dst loaded od)
     else compile_imm_store_words cenv.ce_imm_alloca buf.buf_operand dst
       (((if is_bytestring_type dty then type_memory_bytes cenv sty else mem_size)+31) DIV 32) 0)
      sm = ((),sb)
Proof
  simp[stmtLoweringTheory.compile_assign_value_def, comp_bind_def,
       comp_return_def] >> rpt strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      immutableCopyExecutionTheory.immutable_comp_bind_cases] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (res,sm)` >>
  Cases_on `res` >> metis_tac[]
QED

Theorem immutable_assign_normalized_store:
  compile_assign_value cenv dst LocCode src F src_loc dty sty L sa = ((),sb) /\
  dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w off) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  cenv.ce_imm_alloca = imm /\
  (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  L = type_memory_size dtv /\ L = 32*n /\ 0 < L /\ off+L < dimword (:256) ==>
  ?r q. stmt_state_rel ctx func cenv cx es r /\
    gas_marked_path F ctx func s 0 (OK r) /\
    gas_marked_path F ctx func r 0 (OK q) /\
    gas_marked_path F ctx func s 0 (OK q) /\
    val_in_memory dtv v off q.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at off L q.vs_memory) /\
    (!a k. regions_disjoint a k off L ==>
       mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x r) /\
    (q with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
              vs_immutables := r.vs_immutables; vs_prev_bb := r.vs_prev_bb;
              vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx|>) = r /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `~is_bytestring_type dty` by
    (drule_all immutable_normalized_copy_size >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all immutable_assign_normalized_compile >> strip_tac >>
  `(if is_bytestring_type dty then type_memory_bytes cenv sty else L) = L` by
    (drule_all immutable_normalized_copy_size >>
     disch_then (qspec_then `cenv` mp_tac) >>
     simp[GSYM arithmeticTheory.ADD_ASSOC] >>
     gvs[] >>
     qpat_x_assum `32 * n = type_memory_size dtv` (fn th => rewrite_tac[GSYM th]) >>
     simp[]) >>
  gvs[] >>
  drule immutable_normalized_composite_path >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `(if _ then _ else _) _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP cenv.ce_module_vars _ = _`)) >>
  disch_then (qspecl_then [`tenv`,`n`,`n2w off`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt strip_tac >> gvs[] >> metis_tac[])) >> strip_tac >>
  `val_in_memory dtv v off q.vs_memory /\
   immutable_value_bytes_rel dtv v
     (mem_bytes_at off (type_memory_size dtv) q.vs_memory)` by
    (`val_in_memory dtv v off q.vs_memory` by
       (irule valueEncodingPropsTheory.val_in_memory_relocate >>
        conj_tac >- simp[] >>
        qexistsl_tac [`r.vs_memory`,`type_memory_size dtv`,`w2n pw`] >> simp[]) >>
     simp[] >> irule immutable_memory_bytes >> simp[] >>
     metis_tac[evaluated_immutable_admissible, evaluate_type_well_formed_type_value]) >>
  `ci_mono sa mid` by
    metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono mid sm` by
    metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  qexistsl_tac [`r`,`q`] >> simp[] >>
  metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]
QED

Theorem immutable_assign_bytestring_store:
  compile_assign_value cenv dst LocCode src F src_loc dty sty mem_size sa = ((),sb) /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_in_memory stv v a s.vs_memory /\
  a + val_footprint stv v < dimword (:256) /\
  b + type_memory_size dtv < dimword (:256) /\
  (a + val_footprint stv v <= b \/ b + type_memory_size dtv <= a) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
       vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
       vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
    val_in_memory dtv v b q.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at b (type_memory_size dtv) q.vs_memory) /\
    (!p k. p+k <= b \/ b+type_memory_size dtv <= p ==>
       mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH q.vs_memory /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all immutable_bytestring_runtime_transfer >> strip_tac >>
  `compile_store_immutable_bytestring cenv.ce_imm_alloca src dst sa = ((),sb)` by
    gvs[stmtLoweringTheory.compile_assign_value_def, comp_bind_def, comp_return_def] >>
  `a < dimword (:256)` by decide_tac >>
  drule compile_store_immutable_bytestring_optional_path >>
  disch_then (qspecl_then [`s`,`len`,`func`,`ctx`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  `!n off r. (immutable_transfers T T (n2w a) (n2w b) n off r
      with <|vs_memory := r.vs_memory; vs_immutables := r.vs_immutables|>) = r` by
    (Induct >> simp[immutableCopyExecutionTheory.immutable_transfers_def] >>
     rpt gen_tac >>
     first_x_assum (qspecl_then [`off+32`,
       `immutable_word_transfer T T (n2w a) (n2w b) off r`] mp_tac) >>
     qmatch_goalsub_abbrev_tac `immutable_transfers T T _ _ n _ rr` >>
     qmatch_goalsub_abbrev_tac `tt with <|vs_memory := _; vs_immutables := _|>` >>
     simp[Abbr `rr`, immutableCopyExecutionTheory.immutable_word_transfer_def,
          venomExecSemanticsTheory.istore_def, venomStateTheory.mstore_def,
          venomStateTheory.venom_state_component_equality]) >>
  qexists_tac `t` >>
  qpat_x_assum `t with <|vs_vars := _; vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = _`
    mp_tac >>
  simp[venomStateTheory.venom_state_component_equality] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`word_size len + 1`,`0`,`s`] mp_tac) >>
  simp[venomStateTheory.venom_state_component_equality] >> strip_tac >> gvs[]
QED
