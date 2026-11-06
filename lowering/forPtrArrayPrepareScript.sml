(* Checked finite prefixes of the array loop, ending at the actual body
   compilation point rather than at an erased S1 execution. *)
Theory forPtrArrayPrepare
Ancestors forPtrRangePrepare forPtrAddress forPtrWriteScope forPtrArraySnapshot
  forPtrWord forPtrBulk forPtrBytes forPtrCopyInterface stmtSimForArrayLoop
  fragExec emitHelperProps finite_map list forPtrControl venomState ptrDiscipline
  exprSimProps typedCopyAgreement context compileEnv valueEncoding stmtLowering
  exprLoweringProps rich_list forPtrElementFrame bodyPtrDefs forPtrScope
  exprSimPtrLiteralBuffer venomInst venomExecSemantics vyperState loweringPosts emitHelper fragGasSeqPtr fragGasPathPtr

Theorem for_array_header_test_path_ptr:
  lookup_block cond_lbl func.fn_blocks =
    SOME <| bb_label := cond_lbl;
      bb_instructions := [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
        mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
  lookup_var idx s = SOME (n2w k) /\
  op_taint tn (Var idx) = {} /\ op_prov G (Var idx) = NONE ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {dv}))
    (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to (if (n2w k : bytes32) = n2w n then exit_lbl else stmts_lbl)
      (update_var dv (if (n2w k : bytes32) = n2w n then 1w else 0w) s)))
Proof
  strip_tac >> irule for_counter_test_path_ptr >> simp[] >>
  qexistsl_tac [`Lit (n2w n)`, `idx`, `j1`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := []; cs_next_id := j1 |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
         mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv]];
       cs_next_id := j2 |>`] >>
  simp[fn_has_code_def, emitted_blocks_def, eval_operand_def,
       op_taint_def, op_prov_def]
QED

(* The current word-copy interface's four primitive value constructors do
   not cover AddressT (or fixed byte words). This checked probe records the
   missing branch without changing the frozen For theorem. *)
Theorem for_array_address_word_copy_gap:
  is_word_type (BaseT AddressT) /\
  evaluate_type FEMPTY (BaseT AddressT) = SOME (BaseTV AddressT) /\
  value_has_type (BaseTV AddressT) (BytesV (REPLICATE 20 0w)) /\
  ~((?x. BytesV (REPLICATE 20 0w) = BoolV x) \/
    (?x. BytesV (REPLICATE 20 0w) = IntV x) \/
    (?x. BytesV (REPLICATE 20 0w) = FlagV x) \/
    (?x. BytesV (REPLICATE 20 0w) = DecimalV x))
Proof
  EVAL_TAC >> simp[]
QED

Theorem for_array_bytes_copy_frames:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ type_memory_size tv < dimword (:256) /\
  ptr_covers G tn src s (type_memory_size tv) /\ ~ctx_has_dalloca ctx /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) /\
  run_inst_seq (emitted_insts sa sb) s = OK sf /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s gf tf ==>
  (!i. i < w2n b \/ w2n b + type_memory_size tv <= i ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient
Proof
  strip_tac >> drule_all for_bytes_typed_layout >> strip_tac >>
  `mload (w2n a) s = n2w len /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)` by
    (irule for_bytes_copy_header >> metis_tac[]) >>
  `32 + 32 * word_size cap < dimword (:256)` by metis_tac[] >>
  drule_all for_bytes_runtime_extent >> strip_tac >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac) >>
  `w2n (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) <=
    type_memory_size tv` by metis_tac[] >>
  drule_all compile_bytes_copy_endpoint_frames >> simp[]
QED

(* A common finite-copy boundary: the endpoint and ghost witnesses are the
   same for checked execution, robust representation and old-variable frame. *)
Theorem for_array_element_copy_checked:
  compile_iter_elem_copy cenv (Var src) (Var dst) stride LocMemory F ty ty
    sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  ptr_covers G tn src s (type_memory_size tv) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  ~ctx_has_dalloca ctx /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?gf tf sf.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s gf tf /\
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + type_memory_size tv}
      sf.vs_memory s.vs_memory /\
    (!i. i < w2n b \/ w2n b + type_memory_size tv <= i ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (drule_all word_tv_memory_size >> strip_tac >>
      `compile_store_memory_typed cenv (Var dst) ty (Var src) ty sa = ((),sb)` by
        gvs[compile_store_memory_typed_word, for_memory_element_copy_dispatch] >>
      fs[] >> drule_all for_compile_word_copy_checked >>
      disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
      `emitted_insts sa sb =
        [mk_inst id MLOAD [Var src] [tmp];
         mk_inst (id+1) MSTORE [Var dst; Var tmp] []]` by
        simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
      drule_all word_copy_endpoint_frames >> strip_tac >>
      qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]) >>
  Cases_on `is_bytestring_type ty`
  >- (drule_all for_iter_bytes_copy_checked >>
      disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
      `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s gf tf` by
        (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
          (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
      `compile_store_bytestring (Var src) (Var dst) sa = ((),sb)` by
        gvs[for_memory_element_copy_dispatch] >>
      drule_all for_array_bytes_copy_frames >> strip_tac >>
      qexistsl_tac [`gf`, `tf`, `sf`] >> fs[arithmeticTheory.ADD_COMM] >>
      first_assum ACCEPT_TAC) >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  drule_all for_iter_bulk_copy_checked >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  `compile_copy_memory (Var dst) (Var src) (type_memory_size tv) sa = ((),sb)` by
    gvs[for_memory_element_copy_dispatch] >>
  drule_all compile_bulk_copy_endpoint_frames >> strip_tac >>
  qexistsl_tac [`G`, `tf`, `sf`] >> fs[arithmeticTheory.ADD_COMM] >>
  first_assum ACCEPT_TAC
QED

(* The recorded allocation separates the whole element write, even on a
   re-executed site. Install the new binding only after the finite copy. *)
Theorem for_array_element_install_checked:
  compile_iter_elem_copy cenv (Var src) (Var dst) stride LocMemory F ty ty
    sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  ptr_covers G tn src s (type_memory_size tv) /\
  ptr_covers G tn dst s cap /\ ~ctx_has_dalloca ctx /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [dst] /\ not_local_ptr cenv es.scopes dst /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n b,cap) /\
  type_memory_size tv <= cap /\ local_ptrs_reserved bc sa /\ 
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
    cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var dst) cap) ==>
  ?gf tf sf.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s gf tf /\
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    ghost_inv d bc cx (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes)
      gf tf sf /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `ptr_covers G tn dst s (type_memory_size tv)` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac) >>
  drule_all for_array_element_copy_checked >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`gf`, `tf`, `sf`] >> simp[] >>
  irule ghost_inv_install_after_separated_write >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      `lookup_var dst sf = lookup_var dst s /\ FLOOKUP gf dst = FLOOKUP G dst /\
       op_taint tf (Var dst) = op_taint tn (Var dst)` by metis_tac[] >>
      drule_all for_ptr_covers_transport >> simp[]) >>
  qexistsl_tac [`G`, `cenv`, `{p | not_fresh_at sa p}`, `s`, `tn`,
    `{i | w2n b <= i /\ i < w2n b + type_memory_size tv}`] >>
  simp[] >> conj_tac >- (first_assum ACCEPT_TAC) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name` by
        (drule_all cenv_top_ext_outer_lookup >> simp[]) >>
      `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      simp[] >> drule_all for_alloca_scalar_write_separation >>
      simp[arithmeticTheory.ADD_COMM, arithmeticTheory.NOT_LESS_EQUAL,
           arithmeticTheory.NOT_LESS]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

(* Address arithmetic gives its temporary pointer provenance. No live local
   or return-buffer pointer is changed by assigning that provenance. *)
Theorem for_nonlocal_provenance_ghost:
  ghost_inv d cenv cx es G tn s /\ not_local_ptr cenv es.scopes out /\
  (!sz. cenv.ce_return_buf <> SOME (PtrVar (Var out) sz)) /\
  (!x. x <> out ==> FLOOKUP Gf x = FLOOKUP G x) ==>
  ghost_inv d cenv cx es Gf tn s
Proof
  strip_tac >> fs[ghost_inv_def, not_local_ptr_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> `p <> out` by metis_tac[] >>
      qpat_x_assum `!name entry p sz. _` drule_all >>
      simp[ptr_covers_def]) >>
  Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
  fs[return_buf_ptr_def] >>
  rename1 `cenv.ce_return_buf = SOME (PtrVar (Var rp) slot_size)` >>
  `rp <> out` by metis_tac[] >> gvs[ptr_covers_def]
QED

Theorem for_element_address_outer_ghost:
  ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  (!sz. cenv.ce_return_buf <> SOME (PtrVar (Var ov) sz) /\
    cenv.ce_return_buf <> SOME (PtrVar (Var ep) sz)) ==>
  ghost_inv d cenv cx es
    (set_prov (DRESTRICT G (COMPL {ov})) [ep] prov)
    (tn with t_var := (tn.t_var |+ (ov,{})) |+ (ep,{}))
    ((update_var ep w (update_var ov delta s)) with vs_inst_idx := n)
Proof
  strip_tac >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {ov}))
    (tn with t_var := tn.t_var |+ (ov,{})) (update_var ov delta s)` by
    (irule for_scalar_overwrite_ghost >> simp[]) >>
  `ghost_inv d cenv cx es (DRESTRICT (DRESTRICT G (COMPL {ov})) (COMPL {ep}))
    (tn with t_var := (tn.t_var |+ (ov,{})) |+ (ep,{}))
    (update_var ep w (update_var ov delta s))` by
    (irule (SRULE [] (Q.INST
      [`tn` |-> `tn with t_var := tn.t_var |+ (ov,{})`]
      for_scalar_overwrite_ghost)) >> simp[]) >>
  simp[SRULE [] (Q.INST [`gs` |-> `es.gas_obs`] literal_ptr_ghost_inv_normalize)] >>
  irule for_nonlocal_provenance_ghost >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {ov})) (COMPL {ep})`, `ep`] >>
  simp[] >> Cases_on `prov` >>
  simp[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem for_element_address_slice_coverage:
  ptr_covers G tn bp s ((k+1)*stride) /\ lookup_var bp s = SOME w /\
  w2n w + k*stride < dimword (:256) /\
  lookup_var ep sA = SOME (w + n2w k * n2w stride) /\
  FLOOKUP GA ep = FLOOKUP G bp /\ op_taint tA (Var ep) = {} ==>
  ptr_covers GA tA ep sA stride
Proof
  strip_tac >>
  `w2n (w + n2w k * n2w stride) = w2n w + k*stride` by
    (`k*stride < dimword (:256)` by decide_tac >>
     simp[wordsTheory.word_mul_n2w, wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  gvs[ptr_covers_def, arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac
QED

Theorem for_element_address_ready_ptr:
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  (!sz. cenv.ce_return_buf <> SOME (PtrVar (Var ov) sz) /\
    cenv.ce_return_buf <> SOME (PtrVar (Var ep) sz)) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst j4 ADD [Var bp; Var ov] [ep]) /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var bp s = SOME w /\
  ptr_covers G tn bp s ((k+1)*stride) /\
  w2n w + k*stride < dimword (:256) /\
  op_taint tn (Var idx) = {} /\ bp <> ov /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  sA = ((update_var ep (w + n2w k * n2w stride)
    (update_var ov (n2w k * n2w stride) s))
      with vs_inst_idx := SUC (SUC s.vs_inst_idx)) /\
  GA = set_prov (DRESTRICT G (COMPL {ov})) [ep] (FLOOKUP G bp) /\
  tA = (tn with t_var := (tn.t_var |+ (ov,{})) |+ (ep,{})) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 GA tA (OK sA) /\
  stmt_state_rel ctx func cenv cx es sA /\ ghost_inv d cenv cx es GA tA sA /\
  ptr_covers GA tA ep sA stride /\
  lookup_var ep sA = SOME (w + n2w k * n2w stride) /\
  sA.vs_memory = s.vs_memory /\ tA.t_mem = tn.t_mem /\
  (!x. x <> ov /\ x <> ep ==>
    lookup_var x sA = lookup_var x s /\ FLOOKUP GA x = FLOOKUP G x /\
    op_taint tA (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `op_taint tn (Var bp) = {}` by fs[ptr_covers_def] >>
  `lookup_var ep sA = SOME (w + n2w k * n2w stride) /\
   FLOOKUP GA ep = FLOOKUP G bp /\ op_taint tA (Var ep) = {} /\
   sA.vs_memory = s.vs_memory /\
   tA.t_mem = tn.t_mem /\ tA.t_stor = tn.t_stor /\ tA.t_trans = tn.t_trans /\
   (!x. x <> ov /\ x <> ep ==>
     lookup_var x sA = lookup_var x s /\ FLOOKUP GA x = FLOOKUP G x /\
     op_taint tA (Var x) = op_taint tn (Var x))` by
    (irule for_element_address_frame >> simp[]) >>
  simp[] >> conj_tac
  >- (gvs[] >> irule for_element_address_path_ptr >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (gvs[] >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[] >>
      irule stmt_state_rel_update_var >> simp[]) >>
  conj_tac
  >- (gvs[] >> irule for_element_address_outer_ghost >> simp[]) >>
  drule_all for_element_address_slice_coverage >> simp[]
QED

Theorem for_array_entry_address_inputs:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx (Var bp) arr_base k stride ov ep j3 j4 bb st ==>
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst j4 ADD [Var bp; Var ov] [ep]) /\
  lookup_var bp s = SOME arr_base /\ bp <> ov /\
  not_fresh_at sa p /\ not_local_ptr cenv es.scopes p
Proof
  strip_tac >> fs[array_entry_inputs_def, eval_operand_def] >>
  `?tail. bb.bb_instructions = sb0.cs_current_insts ++ tail` by
    metis_tac[IS_PREFIX_APPEND] >>
  simp[get_instruction_def] >>
  conj_tac
  >- (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[not_local_ptr_def] >> conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name` by
        (drule_all cenv_top_ext_outer_lookup >> simp[]) >>
      fs[lookup_scopes_def] >> metis_tac[]) >>
  fs[loweringPostsTheory.cenv_top_ext_def] >>
  qpat_x_assum `_ with <|ce_vars := _; ce_dynarray_capacity := _;
    ce_var_type := _|> = _`
    (mp_tac o Q.AP_TERM `\ce. ce.ce_imm_alloca`) >> simp[] >> metis_tac[]
QED

Theorem for_array_entry_raw_ready:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx saved_base arr_base k stride ov ep j3 j4 bb st /\
  run_inst_seq sb0.cs_current_insts s = OK t ==>
  array_entry_ready ctx func bc cx es id tv v sb0 sa ov ep st s
    (t with vs_inst_idx := LENGTH sb0.cs_current_insts)
Proof
  pure_rewrite_tac[array_entry_inputs_def] >> rpt strip_tac >>
  drule_all array_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`] strip_assume_tac) >>
  `t' = t` by metis_tac[exec_result_11] >> gvs[] >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_allocas = s.vs_allocas /\
   t.vs_halted = s.vs_halted` by
    (qpat_x_assum `_ with <|vs_memory := _; vs_vars := _|> = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[array_entry_ready_def, stmt_state_rel_inst_idx] >> conj_tac
  >- (fs[ret_pc_ok_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
  `!fuel. run_from fuel ctx func s =
    run_from fuel ctx func (t with vs_inst_idx := s.vs_inst_idx +
      LENGTH sb0.cs_current_insts)` suffices_by simp[] >>
  irule array_seq_prefix_result >> fs[mk_inst_def, is_terminator_def]
QED

Theorem for_array_entry_copy_checked:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx (Var bp) arr_base k stride ov ep j3 j4 bb st /\
  ghost_inv d cenv cx es G tn s /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn bp s ((k+1)*stride) /\ ptr_covers G tn p s sz /\
  op_taint tn (Var idx) = {} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n arr_base + k*stride) m) /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  ?GA tA sA gf tf sf.
    sA = ((update_var ep (arr_base + n2w k * n2w stride)
      (update_var ov (n2w k * n2w stride) s)) with vs_inst_idx := 2) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 GA tA (OK sA) /\
    inst_seq_ptr D 0 ctx func PG GA tA (emitted_insts sa sb0) sA gf tf /\
    run_inst_seq (emitted_insts sa sb0) sA = OK sf /\
    ghost_inv d bc cx (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes)
      gf tf sf /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      FLOOKUP gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule for_array_entry_address_inputs >> strip_tac >>
  fs[array_entry_inputs_def] >>
  qabbrev_tac `sA = (update_var ep (arr_base + n2w k * n2w stride)
    (update_var ov (n2w k * n2w stride) s)) with vs_inst_idx := 2` >>
  qabbrev_tac `GA = set_prov (DRESTRICT G (COMPL {ov})) [ep] (FLOOKUP G bp)` >>
  qabbrev_tac `tA = tn with t_var := (tn.t_var |+ (ov,{})) |+ (ep,{})` >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 GA tA (OK sA) /\
   stmt_state_rel ctx func cenv cx es sA /\ ghost_inv d cenv cx es GA tA sA /\
   ptr_covers GA tA ep sA stride /\
   lookup_var ep sA = SOME (arr_base + n2w k * n2w stride) /\
   sA.vs_memory = s.vs_memory /\ tA.t_mem = tn.t_mem /\
   (!x. x <> ov /\ x <> ep ==>
     lookup_var x sA = lookup_var x s /\ FLOOKUP GA x = FLOOKUP G x /\
     op_taint tA (Var x) = op_taint tn (Var x))` by
    (irule for_element_address_ready_ptr >>
     simp[Abbr `sA`, Abbr `GA`, Abbr `tA`] >> conj_tac
     >- metis_tac[] >> qexistsl_tac [`bp`, `idx`, `j3`, `j4`] >> gvs[]) >>
  `ptr_covers GA tA p sA sz` by
    (`lookup_var p sA = lookup_var p s /\ FLOOKUP GA p = FLOOKUP G p /\
      op_taint tA (Var p) = op_taint tn (Var p)` by metis_tac[] >>
     drule_all for_ptr_covers_transport >> simp[]) >>
  `lookup_var p sA = SOME dst` by metis_tac[] >>
  `FLOOKUP sA.vs_allocas ainst.inst_id = SOME (w2n dst,sz)` by
    simp[Abbr `sA`, update_var_def] >>
  `!m. mem_agree_outside tA.t_mem sA.vs_memory m ==>
    val_in_memory tv v (w2n (arr_base + n2w k * n2w stride)) m` by
    (`k*stride < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.word_mul_n2w, wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  `type_memory_size tv < dimword (:256) /\ type_memory_size tv <= sz /\
   type_memory_bytes cenv et = type_memory_size tv /\
   ptr_covers GA tA ep sA (type_memory_size tv)` by (gvs[] >> decide_tac) >>
  `!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
    cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all for_array_element_install_checked >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`GA`, `tA`, `gf`, `tf`, `sf`] >>
  gvs[Abbr `sA`] >> metis_tac[]
QED

Theorem for_array_element_copy_straight:
  compile_iter_elem_copy cenv src dst stride LocMemory F ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  rewrite_tac[for_memory_element_copy_dispatch] >>
  Cases_on `is_word_type ty`
  >- (simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
      gvs[emitted_insts_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  Cases_on `is_bytestring_type ty` >> simp[] >> strip_tac
  >- (drule for_bytes_copy_code >> strip_tac >>
      simp[mk_inst_def, is_terminator_def]) >>
  drule for_compile_bulk_copy_code >> simp[] >>
  Cases_on `type_memory_bytes cenv ty = 0` >> simp[mk_inst_def, is_terminator_def]
QED

Theorem for_array_entry_copy_ready:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx (Var bp) arr_base k stride ov ep j3 j4 bb st /\
  sA = ((update_var ep (arr_base + n2w k * n2w stride)
    (update_var ov (n2w k * n2w stride) s)) with vs_inst_idx := 2) /\
  run_inst_seq (emitted_insts sa sb0) sA = OK sf ==>
  array_entry_ready ctx func bc cx es id tv v sb0 sa ov ep st s
    (sf with vs_inst_idx := LENGTH sb0.cs_current_insts)
Proof
  strip_tac >>
  `?t. run_inst_seq sb0.cs_current_insts s = OK t /\
    sf = t with vs_inst_idx := 2` suffices_by
    (strip_tac >> drule_all for_array_entry_raw_ready >>
     gvs[]) >>
  qhdtm_x_assum `array_entry_inputs` mp_tac >> pure_rewrite_tac[array_entry_inputs_def] >> strip_tac >>
  drule_all array_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`] strip_assume_tac) >>
  drule_all array_address_prefix_run >>
  disch_then (qspecl_then [`stride`, `ep`, `j3`, `j4`] mp_tac) >>
  rewrite_tac[GSYM wordsTheory.word_add_n2w, GSYM wordsTheory.word_mul_n2w,
    wordsTheory.n2w_w2n] >>
  disch_then (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts sa sb0` assume_tac) >>
  qexists_tac `t` >> conj_tac >- metis_tac[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb0)` by
    fs[EVERY_MEM] >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then
    [`update_var ep (arr_base + n2w k * n2w stride)
      (update_var ov (n2w k * n2w stride) s)`, `2`] mp_tac) >>
  gvs[instIdxIndepTheory.exec_result_map_def]
QED

Theorem for_array_entry_copy_path_ptr:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx (Var bp) arr_base k stride ov ep j3 j4 bb st /\
  sA = ((update_var ep (arr_base + n2w k * n2w stride)
    (update_var ov (n2w k * n2w stride) s)) with vs_inst_idx := 2) /\
  inst_seq_ptr D 0 ctx func PG GA tA (emitted_insts sa sb0) sA gf tf /\
  run_inst_seq (emitted_insts sa sb0) sA = OK sf ==>
  gas_path_ptr D 0 ctx func PG GA tA sA 0 gf tf
    (OK (sf with vs_inst_idx := LENGTH sb0.cs_current_insts))
Proof
  strip_tac >> qhdtm_x_assum `array_entry_inputs` mp_tac >>
  pure_rewrite_tac[array_entry_inputs_def] >> strip_tac >>
  drule for_array_element_copy_straight >> strip_tac >>
  `~sA.vs_halted /\ lookup_block sA.vs_current_bb func.fn_blocks = SOME bb /\
   sA.vs_inst_idx = 2` by simp[update_var_def] >>
  `isPREFIX (emitted_insts sa sb0) (DROP sA.vs_inst_idx bb.bb_instructions)` by
    (`?tail. bb.bb_instructions = sb0.cs_current_insts ++ tail` by
       metis_tac[IS_PREFIX_APPEND] >> simp[] >>
     metis_tac[IS_PREFIX_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb0) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb0) = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `sA.vs_inst_idx + LENGTH (emitted_insts sa sb0) =
    LENGTH sb0.cs_current_insts` by (simp[] >> decide_tac) >>
  drule_all run_inst_seq_gas_path_ptr >>
  pure_asm_rewrite_tac[listTheory.LENGTH, arithmeticTheory.ADD_CLAUSES] >>
  rewrite_tac[]
QED

Theorem for_array_round_prepare_ptr:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx (Var bp) arr_base k stride ov ep j3 j4 bb st /\
  ghost_inv d cenv cx es G tn s /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn bp s ((k+1)*stride) /\ ptr_covers G tn p s sz /\
  op_taint tn (Var idx) = {} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n arr_base + k*stride) m) /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  ?gf tf s2.
    gas_path_ptr D 0 ctx func PG G tn s 0 gf tf (OK s2) /\
    array_entry_ready ctx func bc cx es id tv v sb0 sa ov ep st s s2 /\
    ghost_inv d bc cx (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes)
      gf tf s2 /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      FLOOKUP gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all for_array_entry_copy_checked >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all for_array_entry_copy_ready >> strip_tac >>
  drule_all for_array_entry_copy_path_ptr >> strip_tac >>
  qexistsl_tac [`gf`, `tf`, `sf with vs_inst_idx := LENGTH sb0.cs_current_insts`] >>
  simp[SRULE [] (Q.INST [`gs` |-> `es.gas_obs`] literal_ptr_ghost_inv_normalize)] >>
  drule_all gas_path_ptr_then >> simp[]
QED
