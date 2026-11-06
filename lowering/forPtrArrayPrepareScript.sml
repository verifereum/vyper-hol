(* Checked finite prefixes of the array loop, ending at the actual body
   compilation point rather than at an erased S1 execution. *)
Theory forPtrArrayPrepare
Ancestors forPtrRangePrepare forPtrAddress forPtrWriteScope forPtrArraySnapshot
  forPtrWord forPtrBulk forPtrBytes forPtrCopyInterface stmtSimForArrayLoop
  fragExec emitHelperProps finite_map list forPtrControl venomState ptrDiscipline
  exprSimProps typedCopyAgreement context compileEnv valueEncoding stmtLowering
  exprLoweringProps rich_list forPtrElementFrame bodyPtrDefs

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
