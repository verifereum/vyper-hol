Theory bodyPtrPopStoragePureOutcome
Ancestors
  bodyPtrPopStoragePureEntry bodyPtrPopStoragePureTransfer bodyPtrPopStoragePurePost
  exprSimPopNestedBase fragGasSeqPtr fragGasPathPtr stmtAppendStoragePathPtr
  exprLoweringProps venomInst venomState list rich_list fragExec
  bodyPtrPopTargetDefs bodyPtrDefs bodyPtrPopRootEndpoint
  compileEnv targetPlaceSimDefs exprSimDefs loweringPosts
  vyperStorageBackend vyperStorage vyperValue vyperState vyperInterpreter
  ptrDiscipline context exprSimVVFrame gasSummaryComposePtr
  exprSimPopStorage words pred_set finite_map appendStorageSourcePtr

Theorem pop_storage_suffix_counted:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  code = nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  inst_seq_ptr D lo ctx func PG G tn code s Gf tnf /\
  run_inst_seq code s = OK t ==>
  gas_path_ptr D lo ctx func PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0` by
    (Cases_on `tr` >> simp[nested_pop_suffix_def, mk_inst_def, is_terminator_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[DROP_APPEND]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem pop_storage_suffix_abort_counted:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  code = nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  inst_seq_ptr D lo ctx func PG G tn code s Gf tnf /\
  run_inst_seq code s = Abort a t ==>
  ?j. gas_path_ptr D lo ctx func PG G tn s 0 Gf tnf
    (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >> irule run_inst_seq_abort_zero_path_ptr >>
  fs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `tr` >>
  gvs[nested_pop_suffix_def, mk_inst_def, is_terminator_def, DROP_APPEND]
QED

Theorem pop_storage_emitted_transfer_nonempty:
  compile_dynarray_pop hdr 1 esz is_ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\
  eval_operand hdr s = SOME slot /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  (!x. hdr = Var x ==> not_fresh_at sa x) /\
  (if tr then tload slot s else sload slot s) <> 0w /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  ?Gf tnf xs.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    op_prov Gf r = NONE /\ op_taint tnf r = {} /\
    EVERY (\x. ~not_fresh_at sa x) xs /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
    tnf.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
    (!x. ~MEM x xs ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule nested_pop_suffix_shape >> strip_tac >> gvs[] >>
  qrefinel [`_`, `_`, `[x0;x1;x2;x3;x4;x5;x6]`] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, nested_pop_suffix_def] >>
  irule (SRULE [APPEND, GSYM arithmeticTheory.ADD_ASSOC]
    pop_storage_slice_transfer_nonempty) >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[MEM]
QED

Theorem pop_storage_empty_summary:
  compile_dynarray_pop hdr 1 esz is_ctor imm
    (if tr then LocTransient else LocStorage) sa = (q,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand hdr s = SOME slot /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  (!x. hdr = Var x ==> not_fresh_at sa x) /\
  (if tr then tload slot s else sload slot s) = 0w /\
  lookup_storage slot (get_storage cx es tr) = 0w /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))))
    (es,s,G,tn) Q (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule nested_pop_suffix_shape >> strip_tac >> gvs[] >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
   (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6])` by
    (gvs[EVERY_MEM] >> metis_tac[MEM]) >>
  drule_all nested_pop_suffix_empty >>
  disch_then (qspecl_then [`sa.cs_next_id`, `esz`] strip_assume_tac) >>
  `inst_seq_ptr (cx_dead cx) 0 ctx func PG G tn
    (nested_pop_suffix hdr tr sa.cs_next_id esz x0 x1 x2 x3 x4 x5 x6) s
    (DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x0})) (COMPL {x1})) (COMPL {x2}))
    (tn with t_var := tn.t_var |+ (x0,{}) |+ (x1,{}) |+ (x2,{}))` by
    (simp[nested_pop_suffix_def] >>
     irule (SRULE [APPEND, GSYM arithmeticTheory.ADD_ASSOC]
       pop_storage_slice_transfer_empty) >> simp[]) >>
  `?j. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0
    (DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x0})) (COMPL {x1})) (COMPL {x2}))
    (tn with t_var := tn.t_var |+ (x0,{}) |+ (x1,{}) |+ (x2,{}))
    (Abort a (s' with vs_inst_idx := j))` by
    (metis_tac[pop_storage_suffix_abort_counted]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl [`INR (Error (RuntimeError "pop empty storage array"))`, `es`,
    `DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x0})) (COMPL {x1})) (COMPL {x2})`,
    `tn with t_var := tn.t_var |+ (x0,{}) |+ (x1,{}) |+ (x2,{})`,
    `Abort a (s' with vs_inst_idx := j)`] >> simp[exit_result_def, expr_exit_def] >>
  simp[pop_place_def, get_storage_backend_eq, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, raise_def, get_storage_gas_obs]
QED

Theorem pop_storage_positive_source:
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ 0 < len /\
  ~cx.txn.is_static ==>
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) es =
    (INL (PlaceR (StoragePlace tr
       (slot + n2w (1 + (len - 1) * type_slot_size tv)) tv)),
     set_storage cx es tr
       (apply_writes slot [(0,n2w (len - 1))] (get_storage cx es tr)))
Proof
  strip_tac >>
  simp[pop_place_def, get_storage_backend_eq, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, raise_def, write_storage_slot_eq,
       encode_value_def, encode_base_to_slot_def, integer_wordTheory.i2w_def]
QED
