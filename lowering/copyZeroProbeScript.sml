Theory copyZeroProbe
Ancestors
  loweringPosts exprSimAlloc exprSimOps exprSim exprLowering compileEnv
  context vyperAST vyperInterpreter vyperState valueEncoding
  fragExec localPtrsProps loweringSlice exprLoweringProps emitHelperProps
  exprSimStorageCopy immutableCopyExecution storageDecodeMemory
  vyperTypeStatePreservation vyperTypeValues valueEncodingTyping
  vyperStorageBackend venomInst venomExecSemantics venomState
  list finite_map

(* Candidate type facts only: these are not a frozen-contract counterexample. *)
Theorem zero_tuple_layout:
  type_memory_size (TupleTV []) = 0
Proof
  EVAL_TAC
QED

Theorem zero_tuple_post_type:
  !cenv fid.
  post_value_type (cenv with ce_func_return_type := K (TupleT []))
    (Call (TupleT [TupleT []]) (IntCall fid) [] NONE) = TupleT [] /\
  expr_type (Call (TupleT [TupleT []]) (IntCall fid) [] NONE) <>
    post_value_type (cenv with ce_func_return_type := K (TupleT []))
      (Call (TupleT [TupleT []]) (IntCall fid) [] NONE)
Proof
  simp[post_value_type_def, lowered_value_type_def, is_word_type_def,
       is_bytestring_type_def, expr_type_def]
QED

Theorem zero_tuple_size_premise:
  !cenv cx tvt.
    evaluate_type (get_tenv cx) (TupleT []) = SOME tvt ==>
    type_memory_bytes cenv (TupleT []) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64
Proof
  simp[vyperValueTheory.evaluate_type_def, type_memory_bytes_def, zero_tuple_layout]
QED

Theorem zero_tuple_storage_source:
  !cx es s w.
    storage_holds cx F (TupleT []) (Value (ArrayV (TupleV []))) w es s
Proof
  simp[storage_holds_def, vyperValueTheory.evaluate_type_def, read_result_def,
       read_storage_slot_def, vyperLookupStorageTheory.slots_in_range_def,
       accountsRelPropsTheory.storage_range_agree_def,
       vyperValueTheory.type_slot_size_def, vyperStorageTheory.decode_value_def,
       get_storage_backend_def, get_accounts_def, bind_def, return_def,
       lift_option_def] >>
  rpt gen_tac >> conj_tac
  >- (mp_tac (Q.ISPEC `w:bytes32` wordsTheory.w2n_lt) >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

(* The storage value itself imposes no shape/size obstruction.  The state
   relation and the live-local disjointness are still real obligations. *)
Theorem zero_tuple_input_post:
  !ctx func cenv cx es sa sm s fid.
    stmt_state_rel ctx func (cenv with ce_func_return_type := K (TupleT [])) cx es s /\
    outside_locals (cenv with ce_func_return_type := K (TupleT [])) es.scopes s (Lit 0w) ==>
    vv_post ctx func (cenv with ce_func_return_type := K (TupleT [])) cx
      (Call (TupleT [TupleT []]) (IntCall fid) [] NONE)
      es sa sm s es (Value (ArrayV (TupleV [])))
      (LocatedValue (TupleT []) <|ptr_location := LocStorage; ptr_operand := Lit 0w|>) s
Proof
  rpt strip_tac >>
  simp[vv_post_def, zero_tuple_post_type, vv_holds_def, vv_at_def,
       vv_operand_def, eval_operand_def, zero_tuple_storage_source]
QED

Definition probe_cenv_def:
  probe_cenv cenv = cenv with <|
    ce_vars := FEMPTY |+ ("local", PtrVar (Var "p") 1);
    ce_imm_alloca := NONE;
    ce_is_ctor := F;
    ce_func_return_type := K (TupleT []) |>
End

Definition probe_scopes_def:
  probe_scopes = [FEMPTY |+ ("local",
    <|assignable := T; type := TupleTV []; value := ArrayV (TupleV []); popped := []|>)]
End

Definition probe_state_def:
  probe_state s = s with <|
    vs_vars := FEMPTY |+ ("p", 32w);
    vs_allocas := FEMPTY |+ (0, (32,0));
    vs_alloca_next := 33 |>
End

Theorem probe_local_region:
  !cenv s name base sz.
    local_region (probe_cenv cenv) probe_scopes (probe_state s) name base sz <=>
      name = "local" /\ base = 32 /\ sz = 1
Proof
  simp[local_region_def, probe_cenv_def, probe_scopes_def, probe_state_def,
       lookup_scopes_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DEF] >>
  rpt gen_tac >> Cases_on `name = "local"` >>
  simp[wordsTheory.dimword_def, CONJ_COMM]
QED

Theorem probe_local_ptrs_rel:
  !func cenv s.
    local_ptrs_rel func (probe_cenv cenv) probe_scopes (probe_state s)
Proof
  simp[local_ptrs_rel_def, probe_local_region, probe_cenv_def,
       probe_scopes_def, lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_DEF] >>
  rpt gen_tac >> rpt strip_tac >> gvs[] >>
  simp[probe_state_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DEF,
       val_wf_def, val_in_memory_def, type_memory_size_def, local_backed_def] >>
  simp[compileEnvTheory.regions_disjoint_def, wordsTheory.dimword_def]
QED

Theorem probe_source_outside:
  !cenv s.
    outside_locals (probe_cenv cenv) probe_scopes (probe_state s) (Lit 0w) /\
    ~outside_locals (probe_cenv cenv) probe_scopes (probe_state s) (Lit 32w)
Proof
  simp[outside_locals_def, eval_operand_def, probe_local_region,
       wordsTheory.dimword_def]
QED

Definition probe_cx_def:
  probe_cx = empty_evaluation_context with
    txn := (empty_call_txn with <|block_number := 1; block_hashes := [0w]|>)
End

Definition probe_es_def:
  probe_es = empty_state with <|scopes := probe_scopes; outcomes := SOME []|>
End

Definition probe_ss_def:
  probe_ss = probe_state ((init_venom_state "entry") with
    vs_block_ctx := (empty_block_context with bc_number := 1w))
End

Theorem probe_call_context:
  call_ctx_rel probe_cx.txn probe_ss.vs_call_ctx probe_ss.vs_tx_ctx
    probe_ss.vs_block_ctx /\ ~probe_ss.vs_call_ctx.cc_static
Proof
  simp[probe_cx_def, probe_ss_def, probe_state_def, init_venom_state_def,
       vyperContextTheory.empty_evaluation_context_def, vyperContextTheory.empty_call_txn_def,
       empty_call_context_def, empty_tx_context_def, empty_block_context_def,
       call_ctx_rel_def, tx_env_ok_def] >>
  rpt strip_tac >> Cases_on `n = 0` >> gvs[]
QED

Definition probe_env_def:
  probe_env cenv = probe_cenv (cenv with ce_module_vars := FEMPTY)
End

Theorem probe_global_state_rel:
  !func cenv. state_rel func (probe_env cenv) probe_cx probe_es probe_ss
Proof
  rpt gen_tac >>
  simp[state_rel_def, probe_call_context, probe_env_def,
       probe_es_def, probe_ss_def, probe_local_ptrs_rel] >>
  simp[probe_cenv_def, probe_cx_def, empty_state_def, probe_state_def,
       init_venom_state_def, vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def,
       empty_call_context_def, empty_tx_context_def, empty_block_context_def,
       storage_rel_def, transient_rel_def, accounts_rel_def,
       storage_vars_rel_def, transient_vars_rel_def, immutables_rel_def,
       logs_rel_def, contract_storage_def, contract_transient_def] >>
  simp[vyperContextTheory.get_module_code_def]
QED

Definition probe_sm_def:
  probe_sm = <|cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
    cs_current_bb := "entry"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := []|>
End

Definition probe_copy_def:
  probe_copy = unwrap_value (probe_env ARB)
    (LocatedValue (TupleT []) <|ptr_location := LocStorage; ptr_operand := Lit 0w|>)
    probe_sm
End

Definition probe_sb_def:
  probe_sb = SND probe_copy
End

Definition probe_fn_def:
  probe_fn = mk_raw_function "copy"
    (REVERSE probe_sb.cs_blocks ++
      [<|bb_label := probe_sb.cs_current_bb;
         bb_instructions := probe_sb.cs_current_insts ++ [mk_inst 100 STOP [] []]|>])
End

Definition probe_ctx_def:
  probe_ctx = mk_venom_context [probe_fn] (SOME "copy")
End

Theorem probe_copy_operand:
  FST probe_copy = Var "%0"
Proof
  EVAL_TAC
QED

Theorem probe_alloca_inv:
  venomMemDefs$alloca_inv probe_ss
Proof
  simp[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       probe_ss_def, probe_state_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED

Theorem probe_copy_code:
  fn_has_code probe_sm probe_sb probe_fn /\ fn_inst_ids_distinct probe_fn
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  simp[]
QED

Theorem probe_allocation_agrees:
  !inst n base sz.
    MEM inst (fn_insts probe_fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP probe_ss.vs_allocas inst.inst_id = SOME (base,sz) ==>
    sz = w2n n
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem probe_no_calls:
  fn_directly_calls probe_ctx = EMPTY_REL
Proof
  simp[FUN_EQ_THM, fcgDefsTheory.fn_directly_calls_def,
       probe_ctx_def, mk_venom_context_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs[fn_insts_blocks_def]
QED

Theorem probe_rooms:
  alloca_room probe_ctx probe_fn probe_ss /\
  fmp_room probe_ctx probe_fn probe_ss
Proof
  `TC (EMPTY_REL : string -> string -> bool) = EMPTY_REL` by
    (simp[FUN_EQ_THM, relationTheory.TC_DEF] >> rpt gen_tac >>
     qexists_tac `\x y. F` >> simp[]) >>
  simp[alloca_room_def, fmp_room_def, probe_no_calls] >>
  EVAL_TAC >> simp[fn_insts_blocks_def, wordsTheory.dimword_def]
QED

Theorem probe_stmt_state_rel:
  !cenv. stmt_state_rel probe_ctx probe_fn (probe_env cenv) probe_cx probe_es probe_ss
Proof
  simp[stmt_state_rel_def, probe_global_state_rel, probe_rooms,
       probe_alloca_inv, probe_allocation_agrees, immutable_alloca_sep_def,
       immutable_base_zero_def, probe_env_def, probe_cenv_def] >>
  metis_tac[probe_allocation_agrees]
QED

Theorem probe_vv_post:
  !cenv sa sm fid.
    vv_post probe_ctx probe_fn (probe_env cenv) probe_cx
      (Call (TupleT [TupleT []]) (IntCall fid) [] NONE)
      probe_es sa sm probe_ss probe_es (Value (ArrayV (TupleV [])))
      (LocatedValue (TupleT []) <|ptr_location := LocStorage; ptr_operand := Lit 0w|>)
      probe_ss
Proof
  rpt gen_tac >>
  `outside_locals (probe_env cenv) probe_es.scopes probe_ss (Lit 0w)` by
    simp[probe_env_def, probe_es_def, probe_ss_def, probe_source_outside] >>
  simp[vv_post_def, probe_stmt_state_rel, probe_env_def, probe_cenv_def,
       post_value_type_def, lowered_value_type_def, expr_type_def,
       is_word_type_def, is_bytestring_type_def, vv_holds_def, vv_at_def,
       vv_operand_def, eval_operand_def, zero_tuple_storage_source,
       probe_es_def, probe_ss_def, probe_source_outside] >>
  gvs[probe_env_def, probe_cenv_def, probe_es_def, probe_ss_def]
QED

Theorem probe_frozen_premises:
  unwrap_value (probe_env cenv)
    (LocatedValue (TupleT []) <|ptr_location := LocStorage; ptr_operand := Lit 0w|>)
    probe_sm = (Var "%0", probe_sb) /\
  ~is_word_type (TupleT []) /\
  local_ptrs_reserved (probe_env cenv) probe_sm /\
  MAP FDOM probe_es.scopes = MAP FDOM probe_es.scopes /\
  probe_sm.cs_next_var <= probe_sm.cs_next_var /\
  probe_sm.cs_next_id <= probe_sm.cs_next_id /\
  fn_has_code probe_sm probe_sb probe_fn /\ fn_inst_ids_distinct probe_fn /\
  (!x. (Lit 0w : operand) = Var x ==> not_fresh_at probe_sm x) /\
  (!tvt. evaluate_type (get_tenv probe_cx) (TupleT []) = SOME tvt ==>
    type_memory_bytes (probe_env cenv) (TupleT []) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64)
Proof
  simp[probe_copy_code, zero_tuple_size_premise, is_word_type_def] >>
  conj_tac
  >- (simp[GSYM probe_copy_def, probe_sb_def, probe_copy_operand,
           probe_env_def, probe_cenv_def] >> EVAL_TAC) >>
  simp[local_ptrs_reserved_def, probe_env_def, probe_cenv_def,
       FLOOKUP_UPDATE, not_fresh_at_def, probe_sm_def] >>
  rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def,
                        type_memory_size_def] >> EVAL_TAC
QED

Theorem probe_fn_blocks[compute]:
  probe_fn.fn_blocks =
    [<|bb_label := "entry"; bb_instructions :=
       [mk_inst 0 ALLOCA [Lit 0w] ["%0"];
        mk_inst 1 ASSIGN [Lit 0w] ["%1"];
        mk_inst 2 JMP [Label "@wcopy_cond_0"] []]|>;
     <|bb_label := "@wcopy_cond_0"; bb_instructions :=
       [mk_inst 3 EQ [Var "%1"; Lit 0w] ["%2"];
        mk_inst 4 JNZ [Var "%2"; Label "@wcopy_exit_2"; Label "@wcopy_body_1"] []]|>;
     <|bb_label := "@wcopy_body_1"; bb_instructions :=
       [mk_inst 5 ADD [Lit 0w; Var "%1"] ["%3"];
        mk_inst 6 SLOAD [Var "%3"] ["%4"];
        mk_inst 7 MUL [Var "%1"; Lit 32w] ["%5"];
        mk_inst 8 ADD [Var "%0"; Var "%5"] ["%6"];
        mk_inst 9 MSTORE [Var "%6"; Var "%4"] [];
        mk_inst 10 ADD [Var "%1"; Lit 1w] ["%7"];
        mk_inst 11 ASSIGN [Var "%7"] ["%1"];
        mk_inst 12 JMP [Label "@wcopy_cond_0"] []]|>;
     <|bb_label := "@wcopy_exit_2"; bb_instructions := [mk_inst 100 STOP [] []]|>]
Proof
  EVAL_TAC
QED

Definition probe_halt_def:
  probe_halt = run_from 3 probe_ctx probe_fn probe_ss
End

Theorem probe_run_result:
  !fuel. run_from fuel probe_ctx probe_fn probe_ss =
    if fuel < 2 then Error "out of fuel" else probe_halt
Proof
  Cases >- (EVAL_TAC >> simp[]) >>
  Cases_on `n` >- (EVAL_TAC >> simp[]) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``run_blocks``, ``probe_ctx``, ``probe_fn``]) >> simp[] >>
  simp[Once run_blocks_def, probe_fn_blocks] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``run_blocks``, ``probe_ctx``, ``probe_fn``]) >> simp[] >>
  simp[Once run_blocks_def, probe_fn_blocks] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``run_blocks``, ``probe_ctx``, ``probe_fn``]) >> simp[] >>
  simp[Once run_blocks_def, probe_fn_blocks] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``run_blocks``, ``probe_ctx``, ``probe_fn``]) >> simp[] >>
  simp[Once run_blocks_def, probe_fn_blocks] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``run_blocks``, ``probe_ctx``, ``probe_fn``]) >> simp[]
QED

Definition probe_end_def:
  probe_end = probe_ss with <|
    vs_vars := probe_ss.vs_vars |+ ("%0",32w) |+ ("%1",0w) |+ ("%2",1w);
    vs_prev_bb := SOME "@wcopy_cond_0";
    vs_current_bb := "@wcopy_exit_2"; vs_inst_idx := 0|>
End

Theorem probe_halt_value:
  probe_halt = Halt (probe_end with vs_halted := T)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``run_blocks``, ``probe_ctx``, ``probe_fn``]) >> simp[] >>
  simp[Once run_blocks_def, probe_fn_blocks] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``run_blocks``, ``probe_ctx``, ``probe_fn``]) >> simp[] >>
  simp[Once run_blocks_def, probe_fn_blocks] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``run_blocks``, ``probe_ctx``, ``probe_fn``]) >> simp[]
QED

Theorem probe_endpoint_stop:
  !s. ~s.vs_halted /\ s.vs_current_bb = probe_sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH probe_sb.cs_current_insts ==>
    run_from 0 probe_ctx probe_fn s =
      Halt (s with <|vs_returndata := []; vs_halted := T|>)
Proof
  rpt strip_tac >>
  `probe_sb.cs_current_bb = "@wcopy_exit_2" /\
   probe_sb.cs_current_insts = []` by EVAL_TAC >>
  gvs[run_from_def, probe_fn_blocks, lookup_block_def, FIND_thm, mk_inst_def] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[step_inst_def, step_inst_base_def, halt_state_def]
QED

Theorem probe_endpoint_vars:
  !s. ~s.vs_halted /\ s.vs_current_bb = probe_sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH probe_sb.cs_current_insts /\
    (!fuel r. run_from fuel probe_ctx probe_fn s = r /\ (!e. r <> Error e) ==>
       ?fuel'. run_from fuel' probe_ctx probe_fn probe_ss = r) ==>
    s.vs_vars = probe_end.vs_vars
Proof
  rpt strip_tac >>
  drule_all probe_endpoint_stop >> strip_tac >>
  first_x_assum (qspecl_then [`0`, `Halt (s with <|vs_returndata := []; vs_halted := T|>)`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `fuel' < 2` >> gvs[probe_run_result, probe_halt_value] >>
  qpat_x_assum `_ with <|vs_returndata := []; vs_halted := T|> = _`
    (mp_tac o AP_TERM ``\s:venom_state. s.vs_vars``) >> simp[]
QED

Theorem probe_end_not_outside:
  !cenv s. s.vs_vars = probe_end.vs_vars ==>
    ~outside_locals (probe_env cenv) probe_es.scopes s (Var "%0")
Proof
  simp[outside_locals_def, eval_operand_def, lookup_var_def,
       probe_end_def, probe_ss_def, probe_state_def,
       probe_env_def, probe_cenv_def, probe_es_def,
       local_region_def, probe_scopes_def, lookup_scopes_def,
       FLOOKUP_UPDATE, wordsTheory.dimword_def] >>
  rpt strip_tac >> qexistsl_tac [`"local"`, `32`, `1`] >> simp[]
QED

Theorem probe_storage_copy_failure:
  !cenv fid.
  ~frag_exec probe_ctx probe_sm probe_sb
    (\s. vv_post probe_ctx probe_fn (probe_env cenv) probe_cx
      (Call (TupleT [TupleT []]) (IntCall fid) [] NONE)
      probe_es probe_sm probe_sm probe_ss probe_es (Value (ArrayV (TupleV [])))
      (LocatedValue (TupleT []) <|ptr_location := LocStorage; ptr_operand := Lit 0w|>) s)
    (\s. expr_post probe_ctx probe_fn (probe_env cenv) probe_cx
      (Call (TupleT [TupleT []]) (IntCall fid) [] NONE)
      probe_es probe_sm probe_sb probe_ss probe_es (ArrayV (TupleV [])) (Var "%0") s)
    (K F)
Proof
  rpt gen_tac >> simp[frag_exec_def] >>
  qexistsl_tac [`probe_fn`, `probe_ss`] >>
  simp[probe_copy_code, probe_vv_post] >>
  `~probe_ss.vs_halted /\ probe_ss.vs_current_bb = probe_sm.cs_current_bb /\
    probe_ss.vs_inst_idx = LENGTH probe_sm.cs_current_insts` by
    EVAL_TAC >>
  simp[] >> conj_tac >- (irule (SRULE [] probe_vv_post)) >>
  qx_gen_tac `s'` >> rpt disch_tac >>
  spose_not_then strip_assume_tac >>
  `s'.vs_vars = probe_end.vs_vars` by
    (irule probe_endpoint_vars >> simp[]) >>
  drule probe_end_not_outside >>
  disch_then (qspec_then `cenv` mp_tac) >>
  gvs[expr_post_def, probe_env_def, probe_cenv_def,
      post_value_type_def, lowered_value_type_def, is_word_type_def,
      is_bytestring_type_def, expr_type_def]
QED

(* An instance of every frozen premise, with the exact fragment conclusion
   negated.  probe_vv_post also verifies that its input predicate is inhabited. *)
Theorem storage_copy_frozen_counterexample:
  !cenv fid.
  (unwrap_value (probe_env cenv)
     (LocatedValue (TupleT []) <|ptr_location := LocStorage; ptr_operand := Lit 0w|>)
     probe_sm = (Var "%0", probe_sb) /\
   (LocStorage = LocStorage \/ LocStorage = LocTransient) /\
   ~is_word_type (TupleT []) /\
   local_ptrs_reserved (probe_env cenv) probe_sm /\
   MAP FDOM probe_es.scopes = MAP FDOM probe_es.scopes /\
   probe_sm.cs_next_var <= probe_sm.cs_next_var /\
   probe_sm.cs_next_id <= probe_sm.cs_next_id /\
   fn_has_code probe_sm probe_sb probe_fn /\ fn_inst_ids_distinct probe_fn /\
   (!x. (Lit 0w : operand) = Var x ==> not_fresh_at probe_sm x) /\
   (!tvt. evaluate_type (get_tenv probe_cx) (TupleT []) = SOME tvt ==>
      type_memory_bytes (probe_env cenv) (TupleT []) = type_memory_size tvt /\
      type_memory_size tvt < 2 ** 64)) /\
  ~frag_exec probe_ctx probe_sm probe_sb
    (\s. vv_post probe_ctx probe_fn (probe_env cenv) probe_cx
      (Call (TupleT [TupleT []]) (IntCall fid) [] NONE)
      probe_es probe_sm probe_sm probe_ss probe_es (Value (ArrayV (TupleV [])))
      (LocatedValue (TupleT []) <|ptr_location := LocStorage; ptr_operand := Lit 0w|>) s)
    (\s. expr_post probe_ctx probe_fn (probe_env cenv) probe_cx
      (Call (TupleT [TupleT []]) (IntCall fid) [] NONE)
      probe_es probe_sm probe_sb probe_ss probe_es (ArrayV (TupleV [])) (Var "%0") s)
    (K F)
Proof
  rpt gen_tac >> conj_tac
  >- (mp_tac probe_frozen_premises >> simp[]) >>
  qspecl_then [`cenv`, `fid`] mp_tac probe_storage_copy_failure >> simp[]
QED
