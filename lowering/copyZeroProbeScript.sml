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
