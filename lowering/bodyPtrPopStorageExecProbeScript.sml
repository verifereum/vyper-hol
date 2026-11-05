Theory bodyPtrPopStorageExecProbe
Ancestors
  bodyPtrPopReadBoundary vyperStorageBackend vyperState vyperStorage words
  vfmState vyperValue integer_word fragGasSeqPtr exprSimPopStorage
  venomInst venomState venomExecSemantics rich_list vyperCompiler

(* Current source Pop returns a place and retains the payload; a historical
   compiler comment about clearing is not the source semantics. *)
Theorem pop_singleton_payload_retained_probe:
  !cx es. ~cx.txn.is_static ==>
    pop_place cx (StoragePlace F 0w
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)))
      (set_storage cx es F ((0w =+ 1w) ((1w =+ 7w) (K 0w)))) =
    (INL (PlaceR (StoragePlace F 1w (BaseTV (UintT 256)))),
     set_storage cx (set_storage cx es F ((0w =+ 1w) ((1w =+ 7w) (K 0w)))) F
       (apply_writes 0w [(0,0w)] ((0w =+ 1w) ((1w =+ 7w) (K 0w)))))
Proof
  rpt strip_tac >>
  simp[pop_place_def, get_storage_backend_eq, get_storage_after_set,
       bind_def, ignore_bind_def, check_def, assert_def, return_def,
       lookup_storage_def, type_slot_size_def, write_storage_slot_def,
       check_not_static_def, encode_value_def, set_storage_backend_eq,
       encode_base_to_slot_def, lift_option_type_def, dimword_def, i2w_def,
       SF wordsLib.SIZES_ss]
QED

Theorem pop_singleton_payload_projection_probe:
  lookup_storage (1w:bytes32)
    (apply_writes 0w [(0,0w)] ((0w =+ 1w) ((1w =+ 7w) (K 0w)))) = 7w
Proof
  EVAL_TAC >> simp[dimword_def, SF wordsLib.SIZES_ss]
QED

(* Named concrete fixtures keep the executable probe statements readable;
   these definitions introduce no replacement semantic invariant. *)
Definition pop_probe_code_def:
  pop_probe_code =
    [mk_inst 0 SLOAD [Lit 0w] ["%0"];
     mk_inst 1 ISZERO [Var "%0"] ["%1"];
     mk_inst 2 ISZERO [Var "%1"] ["%2"];
     mk_inst 3 ASSERT [Var "%2"] [];
     mk_inst 4 SUB [Var "%0"; Lit 1w] ["%3"];
     mk_inst 5 SSTORE [Lit 0w; Var "%3"] [];
     mk_inst 6 ADD [Lit 0w; Lit 1w] ["%4"];
     mk_inst 7 MUL [Var "%3"; Lit 1w] ["%5"];
     mk_inst 8 ADD [Var "%4"; Var "%5"] ["%6"]]
End

Definition pop_probe_start_def:
  pop_probe_start = sstore 0w 1w (sstore 1w 7w (init_venom_state "entry"))
End

Theorem pop_probe_run:
  ?t. run_inst_seq pop_probe_code pop_probe_start = OK t /\
      eval_operand (Var "%6") t = SOME 1w /\
      sload 0w t = 0w /\ sload 1w t = 7w
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition pop_probe_fn_def:
  pop_probe_fn = mk_raw_function "%op_probe"
    [<| bb_label := "entry"; bb_instructions := pop_probe_code |>]
End

Theorem pop_probe_checked:
  ?G' tn'. inst_seq_ptr D 0 (mk_venom_context [] NONE) pop_probe_fn
    [] FEMPTY entry_taint pop_probe_code pop_probe_start G' tn'
Proof
  EVAL_TAC >> simp[] >> rpt conj_tac >> gen_tac >>
  Cases_on `op` >> simp[] >> EVAL_TAC >>
  Cases_on `s = "%4"` >> Cases_on `s = "%5"` >> simp[]
QED

Theorem pop_probe_counted_path:
  ?t G' tn'.
    gas_path_ptr D 0 (mk_venom_context [] NONE) pop_probe_fn []
      FEMPTY entry_taint pop_probe_start 0 G' tn'
      (OK (t with vs_inst_idx := 9)) /\
    eval_operand (Var "%6") t = SOME 1w /\
    sload 0w t = 0w /\ sload 1w t = 7w
Proof
  strip_assume_tac pop_probe_run >>
  strip_assume_tac pop_probe_checked >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    run_inst_seq_gas_path_ptr >>
  disch_then (qspecl_then [`t`,
    `<| bb_label := "entry"; bb_instructions := pop_probe_code |>`] mp_tac) >>
  simp[pop_probe_fn_def, mk_raw_function_def, lookup_block_def] >>
  EVAL_TAC >> simp[]
QED

Theorem pop_probe_compiler_code:
  (SND (compile_dynarray_pop (Lit 0w) 1 1 F NONE LocStorage
    (initial_compile_state "entry"))).cs_current_insts = pop_probe_code
Proof
  EVAL_TAC
QED

Theorem pop_probe_compiler_result:
  FST (compile_dynarray_pop (Lit 0w) 1 1 F NONE LocStorage
    (initial_compile_state "entry")) = Var "%6"
Proof
  EVAL_TAC
QED

Theorem pop_probe_compiler_counted:
  ?t G' tn'.
    gas_path_ptr D 0 (mk_venom_context [] NONE) pop_probe_fn []
      FEMPTY entry_taint pop_probe_start 0 G' tn'
      (OK (t with vs_inst_idx := 9)) /\
    eval_operand
      (FST (compile_dynarray_pop (Lit 0w) 1 1 F NONE LocStorage
        (initial_compile_state "entry"))) t = SOME 1w /\
    sload 0w t = 0w /\ sload 1w t = 7w
Proof
  simp[pop_probe_compiler_result, pop_probe_counted_path]
QED
