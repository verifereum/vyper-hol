Theory bodyPtrPopCalleeProbe
Ancestors
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState words
  finite_map pred_set compileEnv vyperValue vfmState

(* Concrete call fixtures expose the real INVOKE taint import. They are
   executable test programs, not a substitute for a source typing invariant. *)
Definition pop_callee_probe_fn_def:
  pop_callee_probe_fn key = mk_raw_function "callee"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 SSTORE [Lit key; Lit 1w] [];
        mk_inst 1 RET [Lit 0w] []] |>]
End

Definition pop_callee_probe_ctx_def:
  pop_callee_probe_ctx key =
    mk_venom_context [pop_callee_probe_fn key] NONE
End

Theorem pop_callee_probe_import:
  (SND (ghost_step 2 (pop_callee_probe_ctx key) [] FEMPTY
    (<| t_mem := {}; t_var := FEMPTY;
        t_stor := {(1w,0);(2w,0)};
        t_trans := {}; t_imm := {} |>)
    (mk_inst 0 INVOKE [Label "callee"; Lit 0w] [])
    (init_venom_state "caller"))).t_stor =
  key_update {(1w,0);(2w,0)} key {}
Proof
  EVAL_TAC
QED

Theorem pop_callee_probe_returns:
  case step_inst 2 (pop_callee_probe_ctx key)
    (mk_inst 0 INVOKE [Label "callee"; Lit 0w] [])
    (init_venom_state "caller") of
    OK s => lookup_storage key
      (s.vs_accounts s.vs_call_ctx.cc_address).storage = 1w
  | _ => F
Proof
  EVAL_TAC
QED

Theorem pop_callee_probe_payload_taint:
  key_update {(1w:bytes32,0:num);(2w,0)} 1w {} =
    {(2w,0)}
Proof
  simp[key_update_def, EXTENSION] >> gen_tac >> PairCases_on `x` >>
  Cases_on `x0 = 0w` >> Cases_on `x0 = 1w` >>
  Cases_on `x0 = 2w` >> gvs[dimword_def, SF wordsLib.SIZES_ss]
QED

Theorem pop_callee_probe_header_taint:
  key_update {(1w:bytes32,0:num);(2w,0)} 0w {} =
    {(1w,0);(2w,0)}
Proof
  simp[key_update_def, EXTENSION] >> gen_tac >> PairCases_on `x` >>
  Cases_on `x0 = 0w` >> Cases_on `x0 = 1w` >>
  Cases_on `x0 = 2w` >> gvs[dimword_def, SF wordsLib.SIZES_ss]
QED

Theorem pop_callee_payload_local_dead:
  !k b. (k,b) IN key_update {(1w:bytes32,0:num);(2w,0)} 1w {} /\
        w2n k < type_slot_size (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) ==>
    dead_bytes st 0 (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (w2n k) b
Proof
  simp[pop_callee_probe_payload_taint, type_slot_size_def,
       dimword_def, SF wordsLib.SIZES_ss]
QED

Theorem pop_callee_header_local_exposed:
  ~(!k b. (k,b) IN key_update {(1w:bytes32,0:num);(2w,0)} 0w {} /\
          w2n k < type_slot_size (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) ==>
    dead_bytes (update_storage 0w 1w st) 0
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (w2n k) b)
Proof
  simp[pop_callee_probe_header_taint, dead_bytes_def, type_slot_size_def,
       lookup_storage_def, update_storage_def, dimword_def, SF wordsLib.SIZES_ss] >>
  qexistsl [`1w`, `0`] >> simp[]
QED
