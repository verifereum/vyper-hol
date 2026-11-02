Theory sourceMeaningLocationCode
Ancestors
  sourceMeaningLocationDefs sourceMeaningCode sourceMeaningDefs sourceMeaningRuntime
  sourceExprDefs vyperInterpreter vyperAbiOperand vyperState vyperAST
  vyperValue vyperValueOperation vyperEvmBoundary vyperContext list

(* This relation is a proof bridge only. Source derivations are defined in a
   separate theory and never consult this relation or runtime expressions. *)
Inductive source_location_code:
[core_literal:]
  source_meaning_code tenv [] core (Literal ty lit) ==>
  source_location_code tenv (SML_Core core) (Literal ty lit)
[core_builtin:]
  source_meaning_code tenv [] core (Builtin ty b es) ==>
  source_location_code tenv (SML_Core core) (Builtin ty b es)
[local_cell:]
  source_location_code tenv (SML_Reference ty (SMR_Local id)) (Name ty id)
[global:]
  source_location_code tenv (SML_Reference ty (SMR_Global gid)) (TopLevelName ty gid)
[apply:]
  b <> Len /\ source_location_codes tenv ms es ==>
  source_location_code tenv (SML_Apply ty b ms) (Builtin ty b es)
[length:]
  source_location_code tenv m e ==>
  source_location_code tenv (SML_Length ty m) (Builtin ty Len [e])
[conditional:]
  source_location_code tenv c ce /\ source_location_code tenv l le /\
  source_location_code tenv r re ==>
  source_location_code tenv (SML_If ty c l r) (IfExp ty ce le re)
[subscript:]
  source_location_code tenv a ae /\ source_location_code tenv i ie ==>
  source_location_code tenv (SML_Subscript ty a i) (Subscript ty ae ie)
[type_apply:]
  source_location_codes tenv ms es ==>
  source_location_code tenv (SML_TypeApply ty tb target_type ms) (TypeBuiltin ty tb target_type es)
[revert:]
  source_location_code tenv m e ==>
  source_location_code tenv (SML_Revert ty m) (Call ty RawRevert [e] NONE)
[raw_call:]
  flags.rcf_kws = [EKValue] /\
  source_location_code tenv t te /\ source_location_code tenv d de /\
  source_location_code tenv v ve ==>
  source_location_code tenv (SML_RawCall ty flags t d v)
    (Call ty (RawCallTarget flags) [te;de;ve] NONE)
[raw_call_default:]
  flags.rcf_kws = [] /\
  source_location_code tenv t te /\ source_location_code tenv d de ==>
  source_location_code tenv
    (SML_RawCall ty flags t d (SML_Core (SM_Literal (BaseT (UintT 256)) (IntL 0))))
    (Call ty (RawCallTarget flags) [te;de] NONE)
[empty_codes:]
  source_location_codes tenv [] []
[cons:]
  source_location_code tenv m e /\ source_location_codes tenv ms es ==>
  source_location_codes tenv (m::ms) (e::es)
End

Theorem source_location_code_types:
  !tenv. (!m e. source_location_code tenv m e ==>
    expr_type e = source_location_type m) /\
  (!ms es. source_location_codes tenv ms es ==>
    LENGTH ms = LENGTH es /\ MAP expr_type es = MAP source_location_type ms)
Proof
  gen_tac >> ho_match_mp_tac source_location_code_ind >>
  rw[source_location_type_def,expr_type_def] >>
  imp_res_tac source_meaning_code_type >> gvs[expr_type_def]
QED

Theorem source_location_core_runtime:
  source_meaning_code tenv [] m e /\ get_tenv cx = tenv ==>
  eval_expr cx e = source_location_eval cx (SML_Core m)
Proof
  strip_tac >> simp[source_location_eval_def] >>
  irule source_meaning_code_evaluates >> qexists_tac `[]` >> simp[]
QED

(* The length check justifies selecting the explicit value operand.  Keeping
   this protocol lemma separate avoids splitting the three effectful children. *)
Theorem source_location_raw_call_protocol:
  flags.rcf_kws = [EKValue] ==>
  (do
    type_check (LENGTH vs = 2 + LENGTH flags.rcf_kws) "raw_call args";
    target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
    data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
    amount <- lift_option_type (raw_call_value flags.rcf_kws (DROP 2 vs)) "raw_call value";
    eval_raw_call cx flags target data amount
      (forwarded_gas default_evm_gas_limit
        (ext_call_kwarg EKGas flags.rcf_kws (DROP 2 vs)))
  od) =
  (do
    type_check (LENGTH vs = 3) "raw_call args";
    target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
    data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
    amount <- lift_option_type (dest_NumV (EL 2 vs)) "raw_call value";
    eval_raw_call cx flags target data amount default_evm_gas_limit
  od)
Proof
  strip_tac >> Cases_on `LENGTH vs = 3`
  >- (gvs[] >> gvs[LENGTH_EQ_NUM_compute,raw_call_value_def,
        ext_call_kwarg_def,forwarded_gas_def]) >>
  simp[FUN_EQ_THM,ignore_bind_def,bind_def,type_check_def,assert_def]
QED

(* With no value keyword the canonical AST has only target and data. The
   independent source rule still ties the semantic default to literal zero. *)
Theorem source_location_raw_call_default_protocol:
  flags.rcf_kws = [] ==>
  (do
    type_check (LENGTH vs = 2 + LENGTH flags.rcf_kws) "raw_call args";
    target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
    data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
    amount <- lift_option_type (raw_call_value flags.rcf_kws (DROP 2 vs)) "raw_call value";
    eval_raw_call cx flags target data amount
      (forwarded_gas default_evm_gas_limit
        (ext_call_kwarg EKGas flags.rcf_kws (DROP 2 vs)))
  od) =
  (do
    type_check (LENGTH vs = 2) "raw_call args";
    target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
    data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
    amount <- return 0;
    eval_raw_call cx flags target data amount default_evm_gas_limit
  od)
Proof
  simp[raw_call_value_def,ext_call_kwarg_def,forwarded_gas_def,
       lift_option_type_def,return_def,bind_def]
QED

(* The simultaneous theorem is essential: ordinary name reads alone cannot
   justify ABI encoding of a local aggregate. The ABI half retains captures,
   projection bounds, delayed staging and final release, including exceptions. *)
Theorem source_location_code_evaluates:
  !tenv. (!m e. source_location_code tenv m e ==>
    !cx. get_tenv cx = tenv ==>
      eval_expr cx e = source_location_eval cx m /\
      eval_abi_expr cx e = source_location_abi cx m) /\
  (!ms es. source_location_codes tenv ms es ==>
    !cx. get_tenv cx = tenv ==>
      eval_exprs cx es = source_location_evals cx ms /\
      eval_abi_exprs cx es = source_location_abis cx ms)
Proof
  gen_tac >> ho_match_mp_tac source_location_code_strongind >> rpt conj_tac >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >- (drule_all source_location_core_runtime >> strip_tac >>
      fs[source_location_eval_def,evaluate_def])
  >- (drule_all source_location_core_runtime >> strip_tac >>
      fs[source_location_eval_def] >> simp[Once evaluate_def])
  >- simp[evaluate_def,source_location_eval_def,source_reference_read_def,
       source_reference_abi_def,source_meaning_local_def]
  >- (Cases_on `gid` >> simp[evaluate_def,source_location_eval_def,
       source_reference_read_def,source_reference_abi_def])
  >- (imp_res_tac (CONJUNCT2 (SPEC_ALL source_location_code_types)) >>
      simp[evaluate_def,source_location_eval_def])
  >- simp[evaluate_def,source_location_eval_def]
  >- simp[evaluate_def,source_location_eval_def]
  >- (imp_res_tac (CONJUNCT1 (SPEC_ALL source_location_code_types)) >>
      simp[evaluate_def,source_location_eval_def])
  >- (imp_res_tac (CONJUNCT2 (SPEC_ALL source_location_code_types)) >>
      simp[evaluate_def,source_location_eval_def])
  >- simp[evaluate_def,source_location_eval_def,source_meaning_args_def]
  >- simp[evaluate_def,source_location_eval_def,source_meaning_args_def,
       source_location_raw_call_protocol]
  >- simp[evaluate_def,source_location_eval_def,source_meaning_args_def,
       source_location_raw_call_default_protocol]
  >- simp[evaluate_def,source_location_eval_def]
  >> simp[evaluate_def,source_location_eval_def]
QED
