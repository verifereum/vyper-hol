Theory deployOutcomesFreeBuiltinBody
Ancestors
  deployOutcomesFreeSelectors deployOutcomesFreeExprBody
  deployOutcomesFreeGenerators exprLowering list

(* Generator obligations are explicit, so this boundary is independent of
   their opcode-specific implementation proofs. *)
Theorem outcomes_free_builtin_unary_scalar:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!v ity st. Q st ==> Q (SND (compile_neg v ity st))) /\
  (!v st. Q st ==> Q (SND (compile_builtin_abs v st))) /\
  (!v st. Q st ==> Q (SND (compile_blockhash v st))) /\
  (!v st. Q st ==> Q (SND (compile_blobhash v st))) /\
  (!v d st. Q st ==> Q (SND (compile_ceil v d st))) /\
  (!v d st. Q st ==> Q (SND (compile_floor v d st))) /\
  (!v n sz st. Q st ==> Q (SND (compile_uint2str v n sz st))) /\
  (!v n sz st. Q st ==> Q (SND (compile_slice_calldata v n sz st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ty bi (MAP expr_type args) /\
  (bi = Neg \/ bi = Abs \/ bi = BlockHash \/ bi = BlobHash \/
   bi = Ceil \/ bi = Floor \/ (?n. bi = Uint2Str n) \/
   (?n. bi = CalldataSlice n)) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty bi args s))
Proof
  strip_tac >>
  `LENGTH args = 1` by metis_tac[outcomes_free_builtin_arities] >>
  `well_typed_expr env (HD args) /\
   ~supported_expr_exists constructor_call_root (HD args)` by
    (drule_all outcomes_free_typed_children >> strip_tac >>
     `args <> []` by (strip_tac >> gvs[]) >>
     drule_all outcomes_free_head >> simp[]) >>
  `!ity st. Q st ==> Q (SND (lower_value f ce ity (HD args) st))` by
    (rpt strip_tac >> irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[]) >>
  Cases_on `bi` >> gvs[] >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[outcomes_free_as_stack_val, outcomes_free_as_ptr_val] >>
  metis_tac[pairTheory.SND]
QED
