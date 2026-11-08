(* Common-tuple semantic audit; code inclusion is supplied by the entry probe.
   The old nested_valid_* semantic certificates have different sources/cenv.
   In particular they are not proofs of the External body_inv or expr_sim_inv.
   Remaining entry boundary: exists ss. stmt_state_rel
     nested_external_unit.cu_context nested_external_entry_fn
     nested_external_slice_cenv nested_external_cx nested_premise_es ss /\
     ~ss.vs_halted /\ ss.vs_current_bb = "fn_probe" /\ ss.vs_inst_idx = 3.
   This includes alloca_inv/room, fmp_room, immutable separation and ALLOCA sizes,
   not merely state_rel. No such entry is asserted here.
   Observation: instruction 43 SLOAD reads slot 2 AFTER the internal call;
   instructions 44--47 subtract 1 and ASSERT no underflow. A zero copied to
   that dead slot can therefore cause an error, unlike an unobserved dead write.
   To refute stmt_frag requires excluding every gas_outcome witness, including
   its gas_exempt_cert alternative, not merely showing one failing IR run. *)
Theory augAssignNestedExternalSemanticAudit
Ancestors
  augAssignNestedExternalEntryProbe augAssignNestedNormalizedProbe
  vyperTypeSystem exprSimLiteralWord
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset

Theorem nested_external_target_syntax:
  (!id. target_root nested_reach_target <> NameTarget id) /\
  ~supported_target_pure nested_external_tops nested_reach_target /\
  (?b k. nested_reach_target = SubscriptTarget b k) /\
  ~immutable_root nested_external_cx nested_reach_target
Proof
  EVAL_TAC >> simp[vyperStateTheory.find_var_decl_by_name_def]
QED

Theorem nested_external_stmt_supported:
  supported_stmt nested_external_tops []
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  EVAL_TAC
QED

Theorem nested_external_stmt_typed:
  type_stmt nested_external_env NoneT
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1))) = SOME nested_external_env
Proof
  EVAL_TAC >> simp[vyperTypeSystemTheory.subscript_vtype_def] >> EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def]
QED

Theorem nested_external_rhs_case:
  expr_sim_case F nested_external_unit.cu_context nested_external_entry_fn
    nested_external_slice_cenv nested_external_cx
    (Literal (BaseT (UintT 256)) (IntL 1))
Proof
  rewrite_tac[exprSimHypsDefsTheory.expr_sim_case_def] >> rpt strip_tac >>
  irule exprSimLiteralWordTheory.compile_literal_word_sim >>
  simp[compileEnvTheory.is_word_type_def]
QED

(* Residual premise matrix for the ONE tuple used above:
   tops=nested_external_tops, ctx=nested_external_unit.cu_context,
   func=nested_external_entry_fn, cenv=nested_external_slice_cenv,
   cx=nested_external_cx, env=env'=nested_external_env,
   es=nested_premise_es, lctx=NoLoop, ret_ty=NoneT, bindings=[].
   Syntax/root/effectful/nonimmutable: nested_external_target_syntax.
   supported_stmt: nested_external_stmt_supported.
   type_stmt: nested_external_stmt_typed.
   Conditional RHS case: nested_external_rhs_case (unconditional).
   fn_has_code: nested_external_slice_code (entry probe).
   nonterminated sa/current label/index: nested_external_slice_position.

   FIRST unresolved semantic boundary (no transfer theorem applies):
     body_inv nested_external_tops nested_external_unit.cu_context
       nested_external_slice_cenv nested_external_cx.
   nested_valid_body_inv is for nested_reach_tops and nested_premise_cenv;
   its transaction-only transfer cannot rewrite a changed sources field.
   Successful lowering is available from nested_external_lowering_exists,
   but the remaining body_inv metadata/pins conjuncts must be checked at
   this External environment rather than assumed from the old certificate.

   Further unresolved frozen premises:
     target_case F nested_external_unit.cu_context nested_external_entry_fn
       nested_external_slice_cenv nested_external_cx nested_reach_target;
     target_indices_pre nested_external_slice_cenv nested_external_cx
       nested_external_env nested_reach_target;
     expr_body_pre nested_external_slice_cenv nested_external_cx
       nested_external_env (Literal (BaseT (UintT 256)) (IntL 1))
       nested_premise_es.
   Old nested_valid_target_case/indices/rhs_pre have different cx and cenv.
   The finite callee boundary remains universal in cx, so it is reusable,
   unlike the old concrete expr_sim_inv certificate.

   Further stmt_frag entry antecedents, beyond the entry existential above:
     fn_inst_ids_distinct nested_external_entry_fn;
     local_ptrs_reserved nested_external_slice_cenv nested_external_slice_start;
     ret_pc_ok nested_external_slice_cenv nested_external_slice_start ss;
     gas_admissible (eval_stmt nested_external_cx
       (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
         (Literal (BaseT (UintT 256)) (IntL 1))))
       (stmt_res_ok NoLoop) nested_premise_es.
   The m sa equation defines cenv' and sb; it introduces no independent
   entry assumption. RetQ may be K (K (K F)) since source success has no
   ReturnException. Neither source success at nested_external_cx nor the
   exclusion of gas_exempt_cert has been certified in this audit.

   Exact observation required: with source res=INL (), stmt_exit is false
   (stmt_exit_loop_ctl). gas_summary_at must therefore end at OK t with
   stmt_post ... (INL ()) ee t, which entails ~t.vs_halted, stmt_lands and
   stmt_state_rel at the slice endpoint. An underflow ASSERT would violate
   that requirement, but only after excluding alternative marked paths AND
   the separate gas_exempt_cert disjunct of gas_outcome. This audit stops
   before that nontrivial execution/exclusion obligation. *)
