Theory concretizePtrOpaqueRetpc
Ancestors
  concretizePtrSharedFields concretizePtrValueSelection concretizePtrValueTransport
  concretizeStepRetpc concretizeStepShape unitShapeDefs
  venomExecSemantics venomState finite_map list words

(* Opaque return-PC interface audit (C1.10.3.1).

   SEMANTIC CONSUMERS (venomExecSemantics).
   - step_inst_base, RETPC_PARAM: [Lit idx]/[out] writes this frame's
     vs_return_pc_token, without reading vs_params or checking idx.
   - RET evaluates all operands, rejects []/undefined, and returns FRONT
     values with iret_adopt_fmp=NONE. It does NOT compare the last value
     with vs_return_pc_token. The optimized step_inst_noninvoke branch
     has the same FRONT rule. RETFMP instead returns SOME vs_fmp;
     DRET parses and packs dynamic returns. They are not interchangeable.
     fn_ptr_ok excludes RETFMP/DRET in source; concretize_positions_other_opcode
     is the existing rewrite exclusion boundary.
   - step_inst INVOKE, frame_reachable ret: neither performs a token check.
     They merge shared callee effects, adopt FMP, bind iret_values.
     Only eval/return arity/active-instruction checks remain.
   - setup_callee puts LAST args (or 0w) in token, clears vars, sets params.
     merge_callee_state_frame restores caller vars, params, token, labels,
     cursor. adopt_return_fmp_frame preserves vars and token.
     An opaque interpretation suffices; no global word renaming is valid.

   SHAPE SUPPLIERS (existing interfaces, do not restate).
   o1_ctx_shape C = ctx_wf C /\ ctx_inst_ids_distinct C /\
     EVERY (o1_fn_shape C) C.ctx_functions.
   o1_fn_shape entails wf_function and fn_shape_ok;
   fn_shape_ok entails opaque_use_ok and retpc_shape_ok.
   opaque_use_ok_retpc_use:
     opaque_use_ok fn /\ retpc_var fn x /\ MEM inst (fn_insts fn) /\
     MEM (Var x) inst.inst_operands ==> retpc_use_ok inst x.
   retpc_use_ok allows ASSIGN, PHI, or a unique final return operand;
   it forbids opaque operands in INVOKE, arithmetic and memory ops.
   retpc_shape_ok constrains writers of opaque vars to RETPC_PARAM,
   copies and all-opaque PHIs, and constrains returns in reachable_fn.
   reachable_retpc_var: retpc_var (reachable_fn fn) x ==> retpc_var fn x.
   Needs actual current source-function membership/reachability from the
   chronological prefix, not an assertion about arbitrary observations.

   Existing concretizeStepRetpc exports:
   concretize_positions_copy_phi:
     MEM origin [GAS;RETPC_PARAM] ==>
     (copy_phi_var origin (concretize_function_with_positions p fn) x <=>
      copy_phi_var origin fn x).
   concretize_positions_opaque_use:
     opaque_use_ok fn ==> opaque_use_ok (concretize_function_with_positions p fn).
   concretize_positions_reachable_fn:
     wf_function fn ==> reachable_fn (concretize_function_with_positions p fn) =
       concretize_function_with_positions p (reachable_fn fn).
   concretize_positions_reachable_copy_phi:
     wf_function fn /\ MEM origin [GAS;RETPC_PARAM] ==>
     (copy_phi_var origin (reachable_fn (concretize_function_with_positions p fn)) x
       <=> copy_phi_var origin (reachable_fn fn) x).
   concretize_positions_retpc_shape:
     wf_function fn /\ retpc_shape_ok fn ==>
     retpc_shape_ok (concretize_function_with_positions p fn).
   concretizeStepShape exports concretize_positions_fn_shape and
   concretize_positions_o1_fn_shape. Paired code only fixes target blocks;
   lifting these facts through metadata differences requires the actual
   production witness, not equality of whole functions invented locally.
   concretize_stage_shape does NOT export EVERY o1_fn_shape C'.

   MIGRATION MAP (not yet installed in production).
   - ptr_paired_sample currently conjoins unrestricted ptr_vars_transport
     and ptr_shared_fields. Replace these only after probes with a mixed
     relation on non-retpc vars + synchronized definedness and own-token
     interpretation on retpc vars, and token-normalized shared fields.
   - ptr_paired_samples_transport and ptr_paired_samples_shared project
     the old relations. No external uses of the shared projection currently
     occur in the pass proofs; their future consumers must use the mixed
     operand boundary or the core-field projection respectively.
   - ptr_vars_transport_def quantifies ALL vars. NONE tag / empty taint
     demands equality (ptr_value_transport_scalar_empty). RETPC_PARAM
     outputs with unequal tokens therefore cannot use the unrestricted
     scalar update theorem. step_prov clears non-pointer outputs and
     step_taint normally clears their variable taint; do not fake a pointer
     tag or taint mask to hide this mismatch.
   - ptr_vars_transport_eval[_all], ptr_eval_operands_transport,
     affine transport and demand/write consumers need non-opaque operand
     premises supplied by opaque_use_ok; the old conditional lemmas remain
     true and must not be weakened or dropped. ASSIGN and PHI need mixed
     update/selection lemmas, splitting opaque from ordinary outputs using
     writer shape. Parallel PHI semantics and definedness matter.
   - ptr_setup_callee_transport handles empty vars already. Core setup
     must NOT require LAST equality. ptr_shared_fields_merge/adopt_none
     need core analogues; saved caller vars/token must be retained while
     adopting callee memory/effects, never pre-call memory.
   - ptr_return_bind_transport assumes equal ordinary iret_values and
     restores DRESTRICT TG/taint after binding; a future mixed version must
     exclude opaque output variables via caller writer shape (INVOKE is
     not an allowed opaque writer). Saved TG/PT/taint witnesses remain.
     Equal returned ordinary values is a SEPARATE obligation; arbitrary
     masked value transport does not imply it. Opaque tokens are omitted
     by FRONT for RET, not returned as ordinary outputs.

   REMAINING GAPS.
   Isolated setup/RETPC_PARAM/merge probes are next, not a universal proof.
   Production migration still needs the mixed definedness invariant,
   opaque-copy/parallel-PHI preservation, source/target observation shape,
   non-opaque operand exclusion and ordinary return-value transport.
   No proof of opaque/pointer-tag disjointness is assumed here. No final
   frozen theorem or full paired-certificate counterexample is claimed.
*)

Definition ptr_core_shared_def:
  ptr_core_shared s t <=>
    ptr_shared_fields (s with vs_return_pc_token := 0w)
      (t with vs_return_pc_token := 0w)
End

Definition ptr_opaque_env_def:
  ptr_opaque_env fn s <=>
    !x v. retpc_var fn x /\ FLOOKUP s.vs_vars x = SOME v ==>
      v = s.vs_return_pc_token
End

Theorem ptr_core_shared_setup:
  ptr_core_shared s t /\
  (NULL f.fn_blocks <=> NULL g.fn_blocks) /\
  setup_callee g argst t = SOME ct ==>
  ?cs. setup_callee f args s = SOME cs /\ ptr_core_shared cs ct
Proof
  simp[setup_callee_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  gvs[ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_opaque_env_setup:
  setup_callee fn args s = SOME cs ==> ptr_opaque_env fn cs
Proof
  simp[setup_callee_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  simp[ptr_opaque_env_def]
QED

Theorem ptr_core_shared_merge:
  ptr_core_shared s t /\ ptr_core_shared u v ==>
  ptr_core_shared (merge_callee_state s u) (merge_callee_state t v)
Proof
  simp[ptr_core_shared_def, ptr_shared_fields_def, merge_callee_state_def]
QED

Theorem ptr_opaque_env_merge:
  ptr_opaque_env fn (merge_callee_state s u) <=> ptr_opaque_env fn s
Proof
  simp[ptr_opaque_env_def, merge_callee_state_frame]
QED

Theorem ptr_core_shared_adopt_none:
  ptr_core_shared s t /\ r.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE ==>
  ptr_core_shared (adopt_return_fmp r s) (adopt_return_fmp rt t)
Proof
  simp[adopt_return_fmp_def]
QED

Theorem ptr_opaque_env_adopt:
  ptr_opaque_env fn (adopt_return_fmp r s) <=> ptr_opaque_env fn s
Proof
  Cases_on `r.iret_adopt_fmp` >>
  simp[ptr_opaque_env_def, adopt_return_fmp_def]
QED

Theorem ptr_opaque_final_operand:
  ptr_opaque_env fn s /\ retpc_var fn x /\
  FLOOKUP s.vs_vars x = SOME v ==>
  eval_operand (Var x) s = SOME s.vs_return_pc_token
Proof
  simp[ptr_opaque_env_def, eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem ptr_opaque_retpc_step:
  step_inst_base (mk_inst id RETPC_PARAM [Lit idx] [out]) s =
    OK (update_var out s.vs_return_pc_token s)
Proof
  simp[step_inst_base_def, venomInstTheory.mk_inst_def]
QED

Theorem ptr_opaque_env_retpc_update:
  ptr_opaque_env fn s ==>
  ptr_opaque_env fn (update_var out s.vs_return_pc_token s)
Proof
  simp[ptr_opaque_env_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `x = out` >> gvs[] >> metis_tac[]
QED

(* Each side writes its OWN token: no equal-token premise. *)
Theorem ptr_opaque_retpc_pair:
  ptr_core_shared s t /\ ptr_opaque_env f s /\ ptr_opaque_env g t ==>
  step_inst_base (mk_inst id RETPC_PARAM [Lit idx] [out]) s =
    OK (update_var out s.vs_return_pc_token s) /\
  step_inst_base (mk_inst id RETPC_PARAM [Lit idx] [out]) t =
    OK (update_var out t.vs_return_pc_token t) /\
  ptr_core_shared (update_var out s.vs_return_pc_token s)
    (update_var out t.vs_return_pc_token t) /\
  ptr_opaque_env f (update_var out s.vs_return_pc_token s) /\
  ptr_opaque_env g (update_var out t.vs_return_pc_token t)
Proof
  simp[ptr_opaque_retpc_step, ptr_opaque_env_retpc_update,
       ptr_core_shared_def, ptr_shared_fields_def, update_var_def]
QED

Theorem ptr_opaque_retpc_not_unrestricted:
  s.vs_return_pc_token <> t.vs_return_pc_token ==>
  ~ptr_vars_transport births positions FEMPTY (tn with t_var := FEMPTY)
    (update_var out s.vs_return_pc_token s)
    (update_var out t.vs_return_pc_token t)
Proof
  strip_tac >> simp[ptr_vars_transport_def] >> qexists_tac `out` >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, ptr_lookup_transport_def,
       ptrDisciplineTheory.op_taint_def, ptr_value_transport_scalar_empty]
QED

Theorem ptr_opaque_nested_restore_probe:
  ~NULL f.fn_blocks ==>
  ?cs ct ds dt.
    setup_callee f [3w] (s with vs_return_pc_token := 1w) = SOME cs /\
    setup_callee f [4w] (s with vs_return_pc_token := 2w) = SOME ct /\
    setup_callee f [5w] cs = SOME ds /\
    setup_callee f [6w] ct = SOME dt /\
    (merge_callee_state cs ds).vs_return_pc_token = 3w /\
    (merge_callee_state ct dt).vs_return_pc_token = 4w /\
    (merge_callee_state (s with vs_return_pc_token := 1w)
      (merge_callee_state cs ds)).vs_return_pc_token = 1w /\
    (merge_callee_state (s with vs_return_pc_token := 2w)
      (merge_callee_state ct dt)).vs_return_pc_token = 2w
Proof
  simp[setup_callee_def, merge_callee_state_frame]
QED

(* Proposed mixed relation for parent review (NOT installed):

   classification premise:
     !x. retpc_var f x <=> retpc_var g x

   mixed_vars births positions TG tn f g s t <=>
     ptr_opaque_env f s /\ ptr_opaque_env g t /\
     (!x. retpc_var f x ==>
          (FLOOKUP s.vs_vars x = NONE <=> FLOOKUP t.vs_vars x = NONE)) /\
     (!x. ~retpc_var f x ==>
          ptr_lookup_transport births positions (FLOOKUP TG x)
            (op_taint tn (Var x)) (lookup_var x s) (lookup_var x t))

   Own-token interpretation alone does not synchronize definedness.
   Need both clauses above, since successful eval on the target must
   supply a successful source eval. For ordinary operands this comes
   from ptr_lookup_transport; opaque operands require the extra NONE iff.
   This is a variable-class relation, never a relation renaming all words.
   Parent migration list and unresolved obligations are in the audit above.
*)
