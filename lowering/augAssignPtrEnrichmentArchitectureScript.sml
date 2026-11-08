(* Bounded architecture audit for C1.4.5.  This theory asserts no universal
   enrichment theorem.  All items marked REQUIRED below are unproved interfaces,
   not consequences of the primitive probes.

   1. Candidate operational contract
   --------------------------------
   Keep ALL quantified inputs and antecedents of bodyPtrDefs.expr_sim_ptr_def
   (bodyPtrDefsScript.sml:216-243), and its source computation
     bind (eval_expr cx e) (read_result cx).
   Replace only its normal post by
     (\res ee G tn t. ?v. res = INL v /\
       expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv d cenv cx ee G tn t /\
       ptr_val_ok cx (expr_type e) v op G tn t /\
       (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
       ghost_kept cenv es sa G0 tn0 s0 G tn /\
       (is_word_type (expr_type e) ==> op_prov G op = NONE)).
   Exceptional post stays (\res ee gt r. expr_exit res r).  No separate
   execution is conjoined with an existing expr_sim_ptr witness.  The stronger
   outcome itself must supply marks/path/final ghost, including the unchanged
   exempt-certificate alternative.  Ordinary outcome follows by consequence.

   The vv version must instead qualify the extra clause:
     !ty' op'. vv = StackValue ty' op' /\ is_word_type (expr_type e) ==>
                 op_prov G op' = NONE.
   A LocatedValue's pointer MUST retain provenance.  Erasing all scalar vv
   operands' provenance would destroy the pointer needed to load that value.
   Ordinary vv post is at bodyPtrDefsScript.sml:263-273.

   2. Loadable interfaces and their actual scope
   -------------------------------------------
   bodyPtrExprCasesScript.sml:24:
     body_ifexp_case_ptr:
       !cx a c l r.
       (!s tv t. eval_expr cx c s = (INL tv,t) ==> body_expr_ptr_ok cx l) /\
       (!s tv t. eval_expr cx c s = (INL tv,t) ==> body_expr_ptr_ok cx r) /\
       body_expr_ptr_ok cx c ==> body_expr_ptr_ok cx (IfExp a c l r).
   This is locally admitted and yields ONLY ordinary simulations.  There is no
   reusable implementation exposing its chosen branch's ghost/path.  The same
   applies to body_type_builtin_case_ptr (there:84), whose premise is
     (!s x t. type_check (type_builtin_args_length_ok tb (LENGTH es))
        "TypeBuiltin args" s = (INL x,t) ==> body_exprs_ptr_ok cx es)
   and conclusion body_expr_ptr_ok cx (TypeBuiltin a tb typ es).

   bodyPtrIntCallCase.body_intcall_case_ptr (Script:18-85) has three premises:
   successful lookup/argument evaluation/binding/push_function implies
   body_stmts_ptr_ok cxf body'; successful lookup/argument evaluation and scope
   reset implies body_exprs_ptr_ok cxd needed_dflts; successful lookup and
   argument-length check implies body_results_ptr_ok cx es.  Its conclusion is
     body_expr_ptr_ok cx (Call a (IntCall (src_id_opt,fn)) es drv).
   The full quantified lookup premises are exactly at lines 20-82 of that
   file.  It too is locally admitted, not an enriched or decomposed call run.

   exprSimMain.compile_expr_sim:
     !ctx func cenv cx env ty e es.
       expr_sim_pre cenv cx env e es ==> expr_sim ctx func cenv cx ty e es.
   compile_expr_vv_sim has the identical premise and expr_vv_sim conclusion
   (Script:113-124).  These locally admitted S1 facts have no pointer ghost.
   compile_expr_sim_mutual proves expr_ok/builtin_sim_ok/type_builtin_sim_ok,
   not enriched pointer cases.  Reference proofs in alan-ref/s1 are NOT
   loadable interfaces and cannot add a ghost to those statements.

   gasSummaryComposePtr.gas_outcome_ptr_conseq (Script:121) weakens posts.
   gas_outcome_ptr_prefix (209):
     gas_path_ptr D 0 ctx func PG G0 tn0 s0 n G1 tn1 (OK s1) /\
     gas_outcome_ptr D tops (ctx,func) PG source (es,s1,G1,tn1) Q R ==>
     gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q R.
   gas_outcome_ptr_bind (253-272) requires a first outcome whose normal post
   already supplies the continuation outcome at (es_mid,t,G,tn), plus the
   error and normal gas_exempt_cert bind rules; it concludes the outcome for
   bind source next at the original input.  It does not extract a stronger
   normal post from an ordinary one.  bind_normal (224) additionally exposes
   the first gas_marked_exec_ptr witness and clears mid.gas_obs.

   3. Case flows on ONE constructed witness (not yet proved)
   --------------------------------------------------------
   IfExp: exprLowering.compile_expr_def:2942-2969 lowers condition, emits JNZ,
   compiles selected arm, unwraps via compile_ifexp_arm, then ASSIGNs to
   result_var and JMPs to exit.  For word res_ty, compile_ifexp_arm_def:2425
   is precisely unwrap_value cenv vv.  REQUIRED: condition outcome permitting
   JNZ; selected arm enriched vv/unwrap outcome; ASSIGN copies NONE to
   result_var; JMP and block entry preserve it.  Compose THAT branch's marks,
   ghost and suffix, not a second ordinary IfExp outcome.  Other branch code
   is layout, not executed.  No actual PHI instruction occurs here; the shared
   result variable is assigned on each arm.  Arbitrary re-entry at exit is
   not the claim.  Ordinary body_ifexp_case_ptr cannot supply this enrichment.

   Convert (representative forwarding operation): compile_type_convert_def
   at exprLoweringScript.sml:1667-1695 returns its input v after integer
   bounds checks, or immediately for a widening conversion; ConvIdentity at
   1868 is return v.  mk_convert_op_def at 1920-1959 selects these cases.
   REQUIRED: clean provenance for child's LOWERED word on the child outcome;
   frame it across fresh comparison temporaries/ASSERT (normal branch);
   propagate the original operand unchanged.  Abort uses the existing exit
   contract.  In particular, creating clean comparison outputs alone cannot
   make the forwarded result clean.  The region/frame theorem below is a
   conditional tool: freshness and suffix-region closure still need proof.

   IntCall: compile_call_def:2627-2667 allocates a return buffer for stack
   results, INVOKEs, stores multi-results, returns LocatedValue call_ty;
   other buffer returns also yield LocatedValue, no-buffer gives Lit 0w.
   lower_value_def:2002 is compile_expr followed by unwrap_value;
   unwrap_value_def:965 loads LocatedValue when its *declared* type is word.
   internal_call_word_return_metadata (augAssignPtrCallWordBoundary:6-23):
     body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
     well_typed_expr env (Call ann (IntCall id) args drv) /\ is_word_type ann /\
     supported_function_decl tops id Internal =
       SOME (mut,nr,rr,params,dflts,ret,body) ==>
     cenv.ce_func_return_type (nsid_to_string id) = ann.
   This validates word-type selection, NOT successful lookup or INVOKE runs.
   A genuinely available ordinary CALL vv outcome can be used unchanged as
   prefix: append the actual unwrap MLOAD, which clears result provenance
   regardless of callee provenance.  This would avoid enriched callee return
   simulation.  REQUIRED: call vv outcome availability, safe covered load,
   typed value/taint post, and counted unwrap composition incl. errors/certs.
   An ordinary scalar expr_sim_ptr outcome alone hides that load and cannot
   serve as its prefix.  Arbitrary callee code remains inside the prefix.

   4. Existing checked probes vs missing recursion interface
   --------------------------------------------------------
   augAssignPtrProvenancePath.gas_path_ptr_untagged_frame (41-47) requires
   region s and per-edge preservation of FLOOKUP G x and region on OK exits.
   load_ghost_result_has_no_provenance (82-86) requires
     MEM opc [MLOAD;SLOAD;TLOAD;CALLDATALOAD] /\
     step_inst fuel ctx (mk_inst id opc [src] [x]) s = OK u
   and concludes op_prov of the actual ghost_step result at Var x is NONE.
   invoke_output_has_no_provenance (55) requires actual decode, lookup,
   eval_operands and setup_callee success; no global call dominance follows.
   augAssignPtrScalarWitnessProbe.local_name_enriched_outcome (98) is a
   constructed primitive Name outcome, with explicit word_value entry.value.
   It cannot be instantiated for AddressT/fixed BytesT merely from typing:
   word_value excludes BytesV.  REQUIRED typed_val_to_w256-based live-word
   robustness/load interface, rather than val_to_w256 extraction.  Metadata
   equality does not solve this typed load issue.

   Natural local recursion source is compile_expr_ind / expr_size with list
   sizes, as exprSimMain:91-108 shows.  This is acyclic for syntax children
   of IfExp/Convert.  Callee bodies and defaults are NOT syntax children of
   Call, so this measure cannot justify their simulation.  evaluate_ind
   includes statements, lists, targets, calls, defaults and expressions
   (bodySimPtrMain:38-53); its statement AugAssign case uses THIS task's
   body_augassign_case_ptr at line 75.  Importing it forms a cycle.  A new
   enriched evaluate_ind over all bodies would duplicate the unresolved
   target and is not a small solution.

   Recommendation: ancestor review is needed before any universal theorem.
   Small next interfaces are (a) typed scalar unwrap on an available vv
   outcome; (b) selected-arm ASSIGN/JMP normal-post transport; (c) forwarding
   Convert suffix frame.  They are necessary but not sufficient.  A theorem
   reconstructing all expressions still needs ordinary outcomes for recursive
   children and atomic calls.  body_expr_ptr_ok for the PARENT alone gives no
   general child body_expr_ptr_ok elimination theorem.  Neither existing case
   lemma supplies that direction.  Passing all child body predicates as extra
   hypotheses would not meet the frozen AugAssign use site.  A candidate
   broad architecture must explicitly solve this availability problem or
   replace it by a checked same-path compiler-region argument.  No frozen
   source change has been proved necessary, and no task counterexample is
   established by this audit.
*)
Theory augAssignPtrEnrichmentArchitecture
Ancestors
  augAssignPtrScalarWitnessProbe augAssignPtrCallWordBoundary
  augAssignPtrProvenancePath
