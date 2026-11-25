Theory entryCreateGroupedLayout
Ancestors
  groupedRuntimeBodyCode groupedInternalLabels entryRejectCode entryCompileIntervals
  externalEntryShape exprLoweringProps fragExec moduleLowering compileEnv emitHelper
  loweringShapeDefs groupedEntryCounters emitHelperProps venomInst list pair
  groupedRuntimeEndpoint
Libs groupedEndpointIntroLib

(* Compatibility instance for the unredecorated public routes. *)
Theorem grouped_registered_intro_unrestricted:
  ^(intro D endpoint_const)
Proof
  rpt gen_tac >>
  disch_then (ACCEPT_TAC o MATCH_MP grouped_registered_body_endpoint o CONJUNCT1)
QED

(* Distinctness at an actual descendant of the grouped dispatch.  Identify
   the compiler states by their equations, not by block lookup in the code. *)
Theorem grouped_entry_end_labels:
  run_grouped_lowering groups ips fb rp "__entry" = SOME unit /\
  EVERY group_entry_labels_ok groups /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fresh_label "fallback" (initial_compile_state "__entry") = (fallback,sf) /\
  compile_group_dispatch_linear groups fallback sf = (jobs,sd) /\
  compile_external_jobs jobs sd = ((),sx) /\
  new_block fallback sx = (sx.cs_current_bb,sn) /\
  (case fb of NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
   | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
       compile_fallback_body ce pay nr key tr view stmts rt) sn = ((),se) ==>
  cs_extends sd se /\ cs_extends sx se /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se))
Proof
  strip_tac >> drule_all run_grouped_lowering_dispatch_code >>
  disch_then (qx_choosel_then [`sf'`,`fallback'`,`jobs'`,`sd'`,`sx'`,`sn'`,`se'`]
    strip_assume_tac) >>
  `sf' = sf /\ fallback' = fallback` by metis_tac[PAIR_EQ] >> gvs[]
QED

Theorem grouped_layout_restrict[local]:
  cs_extends b z /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks z)) ==>
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks b))
Proof
  strip_tac >> drule cs_extends_labels >> strip_tac >> fs[ALL_DISTINCT_APPEND]
QED

(* The selected supplied-argument decoder exposes this compiler equation at
   its exit. Its actual omitted suffix therefore inherits the end layout. *)
Theorem selected_initializer_suffix_layout_at:
  compile_init_kwargs ce vars off k hi last = ((),sb) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks sb)) ==>
  cs_extends last sb /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks sb))
Proof
  strip_tac >> asm_rewrite_tac[] >>
  metis_tac[compile_init_kwargs_ci_mono, SND, ci_mono_def]
QED

(* At a selected initializer, term is the installed jump; dispatch_end is
   the end of the selector interval inside the actual dispatch compiler run. *)
Theorem selected_initializer_layout_at:
  compile_init_kwargs ce vars off k hi last = ((),sb) /\
  emit_inst JMP [Label common] [] sb = ((),term) /\
  cs_extends term dispatch_end /\ cs_extends dispatch_end sd /\
  cs_extends sd se /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se)) ==>
  cs_extends last sb /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks sb))
Proof
  strip_tac >>
  `cs_extends sb term` by
    (drule_then strip_assume_tac emit_inst_extends >> simp[cs_extends_def] >>
     qexists_tac `[]` >> simp[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks sb))` by
    (irule grouped_layout_restrict >> qexists_tac `se` >>
     asm_rewrite_tac[] >> metis_tac[cs_extends_trans]) >>
  drule_all_then ACCEPT_TAC selected_initializer_suffix_layout_at
QED

(* Accept at the actual guarded-body witness, before packaging an endpoint.
   The common job, legacy job and fallback all provide this retained end
   extension (reflexive in the fallback case). *)
Theorem selected_grouped_body_layout_at:
  compile_guarded_body ce nr key tr view stmts rt sa = ((),done) /\
  cs_extends done se /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se)) ==>
  cs_extends sa done /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks done))
Proof
  strip_tac >> conj_tac
  >- metis_tac[cs_appends_guarded_body, cs_appends_def, SND] >>
  metis_tac[grouped_layout_restrict]
QED
