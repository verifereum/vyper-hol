(*
 * The per-pass contract of the O1 pipeline.
 *
 * The pipeline runs its passes function by function, callee first, and a
 * function's passes observe a unit in which its callees are finished and
 * its callers are still raw.  Such a unit has no meaning of its own:
 * FmpLowering gives a finished callee a hidden FMP parameter that a raw
 * caller does not pass.  So the contract is not stated on the units the
 * walk builds but on STAGE CONTEXTS: for the k-th pass of the schedule,
 * the context in which every function has been through the passes before
 * it.  The walk's intermediate functions are exactly these contexts'
 * functions (o1FnScheduleDecomp, o1ScheduleDecomp), so one contract
 * theorem per pass tag, stated between consecutive stage contexts,
 * composes to the pipeline stage theorems S4 and S6 (o1PipelineCorrect).
 *
 * A pass run is a fn_pass_step: the dispatched pass applied to one
 * function on the unit it observed, with the checks the schedule runner
 * makes.  ctx_pass_stage relates two contexts function by function through
 * such steps; the VIEW says what the observed unit's callees are relative
 * to the output context (FmpLowering reads callee signatures,
 * ConcretizeMemLoc reads callee layouts): a callee is observed in its
 * final form, reached from its stage form by the later passes.
 *
 * The contract of a pass tag has two parts.  The step part is structural
 * and per run: it keeps the shape facts S6 needs, draws fresh names from
 * the supply, and (SimplifyCFG) maps only its own merged labels; these
 * make the walk's label-map applications the identity on code.  The stage
 * part is semantic: a forward simulation of terminating runs between
 * consecutive stage contexts from one initial state, under
 * unit_result_rel, with the shared memory invariant (unitMemInv)
 * transported.  GAS reads a compile-time oracle list, so a pass that
 * reorders or drops GAS reads (DFT) relates every output run to some
 * input run that differs only in that list: o1_stage_contract_gas, the
 * forall-out exists-in form; gas_variant is the hook that SEQ-243's oracle
 * instantiates, equality until then.
 *
 * Every contract theorem here is a planned admission for its pass task.
 *)
Theory o1PassContract
Ancestors
  unitTransformDefs unitShapeDefs unitMemInv venomPipelineDriver
  venomPassSchedule venomFnScheduleRunner venomPassDispatcher venomWf
  venomExecSemantics venomInst irSupply contextCodegenRel stackPlanGen
  venomState list

(* ===== Simulation between two initial states ===== *)

Definition ctx_sim_def:
  ctx_sim ctx ctx' s s' <=>
    !fuel. terminates (run_context fuel ctx s) ==>
      ?fuel'. unit_result_rel (run_context fuel ctx s)
                              (run_context fuel' ctx' s')
End

Theorem ctx_transform_correct_ctx_sim:
  ctx_transform_correct ctx ctx' s <=> ctx_sim ctx ctx' s s
Proof
  simp[ctx_transform_correct_def, ctx_sim_def]
QED

(* The gas-oracle hook: two initial states that may differ only in the
   oracle list of GAS readings.  Equality until the oracle lands. *)
Definition gas_variant_def:
  gas_variant (s : venom_state) s' <=> s' = s
End

(* ===== One pass run ===== *)

(* What run_configured_fn_pass_fold does for one pass on one function:
   the pass sees the observed unit with the function current, and the
   result passes the runner's checks. *)
Definition fn_pass_step_def:
  fn_pass_step rpolicy pass observed s fn out <=>
    lookup_unique_function fn.fn_name observed.cu_context.ctx_functions =
      SOME fn /\
    execute_configured_fn_pass rpolicy pass observed s fn = SOME out /\
    out.fpo_function.fn_name = fn.fn_name /\
    fn_pass_effects_hold (fn_pass_tag pass) fn out /\
    introduces_no_invoke_edges fn out.fpo_function /\
    ir_supply_extends s out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply observed
End

(* A function taken through a list of passes by such steps. *)
Definition fn_steps_def:
  (fn_steps rpolicy [] fn fn' <=> fn' = fn) /\
  (fn_steps rpolicy (pass::passes) fn fn' <=>
    ?observed s out.
      fn_pass_step rpolicy pass observed s fn out /\
      fn_steps rpolicy passes out.fpo_function fn')
End

(* ===== Stage contexts ===== *)

(* The observed unit's callees of fn are finished: each is reached from
   its form in the output context C' by the passes still to come. *)
Definition walk_view_def:
  walk_view rpolicy later C' fn observed <=>
    !name g'.
      MEM name (fn_invoke_targets fn) /\
      lookup_function name C'.ctx_functions = SOME g' ==>
      ?g. lookup_function name observed.cu_context.ctx_functions = SOME g /\
          fn_steps rpolicy later g' g
End

(* C' is C with every function taken through pass by one step, each on an
   observed unit with C's entry, reservations and function names, related
   to C' by view. *)
Definition ctx_pass_stage_def:
  ctx_pass_stage rpolicy pass view C C' <=>
    C'.ctx_entry = C.ctx_entry /\
    C'.ctx_global_reserved = C.ctx_global_reserved /\
    LIST_REL
      (\fn fn'. ?observed s out.
         fn_pass_step rpolicy pass observed s fn out /\
         out.fpo_function = fn' /\
         observed.cu_context.ctx_entry = C.ctx_entry /\
         observed.cu_context.ctx_global_reserved = C.ctx_global_reserved /\
         ctx_fn_names observed.cu_context = ctx_fn_names C /\
         view C' fn observed)
      C.ctx_functions C'.ctx_functions
End

(* ===== Shape facts carried through every stage ===== *)

(* Every INVOKE names a function of the context in its first operand. *)
Definition fn_invoke_ok_def:
  fn_invoke_ok names fn <=>
    !inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE ==>
      ?lbl rest. inst.inst_operands = Label lbl :: rest /\ MEM lbl names
End

(* Every other label operand names a block of its own function or a
   reserved label: INVOKE targets are the only cross-function references,
   so one function's label map never touches another function's code. *)
Definition fn_label_refs_ok_def:
  fn_label_refs_ok fn <=>
    !inst l. MEM inst (fn_insts fn) /\ MEM (Label l) inst.inst_operands /\
             inst.inst_opcode <> INVOKE ==>
      MEM l (fn_labels fn) \/ reserved_label l
End

Definition unit_label_refs_ok_def:
  unit_label_refs_ok unit <=>
    EVERY fn_label_refs_ok unit.cu_context.ctx_functions
End

(* The per-function shape facts of o1_source_unit_ok that every pass keeps
   (the raw-opcode restriction is a source-only fact and is not kept),
   with the well-formedness every pass keeps. *)
Definition o1_fn_shape_def:
  o1_fn_shape ctx fn <=>
    wf_function fn /\ fn_inst_wf fn /\
    fn_shape_ok fn /\ first_block_no_preds fn /\
    fn_invoke_ok (ctx_fn_names ctx) fn /\ fn_label_refs_ok fn /\
    (ctx.ctx_entry = SOME fn.fn_name ==>
       entry_fn_no_ret fn /\
       get_params (HD fn.fn_blocks).bb_instructions = []) /\
    (ctx.ctx_entry <> SOME fn.fn_name ==>
       EVERY (\inst. ~MEM inst.inst_opcode [STOP; RETURN]) (fn_insts fn))
End

(* venom_wf without global instruction-id distinctness, which is the IR
   supply's concern and not a pass's. *)
Definition o1_ctx_shape_def:
  o1_ctx_shape ctx <=>
    ctx_wf ctx /\ EVERY (o1_fn_shape ctx) ctx.ctx_functions
End

Theorem o1_ctx_shape_wf_invoke_targets:
  o1_ctx_shape ctx ==> wf_invoke_targets ctx
Proof
  rw[o1_ctx_shape_def, wf_invoke_targets_def, EVERY_MEM] >>
  res_tac >> fs[o1_fn_shape_def, fn_invoke_ok_def] >> metis_tac[]
QED

(* ===== Step contract: structural, per run ===== *)

(* New block labels and instruction ids come from the supply, so they are
   unused anywhere in the observed unit. *)
Definition fresh_names_ok_def:
  fresh_names_ok s fn fn' <=>
    (!l. MEM l (fn_labels fn') ==>
         MEM l (fn_labels fn) \/ ~MEM l s.irs_used_labels) /\
    (!id. MEM id (fn_ir_inst_ids fn') ==>
          MEM id (fn_ir_inst_ids fn) \/ ~MEM id s.irs_used_inst_ids)
End

(* A label map renames only block labels of the input that the output no
   longer has, never the entry label (the function's name). *)
Definition label_map_sources_ok_def:
  label_map_sources_ok fn fn' label_map <=>
    EVERY (\e. MEM (FST e) (fn_labels fn) /\ FST e <> fn.fn_name /\
               ~MEM (FST e) (fn_labels fn')) label_map
End

Definition o1_step_contract_def:
  o1_step_contract rpolicy pass <=>
    !observed s fn out.
      fn_pass_step rpolicy pass observed s fn out /\
      o1_ctx_shape observed.cu_context ==>
      o1_fn_shape observed.cu_context out.fpo_function /\
      fresh_names_ok s fn out.fpo_function /\
      label_map_sources_ok fn out.fpo_function out.fpo_label_map
End

(* ===== Stage contract: semantic, between stage contexts ===== *)

(* The memory facts of unitMemInv depend on a state only through the
   instruction's access ranges and the alloca frame. *)
Definition rangewise_mem_fact_def:
  rangewise_mem_fact M <=>
    ?P. !ctx fn inst s.
      M ctx fn inst s <=>
      P (inst_mem_ranges inst s) s.vs_alloca_next s.vs_allocas
        s.vs_initial_fmp
End

(* The lowered-phase fact with the frame pointer read off the state: the
   semantics never writes vs_initial_fmp, so this is lowered_mem_ok at the
   initial state's fmp along every run. *)
Definition lowered_mem_fact_def:
  lowered_mem_fact eom ctx fn inst s <=>
    lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s
End

Definition o1_stage_contract_def:
  o1_stage_contract rpolicy pass view pre M M' <=>
    !C C' vs.
      ctx_pass_stage rpolicy pass view C C' /\ pre C C' /\
      o1_ctx_shape C /\ o1_initial_state_ok vs /\ mem_inv M C vs ==>
      ctx_sim C C' vs vs /\ mem_inv M' C' vs
End

(* For every output run from vs' there is an input run from a gas variant
   vs of it. *)
Definition o1_stage_contract_gas_def:
  o1_stage_contract_gas rpolicy pass view pre M M' <=>
    !C C' vs'.
      ctx_pass_stage rpolicy pass view C C' /\ pre C C' /\
      o1_ctx_shape C /\ o1_initial_state_ok vs' /\ mem_inv M C vs' ==>
      ?vs. gas_variant vs vs' /\ ctx_sim C C' vs vs' /\ mem_inv M' C' vs'
End

Definition any_view_def:
  any_view (C' : venom_context) (fn : ir_function)
           (observed : compilation_unit) <=> T
End

Definition no_pre_def:
  no_pre (C : venom_context) (C' : venom_context) <=> T
End

(* Every function's static layout end is at most eom. *)
Definition ctx_eom_bounded_def:
  ctx_eom_bounded eom (C : venom_context) C' <=>
    !fn e. MEM fn C'.ctx_functions /\ fn.fn_eom = SOME e ==> e <= eom
End

(* ===== The schedule ===== *)

Definition o1_pre_walk_passes_def:
  o1_pre_walk_passes =
    [CFP_Simple VP_SimplifyCFG; CFP_Simple VP_DretDesugar]
End

Theorem o1_pipeline_spec_pre_walk:
  o1_pipeline_spec.ps_pre_walk_stages =
    MAP PS_MapFunctions o1_pre_walk_passes ++ [PS_DiscardAnalyses]
Proof
  simp[o1_pipeline_spec_def, o1_pre_walk_passes_def]
QED

(* The view of the k-th walk pass: callees are observed after the passes
   that follow it. *)
Definition o1_walk_view_def:
  o1_walk_view rpolicy k = walk_view rpolicy (DROP (SUC k) o1_fn_passes)
End

(* ===== The contract theorems: one planned admission per pass tag ===== *)

(* Memory-neutral passes keep any range-wise memory fact.  The pre-walk
   runs of SimplifyCFG and DretDesugar and the walk runs of every tag but
   ConcretizeMemLoc and FmpLowering are instances. *)

Theorem o1_contract_simplify_cfg:
  o1_step_contract rpolicy (CFP_Simple VP_SimplifyCFG) /\
  (!view M. rangewise_mem_fact M ==>
     o1_stage_contract rpolicy (CFP_Simple VP_SimplifyCFG) view no_pre M M)
Proof
  cheat
QED

Theorem o1_contract_dret_desugar:
  o1_step_contract rpolicy (CFP_Simple VP_DretDesugar) /\
  (!view M. rangewise_mem_fact M ==>
     o1_stage_contract rpolicy (CFP_Simple VP_DretDesugar) view no_pre M M)
Proof
  cheat
QED

Theorem o1_contract_make_ssa:
  o1_step_contract rpolicy (CFP_Simple VP_MakeSSA) /\
  (!view M. rangewise_mem_fact M ==>
     o1_stage_contract rpolicy (CFP_Simple VP_MakeSSA) view no_pre M M)
Proof
  cheat
QED

Theorem o1_contract_lower_dload:
  o1_step_contract rpolicy (CFP_Simple VP_LowerDload) /\
  (!view M. rangewise_mem_fact M ==>
     o1_stage_contract rpolicy (CFP_Simple VP_LowerDload) view no_pre M M)
Proof
  cheat
QED

(* ConcretizeMemLoc reads callee layouts: its view is the walk's.  It takes
   the site-wise raw invariant to the static one below any eom bounding
   every function's layout end. *)
Theorem o1_contract_concretize_mem_loc:
  o1_step_contract rpolicy (CFP_Simple VP_ConcretizeMemLoc) /\
  (!eom.
     o1_stage_contract rpolicy (CFP_Simple VP_ConcretizeMemLoc)
       (o1_walk_view rpolicy 2) (ctx_eom_bounded eom)
       site_mem_ok (static_mem_ok eom))
Proof
  cheat
QED

(* FmpLowering reads callee signatures: its view is the walk's.  Dynamic
   memory starts at the run's initial free-memory pointer. *)
Theorem o1_contract_fmp_lowering:
  o1_step_contract rpolicy (CFP_Simple VP_FmpLowering) /\
  (!eom.
     o1_stage_contract rpolicy (CFP_Simple VP_FmpLowering)
       (o1_walk_view rpolicy 3) no_pre
       (static_mem_ok eom)
       (lowered_mem_fact eom))
Proof
  cheat
QED

Theorem o1_contract_sue:
  o1_step_contract rpolicy (CFP_Simple VP_SingleUseExpansion) /\
  (!view M. rangewise_mem_fact M ==>
     o1_stage_contract rpolicy (CFP_Simple VP_SingleUseExpansion)
       view no_pre M M)
Proof
  cheat
QED

(* DFT reorders GAS reads: forall-out exists-in over the oracle. *)
Theorem o1_contract_dft:
  o1_step_contract rpolicy (CFP_Simple VP_DFT) /\
  (!view M. rangewise_mem_fact M ==>
     o1_stage_contract_gas rpolicy (CFP_Simple VP_DFT) view no_pre M M)
Proof
  cheat
QED

Theorem o1_contract_cfg_normalization:
  o1_step_contract rpolicy (CFP_Simple VP_CFGNormalization) /\
  (!view M. rangewise_mem_fact M ==>
     o1_stage_contract rpolicy (CFP_Simple VP_CFGNormalization)
       view no_pre M M)
Proof
  cheat
QED
