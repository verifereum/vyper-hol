(* Label flow for symbolic semantics with an explicit own-code parameter.
   TOP-LEVEL: label_flow_own_ok; label_flow_ok_imp_label_flow_own_ok;
   fn_shape_codecopy_own_source; label_flow_own_ok_from_code_end_use.
   The existing symbolic semantics and label_flow_ok stay unchanged. *)

Theory codegenSymOwnRel
Ancestors
  codegenSymRel
  unitShapeDefs venomWf stackPlanTypes venomInst list

(* CODESIZE and ordinary value-offset CODECOPY observe the supplied code.
   Code-end pointers retain their existing restricted uses; a return-PC
   variable is never an ordinary value source. *)
Definition label_flow_own_ok_def:
  label_flow_own_ok ctx <=>
    !fn inst.
      MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
      (!x. MEM (Var x) inst.inst_operands /\ code_end_var fn x ==>
           (inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var x]) \/
           (inst.inst_opcode = CODECOPY /\
            ?dst sz. inst.inst_operands = [dst; Var x; sz] /\
                     dst <> Var x /\ sz <> Var x)) /\
      (inst.inst_opcode = CODECOPY ==>
       ?dst src sz.
         inst.inst_operands = [dst; src; sz] /\
         (src = Label "runtime_begin" \/
          (?x. src = Var x /\ code_end_var fn x) \/
          (~is_label_operand src /\
           !x. src = Var x ==> ~code_end_var fn x /\ ~retpc_var fn x)))
End

Theorem label_flow_ok_imp_label_flow_own_ok:
  label_flow_ok ctx ==> label_flow_own_ok ctx
Proof
  simp[label_flow_ok_def, label_flow_own_ok_def] >> metis_tac[]
QED

(* Function shape already classifies every CODECOPY source.  Phase lifts
   therefore only need to preserve the code-end-pointer use restriction. *)
Theorem fn_shape_codecopy_own_source:
  fn_inst_wf fn /\ fn_shape_ok fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = CODECOPY ==>
  ?dst src sz.
    inst.inst_operands = [dst; src; sz] /\
    (src = Label "runtime_begin" \/
     (?x. src = Var x /\ code_end_var fn x) \/
     (~is_label_operand src /\
      !x. src = Var x ==> ~code_end_var fn x /\ ~retpc_var fn x))
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `label_positions_ok inst /\ opaque_use_ok fn` by
    (fs[fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  `LENGTH inst.inst_operands = 3` by gvs[inst_wf_def] >>
  gvs[LENGTH_EQ_NUM_compute] >>
  rename1 `~is_label_operand src` >>
  `!x. src = Var x ==> ~retpc_var fn x` by
    (rpt strip_tac >>
     qpat_x_assum `opaque_use_ok fn`
       (mp_tac o REWRITE_RULE [opaque_use_ok_def]) >>
     disch_then (qspecl_then [`inst`, `x`] mp_tac) >>
     simp[retpc_use_ok_def]) >>
  Cases_on `src` >> gvs[is_label_operand_def, label_positions_ok_def] >>
  metis_tac[]
QED

Theorem label_flow_own_ok_from_code_end_use:
  (!fn. MEM fn ctx.ctx_functions ==> fn_inst_wf fn /\ fn_shape_ok fn) /\
  (!fn inst x.
     MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
     MEM (Var x) inst.inst_operands /\ code_end_var fn x ==>
     (inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var x]) \/
     (inst.inst_opcode = CODECOPY /\
      ?dst sz. inst.inst_operands = [dst; Var x; sz] /\
               dst <> Var x /\ sz <> Var x)) ==>
  label_flow_own_ok ctx
Proof
  rw[label_flow_own_ok_def] >> metis_tac[fn_shape_codecopy_own_source]
QED

(*
# O1 own-code label-flow target statements

These are proposed statements, not proved or admitted results. The only new HOL definition in this change is `label_flow_own_ok`. The abbreviations below are textual notation for fully expanded propositions, not additional HOL constants.

Let `R ctx k f` abbreviate:

label_flow_own_ok (ctx with ctx_functions := [f]) /\
(k <= 1 ==> !i. MEM i (fn_insts f) ==>
  ~MEM (Label "code_end") i.inst_operands) /\
(2 <= k /\ k <= 4 ==> middle_code_end_lifetime f) /\
(k <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f

The last two conjuncts keep the static FMP facts local to label-flow rows, as in the pending static-guard port. They do not restrict the shared O1 rows or change the top pipeline premises.

Name each universally quantified proposition below `O_pre`, `O_first`, `O_dload`, `O_concretize`, `O_fmp`, `O_second`, or `O_late` respectively. Each is a hypothesis of the composition theorem, independently discharged by its phase worker.

`o1_pre_walk_seed_free_own_flow` (`O_pre`):

!rpolicy unit s unit' s'.
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s /\
  o1_source_unit_ok unit /\ unit_defs_reach_uses unit /\
  unit_fmp_unsealed unit /\ label_flow_own_ok unit.cu_context /\
  (!f i. MEM f unit.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  label_flow_own_ok unit'.cu_context /\
  (!f i. MEM f unit'.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands)

`compose_first_ssa_own` (`O_first`):

!rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 0 f /\ R ctx 0 f ==>
  R ctx 1 out.fpo_function

`compose_lower_dload_own` (`O_dload`):

!rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_LowerDload) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 1 f /\ R ctx 1 f ==> R ctx 2 out.fpo_function

`compose_concretize_own` (`O_concretize`):

!rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_ConcretizeMemLoc) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 2 f /\ R ctx 2 f ==> R ctx 3 out.fpo_function

`compose_fmp_own` (`O_fmp`):

!rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_FmpLowering) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 3 f /\ R ctx 3 f ==> R ctx 4 out.fpo_function

`compose_second_ssa_own` (`O_second`):

!rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 4 f /\ R ctx 4 f ==> R ctx 5 out.fpo_function

`compose_late_own` (`O_late`, four obligations when specialized):

!k pass rp observed s f out ctx.
  ((k = 5 /\ pass = CFP_Simple VP_SimplifyCFG) \/
   (k = 6 /\ pass = CFP_Simple VP_SingleUseExpansion) \/
   (k = 7 /\ pass = CFP_Simple VP_DFT) \/
   (k = 8 /\ pass = CFP_Simple VP_CFGNormalization)) /\
  fn_pass_step rp pass observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row k f /\ R ctx k f ==>
  R ctx (SUC k) out.fpo_function

`o1_label_flow_own_walk` is the conditional runner composition (the `O_*` names expand to the propositions above):

O_first /\ O_dload /\ O_concretize /\ O_fmp /\ O_second /\ O_late ==>
!rp names u s u' s'.
  run_named_fn_schedules execute_configured_fn_pass rp o1_fn_passes names u s =
    SOME (u',s') /\ o1_ctx_shape u.cu_context /\
  ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names u.cu_context)) /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) u.cu_context.ctx_functions /\
  EVERY no_raw_fmp_ops u.cu_context.ctx_functions /\
  EVERY fmp_sig_no_param u.cu_context.ctx_functions /\
  label_flow_own_ok u.cu_context /\
  (!f i. MEM f u.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  label_flow_own_ok u'.cu_context

`o1_pipeline_label_flow_own_preserved`:

O_pre /\ O_first /\ O_dload /\ O_concretize /\ O_fmp /\
O_second /\ O_late ==>
!rpolicy unit out.
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  label_flow_own_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "code_end") inst.inst_operands) ==>
  label_flow_own_ok out.po_unit.cu_context

The pipeline composition reuses `o1_pre_walk_rows` to produce the static guards and ordinary row 0 facts, and the existing driver, pruning, namespace, supply and schedule decompositions. The own-flow walk replaces the old instruction-level no-CODESIZE/runtime-only input condition with `label_flow_own_ok` and the unchanged no-code_end-seed condition. In a seed-free function, its CODECOPY source is runtime_begin or a non-label operand whose variable is not a return-PC variable; there is no CODESIZE ban.

Phase implementation map:

`fn_shape_codecopy_own_source` and `label_flow_own_ok_from_code_end_use`
remove the need to lift CODECOPY-source preservation or CODESIZE-absence
through any pass. Only the code-end-pointer use clause needs transport.

- Pre-walk, first SSA (0 to 1), LowerDload (1 to 2), ConcretizeMemLoc
  (2 to 3), and FmpLowering (3 to 4): no new per-pass theories. Compose
  existing shape/row contracts (`o1_fn_passes_steps`) with the seed-free
  or lifetime facts: `simplify_cfg_fn_no_reserved_operand`
  (`o1LabelFlowSourceCfgLabels`), `make_ssa_current_fn_label_absent`,
  `code_end_var_absent` (`o1LabelFlowSourceBoundary`),
  `lower_dload_function_code_end_lifetime` (`o1LabelFlowLowerDload`),
  `concretize_function_code_end_lifetime` (`o1LabelFlowMiddleConcretize`),
  and `fmp_row_code_end_lifetime` (`o1LabelFlowMiddleFmp`). Static row
  guards remain in `o1LabelFlowStaticContracts`.
- Second SSA (4 to 5): a wrapper over `local_adjacent_insertion_lifetime`
  (`o1LabelFlowMiddleInsertion`), `visit_blocks_protected_read`,
  `code_end_var_owned_bound`, `visit_blocks_owned_inst`
  (`o1LabelFlowMiddleTraversal`), `cleanup_code_end_backward_no_phi`,
  and `cleanup_if_origin` (`o1LabelFlowMiddleCleanupFlow`). This replaces
  the label-flow portion of `o1LabelFlowMiddleSsaAssembly`; the existing
  `visit_blocks_codecopy_sources` theorem needs no own-code lift.
- Late (5 to 9): preserve only code-end-pointer uses. SimplifyCFG uses
  `o1LabelFlowSimplifyPreservation`, `o1LabelFlowSimplifyChain`, and
  `o1LabelFlowRetention`; SingleUseExpansion uses negative-flow support
  in `o1LabelFlowSueNegative` (no lift of `o1LabelFlowSuePositive`). DFT
  uses `dft_code_end_var_reflect` (`o1LabelFlowLateDft`); CFGNormalization
  uses `cfg_split_code_end_var_iff` (`o1LabelFlowCfgSplitTaint`) and
  `cfg_split_replacement_not_code_end` (`o1LabelFlowCfgSplitPreservation`).
  Package these in the own-code counterpart of `o1LabelFlowLateContracts`.
- Conditional composition: own-code counterpart of `o1LabelFlowCompose`.
- Source units (`runtimeSymSrcUnit`, `deploySymSrcUnit`): derive own-flow
  directly from `label_flow_own_ok_from_code_end_use`, source shape, and
  `code_end_var_absent`.

*)
