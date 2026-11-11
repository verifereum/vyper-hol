(* Static return routing is indexed by the original selected call, not by
   membership of the generated function in the original context. *)
Theory functionInlinerReturnRouting
Ancestors
  functionInlinerParameterLifecycle functionInlinerSelectedParameterDescriptors
  functionInlinerReturnTransport functionInlinerCuts functionInlinerEnvelopes
  functionInlinerReachableCuts functionInlinerOrigin functionInlinerOccurrences
  functionInlinerRoutedProvenance functionInlinerPairedSelection
  functionInlinerActivation venomExecSemantics venomInst list pred_set

Theorem inline_selected_return_namespace:
  !C n root cert p fn l j call u q e zipper prename sigma child.
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert p (prename:string -> string) fn /\
  inline_namespace_leaf_at cert q sigma child ==>
  EVERY (\x. MEM x (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn x)
    call.inst_outputs /\
  INJ prename UNIV UNIV /\ INJ sigma UNIV UNIV /\
  (!x v. MEM x call.inst_outputs /\ MEM v (cfgTransform$fn_all_vars child) ==>
    prename x <> sigma v)
Proof
  rpt gen_tac >> strip_tac >>
  drule inline_call_incidence_source >>
  disch_then (strip_assume_tac o CONJUNCT2) >>
  drule inline_call_incidence_selected_order >> simp[] >> strip_tac >>
  `p <> q` by metis_tac[inline_leaf_before_irreflexive] >>
  `MEM fn C.ctx_functions` by
    metis_tac[inline_annotated_origin_routed_leaf,
      inline_routed_leaf_source_member] >>
  `inliner_input_ok C` by
    metis_tac[inline_annotated_origin_erasure, qualified_origin_erasure,
      inliner_fn_origin_input_ok] >>
  `MEM call (fn_insts fn)` by
    (gvs[get_instruction_def, AllCaseEqs(), fn_insts_def,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM, MEM_EL]) >>
  `EVERY (\x. MEM x (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn x)
     call.inst_outputs` by metis_tac[inline_call_output_namespace] >>
  `INJ prename UNIV UNIV /\ INJ sigma UNIV UNIV` by
    metis_tac[inline_namespace_leaf_at_def, inline_namespace_node_injective] >>
  drule_all inline_namespace_leaves_separate >>
  gvs[DISJOINT_DEF, EXTENSION, IN_INTER, IN_IMAGE, NOT_IN_EMPTY,
       EVERY_MEM] >> metis_tac[]
QED

Theorem inline_selected_return_call_target:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child ==>
  ?args. call.inst_operands = Label child.fn_name::args
Proof
  strip_tac >>
  drule inline_selected_paired_separation >> simp[] >> disch_then drule >>
  strip_tac >>
  `child = inline_entry_function b` by metis_tac[inline_selected_child_identity] >>
  `ALL_DISTINCT (fn_labels e.ise_caller)` by
    metis_tac[inline_annotated_origin_labels] >>
  `find_invoke_site e.ise_callee.fn_name e.ise_caller.fn_blocks =
    SOME (e.ise_block,e.ise_index)` by gvs[inline_site_edit_valid_def] >>
  drule_all functionInlinerNamespaceTheory.find_invoke_site_lookup_signature >>
  strip_tac >>
  `inline_fetched_fields e.ise_caller e.ise_block e.ise_index
    (inline_inst_fields current)` by
    (drule inline_call_incidence_residual_fetch >> simp[] >>
     disch_then drule >> simp[]) >>
  `current.inst_operands = Label e.ise_callee.fn_name::args` by
    gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
      functionInlinerSiteLayoutTheory.inline_inst_fields_def, get_instruction_def] >>
  `?target ops actual. call.inst_operands = Label target::ops /\
    current.inst_operands = Label target::actual` by
    metis_tac[inline_call_incidence_residual_target] >>
  drule inline_annotated_entry_identity >> strip_tac >> gvs[] >>
  metis_tac[inline_annotated_entry_identity]
QED

Theorem inline_selected_return_arity:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  lookup_block rl child.fn_blocks = SOME rb /\ get_instruction rb ri = SOME ret /\
  (ret.inst_opcode = RET \/ ret.inst_opcode = RETFMP) ==>
  raw_return_user_arity ret = SOME (LENGTH call.inst_outputs)
Proof
  strip_tac >>
  drule_all inline_selected_return_call_target >> strip_tac >>
  drule inline_call_incidence_source >>
  disch_then (strip_assume_tac o CONJUNCT2) >>
  `?path. inline_routed_leaf cert root p fn path` by
    metis_tac[inline_call_incidence_source, inline_annotated_origin_routed_leaf] >>
  `?path. inline_routed_leaf cert root q child path` by
    metis_tac[inline_annotated_origin_routed_leaf] >>
  `MEM fn C.ctx_functions /\ MEM child C.ctx_functions` by
    metis_tac[inline_routed_leaf_source_member] >>
  `inliner_input_ok C` by
    metis_tac[inline_annotated_origin_erasure, qualified_origin_erasure,
      inliner_fn_origin_input_ok] >>
  `MEM call (fn_insts fn) /\ MEM ret (fn_insts child)` by
    (gvs[get_instruction_def, AllCaseEqs(), fn_insts_def,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM, MEM_EL]) >>
  `qualified_origin C 0 fn /\ qualified_origin C 0 child` by
    metis_tac[qualified_origin_rules] >>
  metis_tac[qualified_origin_call_return_arity]
QED
