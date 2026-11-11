(* Static return routing is indexed by the original selected call, not by
   membership of the generated function in the original context. *)
Theory functionInlinerReturnRouting
Ancestors
  functionInlinerReturnPrefix functionInlinerReturnAdapterLayout
  functionInlinerSelectedParameterReads
  functionInlinerParameterPropagation functionInlinerOperationalCuts
  functionInlinerOpacity functionInlinerContract cfgTransform unitShapeDefs
  functionInlinerParameterLifecycle functionInlinerSelectedParameterDescriptors
  functionInlinerReturnTransport functionInlinerCuts functionInlinerEnvelopes
  functionInlinerReachableCuts functionInlinerOrigin functionInlinerOccurrences
  functionInlinerRoutedProvenance functionInlinerPairedSelection
  functionInlinerActivation functionInlinerDefs functionInlinerSiteLayout
  functionInlinerLocation venomExecSemantics venomInst list rich_list indexedLists pred_set

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

(* The unique Enter expands a return into one common contiguous interval. *)
Theorem inline_return_enter_interval:
  inline_annotated_origin C e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin C e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\
  lookup_block rl e.ise_callee.fn_blocks = SOME rb /\
  get_instruction rb ri = SOME ret /\
  (ret.inst_opcode = RET \/ ret.inst_opcode = RETFMP) ==>
  ?bb assigns.
    lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
    assigns = MAP inline_inst_fields (TAKE
      (LENGTH (FST (inline_cell_focus e bb rb ri)) - 1)
      (FST (inline_cell_focus e bb rb ri))) /\
    inline_adapter_interval e.ise_final (STRCAT e.ise_prefix rl)
      (LENGTH (FST (inline_cell_prefix e bb rb ri))) assigns e.ise_return /\
    MEM e.ise_return (fn_labels e.ise_final)
Proof
  strip_tac >> (drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  `MEM rl (fn_labels e.ise_callee)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
               venomExecPropsTheory.lookup_block_label]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexists `bb` >> simp[] >>
  qmatch_goalsub_abbrev_tac `LENGTH (FST focus) - 1` >>
  conj_tac
  >- (simp[inline_adapter_interval_points] >>
      `ri < LENGTH rb.bb_instructions /\ EL ri rb.bb_instructions = ret` by
        gvs[get_instruction_def] >>
      `?assigns jump. FST focus = assigns ++ [jump] /\
        EVERY (\i. i.inst_opcode = ASSIGN) assigns /\
        inline_inst_fields jump = (JMP,[Label e.ise_return],[])` by
        (simp[Abbr `focus`, inline_cell_focus_def, clone_instruction_def,
              rewrite_inline_inst_def, is_param_opcode_def] >>
         simp[EVERY_EL, EL_MAPi, inline_inst_fields_def]) >>
      simp[TAKE_APPEND, EVERY_MAP, inline_inst_fields_def] >>
      `!k. k < LENGTH assigns + 1 ==>
        inline_fetched_fields e.ise_final (STRCAT e.ise_prefix rl)
          (LENGTH (FST (inline_cell_prefix e bb rb ri))+k)
          (EL k (MAP inline_inst_fields assigns ++ [(JMP,[Label e.ise_return],[])]))` by
        (rpt strip_tac >> drule_all inline_edit_enter_focus_fetch >>
         pure_rewrite_tac[LET_THM] >> BETA_TAC >>
         pure_rewrite_tac[GSYM inline_cell_prefix_def, GSYM inline_cell_focus_def] >>
         disch_then (qspec_then `k` mp_tac) >>
         `inline_cell_focus e bb rb ri = focus` by simp[Abbr `focus`] >>
         simp[] >>
         `MEM (EL k (assigns ++ [jump])) (assigns ++ [jump])` by
           (pure_rewrite_tac[MEM_EL] >> qexists `k` >> simp[]) >>
         `~((EL k (assigns ++ [jump])).inst_opcode = PHI)` by
           (gvs[MEM_APPEND, EVERY_MEM, inline_inst_fields_def] >> metis_tac[]) >>
         `MAP inline_inst_fields assigns ++ [(JMP,[Label e.ise_return],[])] =
          MAP inline_inst_fields (assigns ++ [jump])` by simp[] >>
         qpat_x_assum `MAP _ _ ++ _ = MAP _ _` SUBST1_TAC >>
         simp[inline_edit_repair_def, EL_MAP, Excl "MAP_APPEND"]) >>
      `inline_fetched_fields e.ise_final (STRCAT e.ise_prefix rl)
         (LENGTH (FST (inline_cell_prefix e bb rb ri)) + LENGTH assigns)
         (JMP,[Label e.ise_return],[])` by
        (first_x_assum (qspec_then `LENGTH assigns` mp_tac) >>
         simp[EL_APPEND_EQN]) >>
      gvs[inline_fetched_fields_def, get_instruction_def] >>
      qexists `bb'` >> simp[]) >>
  simp[inline_valid_edit_label_set])
QED

Theorem inline_routed_leaf_annotated_path:
  !cert root p fn path. inline_routed_leaf cert root p fn path ==>
  !C n. inline_annotated_origin C n root cert ==>
    inline_annotated_choice_path C path fn root
Proof
  ho_match_mp_tac inline_routed_leaf_strongind >> rpt conj_tac
  >- simp[inline_annotated_choice_path_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule inline_annotated_origin_edit_elim >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  irule inline_annotated_choice_path_append >>
  goal_assum (drule_at Any) >>
  simp[inline_annotated_choice_path_def] >> metis_tac[]
QED

Theorem inline_selected_return_interval:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  lookup_block rl child.fn_blocks = SOME rb /\ get_instruction rb ri = SOME ret /\
  MEM ret.inst_opcode [RET; RETFMP] ==>
  ?prefix frames d cb ret' bb assigns ml mj.
    EVERY (\choice. ?edit. choice = InlineKeep edit) prefix /\
    inline_cell_zipper (inline_make_cell child rl ri (inline_inst_fields ret)) frames d /\
    MAP (\(tag,next). inline_cell_choice tag) frames = prefix /\
    d.ic_function = e.ise_callee /\
    lookup_block d.ic_block e.ise_callee.fn_blocks = SOME cb /\
    get_instruction cb d.ic_index = SOME ret' /\
    inline_inst_fields ret' = inline_inst_fields ret /\
    lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
    assigns = MAP inline_inst_fields (TAKE
      (LENGTH (FST (inline_cell_focus e bb cb d.ic_index))-1)
      (FST (inline_cell_focus e bb cb d.ic_index))) /\
    inline_adapter_interval root ml mj (inline_adapter_path_fields zipper assigns)
      (inline_path_rename zipper e.ise_return) /\
    inline_parameter_boundary_path zipper e.ise_final e.ise_return 0 root
      (inline_path_rename zipper e.ise_return) 0 /\
    (?target. lookup_block (inline_path_rename zipper e.ise_return) root.fn_blocks = SOME target)
Proof
  strip_tac >> (
  qpat_assum `MEM ret.inst_opcode _` (assume_tac o REWRITE_RULE [MEM]) >>
  drule inline_selected_paired_separation >> simp[] >> disch_then drule >> strip_tac >>
  `child = inline_entry_function b` by metis_tac[inline_selected_child_identity] >>
  `?prefix. inline_routed_leaf b e.ise_callee (inline_entry_address b) child prefix /\
     EVERY (\choice. ?edit. choice = InlineKeep edit) prefix` by
    metis_tac[inline_annotated_entry_route] >>
  `inline_annotated_choice_path C prefix child e.ise_callee` by
    metis_tac[inline_routed_leaf_annotated_path] >>
  `?frames d current ret'.
     inline_cell_zipper (inline_make_cell child rl ri (inline_inst_fields ret)) frames d /\
     MAP (\(tag,next). inline_cell_choice tag) frames = prefix /\
     d.ic_function = e.ise_callee /\
     lookup_block d.ic_block e.ise_callee.fn_blocks = SOME current /\
     get_instruction current d.ic_index = SOME ret' /\
     inline_inst_fields ret' = inline_inst_fields ret` by
    metis_tac[inline_return_keep_prefix_fetch] >>
  rename1 `lookup_block d.ic_block e.ise_callee.fn_blocks = SOME cb` >>
  `ret'.inst_opcode = RET \/ ret'.inst_opcode = RETFMP` by
    gvs[inline_inst_fields_def] >>
  `?bb assigns. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
     assigns = MAP inline_inst_fields (TAKE
       (LENGTH (FST (inline_cell_focus e bb cb d.ic_index))-1)
       (FST (inline_cell_focus e bb cb d.ic_index))) /\
     inline_adapter_interval e.ise_final (STRCAT e.ise_prefix d.ic_block)
       (LENGTH (FST (inline_cell_prefix e bb cb d.ic_index))) assigns e.ise_return /\
     MEM e.ise_return (fn_labels e.ise_final)` by
    metis_tac[inline_return_enter_interval] >>
  `inline_annotated_choice_path C zipper e.ise_final root` by
    metis_tac[inline_selected_annotated_choice_path] >>
  drule_all inline_adapter_path_transport >> strip_tac >>
  drule_all inline_adapter_path_entry >> strip_tac >>
  metis_tac[])
QED

Theorem inline_return_user_namespace:
  inliner_input_ok C /\ MEM fn C.ctx_functions /\
  MEM ret (fn_insts fn) /\ MEM ret.inst_opcode [RET; RETFMP] /\
  ret.inst_operands = ops ++ [pc] ==>
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn v) ops
Proof
  strip_tac >> (
  `inline_opacity_ok fn {v | retpc_var fn v}` by
    metis_tac[inliner_input_opacity] >>
  simp[EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> disch_then SUBST_ALL_TAC >> conj_tac
  >- (simp[cfgTransformTheory.fn_all_vars_def, fn_insts_def,
           MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      `?bb. MEM bb fn.fn_blocks /\ MEM ret bb.bb_instructions` by
        metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM] >>
      qexistsl [`bb`,`ret`] >> simp[] >> disj2_tac >>
      qexists `Var v` >> simp[]) >>
  `MEM (Var v) (TAKE (LENGTH ret.inst_operands - 1) ret.inst_operands)` by
    simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  drule inline_opacity_return_front >>
  disch_then (qspecl_then [`v`,`ret`] mp_tac) >> simp[])
QED

Theorem inline_selected_return_user_reads:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  lookup_block rl child.fn_blocks = SOME rb /\ get_instruction rb ri = SOME ret /\
  MEM ret.inst_opcode [RET; RETFMP] /\ ret.inst_operands = ops ++ [pc] /\
  inline_tracked_snapshot child a route snap frame /\
  step_inst fuel C ret snap.ils_state = IntRet ir s' ==>
  eval_operands (MAP (inline_rename_operand route.ir_rename lab) ops)
    frame.ipf_state = SOME ir.iret_values
Proof
  strip_tac >>
  `raw_return_user_arity ret = SOME (LENGTH call.inst_outputs)` by
    metis_tac[inline_selected_return_arity, MEM] >>
  `eval_operands ops snap.ils_state = SOME ir.iret_values` by
    metis_tac[inline_return_source] >>
  `MEM child C.ctx_functions` by
    metis_tac[inline_annotated_origin_routed_leaf, inline_routed_leaf_source_member] >>
  `inliner_input_ok C` by
    metis_tac[inline_annotated_origin_erasure, qualified_origin_erasure,
      inliner_fn_origin_input_ok] >>
  `MEM ret (fn_insts child)` by
    (gvs[get_instruction_def, AllCaseEqs(), fn_insts_def,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM, MEM_EL]) >>
  irule inline_tracked_operands_success >>
  metis_tac[inline_return_user_namespace]
QED

Theorem inline_adapter_path_fields_append:
  !path xs ys. inline_adapter_path_fields path (xs ++ ys) =
    inline_adapter_path_fields path xs ++ inline_adapter_path_fields path ys
Proof
  Induct >> simp[inline_adapter_path_fields_def]
QED

Theorem inline_adapter_path_scalar_fields:
  !path opc ops outs. EVERY (\op. ~is_label_op op) ops ==>
  inline_adapter_path_fields path [(opc,ops,outs)] =
    [(opc, MAP (inline_rename_operand (inline_path_rename path) I) ops,
      MAP (inline_path_rename path) outs)]
Proof
  Induct
  >- (simp[inline_adapter_path_fields_def, inline_path_rename_def] >>
      rpt strip_tac >>
      irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
      Cases_on `EL x ops` >> simp[functionInlinerFrameTheory.inline_rename_operand_def]) >>
  Cases_on `h`
  >- (simp[inline_adapter_path_fields_def, inline_adapter_choice_fields_def,
           inline_path_rename_def, inline_choice_rename_def,
           combinTheory.o_DEF] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  simp[inline_adapter_path_fields_def, inline_adapter_choice_fields_def,
       inline_adapter_clone_fields_def, inline_path_rename_def,
       inline_choice_rename_def] >>
  `EVERY (\op. ~is_label_op op) (MAP (clone_operand i.ise_prefix (fn_labels i.ise_callee)) ops)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     Cases_on `x` >> gvs[clone_operand_def, is_label_op_def, EVERY_MEM] >>
     metis_tac[is_label_op_def]) >>
  first_x_assum (drule_then mp_tac) >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >>
  simp[inline_choice_rename_def] >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  `~is_label_op (EL x ops)` by gvs[EVERY_EL] >>
  Cases_on `EL x ops` >>
  gvs[clone_operand_def, is_label_op_def,
      functionInlinerFrameTheory.inline_rename_operand_def]
QED

Theorem inline_return_focus_assign_fields:
  get_instruction cb ri = SOME ret /\
  MEM ret.inst_opcode [RET; RETFMP] /\
  ret.inst_operands = ops ++ [pc] /\
  EVERY (\op. ~is_label_op op) ops ==>
  MAP inline_inst_fields
    (TAKE (LENGTH (FST (inline_cell_focus e bb cb ri)) - 1)
      (FST (inline_cell_focus e bb cb ri))) =
  MAPi (\k op. (ASSIGN,
    [clone_operand e.ise_prefix (fn_labels e.ise_callee) op],
    [EL k (EL e.ise_index bb.bb_instructions).inst_outputs])) ops
Proof
  strip_tac >>
  `ri < LENGTH cb.bb_instructions /\ EL ri cb.bb_instructions = ret` by
    gvs[get_instruction_def] >>
  `EVERY (\op. ~is_label_op op)
     (MAP (clone_operand e.ise_prefix (fn_labels e.ise_callee)) ops)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >> Cases_on `x` >>
     gvs[clone_operand_def, is_label_op_def, EVERY_MEM] >>
     metis_tac[is_label_op_def]) >>
  `FILTER (\op. ~is_label_op op)
     (MAP (clone_operand e.ise_prefix (fn_labels e.ise_callee)) ops) =
     MAP (clone_operand e.ise_prefix (fn_labels e.ise_callee)) ops` by
    simp[FILTER_EQ_ID] >>
  gvs[inline_cell_focus_def, clone_instruction_def, rewrite_inline_inst_def,
      is_param_opcode_def, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  simp[TAKE_LENGTH_TOO_LONG, FILTER_EQ_ID, MAP_MAPi, inline_inst_fields_def] >>
  irule LIST_EQ >> simp[EL_MAPi, EL_MAP, inline_inst_fields_def]
QED

Theorem inline_selected_return_routes:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert p prename fn /\
  inline_namespace_leaf_at cert q sigma child ==>
  sigma = inline_path_rename zipper o STRCAT e.ise_prefix /\
  ?bb current. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
    get_instruction bb e.ise_index = SOME current /\
    MAP (inline_path_rename zipper) current.inst_outputs = MAP prename call.inst_outputs
Proof
  strip_tac >>
  drule inline_selected_paired_separation >> simp[] >> disch_then drule >> strip_tac >>
  `inline_namespace_leaf_at cert p
     (inline_path_rename (path ++ [InlineKeep e] ++ zipper)) fn` by
    metis_tac[inline_routed_leaf_namespace] >>
  `prename = inline_path_rename (path ++ [InlineKeep e] ++ zipper)` by
    metis_tac[inline_namespace_leaf_at_def, inline_namespace_node_rename_unique] >>
  `inline_namespace_node_at
     (InlineNamespaceEdit e.ise_state e.ise_caller e.ise_callee a b)
     (T::inline_entry_address b) (STRCAT e.ise_prefix)
     (InlineNamespaceLeaf (inline_entry_function b))` by
    (mp_tac (Q.SPEC `b` inline_entry_leaf) >>
     simp[inline_namespace_leaf_at_def, inline_namespace_node_edit] >>
     strip_tac >> qexists `I` >>
     gvs[inline_site_edit_valid_def, FUN_EQ_THM, combinTheory.o_DEF]) >>
  `inline_namespace_node_at cert q
     (inline_path_rename zipper o STRCAT e.ise_prefix)
     (InlineNamespaceLeaf (inline_entry_function b))` by
    (qpat_x_assum `q = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     irule inline_namespace_node_append >>
     goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- metis_tac[inline_namespace_leaf_at_def, inline_namespace_node_rename_unique] >>
  `?rpath. inline_routed_leaf a e.ise_caller oldp fn rpath /\
      current.inst_outputs = MAP (inline_path_rename rpath) call.inst_outputs` by
    metis_tac[inline_call_incidence_residual_routing] >>
  `inline_path_rename rpath = inline_path_rename path` by
    metis_tac[inline_routed_leaf_namespace, inline_namespace_leaf_at_def,
              inline_namespace_node_rename_unique] >>
  `inline_fetched_fields e.ise_caller e.ise_block e.ise_index
     (inline_inst_fields current)` by
    (drule inline_call_incidence_residual_fetch >> simp[] >> disch_then drule >> simp[]) >>
  gvs[inline_fetched_fields_def] >>
  gvs[inline_path_rename_append, inline_path_rename_def, inline_choice_rename_def,
      combinTheory.o_DEF, MAP_MAP_o, inline_inst_fields_def, get_instruction_def]
QED

Theorem inline_adapter_path_fields_scalars:
  !fields path. EVERY (\(opc,ops,outs). EVERY (\op. ~is_label_op op) ops) fields ==>
  inline_adapter_path_fields path fields =
  MAP (\(opc,ops,outs). (opc,
    MAP (inline_rename_operand (inline_path_rename path) I) ops,
    MAP (inline_path_rename path) outs)) fields
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  gvs[] >> pure_once_rewrite_tac[CONS_APPEND] >>
  pure_rewrite_tac[inline_adapter_path_fields_append] >>
  simp[inline_adapter_path_scalar_fields]
QED

Theorem inline_selected_return_layout:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert p prename fn /\
  inline_namespace_leaf_at cert q sigma child /\
  lookup_block rl child.fn_blocks = SOME rb /\ get_instruction rb ri = SOME ret /\
  MEM ret.inst_opcode [RET; RETFMP] /\ ret.inst_operands = ops ++ [pc] ==>
  ?ml mj.
    inline_adapter_interval root ml mj
      (MAPi (\k op. (ASSIGN,[inline_rename_operand sigma I op],
        [EL k (MAP prename call.inst_outputs)])) ops)
      (inline_path_rename zipper e.ise_return) /\
    inline_parameter_boundary_path zipper e.ise_final e.ise_return 0 root
      (inline_path_rename zipper e.ise_return) 0 /\
    (?target. lookup_block (inline_path_rename zipper e.ise_return)
      root.fn_blocks = SOME target)
Proof
  strip_tac >>
  `MEM child C.ctx_functions` by
    metis_tac[inline_annotated_origin_routed_leaf, inline_routed_leaf_source_member] >>
  `inliner_input_ok C` by
    metis_tac[inline_annotated_origin_erasure, qualified_origin_erasure,
      inliner_fn_origin_input_ok] >>
  `MEM ret (fn_insts child)` by
    (gvs[get_instruction_def, AllCaseEqs(), fn_insts_def,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM, MEM_EL]) >>
  `label_positions_ok ret` by
    (qpat_x_assum `inliner_input_ok C` mp_tac >>
     simp[inliner_input_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\op. ~is_label_op op) ops` by
    (gvs[MEM, label_positions_ok_def, EVERY_APPEND, EVERY_MEM] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[is_label_op_def, stackPlanTypesTheory.is_label_operand_def] >>
     metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  `sigma = inline_path_rename zipper o STRCAT e.ise_prefix /\
   ?bb current. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
    get_instruction bb e.ise_index = SOME current /\
    MAP (inline_path_rename zipper) current.inst_outputs = MAP prename call.inst_outputs` by
    metis_tac[inline_selected_return_routes] >>
  drule_all inline_selected_return_interval >> strip_tac >>
  `ret'.inst_operands = ops ++ [pc] /\ MEM ret'.inst_opcode [RET; RETFMP]` by
    gvs[inline_inst_fields_def] >>
  `assigns = MAPi (\k op. (ASSIGN,
    [clone_operand e.ise_prefix (fn_labels e.ise_callee) op],
    [EL k current.inst_outputs])) ops` by
    (drule_all inline_return_focus_assign_fields >>
     gvs[get_instruction_def]) >>
  `LENGTH ops = LENGTH call.inst_outputs` by
    (`raw_return_user_arity ret = SOME (LENGTH call.inst_outputs)` by
       metis_tac[inline_selected_return_arity, MEM] >>
     gvs[callLayoutDefsTheory.raw_return_user_arity_def, inline_inst_fields_def]) >>
  `inline_adapter_path_fields zipper assigns =
    MAPi (\k op. (ASSIGN,[inline_rename_operand sigma I op],
      [EL k (MAP prename call.inst_outputs)])) ops` by
    (qpat_x_assum `assigns = MAP inline_inst_fields _` kall_tac >>
     qpat_x_assum `assigns = MAPi _ ops` SUBST1_TAC >>
     `EVERY (\(opc,os,outs). EVERY (\op. ~is_label_op op) os)
       (MAPi (\k op. (ASSIGN,
         [clone_operand e.ise_prefix (fn_labels e.ise_callee) op],
         [EL k current.inst_outputs])) ops)` by
       (simp[EVERY_EL, EL_MAPi] >> rpt strip_tac >>
        rename1 `is_label_op (clone_operand _ _ (EL k ops))` >>
        `~is_label_op (EL k ops)` by gvs[EVERY_EL] >>
        Cases_on `EL k ops` >> gvs[clone_operand_def, is_label_op_def]) >>
     simp[inline_adapter_path_fields_scalars] >>
     irule LIST_EQ >> simp[EL_MAP, EL_MAPi] >> rpt strip_tac >>
     `LENGTH current.inst_outputs = LENGTH call.inst_outputs` by
       metis_tac[LENGTH_MAP] >>
     `inline_path_rename zipper (EL x current.inst_outputs) =
        prename (EL x call.inst_outputs)` by
       (qpat_x_assum `MAP _ current.inst_outputs = _`
          (mp_tac o Q.AP_TERM `\xs. EL x xs`) >> simp[EL_MAP]) >>
     `~is_label_op (EL x ops)` by gvs[EVERY_EL] >>
     Cases_on `EL x ops` >>
     gvs[clone_operand_def, is_label_op_def,
       functionInlinerFrameTheory.inline_rename_operand_def, combinTheory.o_DEF]) >>
  metis_tac[]
QED
