(*
 * Function Inliner Pass — Definitions
 *
 * Inlines small internal functions at their call sites. Copies callee's
 * basic blocks into the caller, binds parameters, and rewires control flow.
 *
 * Source: vyper/venom/passes/function_inliner.py (~241 LOC)
 * Upstream: vyperlang/vyper@cff4f6822
 *
 * TOP-LEVEL:
 *   clone_function              — clone function with prefixed labels/vars
 *   inline_call_site            — inline callee at a single INVOKE site
 *   fix_inline_phis             — fix PHIs after inlining
 *   inline_at_sites             — inline callee at all sites in a function
 *   remove_function             — remove a function from context
 *   build_call_walk             — postorder DFS walk over call graph
 *   select_inline_candidate     — select next function to inline
 *   function_inliner_ctx        — full pass
 *
 * Helper:
 *   is_label_op / inline_prefix / return_block_label
 *   clone_operand / clone_instruction / clone_basic_block
 *   rotate_invoke_ops
 *   rewrite_inline_inst / rewrite_inline_insts
 *   rewrite_inline_block / rewrite_inline_blocks
 *   find_invoke_idx / find_invoke_site
 *   fn_code_size / fn_code_size_from_ctx
 *)

Theory functionInlinerDefs
Ancestors
  cfgTransform venomWf venomExecSemantics fcgDefs

(* ===== Operand Helpers ===== *)

Definition is_label_op_def:
  is_label_op (Label _) = T ∧
  is_label_op _ = F
End

(* ===== Naming ===== *)

(* Prefix for inline instance N. Python: f"inl{self.inline_count}_" *)
Definition inline_prefix_def:
  inline_prefix (n:num) = STRCAT "inl" (STRCAT (num_to_dec_string n) "_")
End

(* Return block label. Python: ctx.get_next_label(f"{prefix}inline_return")
   produces f"{prefix}inline_return{label_counter}". *)
Definition return_block_label_def:
  return_block_label prefix (label_counter:num) =
    STRCAT prefix (STRCAT "inline_return" (num_to_dec_string label_counter))
End

(* ===== Cloning ===== *)

(* Clone operand: prefix internal labels and all variables.
   fn_block_labels: block labels of the source function.
   Labels not in fn_block_labels (e.g. data labels) are kept as-is. *)
Definition clone_operand_def:
  clone_operand prefix fn_block_labels (Label l) =
    (if MEM l fn_block_labels then Label (STRCAT prefix l) else Label l) ∧
  clone_operand prefix fn_block_labels (Var v) = Var (STRCAT prefix v) ∧
  clone_operand prefix fn_block_labels (Lit w) = Lit w
End

Definition clone_instruction_def:
  clone_instruction prefix fn_block_labels inst =
    inst with <|
      inst_operands :=
        MAP (clone_operand prefix fn_block_labels) inst.inst_operands;
      inst_outputs :=
        MAP (λv. STRCAT prefix v) inst.inst_outputs
    |>
End

Definition clone_basic_block_def:
  clone_basic_block prefix fn_block_labels bb =
    <| bb_label := STRCAT prefix bb.bb_label;
       bb_instructions :=
         MAP (clone_instruction prefix fn_block_labels) bb.bb_instructions |>
End

Definition clone_function_def:
  clone_function prefix func =
    let labels = fn_labels func in
    <| fn_name := STRCAT prefix func.fn_name;
       fn_blocks :=
         MAP (clone_basic_block prefix labels) func.fn_blocks |>
End

(* ===== Parameter / Return Rewriting ===== *)

(* Rotate INVOKE operands for PARAM binding.
   Python: ops = call_site.operands[1:] + [call_site.operands[0]]
   Moves the callee label (return PC) to the end so PARAM indices
   match argument positions. *)
Definition rotate_invoke_ops_def:
  rotate_invoke_ops [] = [] ∧
  rotate_invoke_ops (first::rest) = rest ++ [first]
End

(* Rewrite a single instruction in a cloned block.
   Returns (replacement instructions, updated param_idx).
   PARAM → ASSIGN from caller's operand (rotated).
     The last PARAM gets a Label operand (return PC). Python assigns it
     because labels are addresses at runtime. Our eval_operand returns
     NONE for Labels — the correctness proof must show this assign is
     dead code (output unused after RET → JMP).
   RET → assign return values to INVOKE outputs, then JMP to return block.
   Others → unchanged. *)
Definition rewrite_inline_inst_def:
  rewrite_inline_inst invoke_ops invoke_outs return_label inst param_idx =
    if inst.inst_opcode = PARAM then
      if param_idx < LENGTH invoke_ops then
        let op = EL param_idx invoke_ops in
        (* Label operands (return PC) can't be evaluated — substitute
           a dummy literal. The variable is dead after RET → JMP. *)
        let op' = if is_label_op op then Lit 0w else op in
        ([inst with <| inst_opcode := ASSIGN;
                       inst_operands := [op'] |>],
         param_idx + 1)
      else
        ([inst], param_idx)
    else if inst.inst_opcode = RET then
      (* In the HOL semantics, ALL RET operands are return values
         (no return PC concept — INVOKE/IntRet handles return directly).
         Map each return value to the corresponding INVOKE output. *)
      let ret_vals = inst.inst_operands in
      let assigns = MAPi (λi rv.
        <| inst_id := 0;
           inst_opcode := ASSIGN;
           inst_operands := [rv];
           inst_outputs := [EL i invoke_outs] |>)
        ret_vals in
      let jmp = inst with <| inst_opcode := JMP;
                              inst_operands := [Label return_label];
                              inst_outputs := [] |> in
      (assigns ++ [jmp], param_idx)
    else
      ([inst], param_idx)
End

(* Rewrite an instruction list, threading param_idx. *)
Definition rewrite_inline_insts_def:
  rewrite_inline_insts invoke_ops invoke_outs return_label [] param_idx =
    ([], param_idx) ∧
  rewrite_inline_insts invoke_ops invoke_outs return_label (inst::rest)
      param_idx =
    let (inst_list, pi') =
      rewrite_inline_inst invoke_ops invoke_outs return_label
        inst param_idx in
    let (rest_list, pi'') =
      rewrite_inline_insts invoke_ops invoke_outs return_label rest pi' in
    (inst_list ++ rest_list, pi'')
End

Definition rewrite_inline_block_def:
  rewrite_inline_block invoke_ops invoke_outs return_label bb param_idx =
    let (insts, pi') =
      rewrite_inline_insts invoke_ops invoke_outs return_label
        bb.bb_instructions param_idx in
    (bb with bb_instructions := insts, pi')
End

(* Rewrite all cloned blocks. param_idx is shared across blocks
   (matching Python's shared param_idx counter). *)
Definition rewrite_inline_blocks_def:
  rewrite_inline_blocks invoke_ops invoke_outs return_label [] param_idx =
    ([], param_idx) ∧
  rewrite_inline_blocks invoke_ops invoke_outs return_label (bb::rest)
      param_idx =
    let (bb', pi') =
      rewrite_inline_block invoke_ops invoke_outs return_label bb param_idx in
    let (rest', pi'') =
      rewrite_inline_blocks invoke_ops invoke_outs return_label rest pi' in
    (bb' :: rest', pi'')
End

(* ===== Call Site Inlining ===== *)

(* Inline callee at a single INVOKE call site.
   Steps (matching Python _inline_call_site):
   1. Split call block at INVOKE index
   2. Clone callee with prefix
   3. Rewrite cloned blocks: PARAM → ASSIGN, RET → assigns + JMP
   4. Append return block and cloned blocks to caller
   5. Truncated call block gets JMP to cloned entry *)
Definition inline_call_site_def:
  inline_call_site prefix return_label caller_fn callee_fn
      call_bb_lbl call_idx =
    case lookup_block call_bb_lbl caller_fn.fn_blocks of
      NONE => caller_fn
    | SOME call_bb =>
        let call_inst = EL call_idx call_bb.bb_instructions in
        let invoke_ops = rotate_invoke_ops call_inst.inst_operands in
        let invoke_outs = call_inst.inst_outputs in
        (* Split block *)
        let before_invoke = TAKE call_idx call_bb.bb_instructions in
        let after_invoke =
          DROP (call_idx + 1) call_bb.bb_instructions in
        let return_bb = <| bb_label := return_label;
                           bb_instructions := after_invoke |> in
        (* Clone and rewrite *)
        let callee_clone = clone_function prefix callee_fn in
        let (rewritten_blocks, _) =
          rewrite_inline_blocks invoke_ops invoke_outs return_label
            callee_clone.fn_blocks 0 in
        (* Entry label of cloned callee *)
        let cloned_entry_label =
          case callee_clone.fn_blocks of
            [] => ""
          | (eb::_) => eb.bb_label in
        (* Truncated call block: before_invoke ++ JMP to cloned entry *)
        let jmp_inst =
          <| inst_id := 0; inst_opcode := JMP;
             inst_operands := [Label cloned_entry_label];
             inst_outputs := [] |> in
        let truncated_bb = call_bb with
          bb_instructions := before_invoke ++ [jmp_inst] in
        (* Assemble: replace call block, append return + cloned blocks *)
        caller_fn with fn_blocks :=
          replace_block call_bb_lbl truncated_bb caller_fn.fn_blocks
          ++ [return_bb]
          ++ rewritten_blocks
End

(* ===== PHI Fixup ===== *)

(* After inlining, successors of the return block may have PHIs
   referencing the original call block. Update to reference return block.
   Matches Python _fix_phi. *)
Definition fix_inline_phis_def:
  fix_inline_phis orig_label new_label return_bb func =
    let succ_labels = bb_succs return_bb in
    func with fn_blocks :=
      MAP (λbb.
        if MEM bb.bb_label succ_labels then
          bb with bb_instructions :=
            MAP (λinst.
              if inst.inst_opcode ≠ PHI then inst
              else subst_label_inst orig_label new_label inst)
            bb.bb_instructions
        else bb)
      func.fn_blocks
End

(* ===== Inline State ===== *)

(* Counters threaded through inlining for fresh name generation. *)
Datatype:
  inline_state = <|
    is_inline_count : num;
    is_label_counter : num
  |>
End

(* ===== Find INVOKE Sites ===== *)

(* Find index of first INVOKE targeting callee_name in a block. *)
Definition find_invoke_idx_def:
  find_invoke_idx callee_name [] (n:num) = NONE ∧
  find_invoke_idx callee_name (inst::rest) n =
    if inst.inst_opcode = INVOKE ∧
       (case inst.inst_operands of
          Label l :: _ => l = callee_name
        | _ => F)
    then SOME n
    else find_invoke_idx callee_name rest (n + 1)
End

(* Find a call site (block label, instruction index) in a function. *)
Definition find_invoke_site_def:
  find_invoke_site callee_name [] = NONE ∧
  find_invoke_site callee_name (bb::rest) =
    case find_invoke_idx callee_name bb.bb_instructions 0 of
      SOME idx => SOME (bb.bb_label, idx)
    | NONE => find_invoke_site callee_name rest
End

(* ===== Inline at All Sites ===== *)

(* Inline callee at one call site. Returns NONE if no site found. *)
Definition inline_one_site_def:
  inline_one_site caller_fn callee_fn ist =
    case find_invoke_site callee_fn.fn_name caller_fn.fn_blocks of
      NONE => NONE
    | SOME (bb_lbl, idx) =>
        let prefix = inline_prefix ist.is_inline_count in
        let ret_lbl = return_block_label prefix ist.is_label_counter in
        let caller' =
          inline_call_site prefix ret_lbl caller_fn callee_fn bb_lbl idx in
        let caller'' =
          case lookup_block ret_lbl caller'.fn_blocks of
            SOME ret_bb =>
              fix_inline_phis bb_lbl ret_lbl ret_bb caller'
          | NONE => caller' in
        SOME (renumber_fn_inst_ids caller'',
              ist with <| is_inline_count := ist.is_inline_count + 1;
                          is_label_counter := ist.is_label_counter + 1 |>)
End

(* Inline callee at ALL sites in caller, iterating until no more found.
   Fuel bounds iterations (at most one INVOKE per instruction). *)
Definition inline_at_sites_def:
  inline_at_sites 0 caller_fn callee_fn ist = (caller_fn, ist) ∧
  inline_at_sites (SUC n) caller_fn callee_fn ist =
    case inline_one_site caller_fn callee_fn ist of
      NONE => (caller_fn, ist)
    | SOME (caller', ist') =>
        inline_at_sites n caller' callee_fn ist'
End

(* ===== Function Removal ===== *)

Definition remove_function_def:
  remove_function name ctx =
    ctx with ctx_functions :=
      FILTER (λf. f.fn_name ≠ name) ctx.ctx_functions
End

(* ===== Call Walk Termination Helpers ===== *)

(* All function names mentioned in the FCG callees map (keys and values). *)
Definition fcg_all_names_def:
  fcg_all_names fcg =
    FLAT (MAP (λ(k,v). k :: v) (fmap_to_alist fcg.fcg_callees))
End

(* Adding a name to visited can only decrease the FILTER count. *)
Theorem fc_visited_mono[local]:
  ∀x vis names.
    LENGTH (FILTER (λn. ¬MEM n (x::vis)) names) ≤
    LENGTH (FILTER (λn. ¬MEM n vis) names)
Proof
  rpt gen_tac >> irule listTheory.LENGTH_FILTER_LEQ_MONO >> simp[]
QED

(* General: if P ⊂ Q on a list (pointwise P⇒Q + witness), FILTER P < FILTER Q *)
Theorem filter_strict_sub[local]:
  ∀P Q names.
    (∀x. P x ⇒ Q x) ∧ (∃x. MEM x names ∧ Q x ∧ ¬P x) ⇒
    LENGTH (FILTER P names) < LENGTH (FILTER Q names)
Proof
  ntac 2 gen_tac >> Induct >> rw[] >> gvs[] >>
  TRY (first_x_assum irule >> metis_tac[]) >>
  simp[arithmeticTheory.LT_SUC_LE] >>
  TRY (first_x_assum irule >> metis_tac[]) >>
  irule listTheory.LENGTH_FILTER_LEQ_MONO >> simp[]
QED

(* If name is in the fcg_all_names but not in visited, adding it to
   visited strictly decreases the FILTER count. *)
Theorem fc_visited_shrink[local]:
  ∀fn_name vis fcg.
    MEM fn_name (fcg_all_names fcg) ∧ ¬MEM fn_name vis ⇒
    LENGTH (FILTER (λn. ¬MEM n (fn_name::vis)) (fcg_all_names fcg)) <
    LENGTH (FILTER (λn. ¬MEM n vis) (fcg_all_names fcg))
Proof
  rw[] >> irule filter_strict_sub >> rw[] >> metis_tac[]
QED

(* Length of callees is bounded by length of all names. *)
Theorem callees_length_bound[local]:
  ∀fcg fn_name.
    fn_name ∈ FDOM fcg.fcg_callees ⇒
    LENGTH (fcg_get_callees fcg fn_name) ≤ LENGTH (fcg_all_names fcg)
Proof
  rw[fcg_get_callees_def, finite_mapTheory.FLOOKUP_DEF, fcg_all_names_def] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `LENGTH (fn_name :: fcg.fcg_callees ' fn_name)` >> simp[] >>
  `MEM (fn_name :: fcg.fcg_callees ' fn_name)
       (MAP (\(k,v). k::v) (fmap_to_alist fcg.fcg_callees))`
    by (simp[listTheory.MEM_MAP] >>
        qexists_tac `(fn_name, fcg.fcg_callees ' fn_name)` >>
        simp[alistTheory.MEM_fmap_to_alist]) >>
  drule listTheory.SUM_MAP_MEM_bound >>
  disch_then (qspec_then `LENGTH` mp_tac) >>
  simp[rich_listTheory.LENGTH_FLAT]
QED

(* If fn_name is not in the FCG domain, its callees are empty. *)
Theorem callees_empty_not_in_dom[local]:
  ∀fcg fn_name.
    fn_name ∉ FDOM fcg.fcg_callees ⇒
    fcg_get_callees fcg fn_name = []
Proof
  rw[fcg_get_callees_def, finite_mapTheory.FLOOKUP_DEF]
QED

(* ===== Call Walk (Postorder DFS) ===== *)

(* Postorder DFS over the call graph.
   Matches Python _build_call_walk: for each function, DFS into callees
   first, then append self. Skips already-visited functions.

   Termination uses a flat numeric measure. The hard TC (TC 1, INR→INR)
   requires proving that the WFREC auxiliary only grows the visited set.
   We use Hol_defn + Defn.tprove for full SML-level control, following
   the kapur_subra pattern from $HOLDIR/src/tfl/examples/. *)

val call_walk_dfs_defn = Hol_defn "call_walk_dfs" `
  (call_walk_dfs fcg fn_name visited =
    if MEM fn_name visited then (visited, [])
    else
      let visited' = fn_name :: visited in
      let callees = fcg_get_callees fcg fn_name in
      let (visited'', callee_walk) =
        call_walk_dfs_list fcg callees visited' in
      (visited'', SNOC fn_name callee_walk)) /\
  (call_walk_dfs_list fcg [] visited = (visited, [])) /\
  (call_walk_dfs_list fcg (fn_name::rest) visited =
    let (vis', walk1) = call_walk_dfs fcg fn_name visited in
    let (vis'', walk2) = call_walk_dfs_list fcg rest vis' in
    (vis'', walk1 ++ walk2))`;

(* --- Set the measure relation --- *)

val m_body = ``\x : (fcg_analysis # string # string list)
                   + (fcg_analysis # string list # string list).
  let names = case x of INL (fcg,_,_) => fcg_all_names fcg
                      | INR (fcg,_,_) => fcg_all_names fcg in
  let K = 2 * LENGTH names + 10 in
  case x of
    INL (fcg, fn_name, visited) =>
      K * LENGTH (FILTER (\n. ~MEM n visited) names) + 3
  | INR (fcg, list, visited) =>
      K * LENGTH (FILTER (\n. ~MEM n visited) names) + 2 * LENGTH list + 2``;

val R = ``measure ^m_body``;
val defnR = Defn.set_reln call_walk_dfs_defn R;
val tcs = Defn.tcs_of defnR;

(* --- Prove TCs 0 and 2 (easy) --- *)

(* Helper: a < b ==> k * (a+1) <= k * b *)
val mult_mono_suc = prove(``!a b (k:num). a < b ==> k * (a + 1) <= k * b``,
  rw[arithmeticTheory.LE_MULT_LCANCEL] >> DECIDE_TAC);

(* TC 0: INR(callees, fn::vis) < INL(fn, vis)
   After unfolding measure: K*FC(fn::vis) + 2*|callees| + 2 < K*FC(vis) + 3
   Case fn IN FDOM: FC strict decrease absorbs 2*|callees| (bounded by |names|)
   Case fn NOTIN FDOM: callees=[], FC mono gives K*FC' + 2 < K*FC + 3 *)
val tc0 = List.nth(tcs, 0);
val tc0_thm = prove(tc0,
  REWRITE_TAC[prim_recTheory.measure_thm] >>
  BETA_TAC >> rpt strip_tac >>
  ASM_REWRITE_TAC[] >> BETA_TAC >>
  simp_tac bool_ss [sumTheory.sum_case_def] >>
  BETA_TAC >>
  simp_tac bool_ss [pairTheory.pair_case_thm] >>
  BETA_TAC >>
  simp_tac bool_ss [LET_THM] >> BETA_TAC >>
  Cases_on `fn_name IN FDOM fcg.fcg_callees`
  >- (`MEM fn_name (fcg_all_names fcg)` by (
        rw[fcg_all_names_def, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
        qexists_tac `fn_name :: (fcg.fcg_callees ' fn_name)` >>
        simp[] >>
        qexists_tac `(fn_name, fcg.fcg_callees ' fn_name)` >>
        simp[alistTheory.MEM_fmap_to_alist]) >>
      `LENGTH (FILTER (\n. ~MEM n (fn_name::visited)) (fcg_all_names fcg)) <
       LENGTH (FILTER (\n. ~MEM n visited) (fcg_all_names fcg))` by
        (irule fc_visited_shrink >> simp[]) >>
      imp_res_tac callees_length_bound >>
      drule mult_mono_suc >>
      disch_then (qspec_then `2 * LENGTH (fcg_all_names fcg) + 10` mp_tac) >>
      REWRITE_TAC[arithmeticTheory.LEFT_ADD_DISTRIB,
                  arithmeticTheory.MULT_RIGHT_1] >>
      DECIDE_TAC)
  >- (imp_res_tac callees_empty_not_in_dom >>
      ASM_REWRITE_TAC[listTheory.LENGTH] >>
      `LENGTH (FILTER (\n. ~MEM n (fn_name::visited)) (fcg_all_names fcg)) <=
       LENGTH (FILTER (\n. ~MEM n visited) (fcg_all_names fcg))` by
        (irule fc_visited_mono) >>
      `(2 * LENGTH (fcg_all_names fcg) + 10) *
       LENGTH (FILTER (\n. ~MEM n (fn_name::visited)) (fcg_all_names fcg)) <=
       (2 * LENGTH (fcg_all_names fcg) + 10) *
       LENGTH (FILTER (\n. ~MEM n visited) (fcg_all_names fcg))` by
        (simp[arithmeticTheory.LE_MULT_LCANCEL]) >>
      DECIDE_TAC));

(* TC 2: INL(fn, vis) < INR(fn::rest, vis) — trivial from measure *)
val tc2 = List.nth(tcs, 2);
val tc2_thm = prove(tc2, simp[prim_recTheory.measure_thm]);

(* --- Eliminate easy TCs, access aux function --- *)

val defnR_1 = Defn.elim_tcs defnR [tc0_thm, tc2_thm];
val SOME union_d = Defn.union_defn defnR_1;
val SOME aux_d = Defn.aux_defn union_d;
val [e_inl, e_nil, e_cons] = Defn.eqns_of aux_d;
val SOME aux_ind = Defn.ind_of aux_d;

(* e_cons has TC 1 as hypothesis; e_inl, e_nil are unconditional.
   aux_ind provides induction with TC 1 as a condition on the INR-cons IH.
   We prove visited-set monotonicity by this induction, deriving TC 1
   from the INL IH (the kapur_subra pattern). *)

(* Extract the aux-applied-to-R term from equations *)
val aux_R = e_inl |> concl |> lhs |> rator;

(* Discharge WF hypothesis from e_cons *)
val tc3 = List.nth(tcs, 3);
val tc3_thm = prove(tc3, simp[prim_recTheory.WF_measure]);
val e_cons' = PROVE_HYP tc3_thm e_cons;

(* --- Fn abbreviation: hides measure lambda inside a constant --- *)
val Fn_def = Define `call_walk_Fn = ^aux_R`;
val e_inl_fn = REWRITE_RULE [GSYM Fn_def] e_inl;
val e_nil_fn = REWRITE_RULE [GSYM Fn_def] e_nil;
val e_cons_fn = REWRITE_RULE [GSYM Fn_def] e_cons';
val aux_ind_fn = REWRITE_RULE [GSYM Fn_def] aux_ind;
val aux_ind_clean = PROVE_HYP tc3_thm aux_ind_fn;

(* TC1-as-antecedent equation (avoids alpha-conversion, see LEARNINGS) *)
val eqn_cons = REWRITE_RULE [GSYM Fn_def] (DISCH_ALL e_cons');

(* --- FST helper lemmas (Fn-rewritten) --- *)
val inl_fst_mem_fn = REWRITE_RULE [GSYM Fn_def] (prove(
  ``!fcg fn_name visited.
      MEM fn_name visited ==>
      FST (^aux_R (INL (fcg, fn_name, visited))) = visited``,
  rpt strip_tac >> ONCE_REWRITE_TAC[e_inl] >> ASM_REWRITE_TAC[] >> simp[]));

val inl_fst_lemma_fn = REWRITE_RULE [GSYM Fn_def] (prove(
  ``!fcg fn_name visited.
      ~MEM fn_name visited ==>
      FST (^aux_R (INL (fcg, fn_name, visited))) =
      FST (^aux_R (INR (fcg, fcg_get_callees fcg fn_name, fn_name::visited)))``,
  rpt strip_tac >>
  ONCE_REWRITE_TAC[e_inl] >> ASM_REWRITE_TAC[] >>
  Cases_on `^aux_R (INR (fcg, fcg_get_callees fcg fn_name, fn_name::visited))` >>
  simp[]));

val inr_nil_fst_fn = REWRITE_RULE [GSYM Fn_def] (prove(
  ``!fcg visited. FST (^aux_R (INR (fcg, [], visited))) = visited``,
  rpt strip_tac >> ONCE_REWRITE_TAC[e_nil] >> simp[]));

(* --- General helper: FST distributes through double paired-let --- *)
val fst_double_let = prove(
  ``!(e1:'a#'b) (e2:'a -> 'c#'d) (g:'b -> 'd -> 'e).
      FST (let (a,b) = e1 in let (c,d) = e2 a in (c, g b d)) = FST (e2 (FST e1))``,
  rpt strip_tac >> Cases_on `e1` >> Cases_on `e2 q` >> simp[]);

(* --- Monotonicity helpers --- *)
val fc_le_from_mem_mono = prove(
  ``!q vis (names:string list).
      (!m. MEM m vis ==> MEM m q) ==>
      LENGTH (FILTER (\n. ~MEM n q) names) <= LENGTH (FILTER (\n. ~MEM n vis) names)``,
  rpt strip_tac >> irule listTheory.LENGTH_FILTER_LEQ_MONO >>
  simp[] >> rpt strip_tac >> CCONTR_TAC >> full_simp_tac bool_ss [] >> res_tac);

val le_mult_mono = prove(
  ``!a b (k:num). a <= b ==> k * a <= k * b``,
  rw[arithmeticTheory.LE_MULT_LCANCEL]);

(* --- Measure unfolding tactic (used 3x) --- *)
val unfold_measure_tac =
  REWRITE_TAC[prim_recTheory.measure_thm] >> BETA_TAC >>
  simp_tac bool_ss [sumTheory.sum_case_def] >> BETA_TAC >>
  simp_tac bool_ss [pairTheory.pair_case_thm] >> BETA_TAC >>
  simp_tac bool_ss [LET_THM] >> BETA_TAC >>
  simp_tac bool_ss [listTheory.LENGTH] >> DECIDE_TAC;

(* --- Prove visited-set monotonicity --- *)
val sum_ty = type_of (e_inl |> concl |> lhs |> rand);

fun SPLIT_CONJ_TAC th =
  let val (a,b) = CONJ_PAIR th
  in ASSUME_TAC a THEN ASSUME_TAC b end;

val aux_mono = let
  val mono_goal = ``!x (n:string).
    (case x of INL (_,_,v1) => MEM n v1 | INR (_,_,v2) => MEM n v2) ==>
    MEM n (FST (call_walk_Fn x))``
in prove(mono_goal,
  ho_match_mp_tac aux_ind_clean >> rpt conj_tac
  (* INL case *)
  >- (rpt strip_tac >>
      gvs[sumTheory.sum_case_def, pairTheory.pair_case_thm] >>
      Cases_on `MEM fn_name visited`
      >- gvs[inl_fst_mem_fn]
      >- (gvs[inl_fst_lemma_fn] >>
          `MEM n (fn_name::visited)` by gvs[listTheory.MEM] >>
          res_tac))
  (* INR-nil case *)
  >- (rpt strip_tac >>
      gvs[sumTheory.sum_case_def, pairTheory.pair_case_thm, inr_nil_fst_fn])
  (* INR-cons case *)
  >- (rpt strip_tac >>
      gvs[sumTheory.sum_case_def, pairTheory.pair_case_thm] >>
      Cases_on `call_walk_Fn (INL (fcg, fn_name, visited))` >>
      gvs[pairTheory.FST] >>
      (* Step 1: MEM n visited => MEM n q via IH_INL *)
      `MEM n q` by res_tac >>
      (* Step 2: Prove measure condition to unlock IH_INR *)
      `LENGTH (FILTER (\n'. ~MEM n' q) (fcg_all_names fcg)) <=
       LENGTH (FILTER (\n'. ~MEM n' visited) (fcg_all_names fcg))` by
        (match_mp_tac fc_le_from_mem_mono >> rpt strip_tac >> res_tac) >>
      `LENGTH (FILTER (\n'. ~MEM n' q) (fcg_all_names fcg)) *
       (2 * LENGTH (fcg_all_names fcg) + 10) <=
       LENGTH (FILTER (\n'. ~MEM n' visited) (fcg_all_names fcg)) *
       (2 * LENGTH (fcg_all_names fcg) + 10)` by
        simp[arithmeticTheory.LE_MULT_RCANCEL] >>
      (* Discharge measure condition in IH_INR *)
      `!n'. MEM n' q ==>
            MEM n' (FST (call_walk_Fn (INR (fcg,rest,q))))` by
        (qpat_x_assum `_ ==> !n'. _` mp_tac >>
         impl_tac >- DECIDE_TAC >> simp[]) >>
      (* Step 3: Chain: MEM n q => MEM n (FST(INR(rest,q))) *)
      `MEM n (FST (call_walk_Fn (INR (fcg, rest, q))))` by res_tac >>
      (* Step 4: Rewrite goal using eqn_cons *)
      mp_tac eqn_cons >>
      (impl_tac >- (
        rpt strip_tac >>
        REV_FULL_SIMP_TAC bool_ss [] >>
        full_simp_tac bool_ss [pairTheory.PAIR_EQ] >>
        ASM_REWRITE_TAC[] >>
        unfold_measure_tac)) >>
      strip_tac >>
      ASM_REWRITE_TAC[] >>
      SIMP_TAC bool_ss [fst_double_let] >>
      ASM_REWRITE_TAC[pairTheory.FST]))
end;

val aux_mono = PROVE_HYP tc3_thm aux_mono;

(* --- Prove TC 1 using monotonicity ---
   After unfolding measure, the goal is:
     K*FC(vis') + 2*|rest| + 2 < K*FC(visited) + 2*|fn::rest| + 2
   where FC(v) = |FILTER(¬MEM v) names|, K = 2*|names|+10.
   aux_mono gives vis ⊆ vis' (MEM-wise) ⇒ FC(vis') ≤ FC(visited) ⇒ K*FC(vis') ≤ K*FC(visited).
   Then DECIDE_TAC closes the additive gap from |rest| < |fn::rest|. *)
val tc1 = List.nth(tcs, 1);
val tc1_thm = prove(tc1,
  REWRITE_TAC[prim_recTheory.measure_thm, GSYM Fn_def] >> BETA_TAC >>
  simp_tac bool_ss [sumTheory.sum_case_def] >> BETA_TAC >>
  simp_tac bool_ss [pairTheory.pair_case_thm] >> BETA_TAC >>
  simp_tac bool_ss [LET_THM] >> BETA_TAC >>
  rpt strip_tac >>
  `call_walk_Fn (INL (fcg, fn_name, visited)) = (vis', walk1)` by
    (ONCE_REWRITE_TAC[boolTheory.EQ_SYM_EQ] >> first_assum ACCEPT_TAC) >>
  `(2 * LENGTH (fcg_all_names fcg) + 10) *
   LENGTH (FILTER (\n. ~MEM n vis') (fcg_all_names fcg)) <=
   (2 * LENGTH (fcg_all_names fcg) + 10) *
   LENGTH (FILTER (\n. ~MEM n visited) (fcg_all_names fcg))` by
    (match_mp_tac le_mult_mono >>
     irule listTheory.LENGTH_FILTER_LEQ_MONO >>
     simp[] >> rpt strip_tac >>
     CCONTR_TAC >> full_simp_tac bool_ss [] >>
     mp_tac (Q.SPECL [`INL (fcg, fn_name, visited)`, `x`] aux_mono) >>
     simp_tac bool_ss [sumTheory.sum_case_def, pairTheory.pair_case_thm] >>
     BETA_TAC >>
     ASM_REWRITE_TAC[pairTheory.FST] >>
     disch_tac >> res_tac) >>
  simp_tac bool_ss [listTheory.LENGTH] >>
  DECIDE_TAC);

(* --- Complete the definition --- *)

val (call_walk_dfs_def, call_walk_dfs_ind) =
  Defn.tprove(call_walk_dfs_defn,
    EXISTS_TAC R >>
    REWRITE_TAC [tc0_thm, tc1_thm, tc2_thm, tc3_thm]);

val _ = save_thm("call_walk_dfs_def", call_walk_dfs_def);
val _ = save_thm("call_walk_dfs_ind", call_walk_dfs_ind);


Definition build_call_walk_def:
  build_call_walk fcg entry_name =
    SND (call_walk_dfs fcg entry_name [])
End

(* ===== Candidate Selection ===== *)

(* Non-pseudo instruction count as code size estimate. *)
Definition fn_code_size_def:
  fn_code_size func =
    LENGTH (FILTER (λinst. ¬is_pseudo inst.inst_opcode) (fn_insts func))
End

(* Look up function code size from context. *)
Definition fn_code_size_from_ctx_def:
  fn_code_size_from_ctx ctx fn_name =
    case lookup_function fn_name ctx.ctx_functions of
      NONE => 0
    | SOME func => fn_code_size func
End

(* Select first inlinable function from the walk.
   Inlinable if: has call sites AND (single call site OR cost ≤ threshold).
   Matches Python _select_inline_candidate. *)
Definition select_inline_candidate_def:
  select_inline_candidate ctx fcg threshold [] = NONE ∧
  select_inline_candidate ctx fcg threshold (fn_name::rest) =
    let call_count = LENGTH (fcg_get_call_sites fcg fn_name) in
    if call_count = 0 then
      select_inline_candidate ctx fcg threshold rest
    else if call_count = 1 then
      SOME fn_name
    else if fn_code_size_from_ctx ctx fn_name ≤ threshold then
      SOME fn_name
    else
      select_inline_candidate ctx fcg threshold rest
End

(* ===== Inline a Candidate Across All Callers ===== *)

(* Inline callee into all functions in the context. *)
Definition inline_candidate_def:
  inline_candidate ctx callee ist =
    let (fns', ist') =
      FOLDL (λ(fns, st) caller_fn.
        let max_sites = LENGTH (fn_insts caller_fn) in
        let (caller', st') =
          inline_at_sites max_sites caller_fn callee st in
        (SNOC caller' fns, st'))
      ([], ist)
      ctx.ctx_functions in
    (ctx with ctx_functions := fns', ist')
End

(* ===== Full Pass ===== *)

(* One round: recompute FCG, select candidate, inline, remove.
   Returns NONE if no candidate found. *)
Definition function_inliner_round_def:
  function_inliner_round ctx walk threshold ist =
    let fcg = fcg_analyze ctx in
    case select_inline_candidate ctx fcg threshold walk of
      NONE => NONE
    | SOME candidate_name =>
        case lookup_function candidate_name ctx.ctx_functions of
          NONE => NONE
        | SOME callee =>
            let (ctx', ist') = inline_candidate ctx callee ist in
            let ctx'' = remove_function candidate_name ctx' in
            let walk' = FILTER (λn. n ≠ candidate_name) walk in
            SOME (ctx'', walk', ist')
End

(* Iterate rounds until no more candidates.
   Bounded by function count (one removed per round). *)
Definition function_inliner_loop_def:
  function_inliner_loop 0 ctx walk threshold ist = ctx ∧
  function_inliner_loop (SUC n) ctx walk threshold ist =
    case function_inliner_round ctx walk threshold ist of
      NONE => ctx
    | SOME (ctx', walk', ist') =>
        function_inliner_loop n ctx' walk' threshold ist'
End

(* Top-level entry point. *)
Definition function_inliner_ctx_def:
  function_inliner_ctx threshold ctx =
    let fcg = fcg_analyze ctx in
    let walk =
      case ctx.ctx_entry of
        NONE => []
      | SOME entry => build_call_walk fcg entry in
    let ist = <| is_inline_count := 0; is_label_counter := 0 |> in
    function_inliner_loop (LENGTH ctx.ctx_functions) ctx walk threshold ist
End
