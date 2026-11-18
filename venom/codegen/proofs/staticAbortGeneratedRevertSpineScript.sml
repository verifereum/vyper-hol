Theory staticAbortGeneratedRevertSpine
Ancestors
  fnPlanPrefix staticAbortRevertPlanPieces fnStaticAbortBoundary fnFrameStepsRevertForward fnBlockBodyHelpers
  contextStaticAbortRel codegenRel prefixExec fnPlanLineageInventory venomExecProps
  fnBlockPlanStatic staticAbortPlanBoundary genBlockSim fnFrameTerminalHalt
  stackOpSim planExec planWf list rich_list arithmetic finite_map
  stackPlanGen stackPlanOps stackModel asmIR venomWf contextCodegenRel venomInst

Theorem bounded_spine_choice[local]:
  !n k A E a.
    A k a /\
    (!q x. k <= q /\ q < k+n /\ A q x ==>
      ?y. A (SUC q) y /\ E q x y) ==>
    ?f. f k = a /\
      (!q. k <= q /\ q <= k+n ==> A q (f q)) /\
      (!q. k <= q /\ q < k+n ==> E q (f q) (f (SUC q)))
Proof
  Induct >- (rpt strip_tac >> qexists_tac `\q. a` >> simp[] >> rpt strip_tac >>
             `q = k` by decide_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `?f. f k = a /\
    (!q. k <= q /\ q <= k+n ==> A q (f q)) /\
    (!q. k <= q /\ q < k+n ==> E q (f q) (f (SUC q)))` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  `?y. A (SUC (k+n)) y /\ E (k+n) (f (k+n)) y` by
    (first_x_assum irule >> simp[]) >>
  qexists_tac `\q. if q = SUC(k+n) then y else f q` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >> gvs[] >>
      first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> Cases_on `q = k+n` >> gvs[] >>
  `q <> SUC(k+n) /\ SUC q <> SUC(k+n) /\ q < k+n` by decide_tac >>
  simp[]
QED

Theorem next_term_drop[local]:
  !xs k. (case DROP (SUC k) xs of [] => F
    | x::_ => is_terminator x.inst_opcode) =
    (SUC k < LENGTH xs /\ is_terminator (EL (SUC k) xs).inst_opcode)
Proof
  rpt gen_tac >> Cases_on `SUC k < LENGTH xs`
  >- (drule DROP_CONS_EL >> simp[]) >>
  `DROP (SUC k) xs = []` by simp[DROP_EQ_NIL] >> simp[]
QED

Theorem planner_spine[local]:
  revert_forward_pair bb k j /\
  non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions /\
  block_plan_state lv dfg cfg fn bb B k ps /\
  generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (k - LENGTH (get_params bb.bb_instructions)) (DROP k bb.bb_instructions)
    ps = SOME (ops,qs) /\ asm_block_at prog off (execute_plan fmp ops) ==>
  ?P R pc step.
    P k=ps /\ R k=ops /\ pc k=off /\
    (!q. k<=q /\ q<=SUC j ==>
      block_plan_state lv dfg cfg fn bb B q (P q) /\
      generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        (q - LENGTH (get_params bb.bb_instructions)) (DROP q bb.bb_instructions)
        (P q) = SOME (R q,qs) /\
      asm_block_at prog (pc q) (execute_plan fmp (R q))) /\
    (!q. k<=q /\ q<=j ==>
      generate_inst_plan lv dfg cfg fn (EL q bb.bb_instructions)
        (live_vars_at lv bb.bb_label (SUC q)) (bb_is_halting bb)
        (SUC q < LENGTH bb.bb_instructions /\
         is_terminator (EL (SUC q) bb.bb_instructions).inst_opcode)
        bb.bb_label (P q) = SOME (step q,P (SUC q)) /\
      R q = step q ++ R (SUC q) /\
      pc (SUC q) = pc q + LENGTH (execute_plan fmp (step q)) /\
      asm_block_at prog (pc q) (execute_plan fmp (step q)))
Proof
  strip_tac >>
  qabbrev_tac `A = \q (s,r,c).
    block_plan_state lv dfg cfg fn bb B q s /\
    generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (q - LENGTH (get_params bb.bb_instructions)) (DROP q bb.bb_instructions)
      s = SOME (r,qs) /\ asm_block_at prog c (execute_plan fmp r)` >>
  qabbrev_tac `E = \q (s,r,c) (s',r',c'). ?code.
    generate_inst_plan lv dfg cfg fn (EL q bb.bb_instructions)
      (live_vars_at lv bb.bb_label (SUC q)) (bb_is_halting bb)
      (SUC q < LENGTH bb.bb_instructions /\
       is_terminator (EL (SUC q) bb.bb_instructions).inst_opcode)
      bb.bb_label s = SOME (code,s') /\ r=code++r' /\
    c'=c+LENGTH (execute_plan fmp code) /\
    asm_block_at prog c (execute_plan fmp code)` >>
  `A k (ps,ops,off)` by simp[Abbr `A`] >>
  `!q x. k<=q /\ q<k+(SUC j-k) /\ A q x ==>
    ?y. A (SUC q) y /\ E q x y` by
    (rpt gen_tac >> PairCases_on `x` >> strip_tac >>
     `k<=q /\ q<=j` by (gvs[revert_forward_pair_def] >> decide_tac) >>
     `?inst. get_instruction bb q = SOME inst` by
       metis_tac[rf_forward_instruction_exists] >>
     `q < LENGTH bb.bb_instructions /\ inst=EL q bb.bb_instructions` by
       gvs[get_instruction_def] >>
     gvs[Abbr `A`] >>
     `LENGTH (get_params bb.bb_instructions) <= q` by
       fs[block_plan_state_def] >>
     drule_all rf_block_plan_step >>
     simp[next_term_drop] >> strip_tac >>
     qexists_tac `(ps1,rest_ops,x2+LENGTH (execute_plan fmp step_ops))` >>
     simp[Abbr `E`] >> conj_tac
     >- (conj_tac
         >- (irule block_plan_state_step >> simp[] >>
                qexistsl_tac [`step_ops`, `x0`] >> gvs[ADD1]) >>
         gvs[execute_plan_append, asm_block_at_append]) >>
     gvs[execute_plan_append, asm_block_at_append]) >>
  drule_all bounded_spine_choice >> strip_tac >>
  `k+(SUC j-k)=SUC j` by (gvs[revert_forward_pair_def] >> decide_tac) >>
  gvs[] >>
  qexistsl_tac [`\q. FST (f q)`, `\q. FST (SND (f q))`,
                `\q. SND (SND (f q))`] >>
  simp[] >>
  `!q. k<=q /\ q<=j ==> ?code.
    generate_inst_plan lv dfg cfg fn (EL q bb.bb_instructions)
      (live_vars_at lv bb.bb_label (SUC q)) (bb_is_halting bb)
      (SUC q < LENGTH bb.bb_instructions /\
       is_terminator (EL (SUC q) bb.bb_instructions).inst_opcode)
      bb.bb_label (FST (f q)) = SOME (code,FST (f (SUC q))) /\
    FST (SND (f q))=code++FST (SND (f (SUC q))) /\
    SND (SND (f (SUC q)))=SND (SND (f q))+LENGTH (execute_plan fmp code) /\
    asm_block_at prog (SND (SND (f q))) (execute_plan fmp code)` by
    (rpt strip_tac >> qpat_x_assum `!q. k <= q /\ q < SUC j ==> E q _ _`
       (qspec_then `q` mp_tac) >>
     simp[Abbr `E`] >>
     Cases_on `f q` >> Cases_on `r` >>
     Cases_on `f (SUC q)` >> Cases_on `r` >> gvs[]) >>
  pop_assum (mp_tac o SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]) >>
  disch_then (qx_choose_then `code` assume_tac) >>
  qexists_tac `code` >> simp[] >>
  rpt strip_tac >> qpat_x_assum `!q. k <= q /\ q <= SUC j ==> A q _`
    (qspec_then `q` mp_tac) >>
  Cases_on `f q` >> Cases_on `r` >> gvs[Abbr `A`]
QED

Theorem generated_revert_cut_spine:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 /\ in_revert_forward fn vs ==>
  ?j P R pc step pre emit post m d.
    revert_forward_pair bb k j /\ k < j /\ j < LENGTH bb.bb_instructions /\
    LENGTH (get_params bb.bb_instructions) <= k /\
    phi_prefix_length bb.bb_instructions <= k /\
    non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions /\
    P k = ps /\ R k = rest_ops /\ pc k = ast.as_pc /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops,ps_after) /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs = SOME (block_ops,ps_dfs_after) /\
    asm_block_at prog pc0 (execute_plan cpl.cp_initial_fmp block_ops) /\
    (!q. k <= q /\ q <= SUC j ==>
      block_plan_state liveness dfg cfg fn bb
        (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) q (P q) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (q - LENGTH (get_params bb.bb_instructions))
        (DROP q bb.bb_instructions) (P q) = SOME (R q,ps_after) /\
      asm_block_at prog (pc q) (execute_plan cpl.cp_initial_fmp (R q))) /\
    (!q. k <= q /\ q <= j ==>
      get_instruction bb q = SOME (EL q bb.bb_instructions) /\
      (EL q bb.bb_instructions).inst_opcode =
        (if q=k then RETURNDATACOPY else if q=j then REVERT else ASSIGN) /\
      generate_inst_plan liveness dfg cfg fn (EL q bb.bb_instructions)
        (live_vars_at liveness bb.bb_label (SUC q)) (bb_is_halting bb)
        (SUC q < LENGTH bb.bb_instructions /\
         is_terminator (EL (SUC q) bb.bb_instructions).inst_opcode)
        bb.bb_label (P q) = SOME (step q,P (SUC q)) /\
      R q = step q ++ R (SUC q) /\
      step q = pre q ++ emit q ++ post q /\
      pc (SUC q) = pc q + LENGTH (execute_plan cpl.cp_initial_fmp (step q)) /\
      asm_block_at prog (pc q) (execute_plan cpl.cp_initial_fmp (step q)) /\
      asm_block_at prog (pc q) (execute_plan cpl.cp_initial_fmp (pre q)) /\
      asm_block_at prog (pc q + LENGTH (execute_plan cpl.cp_initial_fmp (pre q)))
        (execute_plan cpl.cp_initial_fmp (emit q)) /\
      asm_block_at prog (pc q + LENGTH (execute_plan cpl.cp_initial_fmp (pre q)) +
        LENGTH (execute_plan cpl.cp_initial_fmp (emit q)))
        (execute_plan cpl.cp_initial_fmp (post q)) /\
      pc (SUC q) = pc q + LENGTH (execute_plan cpl.cp_initial_fmp (pre q)) +
        LENGTH (execute_plan cpl.cp_initial_fmp (emit q)) +
        LENGTH (execute_plan cpl.cp_initial_fmp (post q)) /\
      prefix_wf lo (LENGTH (P q).ps_stack) (pre q) /\
      prefix_end_len lo (LENGTH (P q).ps_stack) (pre q) = m q /\
      prefix_wf lo (d q) (post q) /\
      prefix_end_len lo (d q) (post q) = LENGTH (P (SUC q)).ps_stack /\
      (q=k ==> emit q = [SOEmit "RETURNDATACOPY"] /\ post q = [] /\
        3 <= m q /\ d q + 3 = m q /\
        3 <= m q + extra /\ d q + extra + 3 = m q + extra) /\
      (k<q /\ q<j ==> emit q = [] /\ 1 <= m q /\ d q = m q /\
        d q + extra = m q + extra) /\
      (q=j ==> emit q = [SOEmit "REVERT"] /\ post q = [] /\
        2 <= m q /\ d q + 2 = m q /\
        2 <= m q + extra /\ d q + extra + 2 = m q + extra))
Proof
  pure_rewrite_tac[body_inv_abort_def] >> strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[EL_MEM] >>
  `codegen_ready_fn fn` by
    fs[codegen_context_obligations_abort_def, codegen_ready_def, EVERY_MEM] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = vs.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by metis_tac[] >>
  `non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions` by
    metis_tac[non_param_insts_drop, codegen_ready_fn_def] >>
  `LENGTH (get_params bb.bb_instructions) <= k` by fs[block_plan_state_def] >>
  (* Retired E0154 root route: full-context fs/gvs followed by metis
     timed out; goal_assum drule and qexists j >> simp left equalities
     bb'=bb and vs_inst_idx=k untransported. *)
  `?j. revert_forward_pair bb k j` by
    (qpat_assum `in_revert_forward fn vs` mp_tac >>
     qpat_assum `lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `vs.vs_inst_idx = k` mp_tac >>
     qpat_assum `!i j. revert_forward_pair bb i j ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[in_revert_forward_def, revert_forward_at_def] >> gvs[]
     >- (qexists_tac `j` >> simp[]) >>
     first_x_assum drule >> fs[revert_forward_pair_def] >> decide_tac) >>
  `k<j /\ j<LENGTH bb.bb_instructions` by
    gvs[revert_forward_pair_def, get_instruction_def] >>
  `asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp rest_ops)` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     gvs[execute_plan_append, execute_plan_def, asm_block_at_append, APPEND_ASSOC]) >>
  `DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb) =
   DROP k bb.bb_instructions` by simp[DROP_DROP_T] >>
  `?P R pc step.
    P k=ps /\ R k=rest_ops /\ pc k=ast.as_pc /\
    (!q. k<=q /\ q<=SUC j ==>
      block_plan_state liveness dfg cfg fn bb
        (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) q (P q) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        (q - LENGTH (get_params bb.bb_instructions)) (DROP q bb.bb_instructions)
        (P q) = SOME (R q,ps_after) /\
      asm_block_at prog (pc q) (execute_plan cpl.cp_initial_fmp (R q))) /\
    (!q. k<=q /\ q<=j ==>
      generate_inst_plan liveness dfg cfg fn (EL q bb.bb_instructions)
        (live_vars_at liveness bb.bb_label (SUC q)) (bb_is_halting bb)
        (SUC q < LENGTH bb.bb_instructions /\
         is_terminator (EL (SUC q) bb.bb_instructions).inst_opcode)
        bb.bb_label (P q) = SOME (step q,P (SUC q)) /\
      R q=step q++R(SUC q) /\
      pc(SUC q)=pc q+LENGTH(execute_plan cpl.cp_initial_fmp (step q)) /\
      asm_block_at prog (pc q) (execute_plan cpl.cp_initial_fmp (step q)))` by
    (irule planner_spine >> simp[] >> metis_tac[]) >>
  `!q. k<=q /\ q<=j ==> ?pre emit post m d.
    step' q = pre ++ emit ++ post /\
    prefix_wf lo (LENGTH (P q).ps_stack) pre /\
    prefix_end_len lo (LENGTH (P q).ps_stack) pre=m /\
    prefix_wf lo d post /\ prefix_end_len lo d post=LENGTH (P(SUC q)).ps_stack /\
    (q=k ==> emit=[SOEmit "RETURNDATACOPY"] /\ post=[] /\
      3<=m /\ d+3=m /\ 3<=m+extra /\ d+extra+3=m+extra) /\
    (k<q /\ q<j ==> emit=[] /\ 1<=m /\ d=m /\ d+extra=m+extra) /\
    (q=j ==> emit=[SOEmit "REVERT"] /\ post=[] /\
      2<=m /\ d+2=m /\ 2<=m+extra /\ d+extra+2=m+extra)` by
    (rpt strip_tac >>
     `q<LENGTH bb.bb_instructions /\ phi_prefix_length bb.bb_instructions<=q` by decide_tac >>
     `get_instruction bb q = SOME (EL q bb.bb_instructions)` by simp[get_instruction_def] >>
     drule_all rf_forward_instruction_shape >> strip_tac >>
     drule_all rf_forward_instruction_opcode >> strip_tac >>
     qpat_assum `!q. k<=q /\ q<=j ==> _` (qspec_then `q` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_assum `!q. k<=q /\ q<=SUC j ==> _` (qspec_then `q` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
       inst.inst_operands) bb'.bb_instructions) fn.fn_blocks` by
       metis_tac[codegen_ready_fn_no_marker] >>
     (* E0160 retired forward drule_all / projected drule_at routes:
        simplification normalized only the theorem's analysis aliases. *)
     `LENGTH (compute_operands (EL q bb.bb_instructions)) <=
       LENGTH (SND (emit_input_plan (EL q bb.bb_instructions).inst_opcode
         (compute_operands (EL q bb.bb_instructions))
         (live_vars_at liveness bb.bb_label (SUC q)) (P q))).ps_stack` by
       (qpat_assum `liveness = _` mp_tac >>
        qpat_assum `dfg = _` mp_tac >> qpat_assum `cfg = _` mp_tac >>
        qpat_assum `codegen_ready_fn fn` mp_tac >>
        qpat_assum `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ = _` mp_tac >>
        qpat_assum `EVERY _ fn.fn_blocks` mp_tac >>
        qpat_assum `lookup_block bb.bb_label fn.fn_blocks = SOME bb` mp_tac >>
        qpat_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
        qpat_assum `dfs_block_state _ _ _ _ _ _ _` mp_tac >>
        qpat_assum `generate_block_plan _ _ _ _ _ ps_dfs = _` mp_tac >>
        qpat_assum `generate_block_plan _ _ _ _ _ (_ with <| ps_cleanup_height := _; ps_cleanup_promised := _ |>) = _` mp_tac >>
        qpat_assum `block_plan_state _ _ _ _ _ _ q _` mp_tac >>
        qpat_assum `q < LENGTH bb.bb_instructions` mp_tac >>
        qpat_assum `phi_prefix_length bb.bb_instructions <= q` mp_tac >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >>
        irule (cj 6 block_plan_state_static) >>
        rpt (goal_assum (drule_at Any)) >>
        gvs[GSYM ADD1]) >>
     drule_all rf_forward_regular_plan_result >> strip_tac >>
     `MEM (EL q bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
     `MEM (EL q bb.bb_instructions) (fn_insts fn)` by
       metis_tac[body_inst_ready] >>
     `!l. MEM (Label l) (compute_operands (EL q bb.bb_instructions)) ==>
       IS_SOME (FLOOKUP lo l)` by metis_tac[] >>
     `LENGTH (compute_operands (EL q bb.bb_instructions)) <= 16` by decide_tac >>
     (* Full-context goal_assum then simp/gvs left an existential
        generation equality unmatched (two retired assembly attempts). *)
     (* E0168 wrapper-first irule_at also rejected the equality anchor.
        Retain only the mathematical plan-piece premises for application. *)
     qpat_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `!l. MEM (Label l) (compute_operands _) ==> _` mp_tac >>
     qpat_assum `LENGTH (compute_operands _) <= LENGTH _` mp_tac >>
     qpat_assum `LENGTH (compute_operands _) <= 16` mp_tac >>
     qpat_assum `_.inst_opcode = (if _ then _ else _)` mp_tac >>
     qpat_assum `q=k ==> _` mp_tac >> qpat_assum `q=j ==> _` mp_tac >>
     qpat_assum `k<q /\ q<j ==> _` mp_tac >>
     qpat_assum `k<j` mp_tac >> qpat_assum `k<=q` mp_tac >>
     qpat_assum `q<=j` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     (* Retired E0172: metis_tac[revert_forward_plan_pieces] timed out.
        Match generation first, then opcode fixes the interval indices. *)
     (* E0178 typed diagnostic: cfg has type alpha, whereas lo has
        type string |-> beta. The goal's lo has range num. Instantiate
        beta before disch_then makes that type rigid in a hypothesis. *)
     drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
       (INST_TYPE [beta |-> ``:num``] revert_forward_plan_pieces) >>
     disch_then (drule_at (Pat `_.inst_opcode = (if _ then _ else _)`)) >>
     disch_then (qspecl_then [`lo`, `extra`] mp_tac) >> simp[]) >>
  pop_assum (mp_tac o SIMP_RULE bool_ss
    [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]) >>
  disch_then (qx_choose_then `pre` (qx_choose_then `emit`
    (qx_choose_then `post` (qx_choose_then `m`
      (qx_choose_then `d` assume_tac))))) >>
  qexistsl_tac [`j`, `P`, `R`, `pc`, `step'`, `pre`, `emit`, `post`, `m`, `d`] >>
  simp[] >> gen_tac >> strip_tac >>
  `q < LENGTH bb.bb_instructions` by decide_tac >>
  `get_instruction bb q = SOME (EL q bb.bb_instructions)` by simp[get_instruction_def] >>
  drule_all rf_forward_instruction_opcode >> strip_tac >>
  qpat_assum `!q. k<=q /\ q<=j ==> generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _ /\ _`
    (qspec_then `q` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!q. k<=q /\ q<=j ==> step' q = _ /\ _`
    (qspec_then `q` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  (* Full-context simplification here expanded unrelated analyses (E0178).
     Only the placed step, its factorization and two endpoint bounds remain. *)
  qpat_assum `get_instruction bb q = _` mp_tac >>
  qpat_assum `_.inst_opcode = (if _ then _ else _)` mp_tac >>
  qpat_assum `asm_block_at prog (pc q) (execute_plan _ (step' q))` mp_tac >>
  qpat_assum `step' q = _` mp_tac >>
  qpat_assum `q=k ==> _` mp_tac >> qpat_assum `q=j ==> _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt disch_tac >>
  (* Retired final gvs[execute_plan_append, asm_block_at_append,
     ADD_ASSOC] timed out even in this six-fact context. Keep placement
     decomposition purely equational, outside the ambient simpset. *)
  qpat_x_assum `asm_block_at prog (pc q) (execute_plan _ (step' q))` mp_tac >>
  pure_asm_rewrite_tac [execute_plan_append, asm_block_at_append, LENGTH_APPEND] >>
  strip_tac >>
  ASM_SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM] >>
  (* Retired arithmetic-only decide_tac could not rewrite placement
     arguments or extract endpoint implication conjuncts. *)
  rpt strip_tac >> gvs[]
QED
