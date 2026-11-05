(* Shared boundary probes for frame-aware terminal simulation. *)
Theory fnFrameTerminalPrep
Ancestors
  genFrameSim frameRel contextCodegenRelProps contextCodegenRel codegenRel
  instSimHelpers asmFrame stackPlanTypes stackPlanGen venomInst genBlockSim
  mixedPrefixSim stackModel venomState asmSem planExec unitShapeDefs
  venomExecSemantics symbolResolve dfgDefs frameViewMemory

(* A source read range misses every spill region, so the assembly memory
   and the source memory agree on it, padded as RETURN and REVERT read. *)
Theorem context_source_payload_agree:
  source_memory_reads_disjoint cplan inst vs /\
  context_memory_rel cplan vs.vs_memory m /\
  MEM (off,n) (source_memory_read_ranges inst vs) ==>
  TAKE n (DROP off m ++ REPLICATE n 0w) =
  TAKE n (DROP off vs.vs_memory ++ REPLICATE n 0w)
Proof
  strip_tac >> irule padded_memory_read_cong >> rpt strip_tac >>
  drule context_reads_agree >> simp[] >> disch_then irule >>
  simp[source_memory_read_byte_def] >>
  qexists `(off,n)` >> simp[byte_in_memory_range_def]
QED

Theorem fn_frame_inv_local_state:
  !ctx cplan lo fn ra rest mem0 ps vs st.
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st ==>
  ?top. st.as_stack = top ++ rest /\
    venom_asm_rel lo ps
      (frame_view fn ra vs with vs_memory := st.as_memory)
      (st with as_stack := top)
Proof
  rpt gen_tac >>
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
        operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  simp[fn_frame_inv_def] >> strip_tac >> qexists `top` >>
  gvs[context_venom_asm_rel_def, venom_asm_rel_def,
      plan_stack_rel_def, plan_spill_rel_def, operand_val_def,
      memory_rel_refl]
QED

(* A local prefix's masked memory agreement composes with the ambient
   relation; no ordering of the source read range relative to spills is used. *)
Theorem context_memory_rel_local_prefix:
  !r cplan alloc vm am am'.
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= alloc.sa_spill_base /\
  alloc.sa_next_offset <= r.sr_spill_end /\
  context_memory_rel cplan vm am /\ memory_rel alloc am am' ==>
  context_memory_rel cplan vm am'
Proof
  simp[context_memory_rel_def, memory_rel_def] >> rpt strip_tac >>
  `~(alloc.sa_spill_base <= i /\ i < alloc.sa_next_offset)` by
    (strip_tac >> qpat_x_assum `~context_spill_byte cplan i` mp_tac >>
     simp[context_spill_byte_def] >> qexists `r` >> simp[]) >>
  metis_tac[]
QED

(* Initial depth 15 becomes 16 after the first literal input. *)
Definition terminal_escape_ps_def:
  terminal_escape_ps = (init_plan_state 0) with
    ps_stack := Var "size" :: MAP (\n. Var (REPLICATE n #"x")) (COUNT_LIST 15)
End

Theorem terminal_escape_input_plan:
  FST (emit_input_plan RETURN [Lit 32w; Var "size"] ["size"] terminal_escape_ps) =
  [SOPush (Lit 32w); SOSpill 0; SODup 16; SORestore 0; SOSwap 1]
Proof
  EVAL_TAC
QED

Definition terminal_escape_inst_def:
  terminal_escape_inst = mk_inst 0 RETURN [Var "size"; Lit 32w] []
End

Theorem terminal_escape_generated_ops:
  !lv dfg cfg fn ih nt lbl.
  OPTION_MAP FST (generate_inst_plan lv dfg cfg fn terminal_escape_inst
    ["size"] ih nt lbl terminal_escape_ps) =
  SOME [SOPush (Lit 32w); SOSpill 0; SODup 16; SORestore 0; SOSwap 1;
        SOEmit "RETURN"]
Proof
  rpt gen_tac >> EVAL_TAC
QED

Theorem terminal_escape_initial_wf:
  generated_plan_state_wf 0 terminal_escape_ps /\
  stack_get_depth (Var "size") terminal_escape_ps.ps_stack = SOME 15 /\
  LENGTH (compute_operands terminal_escape_inst) = 2 /\
  LENGTH (SND (emit_input_plan RETURN (compute_operands terminal_escape_inst)
    ["size"] terminal_escape_ps)).ps_stack = 18
Proof
  EVAL_TAC >> simp[]
QED

Theorem terminal_escape_prefix_spill_wf:
  prefix_spill_wf 0 FEMPTY
    [SOPush (Lit 32w); SOSpill 0; SODup 16; SORestore 0; SOSwap 1]
    terminal_escape_ps
Proof
  EVAL_TAC >> simp[] >> qexists `Lit 32w` >> simp[]
QED

Definition terminal_escape_fn_def:
  terminal_escape_fn = mk_raw_function "f"
    [<|bb_label := "entry"; bb_instructions :=
      [mk_inst 1 PARAM [Lit 0w] ["size"]; terminal_escape_inst]|>]
End

Definition terminal_escape_vs_def:
  terminal_escape_vs = (init_venom_state "entry") with vs_vars :=
    FUPDATE_LIST FEMPTY (MAP (\n. (REPLICATE n #"x", 0w:bytes32)) (COUNT_LIST 15)
                        ++ [("size",0w)])
End

Definition terminal_escape_as_def:
  terminal_escape_as = <|
    as_stack := REPLICATE 16 0w; as_memory := [];
    as_accounts := terminal_escape_vs.vs_accounts;
    as_transient := terminal_escape_vs.vs_transient;
    as_returndata := []; as_logs := []; as_pc := 0;
    as_call_ctx := terminal_escape_vs.vs_call_ctx;
    as_tx_ctx := terminal_escape_vs.vs_tx_ctx;
    as_block_ctx := terminal_escape_vs.vs_block_ctx;
    as_code := []; as_prev_hashes := []; as_outcomes := [];
    as_requests := []; as_pending_deletions := []; as_gas_readings := [] |>
End

Definition terminal_escape_cplan_def:
  terminal_escape_cplan = <|
    cp_regions := [<|sr_fn_name := "f"; sr_spill_base := 0;
                    sr_spill_end := 0; sr_plan := []|>];
    cp_max_static_eom := 0; cp_peak_spill_end := 0; cp_initial_fmp := 0 |>
End

Definition terminal_escape_ops_def:
  terminal_escape_ops = [SOPush (Lit 32w); SOSpill 0; SODup 16;
    SORestore 0; SOSwap 1; SOEmit "RETURN"]
End

Definition terminal_escape_prog_def:
  terminal_escape_prog = execute_plan 0 terminal_escape_ops
End

Theorem terminal_escape_no_opaque:
  !origin x. (origin = GAS \/ origin = RETPC_PARAM) ==>
    ~copy_phi_var origin terminal_escape_fn x
Proof
  rpt strip_tac >> drule copy_phi_var_has_seed >>
  simp[terminal_escape_fn_def, terminal_escape_inst_def,
       mk_raw_function_def, mk_inst_def, fn_insts_def, fn_insts_blocks_def] >>
  rpt strip_tac >> disj1_tac >> conj_tac >> strip_tac >> gvs[]
QED

Theorem terminal_escape_function_premises:
  codegen_ready_fn terminal_escape_fn /\ opaque_use_ok terminal_escape_fn /\
  MEM terminal_escape_inst (fn_insts terminal_escape_fn) /\
  inst_wf terminal_escape_inst
Proof
  `!origin x. (origin = GAS \/ origin = RETPC_PARAM) ==>
      ~copy_phi_var origin terminal_escape_fn x` by
    metis_tac[terminal_escape_no_opaque] >>
  reverse (rpt conj_tac)
  >- EVAL_TAC
  >- EVAL_TAC
  >- (simp[opaque_use_ok_def, gas_var_def, retpc_var_def] >> metis_tac[]) >>
  EVAL_TAC >> simp[]
QED

Theorem terminal_escape_reads_disjoint:
  source_memory_reads_disjoint terminal_escape_cplan terminal_escape_inst terminal_escape_vs
Proof
  EVAL_TAC >> simp[]
QED

Theorem terminal_escape_source_halt:
  !fuel ctx. step_inst fuel ctx terminal_escape_inst terminal_escape_vs =
    Halt (halt_state (set_returndata (REPLICATE 32 0w) terminal_escape_vs))
Proof
  rpt gen_tac >> EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem terminal_escape_frame_view:
  !ra vs. frame_view terminal_escape_fn ra vs = vs
Proof
  rpt gen_tac >> simp[frame_view_def, retpc_var_def, terminal_escape_no_opaque] >>
  `FMAP_MAP2 (\(x,v). v) vs.vs_vars = vs.vs_vars` by
    (simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_FMAP_MAP2]) >>
  simp[]
QED

Theorem terminal_escape_initial_frame:
  !ctx. fn_frame_inv ctx terminal_escape_cplan
    (SND (compute_label_offsets terminal_escape_prog)) terminal_escape_fn
    0w [] [] terminal_escape_ps terminal_escape_vs terminal_escape_as
Proof
  gen_tac >> simp[fn_frame_inv_def, terminal_escape_frame_view] >>
  EVAL_TAC >> simp[] >>
  CONV_TAC (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV EVAL)) >> EVAL_TAC >> simp[]
QED

Theorem terminal_escape_equiv:
  !op at. operand_equiv dfg_empty op at <=> op = at
Proof
  `!op. normalize_operand dfg_empty [] op = op` by
    (Cases >> simp[normalize_operand_def, dfg_empty_def]) >>
  simp[operand_equiv_def]
QED

Theorem terminal_escape_operand_premises:
  (!op. MEM op (compute_operands terminal_escape_inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op terminal_escape_ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP terminal_escape_ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands terminal_escape_inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets terminal_escape_prog)) l)) /\
  (!op. MEM op (compute_operands terminal_escape_inst) ==>
    eval_operand op terminal_escape_vs =
    operand_val terminal_escape_vs (SND (compute_label_offsets terminal_escape_prog)) op) /\
  (!op at. MEM op (compute_operands terminal_escape_inst) /\
    (MEM at terminal_escape_ps.ps_stack \/ at IN FDOM terminal_escape_ps.ps_spilled \/
     MEM at (compute_operands terminal_escape_inst)) /\
    operand_equiv dfg_empty op at ==>
    operand_val terminal_escape_vs (SND (compute_label_offsets terminal_escape_prog)) op =
    operand_val terminal_escape_vs (SND (compute_label_offsets terminal_escape_prog)) at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg_empty op at ==> at <> dead_stack_marker)
    (compute_operands terminal_escape_inst)
Proof
  simp[terminal_escape_equiv] >> EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[is_var_operand_def] >> EVAL_TAC
QED

Theorem terminal_escape_program:
  terminal_escape_prog =
    [AsmPush [32w]; AsmPush []; AsmOp "MSTORE"; AsmOp "DUP16";
     AsmPush []; AsmOp "MLOAD"; AsmOp "SWAP1"; AsmOp "RETURN"]
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

val () = computeLib.upd_compset
  (computeLib.add_thms [byteTheory.set_byte_bit_field_insert]);

Theorem terminal_escape_long_run:
  !n. case asm_steps (SND (compute_label_offsets terminal_escape_prog))
     (build_offset_to_pc terminal_escape_prog) terminal_escape_prog (8+n)
     terminal_escape_as of
    AsmHalt st => st.as_returndata <> REPLICATE 32 0w
  | _ => T
Proof
  gen_tac >> rewrite_tac[terminal_escape_program] >>
  `8+n = SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC n)))))))` by decide_tac >>
  pop_assum SUBST1_TAC >> EVAL_TAC >> simp[wordsTheory.dimword_def] >>
  EVAL_TAC >> simp[] >> wordsLib.WORD_EVAL_TAC >>
  simp[byteTheory.set_byte_def] >> EVAL_TAC
QED

Theorem terminal_escape_short_run:
  !n. n < 8 ==> !st.
    asm_steps (SND (compute_label_offsets terminal_escape_prog))
     (build_offset_to_pc terminal_escape_prog) terminal_escape_prog n
     terminal_escape_as <> AsmHalt st
Proof
  rewrite_tac[terminal_escape_program] >>
  CONV_TAC (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV EVAL)) >>
  EVAL_TAC >> simp[]
QED

Theorem terminal_escape_no_matching_halt:
  !n st. asm_steps (SND (compute_label_offsets terminal_escape_prog))
     (build_offset_to_pc terminal_escape_prog) terminal_escape_prog n
     terminal_escape_as = AsmHalt st ==>
    ~venom_asm_terminal_rel
      (halt_state (set_returndata (REPLICATE 32 0w) terminal_escape_vs)) st
Proof
  rpt gen_tac >> Cases_on `n < 8`
  >- metis_tac[terminal_escape_short_run] >>
  `n = 8 + (n-8)` by decide_tac >>
  mp_tac (Q.SPEC `n-8` terminal_escape_long_run) >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  strip_tac >> simp[] >> strip_tac >>
  gvs[venom_asm_terminal_rel_def, halt_state_def, set_returndata_def]
QED

(* Every hypothesis of the frozen Halt theorem, at the escape witness. *)
Theorem terminal_escape_halt_antecedent:
  !ctx lv cfg ih nt lbl.
  ?ps'.
    terminal_escape_inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint terminal_escape_cplan terminal_escape_inst terminal_escape_vs /\
    opaque_use_ok terminal_escape_fn /\
    ~is_param_opcode terminal_escape_inst.inst_opcode /\
    generated_plan_state_wf 0 terminal_escape_ps /\
    codegen_ready_fn terminal_escape_fn /\
    MEM terminal_escape_inst (fn_insts terminal_escape_fn) /\
    inst_wf terminal_escape_inst /\
    LENGTH (compute_operands terminal_escape_inst) <= 16 /\
    LENGTH (compute_operands terminal_escape_inst) <=
      LENGTH (SND (emit_input_plan terminal_escape_inst.inst_opcode
        (compute_operands terminal_escape_inst) ["size"] terminal_escape_ps)).ps_stack /\
    (!op. MEM op (compute_operands terminal_escape_inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op terminal_escape_ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP terminal_escape_ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands terminal_escape_inst) ==>
      IS_SOME (FLOOKUP (SND (compute_label_offsets terminal_escape_prog)) l)) /\
    (!op. MEM op (compute_operands terminal_escape_inst) ==>
      eval_operand op (frame_view terminal_escape_fn 0w terminal_escape_vs) =
      operand_val (frame_view terminal_escape_fn 0w terminal_escape_vs)
        (SND (compute_label_offsets terminal_escape_prog)) op) /\
    (!op at. MEM op (compute_operands terminal_escape_inst) /\
      (MEM at terminal_escape_ps.ps_stack \/ at IN FDOM terminal_escape_ps.ps_spilled \/
       MEM at (compute_operands terminal_escape_inst)) /\ operand_equiv dfg_empty op at ==>
      operand_val (frame_view terminal_escape_fn 0w terminal_escape_vs)
        (SND (compute_label_offsets terminal_escape_prog)) op =
      operand_val (frame_view terminal_escape_fn 0w terminal_escape_vs)
        (SND (compute_label_offsets terminal_escape_prog)) at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg_empty op at ==> at <> dead_stack_marker)
      (compute_operands terminal_escape_inst) /\
    prefix_spill_wf terminal_escape_cplan.cp_initial_fmp
      (SND (compute_label_offsets terminal_escape_prog)) (FRONT terminal_escape_ops) terminal_escape_ps /\
    (!off. MEM (SORestore off) terminal_escape_ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx terminal_escape_cplan (SND (compute_label_offsets terminal_escape_prog))
      terminal_escape_fn 0w [] [] terminal_escape_ps terminal_escape_vs terminal_escape_as /\
    generate_inst_plan lv dfg_empty cfg terminal_escape_fn terminal_escape_inst
      ["size"] ih nt lbl terminal_escape_ps = SOME (terminal_escape_ops, ps') /\
    asm_block_at terminal_escape_prog terminal_escape_as.as_pc
      (execute_plan terminal_escape_cplan.cp_initial_fmp terminal_escape_ops)
Proof
  rpt gen_tac >>
  simp[terminal_escape_frame_view, terminal_escape_reads_disjoint,
       terminal_escape_function_premises, terminal_escape_initial_wf,
       terminal_escape_operand_premises, terminal_escape_initial_frame,
       terminal_escape_equiv] >>
  EVAL_TAC >> simp[]
QED

(* Together with terminal_escape_halt_antecedent this refutes the frozen
   gen_inst_halt_frame_sim: lo and o2pc are precisely the computed maps,
   base = 0, dfg = dfg_empty, ra = 0w, rest = [], mem0 = [].
   The prefix spills the pushed literal 32 at offset 0, outside the empty
   original spill interval [0,0), and RETURN subsequently reads that word.

   Sufficient repair: require every actual prefix spill-write footprint
   to be disjoint from source_memory_read_byte cp inst vs. Merely bounding
   the initial allocator, as fn_frame_inv does, cannot ensure this.
   Containment of *all transient prefix allocations* in cp_regions is a
   stronger convenient sufficient condition; final allocation alone need
   not cover slots freed during the prefix. Frozen statements are untouched. *)
Theorem terminal_escape_halt_counterexample:
  !fuel ctx.
    step_inst fuel ctx terminal_escape_inst terminal_escape_vs =
      Halt (halt_state (set_returndata (REPLICATE 32 0w) terminal_escape_vs)) /\
    ~(?n st.
      asm_steps (SND (compute_label_offsets terminal_escape_prog))
        (build_offset_to_pc terminal_escape_prog) terminal_escape_prog n terminal_escape_as =
        AsmHalt st /\
      venom_asm_terminal_rel
        (halt_state (set_returndata (REPLICATE 32 0w) terminal_escape_vs)) st)
Proof
  simp[terminal_escape_source_halt] >>
  metis_tac[terminal_escape_no_matching_halt]
QED
