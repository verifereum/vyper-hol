(*
 * Function Inliner — Clone Execution Simulation
 *
 * Core lemma: clone_execution_sim
 *   Running the callee function produces equivalent observable results
 *   to running the rewritten clone blocks in the caller.
 *
 * Architecture:
 *   1. Operand/eval helpers for clone_rel_np
 *   2. Structural: lookup in clone blocks
 *   3. Step-level: step_inst for clone (non-INVOKE + INVOKE)
 *   4. Bind/merge helpers for clone_rel_np
 *   5. Block-level simulation
 *   6. Function-level clone_execution_sim (fuel induction)
 *)

Theory functionInlinerCloneExec
Ancestors
  functionInlinerInline functionInlinerDefs functionInlinerSim
  functionInlinerFresh functionInlinerCloneSim functionInlinerStepClone
  functionInlinerCalleeSim
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  execEquivProps cfgTransform cfgTransformProps venomExecProps

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory

val rec_eq = venomStateTheory.venom_state_component_equality;

open functionInlinerDefsTheory functionInlinerInlineTheory
     functionInlinerCloneSimTheory functionInlinerSimTheory
     functionInlinerStepCloneTheory functionInlinerFreshTheory
     functionInlinerRenumberTheory functionInlinerCalleeSimTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     execEquivPropsTheory cfgTransformTheory cfgTransformPropsTheory
     venomExecPropsTheory venomInstPropsTheory

(* ================================================================
   Section 1: Structural lemmas
   ================================================================ *)

Triviality FIND_APPEND:
  !P (xs:'a list) ys.
    FIND P (xs ++ ys) =
    case FIND P xs of SOME x => SOME x | NONE => FIND P ys
Proof
  gen_tac >> Induct >> simp[FIND_thm] >> rpt strip_tac >>
  Cases_on `P h` >> simp[]
QED

Triviality lookup_block_mem_fn_labels[local]:
  !lbl fn bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    MEM lbl (fn_labels fn)
Proof
  rw[fn_labels_def, lookup_block_def] >>
  imp_res_tac FIND_MEM >> imp_res_tac FIND_P >> fs[MEM_MAP] >>
  qexists_tac `bb` >> simp[]
QED

Triviality lookup_block_append:
  !lbl (bbs1 : basic_block list) bbs2.
    lookup_block lbl (bbs1 ++ bbs2) =
    case lookup_block lbl bbs1 of
      SOME bb => SOME bb
    | NONE => lookup_block lbl bbs2
Proof
  rw[lookup_block_def, FIND_APPEND]
QED

(* ================================================================
   Section 3: setup_callee / merge / bind for clone_rel_np
   ================================================================ *)

Theorem setup_callee_shared_globals_np[local]:
  !fn args s1 s2.
    shared_globals_np s1 s2 ==>
    setup_callee fn args s1 = setup_callee fn args s2
Proof
  rw[setup_callee_def, shared_globals_np_def, rec_eq]
QED

Theorem merge_callee_clone_rel_np[local]:
  !prefix labels s_callee s_clone callee_s'.
    clone_rel_np prefix labels s_callee s_clone ==>
    clone_rel_np prefix labels
      (merge_callee_state s_callee callee_s')
      (merge_callee_state s_clone callee_s')
Proof
  simp[clone_rel_np_def, merge_callee_state_def, shared_globals_np_def,
       rec_eq]
QED

Triviality STRCAT_RIGHT_CANCEL:
  !prefix a b. STRCAT prefix a = STRCAT prefix b <=> a = b
Proof
  Induct_on `prefix` >> simp[]
QED

Theorem update_var_clone_rel_np[local]:
  !prefix labels s_c s_cl v val.
    clone_rel_np prefix labels s_c s_cl ==>
    clone_rel_np prefix labels
      (update_var v val s_c)
      (update_var (STRCAT prefix v) val s_cl)
Proof
  simp[clone_rel_np_def, update_var_def, shared_globals_np_def, rec_eq,
       FLOOKUP_UPDATE, FDOM_FUPDATE] >>
  rpt strip_tac >> Cases_on `v' = v` >> simp[] >>
  res_tac >> simp[] >>
  imp_res_tac STRCAT_RIGHT_CANCEL >> gvs[]
QED

Triviality foldl_bind_clone_rel_np:
  !pairs prefix labels s_c s_cl.
    clone_rel_np prefix labels s_c s_cl ==>
    clone_rel_np prefix labels
      (FOLDL (\s' (out,val). update_var out val s') s_c pairs)
      (FOLDL (\s' (out,val). update_var out val s') s_cl
             (MAP (\(out,val). (STRCAT prefix out, val)) pairs))
Proof
  Induct >> simp[] >>
  Cases >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  irule update_var_clone_rel_np >> simp[]
QED

Triviality zip_map_fst:
  !outs vals (f:string->string).
    LENGTH outs = LENGTH vals ==>
    ZIP (MAP f outs, vals) =
    MAP (\(out,val). (f out, val)) (ZIP (outs, vals))
Proof
  Induct >> Cases_on `vals` >> simp[ZIP_def]
QED

Theorem bind_outputs_clone_rel_np[local]:
  !prefix labels s_c s_cl outs vals.
    clone_rel_np prefix labels s_c s_cl /\
    LENGTH outs = LENGTH vals ==>
    clone_rel_np prefix labels
      (THE (bind_outputs outs vals s_c))
      (THE (bind_outputs (MAP (\v. STRCAT prefix v) outs) vals s_cl))
Proof
  rw[bind_outputs_def] >>
  `LENGTH (MAP (\v. STRCAT prefix v) outs) = LENGTH vals` by simp[] >>
  simp[] >>
  imp_res_tac zip_map_fst >> simp[] >>
  irule foldl_bind_clone_rel_np >> simp[]
QED

(* bind_outputs preserves shared_globals_np *)
Triviality foldl_bind_shared_globals_np:
  !pairs s1 s2.
    shared_globals_np s1 s2 ==>
    shared_globals_np
      (FOLDL (\s' (out,val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out,val). update_var out val s') s2 pairs)
Proof
  Induct >> simp[] >>
  Cases >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  fs[update_var_def, shared_globals_np_def, rec_eq]
QED

Triviality bind_outputs_shared_globals_np:
  !outs vals s1 s2.
    shared_globals_np s1 s2 /\ LENGTH outs = LENGTH vals ==>
    shared_globals_np
      (THE (bind_outputs outs vals s1))
      (THE (bind_outputs outs vals s2))
Proof
  rw[bind_outputs_def] >>
  irule foldl_bind_shared_globals_np >> simp[]
QED

(* ================================================================
   Section 4: Clone execution simulation

   The key theorem: callee execution via run_function corresponds to
   clone block execution in caller_xf.

   Preconditions:
   - clone_rel_np holds (vars correspond, globals match, no params match needed)
   - Block lookup: each callee block has a corresponding clone block in caller_xf
   - Callee WF: no self-invoke, extern targets, blocks well-formed, no alloca

   The block lookup condition is the key bridge: it says that for each callee
   block label, the REWRITTEN CLONE block is present in caller_xf.
   ================================================================ *)

(* clone_execution_sim: callee run_function ≈ clone blocks in caller_xf.
 *
 * The callee runs via run_function, producing IntRet/Halt/Abort/Error.
 * The clone blocks (rewritten from callee blocks) run inside caller_xf.
 *
 * Key non-standard feature: callee IntRet → clone OK (reaching ret_lbl).
 * This is because RET → ASSIGN+JMP rewrites produce OK + JMP, not IntRet.
 *
 * Block lookup precondition: for each callee block, the rewritten clone
 * block (produced by rewrite_inline_block) is in caller_xf. This gives
 * us exact knowledge of clone block instruction content.
 *
 * State relation: clone_rel_np (vars correspond via prefix, globals match,
 * no params requirement). Entry block PARAM→ASSIGN is handled because
 * setup_callee sets callee vs_params to match invoke_ops.
 *
 * Proved by complete induction on fuel.
 *)
(* Per-block simulation: for matched callee/clone blocks and states,
   run_block results correspond. Split into non-RET and RET cases. *)
(* run_block OK preserves vs_params: all non-terminator OK steps preserve
   vs_params (step_preserves_params), and OK-producing terminators (JMP/JNZ/DJMP)
   use jump_to which preserves vs_params. *)
(* FOLDL update_var preserves vs_params *)
Triviality foldl_update_var_preserves_params[local]:
  !pairs s.
    (FOLDL (\s' (out,val). update_var out val s') s pairs).vs_params =
    s.vs_params
Proof
  Induct >> simp[] >> Cases >> simp[update_var_def]
QED

(* bind_outputs preserves vs_params *)
Triviality bind_outputs_preserves_params[local]:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' ==> s'.vs_params = s.vs_params
Proof
  rw[bind_outputs_def] >> BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  simp[foldl_update_var_preserves_params]
QED

(* step_inst preserves vs_params for OK results — all opcodes.
   Non-terminator: step_preserves_params.
   Terminator OK: only JMP/JNZ/DJMP (via jump_to).
   INVOKE OK: merge_callee_state + bind_outputs both preserve vs_params. *)
Triviality step_inst_OK_preserves_params[local]:
  !fuel ctx inst s v.
    step_inst fuel ctx inst s = OK v ==> v.vs_params = s.vs_params
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >| [
    (* terminator + INVOKE: impossible — INVOKE is not a terminator *)
    gvs[is_terminator_def],
    (* terminator + not INVOKE: JMP/JNZ/DJMP via jump_to *)
    `step_inst fuel ctx inst s = step_inst_base inst s` by
      fs[step_inst_def] >>
    Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
    qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
    simp[step_inst_base_def] >>
    BasicProvers.EVERY_CASE_TAC >> gvs[jump_to_def] >> rw[] >> simp[],
    (* not terminator + INVOKE *)
    fs[step_inst_def] >>
    BasicProvers.EVERY_CASE_TAC >> gvs[] >>
    imp_res_tac bind_outputs_preserves_params >>
    gvs[merge_callee_state_def],
    (* not terminator + not INVOKE *)
    metis_tac[step_preserves_params]
  ]
QED

Theorem run_block_OK_preserves_params:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ==>
    s'.vs_params = s.vs_params
Proof
  ntac 3 gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[] >>
  rename1 `_ = SOME inst` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    fs[get_instruction_def] >>
  simp[] >>
  Cases_on `step_inst fuel ctx inst s`
  >- (
    rename1 `_ = OK s1` >>
    simp[] >>
    reverse (Cases_on `is_terminator inst.inst_opcode`) >> simp[]
    >- (
      (* non-terminator — IH *)
      strip_tac >>
      `s1.vs_params = s.vs_params` by
        metis_tac[step_inst_OK_preserves_params] >>
      `LENGTH bb.bb_instructions - SUC s.vs_inst_idx < v` by
        decide_tac >>
      first_x_assum drule >>
      disch_then (qspecl_then [`bb`,
        `s1 with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[] >> disch_then drule >> simp[]
    ) >>
    (* terminator — direct *)
    Cases_on `s1.vs_halted` >> simp[] >>
    rw[] >> metis_tac[step_inst_OK_preserves_params]
  )
  >> simp[]
QED

(* step_inst_base preserves vs_allocas for non-ALLOCA opcodes.
   Proof follows same pattern as step_inst_base_OK_preserves_halted
   but needs imp_res_tac for extract_venom_result cases. *)
Triviality extract_venom_result_preserves_allocas[local]:
  !s ov ro rs rr output s'.
    extract_venom_result s ov ro rs rr = SOME (output, s') ==>
    s'.vs_allocas = s.vs_allocas
Proof
  rw[extract_venom_result_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[LET_THM] >>
  gvs[write_memory_with_expansion_def]
QED

Triviality step_inst_base_no_alloca_preserves_allocas[local]:
  !inst (s:venom_state) s'.
    step_inst_base inst s = OK s' /\
    inst.inst_opcode <> ALLOCA ==>
    s'.vs_allocas = s.vs_allocas
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[step_inst_base_def, AllCaseEqs()] >> rw[] >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      update_var_def, AllCaseEqs(), jump_to_def,
      mstore_def, mstore8_def, mload_def, sstore_def, sload_def,
      tstore_def, tload_def, write_memory_with_expansion_def,
      mcopy_def,
      exec_ext_call_def, exec_delegatecall_def,
      exec_create_def] >>
  imp_res_tac extract_venom_result_preserves_allocas >> gvs[update_var_def]
QED

(* FOLDL update_var preserves vs_allocas *)
Triviality foldl_update_var_preserves_allocas[local]:
  !pairs (s:venom_state).
    (FOLDL (\s' (out,val). update_var out val s') s pairs).vs_allocas =
    s.vs_allocas
Proof
  Induct >> simp[] >> Cases >> simp[update_var_def]
QED

(* bind_outputs preserves vs_allocas *)
Triviality bind_outputs_preserves_allocas[local]:
  !outs vals (s:venom_state) s'.
    bind_outputs outs vals s = SOME s' ==> s'.vs_allocas = s.vs_allocas
Proof
  rw[bind_outputs_def] >> BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  simp[foldl_update_var_preserves_allocas]
QED

(* step_inst preserves vs_allocas for non-ALLOCA opcodes *)
Triviality step_inst_no_alloca_preserves_allocas[local]:
  !fuel ctx inst (s:venom_state) s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode <> ALLOCA ==>
    s'.vs_allocas = s.vs_allocas
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* INVOKE *)
    qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
    simp[Once step_inst_def] >>
    BasicProvers.EVERY_CASE_TAC >> gvs[] >>
    strip_tac >>
    imp_res_tac bind_outputs_preserves_allocas >>
    gvs[merge_callee_state_def]
  ) >>
  (* Non-INVOKE: step_inst = step_inst_base *)
  metis_tac[step_inst_non_invoke, step_inst_base_no_alloca_preserves_allocas]
QED

(* run_block preserves vs_allocas when all instructions have no ALLOCA *)
Theorem run_block_no_alloca_preserves_allocas:
  !fuel ctx bb (s:venom_state) s'.
    run_block fuel ctx bb s = OK s' /\
    EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions ==>
    s'.vs_allocas = s.vs_allocas
Proof
  ntac 3 gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[] >>
  rename1 `_ = SOME inst` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    fs[get_instruction_def] >>
  simp[] >>
  `inst.inst_opcode <> ALLOCA` by
    (gvs[get_instruction_def, EVERY_EL] >> metis_tac[EL_MAP]) >>
  Cases_on `step_inst fuel ctx inst s`
  >- (
    rename1 `_ = OK s1` >>
    simp[] >>
    reverse (Cases_on `is_terminator inst.inst_opcode`) >> simp[]
    >- (
      strip_tac >>
      `s1.vs_allocas = s.vs_allocas` by
        metis_tac[step_inst_no_alloca_preserves_allocas] >>
      `LENGTH bb.bb_instructions - SUC s.vs_inst_idx < v` by
        decide_tac >>
      first_x_assum drule >>
      disch_then (qspecl_then [`bb`,
        `s1 with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[] >> disch_then drule >> simp[]
    ) >>
    Cases_on `s1.vs_halted` >> simp[] >>
    rw[] >> metis_tac[step_inst_no_alloca_preserves_allocas]
  )
  >> simp[]
QED

(* Clone block simulation: covers ALL blocks uniformly.
   - OK: clone produces OK with clone_rel_np preserved + current_bb corresponds
   - Halt/Abort: clone produces matching Halt/Abort with shared_globals_np
   - IntRet: if block has RET, clone produces OK at ret_lbl (the key inlining step)
   - Error: trivial *)
Definition clone_block_sim_def:
  clone_block_sim prefix labels ret_lbl output_vars ctx fuel bb bb' sc sd <=>
  case run_block fuel ctx bb sc of
    OK sc' =>
      ?sd'. run_block fuel ctx bb' sd = OK sd' /\
        clone_rel_np prefix labels sc' sd' /\
        sd'.vs_current_bb = STRCAT prefix sc'.vs_current_bb
  | Halt sc' =>
      ?sd'. run_block fuel ctx bb' sd = Halt sd' /\
        shared_globals_np sc' sd'
  | Abort a sc' =>
      ?sd'. run_block fuel ctx bb' sd = Abort a sd' /\
        shared_globals_np sc' sd'
  | IntRet vals sc' =>
      ?sd'. run_block fuel ctx bb' sd = OK sd' /\
        sd'.vs_current_bb = ret_lbl /\
        ~sd'.vs_halted /\
        shared_globals_np sc' sd' /\
        (!i. i < LENGTH vals /\ i < LENGTH output_vars ==>
             lookup_var (EL i output_vars) sd' = SOME (EL i vals))
  | Error e => T
End

(* Helper: chain a block step with a continuation at combined fuel.
   If run_block at fuel f gives OK s' (not halted), and run_function at
   fuel f' from s' gives result r (non-Error), then run_function at
   SUC(f+f') from s gives r. *)
Triviality run_function_chain[local]:
  !ctx fn bb s s' fuel.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block fuel ctx bb s = OK s' /\
    ~s'.vs_halted ==>
    run_function (SUC fuel) ctx fn s = run_function fuel ctx fn s'
Proof
  rpt strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >>
  simp[]
QED

Triviality run_function_extend_fuel[local]:
  !ctx fn bb s sd fuel fuel_k.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block fuel ctx bb s = OK sd /\
    ~sd.vs_halted /\
    terminates (run_function fuel_k ctx fn sd) ==>
    run_function (SUC (fuel + fuel_k)) ctx fn s =
    run_function fuel_k ctx fn sd
Proof
  rpt strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >>
  simp[] >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`] run_block_fuel_mono) >>
  impl_tac >- (rpt strip_tac >> fs[]) >>
  disch_then (qspec_then `fuel_k` (fn th => rewrite_tac[th])) >>
  simp[] >>
  mp_tac (Q.SPECL [`fuel_k`, `ctx`, `fn`, `sd`] run_function_fuel_mono) >>
  simp[] >>
  disch_then (qspec_then `fuel` mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem clone_execution_sim:
  !fuel ctx callee caller_xf prefix ret_lbl frame output_vars args
   s_callee s_clone.
    (* Block lookup + per-block simulation *)
    (!fuel' lbl bb sc sd.
       lookup_block lbl callee.fn_blocks = SOME bb /\
       clone_rel_np prefix (fn_labels callee) sc sd /\
       sc.vs_inst_idx = 0 /\ sd.vs_inst_idx = 0 /\ ~sc.vs_halted /\
       LENGTH args = LENGTH sc.vs_params ==>
       ?bb'. lookup_block (STRCAT prefix lbl) caller_xf.fn_blocks =
               SOME bb' /\
             clone_block_sim prefix (fn_labels callee) ret_lbl output_vars
               ctx fuel' bb bb' sc sd) /\
    (* Frame: clone block OK steps preserve frame vars (callee blocks only) *)
    (!fuel' bb sd sd'.
       (?lbl. MEM lbl (fn_labels callee) /\
              lookup_block (STRCAT prefix lbl) caller_xf.fn_blocks =
                SOME bb) /\
       run_block fuel' ctx bb sd = OK sd' ==>
       !v. frame v ==> lookup_var v sd' = lookup_var v sd) /\
    (* Allocas: clone block OK steps preserve vs_allocas *)
    (!fuel' bb sd sd'.
       (?lbl. MEM lbl (fn_labels callee) /\
              lookup_block (STRCAT prefix lbl) caller_xf.fn_blocks =
                SOME bb) /\
       run_block fuel' ctx bb sd = OK sd' ==>
       sd'.vs_allocas = sd.vs_allocas) /\
    (* State relation *)
    clone_rel_np prefix (fn_labels callee) s_callee s_clone /\
    s_clone.vs_inst_idx = 0 /\ s_callee.vs_inst_idx = 0 /\
    ~s_callee.vs_halted /\
    LENGTH args = LENGTH s_callee.vs_params /\
    s_clone.vs_current_bb = STRCAT prefix s_callee.vs_current_bb ==>
    case run_function fuel ctx callee s_callee of
      IntRet vals s_callee' =>
        ?fuel_clone s_at_ret.
          s_at_ret.vs_current_bb = ret_lbl /\
          s_at_ret.vs_inst_idx = 0 /\
          ~s_at_ret.vs_halted /\
          shared_globals_np s_callee' s_at_ret /\
          s_at_ret.vs_params = s_clone.vs_params /\
          s_at_ret.vs_allocas = s_clone.vs_allocas /\
          (!v. frame v ==> lookup_var v s_at_ret = lookup_var v s_clone) /\
          (!i. i < LENGTH vals /\ i < LENGTH output_vars ==>
               lookup_var (EL i output_vars) s_at_ret =
               SOME (EL i vals)) /\
          !fuel_k.
            terminates (run_function fuel_k ctx caller_xf s_at_ret) ==>
            run_function (fuel_clone + fuel_k) ctx caller_xf s_clone =
            run_function fuel_k ctx caller_xf s_at_ret
    | Halt s_callee' =>
        ?fuel' s_clone'.
          run_function fuel' ctx caller_xf s_clone = Halt s_clone' /\
          shared_globals_np s_callee' s_clone'
    | Abort a s_callee' =>
        ?fuel' s_clone'.
          run_function fuel' ctx caller_xf s_clone = Abort a s_clone' /\
          shared_globals_np s_callee' s_clone'
    | Error e => T
    | OK _ => T
Proof
  Induct_on `fuel`
  >- (rpt strip_tac >> simp[Once run_function_def])
  >>
  rpt strip_tac >>
  Cases_on `lookup_block s_callee.vs_current_bb callee.fn_blocks`
  >- simp[Once run_function_def]
  >>
  rename1 `lookup_block _ _ = SOME bb` >>
  first_assum (qspecl_then [`fuel`, `s_callee.vs_current_bb`, `bb`,
    `s_callee`, `s_clone`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `lookup_block (STRCAT prefix _) _ = SOME bb_clone` >>
  simp[Once run_function_def] >>
  Cases_on `run_block fuel ctx bb s_callee`
  >| [
    (* 1. OK *)
    gvs[clone_block_sim_def] >>
    rename1 `run_block _ _ bb s_callee = OK sc'` >>
    Cases_on `sc'.vs_halted` >> simp[]
    >- (
      (* halted *)
      `sd'.vs_halted` by fs[clone_rel_np_def] >>
      qexistsl_tac [`SUC fuel`, `sd'`] >>
      ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
      fs[clone_rel_np_def]
    )
    >- (
      (* not halted *)
      `~sd'.vs_halted` by fs[clone_rel_np_def] >>
      `sc'.vs_inst_idx = 0` by imp_res_tac run_block_OK_inst_idx_0 >>
      `sd'.vs_inst_idx = 0` by imp_res_tac run_block_OK_inst_idx_0 >>
      (* Frame for this block step: sd' preserves frame vars from s_clone *)
      `!v. frame v ==> lookup_var v sd' = lookup_var v s_clone` by (
        qpat_x_assum `!fuel' bb sd sd'. _ ==> !v. _` (qspecl_then
          [`fuel`, `bb_clone`, `s_clone`, `sd'`] mp_tac) >>
        simp[] >> disch_then match_mp_tac >>
        qexists_tac `s_callee.vs_current_bb` >>
        conj_tac >- (imp_res_tac lookup_block_mem_fn_labels >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC
      ) >>
      `sc'.vs_params = s_callee.vs_params` by
        metis_tac[run_block_OK_preserves_params] >>
      (* Allocas: block step preserves vs_allocas *)
      `sd'.vs_allocas = s_clone.vs_allocas` by (
        qpat_x_assum `!fuel' bb sd sd'. _ ==> sd'.vs_allocas = sd.vs_allocas`
          (qspecl_then [`fuel`, `bb_clone`, `s_clone`, `sd'`] mp_tac) >>
        simp[] >> disch_then match_mp_tac >>
        qexists_tac `s_callee.vs_current_bb` >>
        conj_tac >- (imp_res_tac lookup_block_mem_fn_labels >>
                      first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC
      ) >>
      first_x_assum (qspecl_then [`ctx`, `callee`, `caller_xf`, `prefix`,
        `ret_lbl`, `frame`, `output_vars`, `args`, `sc'`, `sd'`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
      DISCH_TAC >>
      Cases_on `run_function fuel ctx callee sc'` >> gvs[]
      >- (
        (* Halt from IH *)
        rename1 `run_function fuel_ih ctx caller_xf sd' = Halt s_ih` >>
        qexistsl_tac [`SUC (fuel + fuel_ih)`, `s_ih`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        mp_tac (Q.SPECL [`ctx`, `caller_xf`, `bb_clone`, `s_clone`,
          `sd'`, `fuel`, `fuel_ih`] run_function_extend_fuel) >>
        simp[terminates_def]
      )
      >- (
        (* Abort from IH *)
        rename1 `run_function fuel_ih ctx caller_xf sd' = Abort _ s_ih` >>
        qexistsl_tac [`SUC (fuel + fuel_ih)`, `s_ih`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        mp_tac (Q.SPECL [`ctx`, `caller_xf`, `bb_clone`, `s_clone`,
          `sd'`, `fuel`, `fuel_ih`] run_function_extend_fuel) >>
        simp[terminates_def]
      )
      >- (
        (* IntRet from IH — compose frame: s_clone → sd' → s_at_ret *)
        `!v. frame v ==> lookup_var v s_at_ret = lookup_var v s_clone` by
          metis_tac[] >>
        `s_at_ret.vs_params = s_clone.vs_params` by
          metis_tac[run_block_OK_preserves_params] >>
        `s_at_ret.vs_allocas = s_clone.vs_allocas` by
          metis_tac[] >>
        rpt strip_tac >>
        qexistsl_tac [`SUC fuel + fuel_clone`, `s_at_ret`] >>
        conj_tac >- REFL_TAC >>
        simp[] >>
        rpt strip_tac >>
        first_x_assum (qspec_then `fuel_k` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        strip_tac >>
        `terminates (run_function (fuel_clone + fuel_k) ctx caller_xf sd')` by (
          pop_assum (fn eq => rewrite_tac[eq]) >>
          first_assum ACCEPT_TAC
        ) >>
        mp_tac (Q.SPECL [`ctx`, `caller_xf`, `bb_clone`, `s_clone`,
          `sd'`, `fuel`, `fuel_clone + fuel_k`] run_function_extend_fuel) >>
        simp[] >> strip_tac >>
        `fuel_clone + (fuel_k + SUC fuel) =
         SUC (fuel + (fuel_clone + fuel_k))` by decide_tac >>
        pop_assum (fn eq => ONCE_REWRITE_TAC[eq]) >>
        qpat_x_assum `run_function (SUC _) _ _ s_clone = _`
          (fn th => REWRITE_TAC[th]) >>
        first_assum ACCEPT_TAC
      )
    ),
    (* 2. Halt *)
    gvs[clone_block_sim_def] >>
    qexistsl_tac [`SUC fuel`, `sd'`] >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[],
    (* 3. Abort *)
    gvs[clone_block_sim_def] >>
    qexistsl_tac [`SUC fuel`, `sd'`] >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[],
    (* 4. IntRet — output vars now come from clone_block_sim_def *)
    fs[clone_block_sim_def] >> pop_assum strip_assume_tac >>
    `sd'.vs_inst_idx = 0` by imp_res_tac run_block_OK_inst_idx_0 >>
    `sd'.vs_params = s_clone.vs_params` by
      imp_res_tac run_block_OK_preserves_params >>
    (* Frame: block step preserves frame vars *)
    `!v. frame v ==> lookup_var v sd' = lookup_var v s_clone` by (
      qpat_x_assum `!fuel' bb sd sd'. _ ==> !v. _` (qspecl_then
        [`fuel`, `bb_clone`, `s_clone`, `sd'`] mp_tac) >>
      simp[] >> disch_then match_mp_tac >>
      qexists_tac `s_callee.vs_current_bb` >>
      conj_tac >- (imp_res_tac lookup_block_mem_fn_labels >> first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC
    ) >>
    (* Allocas: block step preserves vs_allocas *)
    `sd'.vs_allocas = s_clone.vs_allocas` by (
      qpat_x_assum `!fuel' bb sd sd'. _ ==> sd'.vs_allocas = sd.vs_allocas`
        (qspecl_then [`fuel`, `bb_clone`, `s_clone`, `sd'`] mp_tac) >>
      simp[] >> disch_then match_mp_tac >>
      qexists_tac `s_callee.vs_current_bb` >>
      conj_tac >- (imp_res_tac lookup_block_mem_fn_labels >> first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC
    ) >>
    qexistsl_tac [`SUC fuel`, `sd'`] >>
    simp[] >>
    rpt strip_tac >>
    mp_tac (Q.SPECL [`ctx`, `caller_xf`, `bb_clone`, `s_clone`,
      `sd'`, `fuel`, `fuel_k`] run_function_extend_fuel) >>
    simp[] >>
    `SUC (fuel + fuel_k) = fuel_k + SUC fuel` by decide_tac >>
    simp[],
    (* 5. Error *)
    gvs[clone_block_sim_def]
  ]
QED

(* Helper: args_preserved is maintained after a block step.
   If frame vars are preserved (lookup_var v sd' = lookup_var v sd)
   and params are preserved (sc'.vs_params = sc.vs_params),
   then args_preserved holds for sd'/sc' given it held for sd/sc. *)
Triviality args_preserved_maintained:
  (!v. frame v ==> lookup_var v sd' = lookup_var v sd) /\
  (!i. i < LENGTH args ==>
       ?v. EL i invoke_ops = Var v /\ frame v \/
           ?w. EL i invoke_ops = Lit w) /\
  (!i. i < LENGTH invoke_ops /\ i < LENGTH args ==>
       eval_operand (EL i invoke_ops) sd = SOME (EL i args) /\
       EL i sc.vs_params = EL i args) /\
  sc'.vs_params = sc.vs_params ==>
  (!i. i < LENGTH invoke_ops /\ i < LENGTH args ==>
       eval_operand (EL i invoke_ops) sd' = SOME (EL i args) /\
       EL i sc'.vs_params = EL i args)
Proof
  rpt strip_tac >> metis_tac[eval_operand_def]
QED

(* Extended clone execution sim: threads an args_preserved condition.
   This is needed because PARAM blocks (rewritten to ASSIGN) read invoke_ops
   from the clone state, and we need those values to match the callee's params.
   The args_preserved condition is invariant: clone blocks write only to
   STRCAT prefix vars, while invoke_ops reference unprefixed caller vars. *)
Theorem clone_execution_sim_ext:
  !fuel ctx callee caller_xf prefix ret_lbl frame output_vars
   invoke_ops args s_callee s_clone.
    (* Block lookup + per-block simulation (with args_preserved) *)
    (!fuel' lbl bb sc sd.
       lookup_block lbl callee.fn_blocks = SOME bb /\
       clone_rel_np prefix (fn_labels callee) sc sd /\
       sc.vs_inst_idx = 0 /\ sd.vs_inst_idx = 0 /\ ~sc.vs_halted /\
       LENGTH args = LENGTH sc.vs_params /\
       (!i. i < LENGTH invoke_ops /\ i < LENGTH args ==>
            eval_operand (EL i invoke_ops) sd = SOME (EL i args) /\
            EL i sc.vs_params = EL i args) ==>
       ?bb'. lookup_block (STRCAT prefix lbl) caller_xf.fn_blocks =
               SOME bb' /\
             clone_block_sim prefix (fn_labels callee) ret_lbl output_vars
               ctx fuel' bb bb' sc sd) /\
    (* Frame: clone block OK steps preserve frame vars (callee blocks only) *)
    (!fuel' bb sd sd'.
       (?lbl. MEM lbl (fn_labels callee) /\
              lookup_block (STRCAT prefix lbl) caller_xf.fn_blocks =
                SOME bb) /\
       run_block fuel' ctx bb sd = OK sd' ==>
       !v. frame v ==> lookup_var v sd' = lookup_var v sd) /\
    (* Allocas: clone block OK steps preserve vs_allocas *)
    (!fuel' bb sd sd'.
       (?lbl. MEM lbl (fn_labels callee) /\
              lookup_block (STRCAT prefix lbl) caller_xf.fn_blocks =
                SOME bb) /\
       run_block fuel' ctx bb sd = OK sd' ==>
       sd'.vs_allocas = sd.vs_allocas) /\
    (* Args preserved by frame *)
    (!i. i < LENGTH args ==>
         ?v. EL i invoke_ops = Var v /\ frame v \/
             ?w. EL i invoke_ops = Lit w) /\
    (* State relation *)
    clone_rel_np prefix (fn_labels callee) s_callee s_clone /\
    s_clone.vs_inst_idx = 0 /\ s_callee.vs_inst_idx = 0 /\
    ~s_callee.vs_halted /\
    s_clone.vs_current_bb = STRCAT prefix s_callee.vs_current_bb /\
    LENGTH args = LENGTH s_callee.vs_params /\
    (* Initial args_preserved *)
    (!i. i < LENGTH invoke_ops /\ i < LENGTH args ==>
         eval_operand (EL i invoke_ops) s_clone = SOME (EL i args) /\
         EL i s_callee.vs_params = EL i args) ==>
    case run_function fuel ctx callee s_callee of
      OK v1 => T
    | Halt s_callee'' =>
        ?fuel' s_clone'.
          run_function fuel' ctx caller_xf s_clone = Halt s_clone' /\
          shared_globals_np s_callee'' s_clone'
    | Abort a s_callee' =>
        ?fuel' s_clone'.
          run_function fuel' ctx caller_xf s_clone = Abort a s_clone' /\
          shared_globals_np s_callee' s_clone'
    | IntRet vals s_callee' =>
        ?fuel_clone s_at_ret.
          s_at_ret.vs_current_bb = ret_lbl /\
          s_at_ret.vs_inst_idx = 0 /\
          ~s_at_ret.vs_halted /\
          shared_globals_np s_callee' s_at_ret /\
          s_at_ret.vs_params = s_clone.vs_params /\
          s_at_ret.vs_allocas = s_clone.vs_allocas /\
          (!v. frame v ==> lookup_var v s_at_ret = lookup_var v s_clone) /\
          (!i. i < LENGTH vals /\ i < LENGTH output_vars ==>
               lookup_var (EL i output_vars) s_at_ret =
               SOME (EL i vals)) /\
          !fuel_k.
            terminates (run_function fuel_k ctx caller_xf s_at_ret) ==>
            run_function (fuel_clone + fuel_k) ctx caller_xf s_clone =
            run_function fuel_k ctx caller_xf s_at_ret
    | Error e => T
Proof
  Induct_on `fuel`
  >- (rpt strip_tac >> simp[Once run_function_def])
  >>
  rpt strip_tac >>
  Cases_on `lookup_block s_callee.vs_current_bb callee.fn_blocks`
  >- simp[Once run_function_def]
  >>
  rename1 `lookup_block _ _ = SOME bb` >>
  (* Apply block premise with args_preserved *)
  first_assum (qspecl_then [`fuel`, `s_callee.vs_current_bb`, `bb`,
    `s_callee`, `s_clone`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `lookup_block (STRCAT prefix _) _ = SOME bb_clone` >>
  simp[Once run_function_def] >>
  Cases_on `run_block fuel ctx bb s_callee`
  >| [
    (* 1. OK *)
    gvs[clone_block_sim_def] >>
    rename1 `run_block _ _ bb s_callee = OK sc'` >>
    Cases_on `sc'.vs_halted` >> simp[]
    >- (
      (* halted *)
      `sd'.vs_halted` by fs[clone_rel_np_def] >>
      qexistsl_tac [`SUC fuel`, `sd'`] >>
      ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
      fs[clone_rel_np_def]
    )
    >- (
      (* not halted — apply IH *)
      `~sd'.vs_halted` by fs[clone_rel_np_def] >>
      `sc'.vs_inst_idx = 0` by imp_res_tac run_block_OK_inst_idx_0 >>
      `sd'.vs_inst_idx = 0` by imp_res_tac run_block_OK_inst_idx_0 >>
      (* Frame: sd' preserves frame vars from s_clone *)
      `!v. frame v ==> lookup_var v sd' = lookup_var v s_clone` by (
        qpat_x_assum `!fuel' bb sd sd'. _ ==> !v. _` (qspecl_then
          [`fuel`, `bb_clone`, `s_clone`, `sd'`] mp_tac) >>
        simp[] >> disch_then match_mp_tac >>
        qexists_tac `s_callee.vs_current_bb` >>
        conj_tac >- (imp_res_tac lookup_block_mem_fn_labels >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC
      ) >>
      (* args_preserved for sd': invoke_ops eval same as s_clone *)
      `sc'.vs_params = s_callee.vs_params` by
        imp_res_tac run_block_OK_preserves_params >>
      `LENGTH args = LENGTH sc'.vs_params` by metis_tac[] >>
      `!i. i < LENGTH invoke_ops /\ i < LENGTH args ==>
           eval_operand (EL i invoke_ops) sd' = SOME (EL i args) /\
           EL i sc'.vs_params = EL i args` by (
        rpt strip_tac >> metis_tac[eval_operand_def]
      ) >>
      (* Allocas: block step preserves vs_allocas *)
      `sd'.vs_allocas = s_clone.vs_allocas` by (
        qpat_x_assum `!fuel' bb sd sd'. _ ==> sd'.vs_allocas = sd.vs_allocas`
          (qspecl_then [`fuel`, `bb_clone`, `s_clone`, `sd'`] mp_tac) >>
        simp[] >> disch_then match_mp_tac >>
        qexists_tac `s_callee.vs_current_bb` >>
        conj_tac >- (imp_res_tac lookup_block_mem_fn_labels >>
                      first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC
      ) >>
      (* Apply IH *)
      first_x_assum (qspecl_then [`ctx`, `callee`, `caller_xf`, `prefix`,
        `ret_lbl`, `frame`, `output_vars`, `invoke_ops`, `args`,
        `sc'`, `sd'`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
      DISCH_TAC >>
      Cases_on `run_function fuel ctx callee sc'` >> gvs[]
      >- (
        (* Halt from IH *)
        rename1 `run_function fuel_ih ctx caller_xf sd' = Halt s_ih` >>
        qexistsl_tac [`SUC (fuel + fuel_ih)`, `s_ih`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        mp_tac (Q.SPECL [`ctx`, `caller_xf`, `bb_clone`, `s_clone`,
          `sd'`, `fuel`, `fuel_ih`] run_function_extend_fuel) >>
        simp[terminates_def]
      )
      >- (
        (* Abort from IH *)
        rename1 `run_function fuel_ih ctx caller_xf sd' = Abort _ s_ih` >>
        qexistsl_tac [`SUC (fuel + fuel_ih)`, `s_ih`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        mp_tac (Q.SPECL [`ctx`, `caller_xf`, `bb_clone`, `s_clone`,
          `sd'`, `fuel`, `fuel_ih`] run_function_extend_fuel) >>
        simp[terminates_def]
      )
      >- (
        (* IntRet from IH — compose frame: s_clone → sd' → s_at_ret *)
        `!v. frame v ==> lookup_var v s_at_ret = lookup_var v s_clone` by
          metis_tac[] >>
        `s_at_ret.vs_params = s_clone.vs_params` by
          metis_tac[run_block_OK_preserves_params] >>
        `s_at_ret.vs_allocas = s_clone.vs_allocas` by
          metis_tac[] >>
        rpt strip_tac >>
        qexistsl_tac [`SUC fuel + fuel_clone`, `s_at_ret`] >>
        conj_tac >- REFL_TAC >>
        simp[] >>
        rpt strip_tac >>
        first_x_assum (qspec_then `fuel_k` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        strip_tac >>
        `terminates (run_function (fuel_clone + fuel_k) ctx caller_xf sd')` by (
          pop_assum (fn eq => rewrite_tac[eq]) >>
          first_assum ACCEPT_TAC
        ) >>
        mp_tac (Q.SPECL [`ctx`, `caller_xf`, `bb_clone`, `s_clone`,
          `sd'`, `fuel`, `fuel_clone + fuel_k`] run_function_extend_fuel) >>
        simp[] >> strip_tac >>
        `fuel_clone + (fuel_k + SUC fuel) =
         SUC (fuel + (fuel_clone + fuel_k))` by decide_tac >>
        pop_assum (fn eq => ONCE_REWRITE_TAC[eq]) >>
        qpat_x_assum `run_function (SUC _) _ _ s_clone = _`
          (fn th => REWRITE_TAC[th]) >>
        first_assum ACCEPT_TAC
      )
    ),
    (* 2. Halt *)
    gvs[clone_block_sim_def] >>
    qexistsl_tac [`SUC fuel`, `sd'`] >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[],
    (* 3. Abort *)
    gvs[clone_block_sim_def] >>
    qexistsl_tac [`SUC fuel`, `sd'`] >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[],
    (* 4. IntRet — output vars from clone_block_sim *)
    fs[clone_block_sim_def] >> pop_assum strip_assume_tac >>
    `sd'.vs_inst_idx = 0` by imp_res_tac run_block_OK_inst_idx_0 >>
    `sd'.vs_params = s_clone.vs_params` by
      imp_res_tac run_block_OK_preserves_params >>
    (* Frame: block step preserves frame vars *)
    `!v. frame v ==> lookup_var v sd' = lookup_var v s_clone` by (
      qpat_x_assum `!fuel' bb sd sd'. _ ==> !v. _` (qspecl_then
        [`fuel`, `bb_clone`, `s_clone`, `sd'`] mp_tac) >>
      simp[] >> disch_then match_mp_tac >>
      qexists_tac `s_callee.vs_current_bb` >>
      conj_tac >- (imp_res_tac lookup_block_mem_fn_labels >> first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC
    ) >>
    (* Allocas: block step preserves vs_allocas *)
    `sd'.vs_allocas = s_clone.vs_allocas` by (
      qpat_x_assum `!fuel' bb sd sd'. _ ==> sd'.vs_allocas = sd.vs_allocas`
        (qspecl_then [`fuel`, `bb_clone`, `s_clone`, `sd'`] mp_tac) >>
      simp[] >> disch_then match_mp_tac >>
      qexists_tac `s_callee.vs_current_bb` >>
      conj_tac >- (imp_res_tac lookup_block_mem_fn_labels >> first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC
    ) >>
    qexistsl_tac [`SUC fuel`, `sd'`] >>
    simp[] >>
    rpt strip_tac >>
    mp_tac (Q.SPECL [`ctx`, `caller_xf`, `bb_clone`, `s_clone`,
      `sd'`, `fuel`, `fuel_k`] run_function_extend_fuel) >>
    simp[] >>
    `SUC (fuel + fuel_k) = fuel_k + SUC fuel` by decide_tac >>
    simp[],
    (* 5. Error *)
    gvs[clone_block_sim_def]
  ]
QED

val _ = export_theory();
