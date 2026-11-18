(* Parse the six dynamic peak-memory headers without asserting them. *)
Theory peakMemoryHeaders
Ancestors
  vfmCalldataBound vfmExecution vfmExecutionProp vfmState vfmContext
  vfmConstants vfmBuffer
  fmpLowerSequenceExec venomLayout
  dallocaCalldata rawCallCalldataDalloca
  dallocaCreateCopy dallocaCreateBlueprint dallocaCreateGeometry dallocaBounds
  builtinSystem builtinCreate emitHelper emitHelperProps
  exprLoweringProps loweringStateRelDefs compileEnv fragExec
  loweringCallBudgetHistory loweringCallBudgetBounds
  loweringRuntimeCorrect loweringMemCorrect loweringPtrCorrect
  vyperLoweringCorrect compileVyper vyperCompiler vyperInterpreter e2eDefs
  o1PassContract unitMemInv memSafeRun ptrSafeRun
  contextRawReachable contextCodegenRel
  ptrDiscipline lowerDloadDefs stackPlanGen
  venomExecSemantics venomInst venomState
  arithmetic list rich_list pair words finite_map

val _ = Parse.hide "body";
val _ = Parse.hide "tops";

(*
 * 1. [PEAK-MEMORY-TO-OUT-OF-GAS BRIDGE — raw_call msg.data path]
 *
 * Relates the EVM frame's paid-memory / calldata invariant (calldata_bounded es)
 * and the Venom dynamic-region invariant (fmp_room ctx func s, with separate
 * optimized floor cp_fmp and raw floor w2n fmp tracked by fmp_frontier_rel) at
 * a non-delegate raw_call(msg.data) dynamic allocation site:
 *   - Any EVM memory expansion reaching an endpoint >= 2 ** 64 has
 *     c.msgParams.gasLimit < memory_cost endpoint and exceeds remaining frame
 *     gas c.msgParams.gasLimit - c.gasUsed, forcing EVM out-of-gas.
 *   - When the active Venom memory is below 2 ** 254, the msg.data DALLOCA of
 *     ceil32 (LENGTH s.vs_call_ctx.cc_calldata) does not wrap in either the
 *     raw frontier s.vs_fmp or the lowered runner lo, preserves
 *     fmp_frontier_rel across the pending allocation, and restores fmp_room
 *     after CALLDATACOPY (covering both zero-length and positive-length
 *     msg.data writes without circularly assuming no-wrap).
 *)
val raw_call_msg_data_peak_memory_oog_bridge_quote : term = “
  !ctx func (cp_fmp:num) (fmp:bytes32) (lo:num) (endpoint:num)
   (es:execution_state) (c:context) rb rest (s:venom_state).
    wf_state es /\ calldata_bounded es /\
    es.contexts = (c, rb) :: rest /\
    s.vs_call_ctx.cc_calldata = vfmBuffer$buffer_to_list c.msgParams.data /\
    s.vs_initial_fmp = fmp /\
    fmp_room ctx func s /\
    fmp_frontier_rel cp_fmp (w2n fmp) lo s.vs_fmp ==>
    LENGTH s.vs_call_ctx.cc_calldata < 2 ** 64 /\
    c.msgParams.gasLimit < 2 ** 64 /\
    buffer_length c.memory < 2 ** 64 /\
    (2 ** 64 <= endpoint ==>
     c.msgParams.gasLimit < memory_cost endpoint /\
     c.msgParams.gasLimit - c.gasUsed <
       memory_expansion_cost (buffer_length c.memory)
         (word_size endpoint * 32)) /\
    ((ctx_has_dalloca ctx \/
      EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func)) /\
     LENGTH s.vs_memory < 2 ** 254 ==>
     w2n s.vs_fmp +
       venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
       dimword (:256) /\
     lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
       dimword (:256) /\
     fmp_frontier_rel cp_fmp (w2n fmp)
       (lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))
       (s.vs_fmp +
        n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))) /\
     fmp_room ctx func
       ((write_memory_with_expansion (w2n s.vs_fmp)
           s.vs_call_ctx.cc_calldata s) with
        vs_fmp :=
          s.vs_fmp +
          n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))))
”;

(*
 * 2. [COMPILER CONSUMER — raw_call msg.data path]
 *
 * Compiler consumer for compile_msg_data_to_memory (the CALLDATASIZE, DALLOCA,
 * CALLDATACOPY sequence emitted by non-delegate raw_call forwarding msg.data).
 * Consumes raw_call_msg_data_peak_memory_oog_bridge to discharge the DALLOCA
 * no-wrap, lowered runner no-wrap, fmp_frontier_rel, and stmt_state_rel
 * obligations from the EVM frame invariant calldata_bounded es and the
 * statement-level state relation stmt_state_rel H ctx func cenv cx vy s.
 *)
val compile_msg_data_to_memory_peak_memory_consumer_quote : term = “
  !H ctx func cenv cx vy (cp_fmp:num) (lo:num)
   (es:execution_state) (c:context) rb rest
   (sa:compile_state) (ptr:operand) (len:operand) (sb:compile_state)
   (s:venom_state).
    compile_msg_data_to_memory sa = ((ptr, len), sb) /\
    fn_has_code sa sb func /\
    stmt_state_rel H ctx func cenv cx vy s /\
    local_ptrs_reserved cenv sa /\
    wf_state es /\ calldata_bounded es /\
    es.contexts = (c, rb) :: rest /\
    s.vs_call_ctx.cc_calldata = vfmBuffer$buffer_to_list c.msgParams.data /\
    fmp_frontier_rel cp_fmp (w2n s.vs_initial_fmp) lo s.vs_fmp /\
    LENGTH s.vs_memory < 2 ** 254 ==>
    ?t.
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel H ctx func cenv cx vy t /\
      eval_operand ptr t = SOME s.vs_fmp /\
      eval_operand len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
      w2n s.vs_fmp +
        venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
        dimword (:256) /\
      lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
        dimword (:256) /\
      fmp_frontier_rel cp_fmp (w2n s.vs_initial_fmp)
        (lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))
        t.vs_fmp /\
      t.vs_fmp =
        s.vs_fmp +
        n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata)) /\
      t.vs_memory =
        (write_memory_with_expansion (w2n s.vs_fmp)
          s.vs_call_ctx.cc_calldata s).vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
”;

(*
 * 3. Dynamic peak-memory site statement for create_copy_of
 *    (second compile_alloc_dynamic form: compile_create_copy).
 *
 * Connects the EXTCODESIZE / ASSERT / preamble / ADD / DALLOCA prefix and
 * MSTORE / EXTCODECOPY / CREATE buffer preparation with fmp_room and
 * fmp_frontier_rel (separate optimized floor cp_fmp and raw floor
 * w2n pre.vs_initial_fmp).
 *)
val create_copy_of_peak_memory_step_quote : term = “
  !ctx func (cp_fmp:num) (lo:num)
   target sa code a1 a2 shifted a3 preamble a4 size a5
   alloc_ptr a6 a7 code_dst a8 a9 buf a10 len sc
   (s0:venom_state) (addr:bytes32) (pre:venom_state) (t:venom_state).
    emit_op EXTCODESIZE [target] sa = (code, a1) /\
    emit_void ASSERT [code] a1 = ((), a2) /\
    emit_op SHL [Lit 56w; code] a2 = (shifted, a3) /\
    emit_op OR [Lit 0x620000003d81600b3d39f3w; shifted] a3 = (preamble, a4) /\
    emit_op ADD [code; Lit 32w] a4 = (size, a5) /\
    compile_alloc_dynamic size a5 = (alloc_ptr, a6) /\
    emit_void MSTORE [alloc_ptr; preamble] a6 = ((), a7) /\
    emit_op ADD [alloc_ptr; Lit 32w] a7 = (code_dst, a8) /\
    emit_void EXTCODECOPY [target; code_dst; Lit 0w; code] a8 = ((), a9) /\
    emit_op ADD [alloc_ptr; Lit 21w] a9 = (buf, a10) /\
    emit_op ADD [code; Lit 11w] a10 = (len, sc) /\
    eval_operand target s0 = SOME addr /\
    LENGTH (lookup_account (w2w addr) s0.vs_accounts).code <= 24576 /\
    run_inst_seq (emitted_insts sa a5) s0 = OK pre /\
    run_inst_seq (emitted_insts a5 sc) pre = OK t /\
    (ctx_has_dalloca ctx \/
     EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func)) /\
    fmp_room ctx func pre /\
    fmp_frontier_rel cp_fmp (w2n pre.vs_initial_fmp) lo pre.vs_fmp /\
    LENGTH pre.vs_memory < 2 ** 254 ==>
    ?sz create_len.
      eval_operand size pre = SOME sz /\
      eval_operand buf t = SOME (pre.vs_fmp + 21w) /\
      eval_operand len t = SOME create_len /\
      sz = create_len + 21w /\
      w2n sz <= 24608 /\
      w2n pre.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256) /\
      lo + venomLayout$ceil32 (w2n sz) < dimword (:256) /\
      fmp_frontier_rel cp_fmp (w2n pre.vs_initial_fmp)
        (lo + venomLayout$ceil32 (w2n sz)) t.vs_fmp /\
      fmp_room ctx func t /\
      t.vs_fmp = pre.vs_fmp + n2w (venomLayout$ceil32 (w2n sz))
”;

(*
 * 4. Dynamic peak-memory site statement for create_from_blueprint
 *    (third compile_alloc_dynamic form: compile_create_blueprint).
 *
 * Connects the signed blueprint check prefix, constructor-argument length
 * staging, total-extent ADD + DALLOCA, EXTCODECOPY, and optional dynamic
 * argument copy with fmp_room and fmp_frontier_rel.
 *)
val create_from_blueprint_peak_memory_step_quote : term = “
  !ctx func (cp_fmp:num) (lo:num)
   target offset ca code_op cb (s0:venom_state) (s1:venom_state)
   (s2:venom_state) args_len (args:bytes32) sa size sm alloc_ptr sn
   se sc args_ptr (pre:venom_state) (t:venom_state).
    compile_create_blueprint_check T target offset ca = (code_op, cb) /\
    run_inst_seq (emitted_insts ca cb) s0 = OK s1 /\
    eval_operand code_op s2 = eval_operand code_op s1 /\
    eval_operand args_len s2 = SOME args /\ w2n args < 2 ** 64 /\
    emit_op ADD [code_op; args_len] sa = (size, sm) /\
    run_inst_seq (emitted_insts sa sm) s2 = OK pre /\
    compile_alloc_dynamic size sm = (alloc_ptr, sn) /\
    emit_void EXTCODECOPY [target; alloc_ptr; offset; code_op] sn = ((), se) /\
    (if args_len = Lit 0w then sc = se else
       ?args_dest sx.
         emit_op ADD [alloc_ptr; code_op] se = (args_dest, sx) /\
         compile_copy_memory_dynamic args_dest args_ptr args_len sx =
           ((), sc)) /\
    run_inst_seq (emitted_insts sm sc) pre = OK t /\
    (ctx_has_dalloca ctx \/
     EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func)) /\
    fmp_room ctx func pre /\
    fmp_frontier_rel cp_fmp (w2n pre.vs_initial_fmp) lo pre.vs_fmp /\
    LENGTH pre.vs_memory < 2 ** 254 ==>
    ?sz.
      eval_operand size pre = SOME sz /\
      eval_operand size t = SOME sz /\
      eval_operand alloc_ptr t = SOME pre.vs_fmp /\
      venomLayout$ceil32 (w2n sz) <= 2 ** 255 + 2 ** 64 /\
      w2n pre.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256) /\
      lo + venomLayout$ceil32 (w2n sz) < dimword (:256) /\
      fmp_frontier_rel cp_fmp (w2n pre.vs_initial_fmp)
        (lo + venomLayout$ceil32 (w2n sz)) t.vs_fmp /\
      fmp_room ctx func t /\
      t.vs_fmp = pre.vs_fmp + n2w (venomLayout$ceil32 (w2n sz))
”;

(*
 * 5. Whole-run dynamic FMP and DALLOCA no-wrap bound across all three
 *    compile_alloc_dynamic forms (raw_call with msg.data, create_copy_of,
 *    create_from_blueprint), replacing the rejected 2026-11-17 static
 *    allocation-budget entry interface (ac0e363f9).
 *
 * Uses separate optimized (cp.cp_initial_fmp on vs) and raw (fmp on vs0 via
 * raw_variant fmp vs vs0) entry floors, tracks fmp_frontier_rel from
 * cp.cp_initial_fmp and w2n fmp, and carries the storage-correspondence and
 * non-exemption premises required by lower_vyper_runtime_unit_allocation_history.
 *)
val lower_vyper_runtime_unit_dynamic_peak_memory_bound_quote : term = “
  !tops rpolicy (unit:compilation_unit) cp am tx ret (fmp:bytes32) vs vs0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    generate_context_plan unit.cu_context = SOME cp /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs0.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp /\
    vs.vs_fmp = n2w cp.cp_initial_fmp /\
    cp.cp_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    raw_variant fmp vs vs0 /\
    LENGTH vs0.vs_outcomes < 2 ** 64 /\
    (!marks.
       call_storage_ok am tx vs0.vs_outcomes
         (gas_explicit marks vs0.vs_gas_readings)) /\
    (!marks.
       ~source_exempt tops
         (call_external (SOME vs0.vs_outcomes)
           (gas_explicit marks vs0.vs_gas_readings) am tx)) /\
    outcomes_accounts_typed (SOME vs0.vs_outcomes) /\
    LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn i s.
      raw_reachable vs0 unit.cu_context fn i s ==>
      s.vs_initial_fmp = fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
      fmp_frontier_rel cp.cp_initial_fmp (w2n fmp)
        (cp.cp_initial_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
      (i.inst_opcode = DALLOCA ==>
       !sz_op sz.
         i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
         w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))
”;

(*
 * 6. Additive runtime memory and pointer-discipline companion on the raw
 *    variant vs0, preserving the gated lower_vyper_runtime_unit_memory_ok
 *    and lower_vyper_runtime_unit_ptr_taint theorems untouched for the first
 *    supported_program result.
 *)
val lower_vyper_runtime_unit_memory_ptr_dynamic_companion_quote : term = “
  !tops rpolicy (unit:compilation_unit) am tx (fmp:bytes32) vs vs0 fn lbl D.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    initial_venom_state_rel tops am tx vs /\
    raw_variant fmp vs vs0 /\
    (!f i s.
       raw_reachable vs0 unit.cu_context f i s ==>
       w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
       (i.inst_opcode = DALLOCA ==>
        !sz_op sz.
          i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
          w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>)) /\
    (!fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>)) ==>
    raw_unit_memory_ok unit.cu_context vs0 /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved 0 unit.cu_context /\
    ptr_discipline 0 unit.cu_context vs0 /\
    taint_within D unit.cu_context vs0
”;

val check_peak_memory_header = fn (name, tm) =>
  let
    val fv = free_vars tm
  in
    if type_of tm <> bool then
      raise mk_HOL_ERR "peakMemoryHeaders" name "not boolean"
    else if not (null fv) then
      raise mk_HOL_ERR "peakMemoryHeaders" name
        ("free vars: " ^ String.concatWith ", " (map (#1 o dest_var) fv))
    else (name, tm)
  end;

val peak_memory_headers : (string * term) list =
  map check_peak_memory_header
    [("raw_call_msg_data_peak_memory_oog_bridge",
      raw_call_msg_data_peak_memory_oog_bridge_quote),
     ("compile_msg_data_to_memory_peak_memory_consumer",
      compile_msg_data_to_memory_peak_memory_consumer_quote),
     ("create_copy_of_peak_memory_step",
      create_copy_of_peak_memory_step_quote),
     ("create_from_blueprint_peak_memory_step",
      create_from_blueprint_peak_memory_step_quote),
     ("lower_vyper_runtime_unit_dynamic_peak_memory_bound",
      lower_vyper_runtime_unit_dynamic_peak_memory_bound_quote),
     ("lower_vyper_runtime_unit_memory_ptr_dynamic_companion",
      lower_vyper_runtime_unit_memory_ptr_dynamic_companion_quote)];

val expected_constant_owners =
  [("vfmExecutionProp", ["wf_state"]),
   ("vfmCalldataBound", ["calldata_bounded"]),
   ("vfmBuffer", ["buffer_length", "buffer_to_list"]),
   ("vfmExecution", ["memory_cost", "memory_expansion_cost"]),
   ("vfmConstants", ["word_size"]),
   ("vfmState", ["lookup_account"]),
   ("ptrDiscipline", ["ctx_has_dalloca", "entry_taint",
                     "fixed_region_reserved", "ptr_discipline", "taint_within"]),
   ("venomInst", ["fn_insts", "lookup_function", "fn_entry_label",
                  "DALLOCA", "EXTCODESIZE", "ASSERT", "SHL", "OR", "ADD",
                  "MSTORE", "EXTCODECOPY"]),
   ("exprLoweringProps", ["fmp_room", "stmt_state_rel", "run_inst_seq",
                         "emitted_insts"]),
   ("fmpLowerSequenceExec", ["fmp_frontier_rel"]),
   ("venomLayout", ["ceil32"]),
   ("venomState", ["write_memory_with_expansion", "eval_operand",
                   "lookup_var", "Lit"]),
   ("venomExecSemantics", ["OK"]),
   ("builtinSystem", ["compile_msg_data_to_memory"]),
   ("fragExec", ["fn_has_code"]),
   ("loweringStateRelDefs", ["local_ptrs_reserved", "not_fresh_at"]),
   ("emitHelper", ["emit_op", "emit_void"]),
   ("context", ["compile_alloc_dynamic", "compile_copy_memory_dynamic"]),
   ("builtinCreate", ["compile_create_blueprint_check"]),
   ("compileVyper", ["lower_vyper_runtime_unit"]),
   ("stackPlanGen", ["generate_context_plan"]),
   ("e2eDefs", ["source_typing_ok", "source_deployment_rel", "valid_vyper_call",
                "call_storage_ok", "source_exempt"]),
   ("vyperLoweringCorrect", ["initial_venom_state_rel"]),
   ("vyperCompiler", ["unit_alloca_budget"]),
   ("lowerDloadDefs", ["ctx_dload_count"]),
   ("o1PassContract", ["raw_variant"]),
   ("gasSummary", ["gas_explicit"]),
   ("vyperInterpreter", ["call_external"]),
   ("exprSimHypsDefs", ["outcomes_accounts_typed"]),
   ("contextRawReachable", ["raw_reachable"]),
   ("memSafeRun", ["mem_safe_blocks"]),
   ("ptrSafeRun", ["ptr_safe_blocks"]),
   ("unitTransformDefs", ["raw_unit_memory_ok"])];

fun constant_owner tm =
  let val {Thy, Name, ...} = dest_thy_const tm in (Name, Thy) end;

val header_constant_owners =
  map (fn (name, tm) => (name, map constant_owner (find_terms is_const tm)))
    peak_memory_headers;

fun check_constant_owner expected name =
  let
    val found = List.concat (map (fn (header, owners) =>
      map (fn (_, owner) => (header, owner))
        (List.filter (fn (constant, _) => constant = name) owners))
      header_constant_owners)
    fun check (header, actual) =
      if actual = expected then ()
      else raise Fail (header ^ ": " ^ name ^ " binds to " ^ actual ^
                       ", expected " ^ expected)
  in
    if null found then raise Fail ("missing constant " ^ expected ^ "$" ^ name)
    else List.app check found
  end;

val _ = List.app (fn (owner, names) => List.app (check_constant_owner owner) names)
  expected_constant_owners;

val _ = List.app (fn (name, _) => print ("CLOSED_HEADER " ^ name ^ " : bool\n"))
  peak_memory_headers;
