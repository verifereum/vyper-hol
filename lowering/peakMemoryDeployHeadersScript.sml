(* Parse the deployment-unit dynamic peak-memory headers without asserting them.
 * Deployment twin of lowering/peakMemoryHeadersScript.sml (H5/H6) and
 * replacement for superseded 4a5e29ca03:lowering/proofs/deployDallocaBoundScript.sml.
 *)
Theory peakMemoryDeployHeaders
Ancestors
  ctorDeployDefs e2eDeployDefs immSectionDead
  fmpLowerSequenceExec venomLayout
  exprSimHypsDefs compileEnv fragExec fragGasPath
  compileVyper vyperCompiler vyperInterpreter e2eDefs
  o1PassContract unitMemInv unitTransformDefs ptrSafeRun
  contextRawReachable contextCodegenRel
  fragGasOrigin gasExplicitSites gasShadow gasSummary
  ptrDiscipline lowerDloadDefs
  venomExecSemantics venomInst venomState
  arithmetic list rich_list pair words finite_map

val _ = Parse.hide "body";
val _ = Parse.hide "tops";

(*
 * 1. [DEPLOYMENT WHOLE-RUN DYNAMIC FMP / DALLOCA NO-WRAP BOUND — deploy twin of H5]
 *
 * Whole-run dynamic FMP and DALLOCA no-wrap bound on the deployment unit dunit
 * produced by deploy_phases / lower_vyper_deploy_unit, replacing the superseded
 * lower_vyper_deploy_unit_dalloca_bound (4a5e29ca03) without the rejected
 * static allocation budget.
 *
 * Uses separate optimized (cp_fmp on vs = deploy_entry_state prog cplan tops es,
 * where vs.vs_alloca_next = imm_len tops) and raw (fmp on vs0 via
 * raw_variant fmp vs0 vs, with imm_len tops + unit_alloca_budget dunit.cu_context
 * + 32 * ctx_dload_count dunit.cu_context <= w2n fmp) entry floors, tracks
 * fmp_frontier_rel from cp_fmp and w2n fmp, and pins marks via memory-erased
 * gas_origin_path F at the selected (marks, tail) where deploy_storage_ok and
 * ~deploy_source_exempt hold.
 *)
val lower_vyper_deploy_unit_dynamic_peak_memory_bound_quote : term = “
  !policy tops deploy_bc runtime_bc rpolicy (dunit:compilation_unit) dout
   prog cplan (cp_fmp:num) am tx es (fmp:bytes32) vs vs0 marks tail.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    (?shadow_unit func r.
       lower_vyper_deploy_unit (MAP gas_shadow_toplevel tops) rpolicy
         runtime_bc = SOME shadow_unit /\
       lookup_function "__deploy" dunit.cu_context.ctx_functions =
         SOME func /\
       fn_entry_label func = SOME "__deploy" /\
       exit_result r /\
       gas_origin_path F
         (gas_explicit_sites dunit.cu_context shadow_unit.cu_context)
         dunit.cu_context func
         (vs0 with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                      vs_inst_idx := 0 |>) marks r) /\
    deploy_storage_ok tops am tx vs0.vs_outcomes
      (gas_explicit marks vs0.vs_gas_readings ++ tail) /\
    ~deploy_source_exempt tops
      (load_contract (SOME vs0.vs_outcomes)
        (gas_explicit marks vs0.vs_gas_readings ++ tail)
        am tx [(NONE, tops)] []) /\
    vs = deploy_entry_state prog cplan tops es /\
    vs.vs_initial_fmp = n2w cp_fmp /\
    vs.vs_fmp = n2w cp_fmp /\
    cp_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vs0 vs /\
    LENGTH vs0.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vs0.vs_outcomes) /\
    LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn i s.
      raw_reachable vs0 dunit.cu_context fn i s ==>
      s.vs_initial_fmp = fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
      fmp_frontier_rel cp_fmp (w2n fmp)
        (cp_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
      (i.inst_opcode = DALLOCA ==>
       w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64 /\
       !sz_op sz.
         i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
         w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))
”;

(*
 * 2. [DEPLOYMENT MEMORY AND POINTER-DISCIPLINE COMPANION — deploy twin of H6]
 *
 * Additive deployment memory and pointer-discipline companion on the raw
 * variant vs0 above the immutables region (imm_len tops), without
 * ~ctx_has_dalloca, preserving the existing ~ctx_has_dalloca-gated deploy
 * bridges in ctorDeployMemoryFrontier untouched for the first
 * supported_program result.
 *)
val lower_vyper_deploy_unit_memory_ptr_dynamic_companion_quote : term = “
  !policy tops deploy_bc runtime_bc rpolicy (dunit:compilation_unit) dout
   prog cplan am tx es (fmp:bytes32) vs vs0 fn lbl D.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops deploy_bc am tx es /\
    vs = deploy_entry_state prog cplan tops es /\
    raw_variant fmp vs0 vs /\
    (!f i s.
       raw_reachable vs0 dunit.cu_context f i s ==>
       (inst_mem_below_frontiers i s \/
        ?bb. lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
             revert_forward_at bb s.vs_inst_idx) /\
       w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
       (i.inst_opcode = DALLOCA ==>
        !sz_op sz.
          i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
          w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. ptr_safe_blocks D (imm_len tops) fuel dunit.cu_context fn []
       FEMPTY entry_taint
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>)) ==>
    raw_unit_memory_ok dunit.cu_context vs0 /\
    EVERY (\fn. fn.fn_eom = NONE) dunit.cu_context.ctx_functions /\
    fixed_region_reserved (imm_len tops) dunit.cu_context /\
    ptr_discipline (imm_len tops) dunit.cu_context vs0 /\
    taint_within D dunit.cu_context vs0
”;

(*
 * 3. [CONSTRUCTOR BODY FRAG_REACHABLE COROLLARY — replacement for
 *     deploy_ctor_frag_dalloca_no_wrap]
 *
 * Lifts the deployment unit's whole-run dynamic FMP and DALLOCA no-wrap bound
 * along the zero-GAS constructor entry prefix gas_path ... 0 (OK s0) to every
 * state frag_reachable from the constructor body start state s0, supplying the
 * joint body induction's dalloca_no_wrap and cumulative allocation bounds at
 * the constructor root.
 *)
val deploy_ctor_frag_dalloca_no_wrap_quote : term = “
  !policy tops deploy_bc runtime_bc rpolicy (dunit:compilation_unit) dout
   prog cplan (cp_fmp:num) am tx es (fmp:bytes32) vs vs0 marks tail
   func (s0:venom_state).
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    (?shadow_unit r.
       lower_vyper_deploy_unit (MAP gas_shadow_toplevel tops) rpolicy
         runtime_bc = SOME shadow_unit /\
       exit_result r /\
       gas_origin_path F
         (gas_explicit_sites dunit.cu_context shadow_unit.cu_context)
         dunit.cu_context func
         (vs0 with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                      vs_inst_idx := 0 |>) marks r) /\
    deploy_storage_ok tops am tx vs0.vs_outcomes
      (gas_explicit marks vs0.vs_gas_readings ++ tail) /\
    ~deploy_source_exempt tops
      (load_contract (SOME vs0.vs_outcomes)
        (gas_explicit marks vs0.vs_gas_readings ++ tail)
        am tx [(NONE, tops)] []) /\
    vs = deploy_entry_state prog cplan tops es /\
    vs.vs_initial_fmp = n2w cp_fmp /\
    vs.vs_fmp = n2w cp_fmp /\
    cp_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vs0 vs /\
    LENGTH vs0.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vs0.vs_outcomes) /\
    LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 /\
    dunit.cu_context.ctx_entry = SOME "__deploy" /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__deploy" /\
    gas_path dunit.cu_context func
      (vs0 with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                   vs_inst_idx := 0 |>) 0 (OK s0) ==>
    !fn inst s.
      frag_reachable dunit.cu_context func s0 fn inst s ==>
      s.vs_initial_fmp = fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
      fmp_frontier_rel cp_fmp (w2n fmp)
        (cp_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
      dalloca_no_wrap inst s /\
      (inst.inst_opcode = DALLOCA ==>
       w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64)
”;

val check_peak_memory_header = fn (name, tm) =>
  let
    val fv = free_vars tm
  in
    if type_of tm <> bool then
      raise mk_HOL_ERR "peakMemoryDeployHeaders" name "not boolean"
    else if not (null fv) then
      raise mk_HOL_ERR "peakMemoryDeployHeaders" name
        ("free vars: " ^ String.concatWith ", " (map (#1 o dest_var) fv))
    else (name, tm)
  end;

val deploy_peak_memory_headers : (string * term) list =
  map check_peak_memory_header
    [("lower_vyper_deploy_unit_dynamic_peak_memory_bound",
      lower_vyper_deploy_unit_dynamic_peak_memory_bound_quote),
     ("lower_vyper_deploy_unit_memory_ptr_dynamic_companion",
      lower_vyper_deploy_unit_memory_ptr_dynamic_companion_quote),
     ("deploy_ctor_frag_dalloca_no_wrap",
      deploy_ctor_frag_dalloca_no_wrap_quote)];

val expected_constant_owners =
  [("ctorDeployDefs", ["deploy_phases", "deploy_entry_state",
                       "deploy_source_exempt"]),
   ("e2eDeployDefs", ["deploy_typing_ok", "deploy_state_rel",
                      "deploy_storage_ok"]),
   ("immSectionDead", ["imm_len"]),
   ("compileVyper", ["lower_vyper_deploy_unit"]),
   ("gasShadow", ["gas_shadow_toplevel"]),
   ("venomInst", ["lookup_function", "lookup_block", "fn_entry_label",
                  "DALLOCA"]),
   ("fragExec", ["exit_result"]),
   ("fragGasOrigin", ["gas_origin_path"]),
   ("fragGasPath", ["gas_path"]),
   ("gasExplicitSites", ["gas_explicit_sites"]),
   ("gasSummary", ["gas_explicit"]),
   ("vyperInterpreter", ["load_contract"]),
   ("vyperCompiler", ["unit_alloca_budget"]),
   ("lowerDloadDefs", ["ctx_dload_count"]),
   ("o1PassContract", ["raw_variant"]),
   ("exprSimHypsDefs", ["outcomes_accounts_typed"]),
   ("contextRawReachable", ["raw_reachable", "frag_reachable"]),
   ("fmpLowerSequenceExec", ["fmp_frontier_rel"]),
   ("venomState", ["eval_operand"]),
   ("venomLayout", ["ceil32"]),
   ("venomExecSemantics", ["OK"]),
   ("unitTransformDefs", ["inst_mem_below_frontiers", "raw_unit_memory_ok",
                          "dalloca_no_wrap"]),
   ("contextCodegenRel", ["revert_forward_at"]),
   ("ptrSafeRun", ["ptr_safe_blocks"]),
   ("ptrDiscipline", ["entry_taint", "fixed_region_reserved",
                      "ptr_discipline", "taint_within"])];

fun constant_owner tm =
  let val {Thy, Name, ...} = dest_thy_const tm in (Name, Thy) end;

val header_constant_owners =
  map (fn (name, tm) => (name, map constant_owner (find_terms is_const tm)))
    deploy_peak_memory_headers;

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
  deploy_peak_memory_headers;
