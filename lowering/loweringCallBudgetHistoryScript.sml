(* Quantitative lowering histories and unasserted correctness headers.
 * All thirteen accepted headers remain as closed ML quotations below.
 * Only the structural subset is proved at the end of this file.
 * No source/emitter correspondence follows from these definitions.
 *)
Theory loweringCallBudgetHistory
Ancestors
  ptrDiscipline ptrSafeRun gasOutcomeFull gasEvents gasExplicitSites
  sourceCallCount sourceCallCountEntryReplay sourceCallCountMonotone
  sourceCallCountWitness loweringStateRelDefs compileVyper vyperCompiler
  o1PassContract fragGasOriginPtr contextRawReachable
  vyperLoweringCorrect e2eDefs exprSimHypsDefs lowerDloadDefs
  list rich_list arithmetic pred_set
  concretizePtrCoverageStaticMemReachability

Datatype:
  lower_budget_point = <|
    bp_stack : call_frame list;
    bp_params : (num # num) option list;
    bp_prov : (string, num # num) fmap;
    bp_taint : taint;
    bp_fn : ir_function;
    bp_state : venom_state
  |>
End

(* Ordinals are LENGTH of the preceding event list, never inst_id.
 * Step stores the actual pre/step-result/post-cursor and its actual fuel.
 * Call is setup, NOT an invented step_inst result for INVOKE.
 * Return stores the actual IntRet token/state and the bound caller state.
 *)
Datatype:
  lower_budget_event =
    BudgetStep num lower_budget_point instruction num exec_result
      lower_budget_point
  | BudgetCall num lower_budget_point instruction ir_function venom_state
      lower_budget_point
  | BudgetReturn num lower_budget_point instruction num internal_return
      venom_state venom_state lower_budget_point
End

Definition lower_event_ordinal_def:
  lower_event_ordinal (BudgetStep n p i f r q) = n /\
  lower_event_ordinal (BudgetCall n p i fn cs q) = n /\
  lower_event_ordinal (BudgetReturn n p i f ret se sb q) = n
End

(* All recorded base Step events in the five rules have an actual OK
 * result. Static/size aborts have no advancing Step event and no debit.
 * Empty-oracle CALL/CREATE still return OK and therefore debit one.
 *)
Definition lower_event_consumes_def:
  (lower_event_consumes (BudgetStep n p i f r q) <=>
    (?s. r = OK s) /\
    MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) /\
  (lower_event_consumes (BudgetCall n p i fn cs q) <=> F) /\
  (lower_event_consumes (BudgetReturn n p i f ret se sb q) <=> F)
End

Definition lower_event_allocates_def:
  (lower_event_allocates (BudgetStep n p i f r q) <=>
    i.inst_opcode = DALLOCA /\ (?s. r = OK s)) /\
  (lower_event_allocates (BudgetCall n p i fn cs q) <=> F) /\
  (lower_event_allocates (BudgetReturn n p i f ret se sb q) <=> F)
End

Definition lower_history_count_def:
  lower_history_count h = LENGTH (FILTER lower_event_consumes h)
End

Definition lower_alloc_record_def:
  lower_alloc_record h n fn i s op sz t <=>
    n < LENGTH h /\
    ?p fuel q.
      EL n h = BudgetStep n p i fuel (OK t) q /\
      p.bp_fn = fn /\ p.bp_state = s /\
      i.inst_opcode = DALLOCA /\ i.inst_operands = [op] /\
      eval_operand op s = SOME sz /\
      w2n sz <= 2 ** 255 + 2 ** 64
End

(* Pairing is injective on completed allocations, chronological, and has
 * at most one trailing pending allocation. The current unexecuted
 * DALLOCA is handled separately by lower_history_current below.
 * Completed pairs additionally expose actual same-site operand geometry
 * and an interval with no nested call/effect/allocation. The CopyOf
 * allocation is CREATE extent+21w; blueprint uses that extent unchanged.
 * Pending-site source argument bounds remain local supplier obligations.
 * No SETFMP condition: this works before/after the P7 removal.
 *)
Definition lower_history_pairs_def:
  lower_history_pairs h pair <=>
    (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
      ((a < pair a /\ pair a < LENGTH h /\
        lower_event_consumes (EL (pair a) h)) \/
       (pair a = LENGTH h /\
        !j. a < j /\ j < LENGTH h ==>
          ~lower_event_allocates (EL j h) /\
          ~lower_event_consumes (EL j h)))) /\
    (!a b. a < LENGTH h /\ b < LENGTH h /\
      lower_event_allocates (EL a h) /\
      lower_event_allocates (EL b h) /\
      pair a < LENGTH h /\ pair b < LENGTH h /\ pair a = pair b ==>
      a = b) /\
    (!a b. a < LENGTH h /\ b < LENGTH h /\
      lower_event_allocates (EL a h) /\
      lower_event_allocates (EL b h) /\
      pair a = LENGTH h /\ pair b = LENGTH h ==> a = b) /\
    (!a. a < LENGTH h /\ lower_event_allocates (EL a h) /\
      pair a < LENGTH h ==>
      ?fn ai pre op sz post ap af aq ep ei ef et eq ws.
        lower_alloc_record h a fn ai pre op sz post /\
        EL a h = BudgetStep a ap ai af (OK post) aq /\
        EL (pair a) h = BudgetStep (pair a) ep ei ef (OK et) eq /\
        ep.bp_fn = fn /\ ep.bp_stack = ap.bp_stack /\
        eval_operands ei.inst_operands ep.bp_state = SOME ws /\
        (!j. a < j /\ j < pair a ==>
          ?jp ji jf jt jq.
            EL j h = BudgetStep j jp ji jf (OK jt) jq /\
            ~lower_event_consumes (EL j h) /\
            ~lower_event_allocates (EL j h)) /\
        ((sz = n2w (LENGTH pre.vs_call_ctx.cc_calldata) /\
          ?g addr v ro rz.
            (ei.inst_opcode = CALL /\
              ws = [g; addr; v; pre.vs_fmp; sz; ro; rz]) \/
            (MEM ei.inst_opcode [STATICCALL; DELEGATECALL] /\
              ws = [g; addr; pre.vs_fmp; sz; ro; rz])) \/
         (?v offset len salt.
           ((ei.inst_opcode = CREATE /\ ws = [v; offset; len]) \/
            (ei.inst_opcode = CREATE2 /\ ws = [v; offset; len; salt])) /\
           ((offset = pre.vs_fmp /\ sz = len) \/
            (offset = pre.vs_fmp + 21w /\ sz = len + 21w)))))
End

Definition lower_history_current_def:
  lower_history_current h pair q <=>
    (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
      (!op sz. i.inst_operands = [op] /\
        eval_operand op q.bp_state = SOME sz ==>
        w2n sz <= 2 ** 255 + 2 ** 64) /\
      !a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
        pair a < LENGTH h)
End

(* checked=F gives the actual frame traversal, with no memory/pointer
 * assumptions. checked=T checks those at the SAME recorded base-step
 * fuel/pre-state; call setup is explicit, not an atomic INVOKE check.
 * Marks are recorded from the actual instruction/function, including
 * nested calls; GAS is not used as an external-effect counter.
 *
 * bp_stack has exactly ptrDiscipline's saved caller record. The history
 * retains the whole pre-point, including full pre-call taint, when an
 * exceptional atomic INVOKE projection needs the saved caller ghosts.
 *)
Inductive lower_budget_path:
[~entry:]
  (!checked D lo explicit ctx p i.
    ~p.bp_state.vs_halted /\ active_inst p.bp_fn i p.bp_state ==>
    lower_budget_path checked (D,lo,explicit,ctx) p [] [] p)
[~next:]
  (!checked D lo explicit ctx root h marks p i fuel t j q.
    lower_budget_path checked (D,lo,explicit,ctx) root h marks p /\
    active_inst p.bp_fn i p.bp_state /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    step_inst fuel ctx i p.bp_state = OK t /\
    q = p with <|
      bp_state := (t with vs_inst_idx := SUC p.bp_state.vs_inst_idx);
      bp_prov := step_prov p.bp_params p.bp_prov i t;
      bp_taint := step_taint i p.bp_state t p.bp_taint |> /\
    active_inst q.bp_fn j q.bp_state /\
    (checked ==>
      (in_revert_forward p.bp_fn p.bp_state \/
       mem_safe_step fuel ctx i p.bp_state) /\
      ptr_safe_step D lo fuel ctx p.bp_fn p.bp_params p.bp_prov
        p.bp_taint i p.bp_state) ==>
    lower_budget_path checked (D,lo,explicit,ctx) root
      (h ++ [BudgetStep (LENGTH h) p i fuel (OK t) q])
      (marks ++ MAP (\key. key IN explicit)
        (gas_events_step fuel ctx p.bp_fn.fn_name i p.bp_state)) q)
[~block:]
  (!checked D lo explicit ctx root h marks p i fuel t entered j q.
    lower_budget_path checked (D,lo,explicit,ctx) root h marks p /\
    active_inst p.bp_fn i p.bp_state /\ is_terminator i.inst_opcode /\
    step_inst fuel ctx i p.bp_state = OK t /\ ~t.vs_halted /\
    enters_block p.bp_fn t entered /\
    q = p with <|
      bp_state := entered;
      bp_prov := entry_prov p.bp_fn t p.bp_prov;
      bp_taint := entry_taint_vars p.bp_fn t p.bp_taint |> /\
    active_inst q.bp_fn j q.bp_state /\
    (checked ==>
      (in_revert_forward p.bp_fn p.bp_state \/
       mem_safe_step fuel ctx i p.bp_state) /\
      ptr_safe_step D lo fuel ctx p.bp_fn p.bp_params p.bp_prov
        p.bp_taint i p.bp_state) ==>
    lower_budget_path checked (D,lo,explicit,ctx) root
      (h ++ [BudgetStep (LENGTH h) p i fuel (OK t) q])
      (marks ++ MAP (\key. key IN explicit)
        (gas_events_step fuel ctx p.bp_fn.fn_name i p.bp_state)) q)
[~call:]
  (!checked D lo explicit ctx root h marks p inv nm ops callee args cs entered j q.
    lower_budget_path checked (D,lo,explicit,ctx) root h marks p /\
    active_inst p.bp_fn inv p.bp_state /\ inv.inst_opcode = INVOKE /\
    decode_invoke inv = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops p.bp_state = SOME args /\
    setup_callee callee args p.bp_state = SOME cs /\
    enters_block callee cs entered /\
    q = <| bp_stack :=
      <| cf_fn := p.bp_fn; cf_inst := inv; cf_state := p.bp_state;
         cf_params := p.bp_params; cf_prov := p.bp_prov;
         cf_tvar := p.bp_taint.t_var |> :: p.bp_stack;
      bp_params := MAP (op_prov p.bp_prov) ops;
      bp_prov := FEMPTY; bp_taint := (p.bp_taint with t_var := FEMPTY);
      bp_fn := callee; bp_state := entered |> /\
    active_inst q.bp_fn j q.bp_state /\
    (checked ==> ptr_inst_ok D lo 0 ctx p.bp_fn p.bp_prov
                   p.bp_taint inv p.bp_state) ==>
    lower_budget_path checked (D,lo,explicit,ctx) root
      (h ++ [BudgetCall (LENGTH h) p inv callee cs q]) marks q)
[~ret:]
  (!checked D lo explicit ctx root h marks p f stk i fuel ret s_end s' j q.
    lower_budget_path checked (D,lo,explicit,ctx) root h marks p /\
    p.bp_stack = f::stk /\ active_inst p.bp_fn i p.bp_state /\
    step_inst fuel ctx i p.bp_state = IntRet ret s_end /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' /\
    q = <| bp_stack := stk; bp_params := f.cf_params;
      bp_prov := DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs));
      bp_taint := (p.bp_taint with t_var :=
        DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)));
      bp_fn := f.cf_fn;
      bp_state := (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) |> /\
    active_inst q.bp_fn j q.bp_state /\
    (checked ==>
      (in_revert_forward p.bp_fn p.bp_state \/
       mem_safe_step fuel ctx i p.bp_state) /\
      ptr_safe_step D lo fuel ctx p.bp_fn p.bp_params p.bp_prov
        p.bp_taint i p.bp_state) ==>
    lower_budget_path checked (D,lo,explicit,ctx) root
      (h ++ [BudgetReturn (LENGTH h) p i fuel ret s_end s' q])
      (marks ++ MAP (\key. key IN explicit)
        (gas_events_step fuel ctx p.bp_fn.fn_name i p.bp_state)) q)
End

(* A proposition about an ACTUAL source continuation and current target
 * cursor/call stack, not a top-level premise and not a second counter.
 * Every actual future prefix is covered; physical count<=k and residual
 * may be zero. Internal correspondence must show T<=C+1 with C<k.
 * The final extra precompile must abort the whole nested execution.
 * Direct allocation-count/next-allocation bounds retain the stricter
 * internal matched-effect consequence without exposing a charge mask.
 * That proof obligation is not a new public predicate or premise.
 * C includes the remaining source continuation, not merely the current
 * expression if target execution can continue into later statements.
 *)
Definition lower_budget_continuation_def:
  lower_budget_continuation k C es (D,lo,explicit,ctx) root <=>
    es.outcomes = SOME root.bp_state.vs_outcomes /\
    ((!obs. entry_calls_within k root.bp_state.vs_outcomes
        (\xs. SOME (C (es with <| outcomes := SOME xs; gas_obs := obs |>)))) ==>
      !h marks q.
        lower_budget_path F (D,lo,explicit,ctx) root h marks q ==>
        ?remaining pair.
          lower_history_count h + remaining = k /\
          LENGTH (FILTER lower_event_allocates h) <= k /\
          (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
            SUC (LENGTH (FILTER lower_event_allocates h)) <= k) /\
          lower_history_pairs h pair /\
          lower_history_current h pair q /\
          (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
            ?fn i s op sz t. lower_alloc_record h n fn i s op sz t))
End

(* C is the WHOLE remaining source continuation. source is the fragment
 * whose old GAS/storage/result judgement is being strengthened. A proof
 * producing this judgement must relate that actual C to the compiler's
 * continuation; this definition is never an aligned-run top premise.
 *
 * The second conjunct bounds EVERY unchecked history from this exact
 * target start, not a separately selected path. Thus checked histories
 * belonging to the first conjunct's good/bad/exempt witness use the same
 * per-instruction fuel/memory/pointer checks by forget_checks. There is
 * no new GAS horizon, oracle padding or replacement result witness.
 *)
Definition gas_outcome_full_budget_def:
  gas_outcome_full_budget k C (DF,lo,explicit,ctx,func,PG)
      tops cx st0 source (es,s,G,tn) Q R <=>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG)
      tops cx st0 source (es,s,G,tn) Q R /\
    (!H. lower_budget_continuation k C es (DF H,lo,explicit,ctx)
      <| bp_stack := []; bp_params := PG; bp_prov := G;
         bp_taint := tn; bp_fn := func; bp_state := s |>)
End


(* Complete closed quotations; none is asserted as a theorem. *)
val call_budget_headers = [
  ("lower_budget_path_ordinals",
   ``!checked D lo explicit ctx p h marks q n.
    lower_budget_path checked (D,lo,explicit,ctx) p h marks q /\ n < LENGTH h ==>
    lower_event_ordinal (EL n h) = n``),
  ("lower_budget_path_forget_checks",
   ``!D lo explicit ctx p h marks q.
    lower_budget_path T (D,lo,explicit,ctx) p h marks q ==>
    lower_budget_path F (D,lo,explicit,ctx) p h marks q``),
  ("lower_budget_remaining_step",
   ``!k h e remaining.
    lower_history_count (h ++ [e]) + remaining = k ==>
    lower_history_count h +
      (if lower_event_consumes e then SUC remaining else remaining) = k``),
  ("lower_budget_pairs_count",
   ``!h pair.
    lower_history_pairs h pair ==>
    LENGTH (FILTER lower_event_allocates h) <= SUC (lower_history_count h)``),
  ("lower_budget_completed_pairs_count",
   ``!h pair q.
    lower_history_pairs h pair /\ lower_history_current h pair q ==>
    LENGTH (FILTER (\a. lower_event_allocates (EL a h) /\
      pair a < LENGTH h) (GENLIST I (LENGTH h))) <= lower_history_count h /\
    (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
      LENGTH (FILTER lower_event_allocates h) <= lower_history_count h)``),
  ("gas_outcome_full_budget_forget",
   ``!k C DF lo explicit ctx func PG tops cx st0 source es s G tn Q R.
    gas_outcome_full_budget k C (DF,lo,explicit,ctx,func,PG)
      tops cx st0 source (es,s,G,tn) Q R ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG)
      tops cx st0 source (es,s,G,tn) Q R``),
  ("gas_outcome_full_budget_prefix",
   ``!k C DF lo explicit ctx func PG tops cx st0 source es s G tn Q R
    H h marks q.
    gas_outcome_full_budget k C (DF,lo,explicit,ctx,func,PG)
      tops cx st0 source (es,s,G,tn) Q R /\
    (!obs. entry_calls_within k s.vs_outcomes
      (\xs. SOME (C (es with <| outcomes := SOME xs; gas_obs := obs |>)))) /\
    lower_budget_path T (DF H,lo,explicit,ctx)
      <| bp_stack := []; bp_params := PG; bp_prov := G;
         bp_taint := tn; bp_fn := func; bp_state := s |>
      h marks q ==>
    ?remaining pair.
      lower_history_count h + remaining = k /\
      LENGTH (FILTER lower_event_allocates h) <= k /\
      (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
        SUC (LENGTH (FILTER lower_event_allocates h)) <= k) /\
      lower_history_pairs h pair /\ lower_history_current h pair q /\
      (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
        ?fn i pre op sz post. lower_alloc_record h n fn i pre op sz post)``),
  ("lower_budget_raw_history",
   ``!vs ctx fn inst s D lo explicit.
    ~vs.vs_halted /\ raw_reachable vs ctx fn inst s ==>
    ?name entry lbl entered p h marks q.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME entry /\
      fn_entry_label entry = SOME lbl /\
      enters_block entry
        (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) entered /\
      p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
             bp_taint := entry_taint; bp_fn := entry; bp_state := entered |> /\
      lower_budget_path F (D,lo,explicit,ctx) p h marks q /\
      q.bp_fn = fn /\ q.bp_state = s /\ active_inst fn inst s``),
  ("lower_vyper_runtime_unit_call_budget",
   ``!tops rpolicy unit am tx ret vs k.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    k <= 2 ** 64 /\
    (!obs. source_calls_within k am tx vs.vs_outcomes obs) /\
    (!marks.
      source_storage_ok am tx vs.vs_outcomes
        (gas_explicit marks vs.vs_gas_readings) /\
      call_outcomes_storage_ok am tx vs.vs_outcomes
        (gas_explicit marks vs.vs_gas_readings)) /\
    (!marks. ~source_exempt tops
      (call_external (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !D lo explicit name fn lbl entered p h marks q.
      unit.cu_context.ctx_entry = SOME name /\
      lookup_function name unit.cu_context.ctx_functions = SOME fn /\
      fn_entry_label fn = SOME lbl /\
      enters_block fn
        (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) entered /\
      p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
             bp_taint := entry_taint; bp_fn := fn; bp_state := entered |> /\
      lower_budget_path F (D,lo,explicit,unit.cu_context) p h marks q ==>
      ?remaining pair.
        remaining <= k /\ remaining <= 2 ** 64 /\
        lower_history_count h + remaining = k /\
        LENGTH (FILTER lower_event_allocates h) <= k /\
        (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
          SUC (LENGTH (FILTER lower_event_allocates h)) <= k) /\
        lower_history_pairs h pair /\ lower_history_current h pair q /\
        (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
          ?f i s op sz t. lower_alloc_record h n f i s op sz t)``),
  ("lower_vyper_runtime_unit_allocation_history",
   ``!tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (!obs. source_calls_within (2 ** 64) am tx vs.vs_outcomes obs) /\
    (!marks.
      source_storage_ok am tx vs.vs_outcomes
        (gas_explicit marks vs.vs_gas_readings) /\
      call_outcomes_storage_ok am tx vs.vs_outcomes
        (gas_explicit marks vs.vs_gas_readings)) /\
    (!marks. ~source_exempt tops
      (call_external (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !f i s D lo explicit.
      raw_reachable vs unit.cu_context f i s ==>
      ?name fn lbl entered p h marks q pair remaining.
        unit.cu_context.ctx_entry = SOME name /\
        lookup_function name unit.cu_context.ctx_functions = SOME fn /\
        fn_entry_label fn = SOME lbl /\
        enters_block fn
          (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                      vs_inst_idx := 0 |>) entered /\
        p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
               bp_taint := entry_taint; bp_fn := fn; bp_state := entered |> /\
        lower_budget_path F (D,lo,explicit,unit.cu_context) p h marks q /\
        q.bp_fn = f /\ q.bp_state = s /\ active_inst f i s /\
        lower_history_count h + remaining = 2 ** 64 /\
        LENGTH (FILTER lower_event_allocates h) <= 2 ** 64 /\
        (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
          SUC (LENGTH (FILTER lower_event_allocates h)) <= 2 ** 64) /\
        lower_history_pairs h pair /\ lower_history_current h pair q /\
        (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
          ?af ai pre op sz post.
            lower_alloc_record h n af ai pre op sz post)``),
  ("lower_vyper_runtime_unit_joint_prefix_history",
   ``!tops rpolicy unit am tx ret vs k.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    k <= 2 ** 64 /\
    (!obs. source_calls_within k am tx vs.vs_outcomes obs) /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !D explicit fn marks leaf leaf_pg leaf_g leaf_tn finish inst.
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
      gas_origin_ptr_focus (D,0,explicit,unit.cu_context,fn,[])
        ((vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0 |>),FEMPTY,entry_taint)
        marks (leaf,leaf_pg,leaf_g,leaf_tn,finish) /\
      active_inst leaf inst finish ==>
      ?p h q remaining pair.
        p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
          bp_taint := entry_taint; bp_fn := fn;
          bp_state := (vs with <| vs_prev_bb := NONE;
            vs_current_bb := "__entry"; vs_inst_idx := 0 |>) |> /\
        lower_budget_path T (D,0,explicit,unit.cu_context) p h marks q /\
        q.bp_fn = leaf /\ q.bp_params = leaf_pg /\ q.bp_prov = leaf_g /\
        q.bp_taint = leaf_tn /\ q.bp_state = finish /\
        lower_history_count h + remaining = k /\
        LENGTH (FILTER lower_event_allocates h) <= k /\
        (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
          SUC (LENGTH (FILTER lower_event_allocates h)) <= k) /\
        lower_history_pairs h pair /\ lower_history_current h pair q /\
        (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
          ?af ai pre op sz post.
            lower_alloc_record h n af ai pre op sz post)``),
  ("lower_budget_raw_variant_entry",
   ``!tops am tx fmp vs_in vs.
    gas_variant vs_in
      (vs with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) /\ initial_venom_state_rel tops am tx vs ==>
    initial_venom_state_rel tops am tx vs_in /\
    vs_in.vs_fmp = fmp /\ vs_in.vs_initial_fmp = fmp /\
    vs_in.vs_outcomes = vs.vs_outcomes /\
    vs_in.vs_call_ctx = vs.vs_call_ctx /\
    vs_in.vs_memory = vs.vs_memory``),
  ("lower_vyper_runtime_unit_raw_variant_history",
   ``!tops rpolicy unit am tx ret vs fmp.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (!obs. source_calls_within (2 ** 64) am tx vs.vs_outcomes obs) /\
    (!gs.
      source_storage_ok am tx vs.vs_outcomes gs /\
      call_outcomes_storage_ok am tx vs.vs_outcomes gs) /\
    (!gs. ~source_exempt tops
      (call_external (SOME vs.vs_outcomes) gs am tx)) /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !vs_in f i s D lo explicit.
      gas_variant vs_in
      (vs with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) /\
      raw_reachable vs_in unit.cu_context f i s ==>
      ?name fn lbl entered p h marks q pair remaining.
        unit.cu_context.ctx_entry = SOME name /\
        lookup_function name unit.cu_context.ctx_functions = SOME fn /\
        fn_entry_label fn = SOME lbl /\
        enters_block fn
          (vs_in with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>) entered /\
        p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
               bp_taint := entry_taint; bp_fn := fn; bp_state := entered |> /\
        lower_budget_path F (D,lo,explicit,unit.cu_context) p h marks q /\
        q.bp_fn = f /\ q.bp_state = s /\ active_inst f i s /\
        lower_history_count h + remaining = 2 ** 64 /\
        LENGTH (FILTER lower_event_allocates h) <= 2 ** 64 /\
        (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
          SUC (LENGTH (FILTER lower_event_allocates h)) <= 2 ** 64) /\
        lower_history_pairs h pair /\ lower_history_current h pair q /\
        (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
          ?af ai pre op sz post. lower_alloc_record h n af ai pre op sz post)``)
];

fun check_call_budget_header (name, tm) =
  if not (null (free_vars tm)) then
    raise Fail (name ^ ": free variables in header: " ^
      String.concatWith ", " (map term_to_string (free_vars tm)))
  else if type_of tm <> bool then
    raise Fail (name ^ ": header is not boolean")
  else print ("CLOSED_HEADER " ^ name ^ " : bool\n");

val _ = app check_call_budget_header call_budget_headers;

fun call_budget_constants tm =
  if is_const tm then
    let val {Thy, Name, Ty} = dest_thy_const tm
    in [Thy ^ "." ^ Name ^ " : " ^ Parse.type_to_string Ty] end
  else if is_comb tm then
    let val (f, x) = dest_comb tm
    in call_budget_constants f @ call_budget_constants x end
  else if is_abs tm then call_budget_constants (snd (dest_abs tm))
  else [];

val call_budget_constant_owners =
  Lib.mk_set (List.concat (map (call_budget_constants o snd)
    call_budget_headers));
val _ = app (fn owner => print ("CONSTANT_OWNER " ^ owner ^ "\n"))
  call_budget_constant_owners;
val _ = print ("CALL_BUDGET_HEADERS_CLOSED 13\n");

Theorem lower_budget_path_ordinals:
  !checked D lo explicit ctx p h marks q n.
    lower_budget_path checked (D,lo,explicit,ctx) p h marks q /\ n < LENGTH h ==>
    lower_event_ordinal (EL n h) = n
Proof
  qsuff_tac
    `!checked cfg p h marks q.
      lower_budget_path checked cfg p h marks q ==>
      !n. n < LENGTH h ==> lower_event_ordinal (EL n h) = n`
  >- metis_tac[] >>
  ho_match_mp_tac lower_budget_path_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[LENGTH_APPEND, EL_APPEND_EQN] >>
  Cases_on `n < LENGTH h` >> gvs[lower_event_ordinal_def] >>
  `n = LENGTH h` by decide_tac >> gvs[lower_event_ordinal_def]
QED

Theorem lower_budget_frame_history[local]:
  !vs ctx stk PG G tn fn inst s.
    frame_reachable vs ctx stk PG G tn fn inst s ==>
    !D lo explicit. ~vs.vs_halted ==>
    ?name entry lbl entered h marks.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME entry /\
      fn_entry_label entry = SOME lbl /\
      enters_block entry
        (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) entered /\
      lower_budget_path F (D,lo,explicit,ctx)
        <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
           bp_taint := entry_taint; bp_fn := entry; bp_state := entered |>
        h marks
        <| bp_stack := stk; bp_params := PG; bp_prov := G;
           bp_taint := tn; bp_fn := fn; bp_state := s |>
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >- suspend "ret"
QED

Resume lower_budget_frame_history[entry]:
  (rename1 `ctx.ctx_entry = SOME entry_name` >>
      rename1 `fn_entry_label entry_fn = SOME entry_label` >>
      rename1 `enters_block entry_fn _ entry_state` >>
      qexistsl_tac [`entry_name`, `entry_fn`, `entry_label`,
                    `entry_state`, `[]`, `[]`] >>
      simp[] >> irule lower_budget_path_entry >>
      simp[] >> conj_tac
      >- (fs[contextCodegenRelTheory.enters_block_def] >>
          drule venomExecProofsTheory.eval_phis_preserves_halted >> simp[]) >>
      metis_tac[])
QED

Resume lower_budget_frame_history[next]:
  (first_x_assum (qspecl_then [`D`, `lo`, `explicit`] mp_tac) >>
      simp[] >> strip_tac >>
      rename1 `lower_budget_path F (_,_,_,ctx0) _ _ _
        <| bp_stack := stk0; bp_params := PG0; bp_prov := G0;
           bp_taint := tn0; bp_fn := fn0; bp_state := pre0 |>` >>
      rename1 `step_inst fuel0 ctx0 i0 pre0 = OK post0` >>
      metis_tac[SIMP_RULE (srw_ss()) []
        (Q.INST [`checked` |-> `F`,
          `p` |-> `<| bp_stack := stk0; bp_params := PG0; bp_prov := G0;
                      bp_taint := tn0; bp_fn := fn0; bp_state := pre0 |>`,
          `q` |-> `<| bp_stack := stk0; bp_params := PG0;
                      bp_prov := step_prov PG0 G0 i0 post0;
                      bp_taint := step_taint i0 pre0 post0 tn0;
                      bp_fn := fn0;
                      bp_state := post0 with vs_inst_idx := SUC pre0.vs_inst_idx |>`]
          (SPEC_ALL lower_budget_path_next))])
QED

Resume lower_budget_frame_history[block]:
  (first_x_assum (qspecl_then [`D`, `lo`, `explicit`] mp_tac) >>
      simp[] >> strip_tac >>
      rename1 `lower_budget_path F (_,_,_,ctx0) _ _ _
        <| bp_stack := stk0; bp_params := PG0; bp_prov := G0;
           bp_taint := tn0; bp_fn := fn0; bp_state := pre0 |>` >>
      rename1 `step_inst fuel0 ctx0 i0 pre0 = OK post0` >>
      rename1 `enters_block fn0 post0 entered0` >>
      metis_tac[SIMP_RULE (srw_ss()) []
        (Q.INST [`checked` |-> `F`,
          `p` |-> `<| bp_stack := stk0; bp_params := PG0; bp_prov := G0;
                      bp_taint := tn0; bp_fn := fn0; bp_state := pre0 |>`,
          `q` |-> `<| bp_stack := stk0; bp_params := PG0;
                      bp_prov := entry_prov fn0 post0 G0;
                      bp_taint := entry_taint_vars fn0 post0 tn0;
                      bp_fn := fn0; bp_state := entered0 |>`]
          (SPEC_ALL lower_budget_path_block))])
QED

Resume lower_budget_frame_history[call]:
  (first_x_assum (qspecl_then [`D`, `lo`, `explicit`] mp_tac) >>
      simp[] >> strip_tac >>
      rename1 `lower_budget_path F (_,_,_,ctx0) _ _ _
        <| bp_stack := stk0; bp_params := PG0; bp_prov := G0;
           bp_taint := tn0; bp_fn := fn0; bp_state := pre0 |>` >>
      rename1 `setup_callee callee0 args0 pre0 = SOME cs0` >>
      rename1 `eval_operands ops0 pre0 = SOME args0` >>
      rename1 `active_inst fn0 inv0 pre0` >>
      rename1 `enters_block callee0 cs0 entered0` >>
      metis_tac[SIMP_RULE (srw_ss()) []
        (Q.INST [`checked` |-> `F`,
          `p` |-> `<| bp_stack := stk0; bp_params := PG0; bp_prov := G0;
                      bp_taint := tn0; bp_fn := fn0; bp_state := pre0 |>`,
          `q` |-> `<| bp_stack := <| cf_fn := fn0; cf_inst := inv0;
                        cf_state := pre0; cf_params := PG0; cf_prov := G0;
                        cf_tvar := tn0.t_var |> :: stk0;
                      bp_params := MAP (op_prov G0) ops0;
                      bp_prov := FEMPTY; bp_taint := tn0 with t_var := FEMPTY;
                      bp_fn := callee0; bp_state := entered0 |>`]
          (SPEC_ALL lower_budget_path_call))])
QED

Resume lower_budget_frame_history[ret]:
  (first_x_assum (qspecl_then [`D`, `lo`, `explicit`] mp_tac) >>
      simp[] >> strip_tac >>
      rename1 `lower_budget_path F (_,_,_,ctx0) _ _ _
        <| bp_stack := frame0::stk0; bp_params := PG0; bp_prov := G0;
           bp_taint := tn0; bp_fn := fn0; bp_state := pre0 |>` >>
      rename1 `bind_outputs _ _ _ = SOME post0` >>
      metis_tac[SIMP_RULE (srw_ss()) []
        (Q.INST [`checked` |-> `F`,
          `p` |-> `<| bp_stack := frame0::stk0; bp_params := PG0; bp_prov := G0;
                      bp_taint := tn0; bp_fn := fn0; bp_state := pre0 |>`,
          `q` |-> `<| bp_stack := stk0; bp_params := frame0.cf_params;
                      bp_prov := DRESTRICT frame0.cf_prov
                        (COMPL (set frame0.cf_inst.inst_outputs));
                      bp_taint := tn0 with t_var := DRESTRICT frame0.cf_tvar
                        (COMPL (set frame0.cf_inst.inst_outputs));
                      bp_fn := frame0.cf_fn;
                      bp_state := post0 with vs_inst_idx :=
                        SUC frame0.cf_state.vs_inst_idx |>`]
          (SPEC_ALL lower_budget_path_ret))])
QED
Finalise lower_budget_frame_history[local]

Theorem lower_budget_raw_history:
  !vs ctx fn inst s D lo explicit.
    ~vs.vs_halted /\ raw_reachable vs ctx fn inst s ==>
    ?name entry lbl entered p h marks q.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME entry /\
      fn_entry_label entry = SOME lbl /\
      enters_block entry
        (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) entered /\
      p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
             bp_taint := entry_taint; bp_fn := entry; bp_state := entered |> /\
      lower_budget_path F (D,lo,explicit,ctx) p h marks q /\
      q.bp_fn = fn /\ q.bp_state = s /\ active_inst fn inst s
Proof
  rpt strip_tac >> drule ptr_raw_reachable_frame >> strip_tac >>
  drule lower_budget_frame_history >>
  disch_then (qspecl_then [`D`, `lo`, `explicit`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `ctx.ctx_entry = SOME name0` >>
  rename1 `fn_entry_label entry0 = SOME lbl0` >>
  rename1 `enters_block entry0 _ entered0` >>
  rename1 `lower_budget_path F _ _ history0 marks0
    <| bp_stack := stk0; bp_params := PG0; bp_prov := G0;
       bp_taint := tn0; bp_fn := fn; bp_state := s |>` >>
  qexistsl_tac [`name0`, `entry0`, `lbl0`, `entered0`, `history0`, `marks0`,
    `<| bp_stack := stk0; bp_params := PG0; bp_prov := G0;
        bp_taint := tn0; bp_fn := fn; bp_state := s |>`] >>
  simp[] >> metis_tac[stepWriteFootprintBaseTheory.raw_reachable_active]
QED

Theorem lower_budget_filter_indices_length[local]:
  !P h.
    LENGTH (FILTER (\a. P (EL a h)) (GENLIST I (LENGTH h))) =
    LENGTH (FILTER P h)
Proof
  rpt gen_tac >>
  qspecl_then [`P`, `\a. EL a h`, `GENLIST I (LENGTH h)`]
    (mp_tac o AP_TERM ``LENGTH``) FILTER_MAP >>
  simp[MAP_GENLIST, combinTheory.o_DEF, GENLIST_ID]
QED

Theorem lower_budget_inj_list_length[local]:
  !f xs ys.
    ALL_DISTINCT xs /\ INJ f (set xs) (set ys) ==>
    LENGTH xs <= LENGTH ys
Proof
  rpt strip_tac >>
  `CARD (set xs) <= CARD (set ys)` by
    metis_tac[INJ_CARD, FINITE_LIST_TO_SET] >>
  `CARD (set xs) = LENGTH xs` by
    metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  metis_tac[CARD_LIST_TO_SET, LESS_EQ_TRANS]
QED

Theorem lower_budget_pairs_count:
  !h pair.
    lower_history_pairs h pair ==>
    LENGTH (FILTER lower_event_allocates h) <= SUC (lower_history_count h)
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac kall_tac)) o
    REWRITE_RULE [lower_history_pairs_def]) >>
  qabbrev_tac `allocs = FILTER (\a. lower_event_allocates (EL a h))
    (GENLIST I (LENGTH h))` >>
  qabbrev_tac `effects = FILTER (\a. lower_event_consumes (EL a h))
    (GENLIST I (LENGTH h)) ++ [LENGTH h]` >>
  `ALL_DISTINCT allocs` by
    simp[Abbr`allocs`, FILTER_ALL_DISTINCT, ALL_DISTINCT_GENLIST] >>
  `INJ pair (set allocs) (set effects)` by
    (simp_tac (srw_ss())
       [INJ_DEF, Abbr`allocs`, Abbr`effects`, MEM_FILTER, MEM_GENLIST] >>
     rpt strip_tac >>
     metis_tac[prim_recTheory.LESS_REFL]) >>
  qspecl_then [`pair`, `allocs`, `effects`] mp_tac lower_budget_inj_list_length >>
  simp[Abbr`allocs`, Abbr`effects`, lower_budget_filter_indices_length,
       lower_history_count_def]
QED

Theorem lower_budget_completed_pairs_count:
  !h pair q.
    lower_history_pairs h pair /\ lower_history_current h pair q ==>
    LENGTH (FILTER (\a. lower_event_allocates (EL a h) /\
      pair a < LENGTH h) (GENLIST I (LENGTH h))) <= lower_history_count h /\
    (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
      LENGTH (FILTER lower_event_allocates h) <= lower_history_count h)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (FILTER (\a. lower_event_allocates (EL a h) /\
    pair a < LENGTH h) (GENLIST I (LENGTH h))) <= lower_history_count h` by
    (qpat_x_assum `lower_history_pairs h pair`
       (CONJUNCTS_THEN2 assume_tac
         (CONJUNCTS_THEN2 assume_tac kall_tac) o
         REWRITE_RULE [lower_history_pairs_def]) >>
     qabbrev_tac `allocs = FILTER (\a. lower_event_allocates (EL a h) /\
       pair a < LENGTH h) (GENLIST I (LENGTH h))` >>
     qabbrev_tac `effects = FILTER (\a. lower_event_consumes (EL a h))
       (GENLIST I (LENGTH h))` >>
     `ALL_DISTINCT allocs` by
       simp[Abbr`allocs`, FILTER_ALL_DISTINCT, ALL_DISTINCT_GENLIST] >>
     `INJ pair (set allocs) (set effects)` by
       (simp_tac (srw_ss())
          [INJ_DEF, Abbr`allocs`, Abbr`effects`, MEM_FILTER, MEM_GENLIST] >>
        rpt strip_tac >>
        metis_tac[prim_recTheory.LESS_REFL]) >>
     qspecl_then [`pair`, `allocs`, `effects`] mp_tac lower_budget_inj_list_length >>
     simp[Abbr`allocs`, Abbr`effects`, lower_budget_filter_indices_length,
          lower_history_count_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
  `FILTER (\a. lower_event_allocates (EL a h) /\ pair a < LENGTH h)
     (GENLIST I (LENGTH h)) =
   FILTER (\a. lower_event_allocates (EL a h)) (GENLIST I (LENGTH h))` by
    (rw[FILTER_EQ, MEM_GENLIST] >>
     fs[lower_history_current_def] >> metis_tac[]) >>
  fs[lower_budget_filter_indices_length]
QED

Theorem lower_budget_path_forget_checks:
  !D lo explicit ctx p h marks q.
    lower_budget_path T (D,lo,explicit,ctx) p h marks q ==>
    lower_budget_path F (D,lo,explicit,ctx) p h marks q
Proof
  qsuff_tac
    `!checked cfg p h marks q.
      lower_budget_path checked cfg p h marks q ==>
      lower_budget_path F cfg p h marks q`
  >- metis_tac[] >>
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- metis_tac[lower_budget_path_entry]
  >- metis_tac[lower_budget_path_next]
  >- metis_tac[lower_budget_path_block]
  >- metis_tac[lower_budget_path_call]
  >- metis_tac[lower_budget_path_ret]
QED

Theorem lower_budget_remaining_step:
  !k h e remaining.
    lower_history_count (h ++ [e]) + remaining = k ==>
    lower_history_count h +
      (if lower_event_consumes e then SUC remaining else remaining) = k
Proof
  rpt gen_tac >> Cases_on `lower_event_consumes e` >>
  simp[lower_history_count_def, FILTER_APPEND]
QED

Theorem gas_outcome_full_budget_forget:
  !k C DF lo explicit ctx func PG tops cx st0 source es s G tn Q R.
    gas_outcome_full_budget k C (DF,lo,explicit,ctx,func,PG)
      tops cx st0 source (es,s,G,tn) Q R ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG)
      tops cx st0 source (es,s,G,tn) Q R
Proof
  simp[gas_outcome_full_budget_def]
QED

Theorem gas_outcome_full_budget_prefix:
  !k C DF lo explicit ctx func PG tops cx st0 source es s G tn Q R
    H h marks q.
    gas_outcome_full_budget k C (DF,lo,explicit,ctx,func,PG)
      tops cx st0 source (es,s,G,tn) Q R /\
    (!obs. entry_calls_within k s.vs_outcomes
      (\xs. SOME (C (es with <| outcomes := SOME xs; gas_obs := obs |>)))) /\
    lower_budget_path T (DF H,lo,explicit,ctx)
      <| bp_stack := []; bp_params := PG; bp_prov := G;
         bp_taint := tn; bp_fn := func; bp_state := s |>
      h marks q ==>
    ?remaining pair.
      lower_history_count h + remaining = k /\
      LENGTH (FILTER lower_event_allocates h) <= k /\
      (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
        SUC (LENGTH (FILTER lower_event_allocates h)) <= k) /\
      lower_history_pairs h pair /\ lower_history_current h pair q /\
      (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
        ?fn i pre op sz post. lower_alloc_record h n fn i pre op sz post)
Proof
  rw[gas_outcome_full_budget_def, lower_budget_continuation_def] >>
  metis_tac[lower_budget_path_forget_checks]
QED

Theorem lower_budget_raw_variant_entry:
  !tops am tx fmp vs_in vs.
    gas_variant vs_in
      (vs with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) /\ initial_venom_state_rel tops am tx vs ==>
    initial_venom_state_rel tops am tx vs_in /\
    vs_in.vs_fmp = fmp /\ vs_in.vs_initial_fmp = fmp /\
    vs_in.vs_outcomes = vs.vs_outcomes /\
    vs_in.vs_call_ctx = vs.vs_call_ctx /\
    vs_in.vs_memory = vs.vs_memory
Proof
  rw[gas_variant_def, venomStateTheory.venom_state_component_equality] >>
  fs[initial_venom_state_rel_def, venom_env_rel_def] >>
  metis_tac[]
QED
