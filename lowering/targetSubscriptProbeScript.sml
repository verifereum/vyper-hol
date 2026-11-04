(* Relation-level probes only: not a counterexample to target_case. *)
Theory targetSubscriptProbe
Ancestors
  venomMemProps moduleLowering moduleLoweringProps venomStepProps vyperCompiler compileEnv vyperStoragePlaceRegion vyperStorageLayoutSafety vfmState
  words finite_map combin vyperValue targetSubscriptSim
  emitHelperProps emitHelper exprLoweringProps venomExecSemantics venomState venomInst
  fragExec vyperInterpreter vyperContext vyperState vyperStorageBackend exprSimHyps
  calleeTransport

Theorem frag_exec_refutation_probe:
  !ctx sa sb P Q R fn s.
    fn_has_code sa sb fn /\ P s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!s'. Q s' /\ ~s'.vs_halted /\
      s'.vs_current_bb = sb.cs_current_bb /\
      s'.vs_inst_idx = LENGTH sb.cs_current_insts ==>
      ?fuel r. run_from fuel ctx fn s' = r /\ (!e. r <> Error e) /\
        !fuel'. run_from fuel' ctx fn s <> r) /\
    (!fuel r. run_from fuel ctx fn s = r ==> ~(exit_result r /\ R r)) ==>
    ~frag_exec ctx sa sb P Q R
Proof
  rpt gen_tac >> strip_tac >>
  simp[frag_exec_def] >>
  qexistsl [`fn`,`s`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> spose_not_then strip_assume_tac >>
      first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  metis_tac[]
QED

Theorem probe_STOP_observation:
  !ctx fn s bb id.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] []) ==>
    run_from 0 ctx fn s = Halt (halt_state (s with vs_returndata := []))
Proof
  rpt strip_tac >> irule run_from_halt >>
  qexistsl [`bb`,`mk_inst id STOP [] []`] >>
  simp[mk_inst_def, Once step_inst_base_def]
QED

Theorem probe_STOP_distinguishes_no_halt:
  !ctx fn s0 s bb id.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] []) /\
    (!fuel t. run_from fuel ctx fn s0 <> Halt t) ==>
    ?fuel r. run_from fuel ctx fn s = r /\ (!e. r <> Error e) /\
      !fuel'. run_from fuel' ctx fn s0 <> r
Proof
  rpt strip_tac >> drule_all probe_STOP_observation >> strip_tac >>
  qexistsl [`0`,`Halt (halt_state (s with vs_returndata := []))`] >>
  simp[] >> metis_tac[exec_result_distinct]
QED

Theorem probe_RET_literals:
  !id ss.
    step_inst_base (mk_inst id RET [Lit 0w; Lit 0w] []) ss =
    IntRet <| iret_values := [0w]; iret_adopt_fmp := NONE |> ss
Proof
  simp[step_inst_base_def, mk_inst_def, eval_operands_def, eval_operand_def]
QED

Theorem probe_clear_tail:
  !ss.
    run_inst_seq
      [mk_inst 0 SSTORE [Lit 0w; Lit 0w] [];
       mk_inst 1 SSTORE [Lit 1w; Lit 0w] [];
       mk_inst 2 RET [Lit 0w; Lit 0w] []] ss =
    IntRet <| iret_values := [0w]; iret_adopt_fmp := NONE |>
      (sstore 1w 0w (sstore 0w 0w ss))
Proof
  simp[run_inst_seq_def, step_SSTORE_literals, probe_RET_literals]
QED

Definition probe_clear_block_def:
  probe_clear_block = <| bb_label := "entry";
    bb_instructions :=
      [mk_inst 0 SSTORE [Lit 0w; Lit 0w] [];
       mk_inst 1 SSTORE [Lit 1w; Lit 0w] [];
       mk_inst 2 RET [Lit 0w; Lit 0w] []] |>
End

Definition probe_clear_function_def:
  probe_clear_function = mk_raw_function "shrink" [probe_clear_block]
End

Theorem probe_clear_exec_block:
  !fuel ctx ss.
    ss.vs_inst_idx = 0 ==>
    exec_block fuel ctx probe_clear_block ss =
    IntRet <| iret_values := [0w]; iret_adopt_fmp := NONE |>
      ((sstore 1w 0w (sstore 0w 0w ss)) with vs_inst_idx := 2)
Proof
  rpt strip_tac >>
  simp[Once exec_block_def, probe_clear_block_def, get_instruction_def,
       Once step_inst_def, step_SSTORE_literals, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, Once step_inst_def,
       step_SSTORE_literals, is_terminator_def, sstore_def] >>
  simp[Once exec_block_def, get_instruction_def, Once step_inst_def,
       probe_RET_literals, sstore_def]
QED

Theorem probe_clear_run_blocks:
  !fuel ctx ss.
    ss.vs_current_bb = "entry" ==>
    run_blocks (SUC fuel) ctx probe_clear_function ss =
    IntRet <| iret_values := [0w]; iret_adopt_fmp := NONE |>
      ((sstore 1w 0w (sstore 0w 0w (ss with vs_inst_idx := 0)))
        with vs_inst_idx := 2)
Proof
  rpt strip_tac >>
  simp[Once run_blocks_def, probe_clear_function_def, mk_raw_function_def,
       lookup_block_def] >>
  simp[probe_clear_block_def, listTheory.FIND_thm,
       eval_phis_def, phi_prefix_length_def] >>
  rewrite_tac[GSYM probe_clear_block_def] >>
  simp[probe_clear_exec_block]
QED

Theorem probe_clear_invoke:
  !fuel ctx ss id out cs.
    lookup_function "shrink" ctx.ctx_functions = SOME probe_clear_function /\
    setup_callee probe_clear_function [] ss = SOME cs ==>
    step_inst (SUC fuel) ctx
      (mk_inst id INVOKE [Label "shrink"] [out]) ss =
    OK (update_var out 0w
      (merge_callee_state ss
        ((sstore 1w 0w (sstore 0w 0w (cs with vs_inst_idx := 0)))
          with vs_inst_idx := 2)))
Proof
  rpt strip_tac >>
  `cs.vs_current_bb = "entry"` by
    gvs[setup_callee_def, probe_clear_function_def, mk_raw_function_def,
        probe_clear_block_def] >>
  simp[Once step_inst_def, decode_invoke_def, eval_operands_def,
       probe_clear_run_blocks, bind_outputs_def, adopt_return_fmp_def]
QED

Theorem nested_capacity_probe:
  storage_subregion
    (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
    [ValueSubscript (IntV 0)] 1
    (ArrayTV (BaseTV BoolT) (Dynamic 1))
Proof
  EVAL_TAC >> simp[]
QED

(* Conditional on a declared isolated region. Inhabitation of a full context
   and reachability after an actual index are separate obligations. *)
Theorem nested_dead_header_discrepancy_probe:
  !cx mid name subs st.
    declared_storage_region cx mid name subs =
      SOME (F,0w,ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)) /\
    (!mid' name' subs' slot' tv'.
      declared_storage_region cx mid' name' subs' = SOME (F,slot',tv') /\
      (slot',tv') <>
        (0w,ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)) ==>
      ranges_disjoint 0 3 (w2n slot') (type_slot_size tv')) /\
    lookup_storage 0w st = 0w /\ lookup_storage 1w st = 0w ==>
    storage_agree (storage_dead cx F st) st (update_storage 1w 1w st) /\
    lookup_storage 0w (update_storage 1w 1w st) = 0w /\
    lookup_storage 1w st <> lookup_storage 1w (update_storage 1w 1w st)
Proof
  rpt strip_tac
  >- (simp[storage_agree_def] >> rpt strip_tac >>
      Cases_on `k = 1w`
      >- (gvs[] >>
          `storage_dead cx F st 1 b` by
            (pure_rewrite_tac[storage_dead_def] >>
             qexistsl [`mid`,`name`,`subs`,`0w`,
               `ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)`] >>
             simp[type_slot_size_def, dead_bytes_def, dimword_def,
                  fcpLib.INDEX_CONV ``dimindex (:256)``] >>
             rpt strip_tac >> first_x_assum irule >> simp[] >>
             goal_assum (drule_at Any)) >>
          gvs[]) >>
      simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM])
  >- gvs[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
  >> gvs[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
QED

(* Captured child selection consults only the child, not the parent length. *)
Theorem captured_child_extension_probe:
  !cx es.
    lookup_storage 1w (get_storage cx es F) = 0w ==>
    extend_place cx
      (PlaceR (StoragePlace F 1w (ArrayTV (BaseTV BoolT) (Dynamic 1))))
      (ValueSubscript (IntV 0)) es =
    (INR (Error (RuntimeError "array dynamic length oob")),es)
Proof
  simp[extend_place_storage_array_index, word_add_n2w]
QED

Theorem captured_child_extension_nonempty_probe:
  !cx es.
    lookup_storage 1w (get_storage cx es F) = 1w ==>
    extend_place cx
      (PlaceR (StoragePlace F 1w (ArrayTV (BaseTV BoolT) (Dynamic 1))))
      (ValueSubscript (IntV 0)) es =
    (INL (PlaceR (StoragePlace F 2w (BaseTV BoolT))),es)
Proof
  simp[extend_place_storage_array_index, word_add_n2w]
QED

(* Audit candidate (NOT a verified theorem counterexample):
   nocalls = F;
   bt = SubscriptTarget (TopLevelNameTarget (NONE,"outer"))
          (Literal (BaseT (UintT 256)) (IntL 0));
   e = Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE.
   Declare outer: DynArray[DynArray[bool,1],1] at slot zero.
   Initial source and machine: parent header 1, child header 1, element 0.
   Source shrink pops outer, returns index zero; it retains child header 1.
   A candidate *abstract* machine callee additionally clears child header.
   Since the child is now dead, expr_post's storage relation need not forbid
   that extra write. ctx/func are arbitrary theorem parameters, not required
   to be the output of compiling this particular source callee. This is an
   avenue to investigate, NOT permission to assume expr_sim_case.

   Premise ledger still OPEN:
   - concrete cx (code, layout, typing, supported_program, call safety),
     cenv (tables and locals), env, ctx and func have not been constructed;
   - target_case bt and both universal judgments for e are unproved;
   - target_pre requires expr_sim_inv, hence storage_layout_safe,
     contract_storage_well_formed, oracle_storage_ok, IS_SOME outcomes,
     typed states/accounts/context/functions, and target_indices_pre;
   - compile_get_target_ptr, fn_has_code, fn_inst_ids_distinct,
     local_ptrs_reserved and an initial stmt_state_rel need witnesses;
   - actual eval_base_place and call execution, exact machine suffix and
     failure of frag_exec remain unproved.
   Checked reductions above: a saved child pointer consults its own current
   header, independent of parent length, and produces either a permitted
   runtime error or a successful place depending on that header.
   A plain correctly implemented pop changes only the parent header on both
   sides; it does NOT itself create the discrepancy. Thus C0.1 alone cannot
   establish reachability, even with a source shrink operation.
*)
Theorem internal_index_syntactically_nopop_probe:
  ~expr_has_pop
    (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
Proof
  EVAL_TAC
QED

(* Executable-interface audit for C0.2.1 (not universal simulation):
   probe_clear_invoke now checks an actual INVOKE, with lookup_function and
   setup_callee premises exposed. probe_clear_run_blocks checks the body; no
   arbitrary post-state is substituted for a callee execution.

   Exact remaining universal interface for e from the ledger above:
   expr_sim_case F ctx func cenv cx e expands to
     !env ty es. expr_body_pre cenv cx env e es ==>
       !sa sb op res es' s0.
         lower_value compile_expr cenv ty e sa = (op,sb) /\
         (do result <- eval_expr cx e; read_result cx result od) es =
           (res,es') /\ expr_res_ok res /\ fn_has_code sa sb func /\
         fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
         frag_exec ctx sa sb
           (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
           (\s. ?v. res = INL v /\
             expr_post ctx func cenv cx e es sa sb s0 es' v op s)
           (expr_exit res).
   expr_vv_case has the same env/ty/es universality, then quantifies
   sa,sb,vv,res,es',s0; compile_expr replaces lower_value, eval_expr replaces
   eval_expr/read_result, expr_vv_res_ok replaces expr_res_ok, and vv_post
   replaces expr_post. Neither universal obligation is proved here.

   expr_body_pre includes expr_sim_inv, well_typed_expr, byte widths,
   allocation limits, call_evaluation_safe, no EVMRun, and supported module
   code for every internal call. All environments and admissible states,
   not just the selected initial storage, must be handled. In particular:
   - capacity one is NOT a proof of positive length. At length one the
     proposed source pop can shrink to zero; at length zero an unguarded
     pop errors, while the checked machine body always returns normally.
     No zero-length source execution or expr_exit proof has been supplied.
     A guard or rejecting machine branch would change the candidate;
     neither may be assumed as part of this checked body.
   - at length one, the extra slot-1 clear is harmless to the final storage
     relation only after proving the declared-region/dead-byte premises.
     Larger lengths would make this unconditional clear unsound; the
     capacity-one typing argument itself remains to be proved universally.
   - the actual label is internal_fn_label of cenv's function id, parameter
     types and constructor flag, not necessarily the literal "shrink".
     probe_clear_invoke deliberately exposes this unresolved linkage.
   - compile_call's returns_count > 0 branch allocates a return buffer,
     emits INVOKE with that many outputs, then stores the outputs in the
     buffer. With one output our RET [0,0] provides one user word; the last
     operand is a return-PC token discarded by RET. FMP is not adopted.
     Buffer allocation, store_multi_results, lower_value's unwrap and all
     fn_has_code slices are still separate obligations. A zero-output
     INVOKE cannot consume this one-output return (arity mismatch).
   - expr_post additionally requires stmt_state_rel, expr_val_rel,
     expr_val_at, preservation of old SOME variables and allocas, disjoint
     memory regions and locals_kept. vv_post additionally requires vv_holds
     and vv_at for the compiler's actual value_vv. Returning the integer
     zero is not by itself either postcondition.
   - eventual target refutation still needs target_case bt, a concrete
     target_pre witness, the full compiled target fragment and proof that
     no successful frag_exec/allowed exit exists. All remain open.
*)

(* Continuation audit for C0.2.2.1:
   frag_exec_refutation_probe handles BOTH existential alternatives. A bad
   actual endpoint alone cannot refute frag_exec. probe_STOP_observation
   checks the proposed suffix: append mk_inst id STOP [] [] exactly at
   sb's endpoint, in a function containing the fragment. Every nonhalted
   alleged endpoint at that instruction yields a Halt observation, regardless
   of its variables, memory, accounts or target_post fields. The result may
   depend on that endpoint state; probe_STOP_distinguishes_no_halt still
   excludes it if no fuel from the initial state yields any Halt.

   Missing for application to the captured-header candidate: a concrete fn
   containing the full lowered target plus this STOP; the exact endpoint
   instruction lookup for every proposed successful state; and proof that
   every fuel from the start aborts (or otherwise cannot produce any such
   Halt). Internal INVOKE consumes fuel, so out-of-fuel Error for small fuel
   must also be handled, not assumed to be Abort. A suitable more precise
   application premise is 'no fuel from the start yields Halt', allowing
   both Abort and Error. Finally the permitted-exit disjunct must be ruled
   out with expr_exit/target source success. None of those complete-target
   facts follows from the checked callee alone. The STOP probe establishes
   a non-Error distinguishing suffix interface, not a target counterexample.
*)

Definition probe_outer_type_def:
  probe_outer_type = ArrayT (ArrayT (BaseT BoolT) (Dynamic 1)) (Dynamic 1)
End

Definition probe_guarded_code_def:
  probe_guarded_code =
    [VariableDecl Private Storage "outer" probe_outer_type (SOME 0);
     FunctionDecl Internal Nonpayable F F "shrink" [] [] (BaseT (UintT 256))
       [If (Builtin (BaseT BoolT) (Bop Gt)
              [Builtin (BaseT (UintT 256)) Len
                [TopLevelName probe_outer_type (NONE,"outer")];
               Literal (BaseT (UintT 256)) (IntL 0)])
           [Expr (Pop (ArrayT (BaseT BoolT) (Dynamic 1))
                   (TopLevelNameTarget (NONE,"outer")))] [];
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]]
End

Definition probe_guarded_context_def:
  probe_guarded_context = empty_evaluation_context with
    <| sources := [(0w,[(NONE,probe_guarded_code)])];
       layouts := [(0w,([((NONE,"outer"),0)],[]))] |>
End

Definition probe_guarded_state_def:
  probe_guarded_state len = SND (set_storage_backend probe_guarded_context F
    (update_storage 0w (n2w len) (update_storage 1w 1w empty_storage))
    empty_state)
End

(* Concrete empty and singleton call results are checked below. These
   evaluator fixtures do not inhabit expr_sim_inv: see the no-oracle check.
   Neither universal expression simulation nor target_pre is established. *)

(* Gt on IntV uses integer$int_gt, explicitly nocompute in integerTheory. *)
Theorem probe_guard_comparisons[local]:
  (integer$int_gt (0:int) 0 = F) /\
  (integer$int_gt (1:int) 0 = T)
Proof
  simp[integerTheory.int_gt]
QED

Theorem probe_guarded_empty_return:
  FST (eval_expr probe_guarded_context
    (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
    (probe_guarded_state 0)) = INL (Value (IntV 0))
Proof
  EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[integerTheory.int_gt] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem probe_guarded_singleton_return:
  FST (eval_expr probe_guarded_context
    (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
    (probe_guarded_state 1)) = INL (Value (IntV 0))
Proof
  EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[integerTheory.int_gt] >> EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

(* The concrete evaluator fixtures above are not yet invariant witnesses:
   empty_state supplies NONE, whereas simulation requires an outcome oracle. *)
Theorem probe_guarded_state_no_oracle:
  !len. (probe_guarded_state len).outcomes = NONE
Proof
  gen_tac >> EVAL_TAC
QED

Theorem probe_guarded_fixture_not_invariant:
  !cenv env len.
    ~expr_sim_inv cenv probe_guarded_context env (probe_guarded_state len)
Proof
  simp[expr_sim_inv_def, probe_guarded_state_no_oracle]
QED

(* Symbolic operational contract: no typing or simulation premise is used. *)
Theorem probe_guarded_symbolic_call:
  !es n.
    n <= 1 /\
    lookup_storage 0w (get_storage probe_guarded_context es F) = n2w n ==>
    eval_expr probe_guarded_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
    (INL (Value (IntV 0)),
     if n = 0 then es else
       set_storage probe_guarded_context es F
         (update_storage 0w 0w (get_storage probe_guarded_context es F)))
Proof
  rpt strip_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[get_storage_backend_eq, get_storage_scopes] >>
  gvs[get_storage_def, probe_guarded_context_def,
      empty_evaluation_context_def, empty_call_txn_def] >>
  `n = 0 \/ n = 1` by decide_tac >> gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``set_storage_backend``,
    ``lookup_storage``]) >>
  simp[integerTheory.int_gt] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[return_def] >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[get_storage_backend_eq, get_storage_scopes, get_storage_def] >>
  simp[set_storage_backend_eq, set_storage_def, get_storage_def,
       probe_guarded_context_def, empty_evaluation_context_def,
       empty_call_txn_def, handle_function_def, return_def] >>
  simp[evaluation_state_component_equality]
QED

Theorem probe_guarded_symbolic_projections:
  !es n res es'.
    n <= 1 /\
    lookup_storage 0w (get_storage probe_guarded_context es F) = n2w n /\
    eval_expr probe_guarded_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
      (res,es') ==>
    res = INL (Value (IntV 0)) /\ es'.scopes = es.scopes /\
    lookup_storage 0w (get_storage probe_guarded_context es' F) = 0w /\
    (!k. k <> 0w ==>
      lookup_storage k (get_storage probe_guarded_context es' F) =
      lookup_storage k (get_storage probe_guarded_context es F))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all probe_guarded_symbolic_call >>
  Cases_on `n = 0` >>
  gvs[get_storage_after_set, lookup_storage_def, update_storage_def,
      APPLY_UPDATE_THM]
QED

Theorem probe_guarded_declared_region:
  !mid name subs tr slot tv.
    declared_storage_region probe_guarded_context mid name subs =
      SOME (tr,slot,tv) <=>
    mid = NONE /\ name = "outer" /\ subs = [] /\ tr = F /\ slot = 0w /\
    tv = ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)
Proof
  rpt gen_tac >> Cases_on `mid` >>
  simp[declared_storage_region_def] >>
  EVAL_TAC >>
  Cases_on `name = "outer"` >> gvs[] >>
  Cases_on `subs = []` >> gvs[] >>
  EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  metis_tac[]
QED

Theorem probe_guarded_pre_capacity:
  !cenv env e es.
    expr_body_pre cenv probe_guarded_context env e es ==>
    w2n (lookup_storage 0w (get_storage probe_guarded_context es F)) <= 1
Proof
  rpt strip_tac >>
  `contract_storage_well_formed probe_guarded_context es` by
    metis_tac[expr_body_pre_def, expr_sim_inv_def] >>
  `slots_in_range (get_storage probe_guarded_context es F) (w2n (0w:bytes32))
     (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))` by
    (qpat_assum `contract_storage_well_formed _ _` mp_tac >>
     simp[NoAsms, contract_storage_well_formed_def, get_storage_backend_eq,
          probe_guarded_declared_region]) >>
  qpat_x_assum `slots_in_range _ _ _` mp_tac >>
  simp[Once vyperLookupStorageTheory.slots_in_range_def,
       vyperStorageTheory.read_slot_def]
QED

Theorem probe_guarded_pre_call:
  !cenv env es.
    expr_body_pre cenv probe_guarded_context env
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es ==>
    eval_expr probe_guarded_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
    (INL (Value (IntV 0)),
     if lookup_storage 0w (get_storage probe_guarded_context es F) = 0w
     then es else set_storage probe_guarded_context es F
       (update_storage 0w 0w (get_storage probe_guarded_context es F)))
Proof
  rpt strip_tac >> drule probe_guarded_pre_capacity >> strip_tac >>
  qspec_then `es` mp_tac probe_guarded_symbolic_call >>
  disch_then (qspec_then
    `w2n (lookup_storage 0w (get_storage probe_guarded_context es F))` mp_tac) >>
  simp[]
QED

Theorem probe_guarded_pre_projections:
  !cenv env es res es'.
    expr_body_pre cenv probe_guarded_context env
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es /\
    eval_expr probe_guarded_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
      (res,es') ==>
    res = INL (Value (IntV 0)) /\ es'.scopes = es.scopes /\
    lookup_storage 0w (get_storage probe_guarded_context es' F) = 0w /\
    (!k. k <> 0w ==>
      lookup_storage k (get_storage probe_guarded_context es' F) =
      lookup_storage k (get_storage probe_guarded_context es F))
Proof
  rpt gen_tac >> strip_tac >>
  drule probe_guarded_pre_capacity >> strip_tac >>
  qspecl_then [`es`,
    `w2n (lookup_storage 0w (get_storage probe_guarded_context es F))`]
    mp_tac probe_guarded_symbolic_projections >>
  simp[]
QED

Theorem probe_guarded_empty_parent_dead:
  !st b. lookup_storage 0w st = 0w /\ b < 32 ==>
    storage_dead probe_guarded_context F st 1 b
Proof
  rpt strip_tac >>
  simp[storage_dead_def, probe_guarded_declared_region] >>
  simp[Once dead_bytes_def, type_slot_size_def, dimword_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  qexists_tac `0` >> simp[]
QED

Theorem probe_guarded_pre_call_dead:
  !cenv env es res es' b.
    expr_body_pre cenv probe_guarded_context env
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es /\
    eval_expr probe_guarded_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
      (res,es') /\ b < 32 ==>
    storage_dead probe_guarded_context F
      (get_storage probe_guarded_context es' F) 1 b
Proof
  rpt strip_tac >> drule_all probe_guarded_pre_projections >> strip_tac >>
  irule probe_guarded_empty_parent_dead >> simp[]
QED

(* Empty external oracle for the future invariant witness.  This interface
   alone does not establish the typing or simulation invariant. *)
Definition probe_guarded_inhabited_state_def:
  probe_guarded_inhabited_state =
    probe_guarded_state 1 with outcomes := SOME []
End

Theorem probe_guarded_inhabited_oracle:
  IS_SOME probe_guarded_inhabited_state.outcomes /\
  outcomes_accounts_typed probe_guarded_inhabited_state.outcomes /\
  oracle_storage_ok probe_guarded_context probe_guarded_inhabited_state
Proof
  simp[probe_guarded_inhabited_state_def, outcomes_accounts_typed_def,
       vyperTypeStoragePreservationTheory.oracle_storage_ok_def]
QED

Theorem probe_guarded_inhabited_storage:
  lookup_storage 0w
    (get_storage probe_guarded_context probe_guarded_inhabited_state F) = 1w /\
  lookup_storage 1w
    (get_storage probe_guarded_context probe_guarded_inhabited_state F) = 1w /\
  probe_guarded_inhabited_state.scopes = (probe_guarded_state 1).scopes
Proof
  EVAL_TAC
QED

Theorem probe_guarded_inhabited_call:
  eval_expr probe_guarded_context
    (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
    probe_guarded_inhabited_state =
  (INL (Value (IntV 0)),
   set_storage probe_guarded_context probe_guarded_inhabited_state F
     (update_storage 0w 0w
       (get_storage probe_guarded_context probe_guarded_inhabited_state F)))
Proof
  qspec_then `probe_guarded_inhabited_state` mp_tac
    probe_guarded_symbolic_call >>
  disch_then (qspec_then `1` mp_tac) >>
  simp[probe_guarded_inhabited_storage]
QED

Theorem probe_guarded_context_typed:
  context_well_typed probe_guarded_context
Proof
  EVAL_TAC
QED

Theorem probe_guarded_module_code:
  !src. get_module_code probe_guarded_context src =
    if src = NONE then SOME probe_guarded_code else NONE
Proof
  Cases >> EVAL_TAC
QED

Definition probe_guarded_env_def:
  probe_guarded_env = <|
    current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY |+ ((NONE,"outer"), Type probe_outer_type);
    type_defs := FEMPTY;
    fn_sigs := FEMPTY |+ ((NONE,"shrink"),
      <|param_types := []; num_defaults := 0; ret_ty := BaseT (UintT 256)|>);
    flag_members := FEMPTY |>
End

Theorem probe_guarded_body_typed:
  ?env_after. type_stmts probe_guarded_env (BaseT (UintT 256))
    [If (Builtin (BaseT BoolT) (Bop Gt)
           [Builtin (BaseT (UintT 256)) Len
             [TopLevelName probe_outer_type (NONE,"outer")];
            Literal (BaseT (UintT 256)) (IntL 0)])
        [Expr (Pop (ArrayT (BaseT BoolT) (Dynamic 1))
                (TopLevelNameTarget (NONE,"outer")))] [];
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))] = SOME env_after
Proof
  EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[]
QED

Theorem probe_guarded_env_context:
  env_context_consistent probe_guarded_env probe_guarded_context
Proof
  rw[vyperTypeInvariantsTheory.env_context_consistent_def,
     vyperTypeInvariantsTheory.fn_sigs_consistent_def,
     vyperTypeInvariantsTheory.fn_sigs_live_def,
     vyperTypeInvariantsTheory.fn_sigs_declared_complete_def,
     vyperTypeInvariantsTheory.toplevel_vtypes_complete_def,
     vyperTypeInvariantsTheory.bare_globals_complete_def,
     vyperTypeInvariantsTheory.bare_global_assignable_complete_def,
     vyperTypeInvariantsTheory.flag_members_complete_def,
     probe_guarded_env_def, probe_guarded_module_code] >>
  gvs[probe_guarded_code_def, FLOOKUP_UPDATE, FUNION_FEMPTY_1,
      FUNION_FEMPTY_2] >>
  EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[]
QED

Theorem probe_guarded_base_type:
  type_place_target probe_guarded_env
    (SubscriptTarget (TopLevelNameTarget (NONE,"outer"))
      (Literal (BaseT (UintT 256)) (IntL 0))) =
    SOME (Type (ArrayT (BaseT BoolT) (Dynamic 1)))
Proof
  EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC
QED

Theorem probe_guarded_call_type:
  well_typed_expr probe_guarded_env
    (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_guarded_callable:
  !fn fm nr args dflts ret body.
    lookup_callable_function probe_guarded_context.in_deploy fn
      probe_guarded_code = SOME (fm,nr,args,dflts,ret,body) ==>
    fn = "shrink" /\ fm = Nonpayable /\ nr = F /\ args = [] /\
    dflts = [] /\ ret = BaseT (UintT 256) /\
    body = [If (Builtin (BaseT BoolT) (Bop Gt)
           [Builtin (BaseT (UintT 256)) Len
             [TopLevelName probe_outer_type (NONE,"outer")];
            Literal (BaseT (UintT 256)) (IntL 0)])
        [Expr (Pop (ArrayT (BaseT BoolT) (Dynamic 1))
                (TopLevelNameTarget (NONE,"outer")))] [];
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]
Proof
  rpt gen_tac >> Cases_on `fn = "shrink"` >>
  EVAL_TAC >> gvs[]
QED

Theorem probe_guarded_functions_typed:
  functions_well_typed probe_guarded_context
Proof
  rewrite_tac[vyperTypeInvariantsTheory.functions_well_typed_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[probe_guarded_module_code] >>
  drule probe_guarded_callable >> strip_tac >> gvs[] >>
  qexists_tac `probe_guarded_env with <|fn_sigs := fn_sigs;
    bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
    toplevel_vtypes := toplevel_vtypes; flag_members := flag_members|>` >>
  qpat_x_assum `toplevel_vtypes_complete _ _` mp_tac >>
  simp[vyperTypeInvariantsTheory.toplevel_vtypes_complete_def,
       probe_guarded_module_code, probe_guarded_code_def] >>
  strip_tac >>
  `IS_SOME (lookup_var_slot_from_layout probe_guarded_context F NONE "outer")`
    by EVAL_TAC >>
  first_x_assum drule >> strip_tac >>
  `FLOOKUP bare_globals (NONE,"outer") = NONE` by
    (Cases_on `FLOOKUP bare_globals (NONE,"outer")` >> simp[] >>
     qpat_x_assum `!src id ty. FLOOKUP bare_globals _ = _ ==> _` drule >>
     CONV_TAC (computeLib.RESTR_EVAL_CONV [``FLOOKUP``]) >> simp[]) >>
  `FLOOKUP bare_global_assignable (NONE,"outer") = NONE` by
    (Cases_on `FLOOKUP bare_global_assignable (NONE,"outer")` >> simp[] >>
     qpat_x_assum `!src id ty. FLOOKUP bare_global_assignable _ = _ ==> _` drule >>
     CONV_TAC (computeLib.RESTR_EVAL_CONV [``FLOOKUP``]) >> simp[]) >>
  qpat_x_assum `FLOOKUP toplevel_vtypes _ = _` mp_tac >>
  qpat_x_assum `FLOOKUP bare_globals _ = NONE` mp_tac >>
  qpat_x_assum `FLOOKUP bare_global_assignable _ = NONE` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``FLOOKUP``]) >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``FLOOKUP``]) >>
  simp[]
QED

Theorem probe_guarded_captured_base:
  eval_base_place probe_guarded_context
    (SubscriptTarget (TopLevelNameTarget (NONE,"outer"))
      (Literal (BaseT (UintT 256)) (IntL 0)))
    probe_guarded_inhabited_state =
  (INL (PlaceR (StoragePlace F 1w (ArrayTV (BaseTV BoolT) (Dynamic 1)))),
   probe_guarded_inhabited_state)
Proof
  EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem probe_guarded_storage_var_info:
  !mid name b off tv.
    storage_var_info probe_guarded_context mid name = SOME (b,off,tv) <=>
    mid = NONE /\ name = "outer" /\ b = F /\ off = 0 /\
    tv = ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)
Proof
  rpt gen_tac >> Cases_on `mid` >>
  simp[vyperLookupStorageTheory.storage_var_info_def, probe_guarded_module_code] >>
  Cases_on `name = "outer"` >> gvs[] >> EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC >> simp[]
QED

Theorem probe_guarded_layout_safe:
  storage_layout_safe probe_guarded_context
Proof
  simp[storage_layout_safe_def, probe_guarded_declared_region,
       vyperLookupStorageTheory.well_formed_layout_def,
       probe_guarded_storage_var_info] >>
  EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem probe_guarded_inhabited_storage_typed:
  contract_storage_well_formed probe_guarded_context
    probe_guarded_inhabited_state
Proof
  simp[contract_storage_well_formed_def, probe_guarded_declared_region,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       probe_guarded_storage_var_info, get_storage_backend_eq] >>
  EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC >> simp[] >>
  CONV_TAC (RAND_CONV numLib.num_CONV) >>
  pure_once_rewrite_tac[vyperLookupStorageTheory.slots_in_range_def] >>
  EVAL_TAC >> simp[dimword_def,
    fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Definition probe_guarded_cenv_def:
  probe_guarded_cenv ce = ce with <|
    ce_vars := FEMPTY; ce_var_type := (\id. NONE);
    ce_struct_fields := FEMPTY; ce_hashmap_info := (\nsid. NONE);
    ce_module_vars := FEMPTY |+ ((NONE,"outer"), StorageLoc 0w);
    ce_module_var_type := (\nsid. if nsid = (NONE,"outer")
                                  then SOME probe_outer_type else NONE) |>
End

Theorem probe_guarded_inhabited_empty_scopes:
  probe_guarded_inhabited_state.scopes = []
Proof
  EVAL_TAC
QED

Theorem probe_guarded_inhabited_not_env_consistent:
  !env. ~env_consistent env probe_guarded_context
    probe_guarded_inhabited_state
Proof
  simp[vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_scopes_consistent_def,
       probe_guarded_inhabited_empty_scopes]
QED

Definition probe_guarded_ready_state_def:
  probe_guarded_ready_state =
    probe_guarded_inhabited_state with scopes := [FEMPTY]
End

Theorem probe_guarded_ready_env:
  env_consistent probe_guarded_env probe_guarded_context
    probe_guarded_ready_state
Proof
  simp[vyperTypeInvariantsTheory.env_consistent_def,
       probe_guarded_env_context] >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem probe_guarded_ready_storage:
  get_storage probe_guarded_context probe_guarded_ready_state F =
    get_storage probe_guarded_context probe_guarded_inhabited_state F
Proof
  simp[probe_guarded_ready_state_def, get_storage_scopes]
QED

Theorem probe_guarded_ready_oracle:
  IS_SOME probe_guarded_ready_state.outcomes /\
  outcomes_accounts_typed probe_guarded_ready_state.outcomes /\
  oracle_storage_ok probe_guarded_context probe_guarded_ready_state
Proof
  simp[probe_guarded_ready_state_def, probe_guarded_inhabited_state_def,
       outcomes_accounts_typed_def,
       vyperTypeStoragePreservationTheory.oracle_storage_ok_def]
QED

Theorem probe_guarded_ready_storage_typed:
  contract_storage_well_formed probe_guarded_context probe_guarded_ready_state
Proof
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `probe_guarded_inhabited_state` >>
  simp[probe_guarded_inhabited_storage_typed,
       probe_guarded_ready_state_def, get_storage_scopes]
QED

Theorem probe_guarded_ready_inv:
  !ce. expr_sim_inv (probe_guarded_cenv ce) probe_guarded_context
    probe_guarded_env probe_guarded_ready_state
Proof
  gen_tac >>
  simp[expr_sim_inv_def, probe_guarded_ready_env,
       probe_guarded_context_typed, probe_guarded_functions_typed,
       probe_guarded_ready_storage_typed, probe_guarded_layout_safe,
       probe_guarded_ready_oracle, probe_guarded_cenv_def,
       probe_guarded_env_def, probe_guarded_module_code] >>
  EVAL_TAC >> simp[] >> gen_tac >> Cases_on `addr = 0w` >> simp[]
QED

Theorem probe_guarded_ready_call:
  eval_expr probe_guarded_context
    (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
    probe_guarded_ready_state =
  (INL (Value (IntV 0)),
   set_storage probe_guarded_context probe_guarded_ready_state F
     (update_storage 0w 0w
       (get_storage probe_guarded_context probe_guarded_ready_state F)))
Proof
  qspec_then `probe_guarded_ready_state` mp_tac probe_guarded_symbolic_call >>
  disch_then (qspec_then `1` mp_tac) >>
  simp[probe_guarded_ready_storage, probe_guarded_inhabited_storage]
QED

Theorem probe_guarded_ready_captured_base:
  eval_base_place probe_guarded_context
    (SubscriptTarget (TopLevelNameTarget (NONE,"outer"))
      (Literal (BaseT (UintT 256)) (IntL 0)))
    probe_guarded_ready_state =
  (INL (PlaceR (StoragePlace F 1w (ArrayTV (BaseTV BoolT) (Dynamic 1)))),
   probe_guarded_ready_state)
Proof
  EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem probe_guarded_supported_probe:
  ~supported_program probe_guarded_code
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_guarded_no_call_body_pre:
  !ce env es.
    ~expr_body_pre ce probe_guarded_context env
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es
Proof
  simp[expr_body_pre_def, vyperTypeCallGraphTheory.int_calls_expr_def,
       probe_guarded_module_code, probe_guarded_supported_probe]
QED

(* Admission-first replacement candidate; no simulation claim. *)
Definition probe_copy_code_def:
  probe_copy_code =
    [VariableDecl Private Storage "outer" probe_outer_type (SOME 0);
     VariableDecl Private Storage "donor" probe_outer_type (SOME 3);
     FunctionDecl Internal Nonpayable F F "shrink" [] [] (BaseT (UintT 256))
       [Assign (BaseTarget (TopLevelNameTarget (NONE,"outer")))
          (TopLevelName probe_outer_type (NONE,"donor"));
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]]
End

Theorem probe_copy_not_supported:
  ~supported_program probe_copy_code
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_copy_call_supported:
  supported_expr probe_copy_code
    (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_copy_call_nopop:
  ~expr_has_pop
    (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
Proof
  EVAL_TAC
QED

Theorem probe_copy_assignment_admission_probe:
  ~supported_assignment probe_copy_code []
    (BaseTarget (TopLevelNameTarget (NONE,"outer")))
    (TopLevelName probe_outer_type (NONE,"donor"))
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_copy_rhs_admission_probe:
  ~supported_expr probe_copy_code
    (TopLevelName probe_outer_type (NONE,"donor"))
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_copy_target_admission_probe:
  supported_target_info probe_copy_code []
    (TopLevelNameTarget (NONE,"outer")) = NONE
Proof
  EVAL_TAC >> simp[]
QED

(* The Bool leaf is not a full storage word; nesting does not remove this
   admission guard. Equal copy layouts alone do not admit the assignment. *)
Theorem probe_copy_storage_type_rejected:
  ~supported_full_word_type (BaseT BoolT) /\
  ~supported_storage_type probe_copy_code probe_outer_type
Proof
  EVAL_TAC >> simp[]
QED

(* Full-word-leaf admission probe, distinct from both rejected candidates. *)
Definition probe_word_outer_type_def:
  probe_word_outer_type =
    ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Dynamic 1)
End

Definition probe_word_copy_code_def:
  probe_word_copy_code =
    [VariableDecl Private Storage "outer" probe_word_outer_type (SOME 0);
     VariableDecl Private Storage "donor" probe_word_outer_type (SOME 3);
     FunctionDecl Internal Nonpayable F F "shrink" [] [] (BaseT (UintT 256))
       [Assign (BaseTarget (TopLevelNameTarget (NONE,"outer")))
          (TopLevelName probe_word_outer_type (NONE,"donor"));
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]]
End

Theorem probe_word_copy_supported:
  supported_program probe_word_copy_code
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_word_copy_storage_supported:
  supported_storage_type probe_word_copy_code probe_word_outer_type
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_word_copy_assignment_supported:
  supported_assignment probe_word_copy_code []
    (BaseTarget (TopLevelNameTarget (NONE,"outer")))
    (TopLevelName probe_word_outer_type (NONE,"donor"))
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_word_copy_rhs_supported:
  supported_expr probe_word_copy_code
    (TopLevelName probe_word_outer_type (NONE,"donor"))
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_word_copy_target_info:
  supported_target_info probe_word_copy_code []
    (TopLevelNameTarget (NONE,"outer")) = SOME (ValPT probe_word_outer_type)
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_word_copy_call_supported:
  supported_expr probe_word_copy_code
    (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
Proof
  EVAL_TAC >> simp[]
QED

(* Symbolic copy probe: keep all caller-state fields arbitrary. *)
Definition probe_word_context_def:
  probe_word_context = empty_evaluation_context with
    <| sources := [(0w,[(NONE,probe_word_copy_code)])];
       layouts := [(0w,([((NONE,"outer"),0);((NONE,"donor"),3)],[]))];
       stk := [(NONE,"caller")] |>
End

Theorem probe_word_copy_symbolic_success:
  !es n m.
    n <= 1 /\ (n = 1 ==> m <= 1) /\
    lookup_storage 3w (get_storage probe_word_context es F) = n2w n /\
    lookup_storage 4w (get_storage probe_word_context es F) = n2w m ==>
    ?es'. eval_expr probe_word_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
      (INL (Value (IntV 0)), es') /\ es'.scopes = es.scopes /\
      es' = set_storage probe_word_context es F
        (if n = 0 then
           update_storage 0w 0w (get_storage probe_word_context es F)
         else if m = 0 then
           update_storage 1w 0w
             (update_storage 0w 1w (get_storage probe_word_context es F))
         else
           update_storage 2w
             (lookup_storage 5w (get_storage probe_word_context es F))
             (update_storage 1w 1w
               (update_storage 0w 1w (get_storage probe_word_context es F))))
Proof
  rpt strip_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[get_storage_backend_eq, get_storage_scopes] >>
  gvs[get_storage_def, probe_word_context_def,
      empty_evaluation_context_def, empty_call_txn_def] >>
  `n = 0 \/ n = 1` by decide_tac >> gvs[] >>
  Cases_on `m = 0` >> Cases_on `m = 1` >> gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[set_storage_backend_eq, handle_function_def, return_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[set_storage_backend_eq, handle_function_def, return_def] >>
  simp[evaluation_state_component_equality] >>
  qspec_then `lookup_storage 5w (es.accounts 0w).storage` mp_tac
    wordsTheory.w2n_lt >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  strip_tac >> simp[]
QED

Theorem probe_word_declared_region:
  !mid name subs tr slot tv.
    declared_storage_region probe_word_context mid name subs =
      SOME (tr,slot,tv) <=>
    mid = NONE /\ subs = [] /\ tr = F /\
    tv = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1) /\
    ((name = "outer" /\ slot = 0w) \/ (name = "donor" /\ slot = 3w))
Proof
  rpt gen_tac >> Cases_on `mid` >>
  simp[declared_storage_region_def] >> EVAL_TAC >>
  Cases_on `name = "outer"` >> gvs[] >>
  Cases_on `name = "donor"` >> gvs[] >>
  Cases_on `subs = []` >> gvs[] >> EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  metis_tac[]
QED

Theorem probe_word_pre_shapes:
  !cenv env e es.
    expr_body_pre cenv probe_word_context env e es ==>
    w2n (lookup_storage 3w (get_storage probe_word_context es F)) <= 1 /\
    (lookup_storage 3w (get_storage probe_word_context es F) = 1w ==>
     w2n (lookup_storage 4w (get_storage probe_word_context es F)) <= 1)
Proof
  rpt gen_tac >> strip_tac >>
  `contract_storage_well_formed probe_word_context es` by
    metis_tac[expr_body_pre_def, expr_sim_inv_def] >>
  `slots_in_range (get_storage probe_word_context es F) 3
     (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1))` by
    (qpat_assum `contract_storage_well_formed _ _` mp_tac >>
     simp[NoAsms, contract_storage_well_formed_def, get_storage_backend_eq,
          probe_word_declared_region] >> strip_tac >>
     first_x_assum (qspecl_then [`"donor"`,`3w`] mp_tac) >>
     simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  qpat_x_assum `slots_in_range _ _ _` mp_tac >>
  simp[Once vyperLookupStorageTheory.slots_in_range_def,
       vyperStorageTheory.read_slot_def] >>
  strip_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `dyn_slots_in_range _ _ _ _` mp_tac >>
  pure_rewrite_tac[arithmeticTheory.ONE,
    vyperLookupStorageTheory.slots_in_range_def] >>
  simp[vyperStorageTheory.read_slot_def]
QED

Theorem probe_word_dead_bytes:
  !st j b. b < 32 ==>
    (storage_dead probe_word_context F st j b <=>
     (lookup_storage 0w st = 0w /\ (j = 1 \/ j = 2)) \/
     (lookup_storage 1w st = 0w /\ j = 2) \/
     (lookup_storage 3w st = 0w /\ (j = 4 \/ j = 5)) \/
     (lookup_storage 4w st = 0w /\ j = 5))
Proof
  rpt strip_tac >>
  simp[storage_dead_def, probe_word_declared_region,
       type_slot_size_def, vyperStorageFrameTheory.ranges_disjoint_def,
       dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  dsimp[EXISTS_OR_THM, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  simp[dead_bytes_def, type_slot_size_def] >>
  Cases_on `lookup_storage 0w st = 0w` >>
  Cases_on `lookup_storage 3w st = 0w` >>
  Cases_on `lookup_storage 1w st = 0w` >>
  Cases_on `lookup_storage 4w st = 0w` >>
  gvs[GSYM arithmeticTheory.NOT_ZERO_LT_ZERO, wordsTheory.w2n_eq_0] >>
  decide_tac
QED

Theorem probe_word_copy_relational_agree:
  !st mt n m.
    n <= 1 /\ (n = 1 ==> m <= 1) /\
    lookup_storage 3w st = n2w n /\ lookup_storage 4w st = n2w m /\
    storage_agree (storage_dead probe_word_context F st) st mt ==>
    let live =
      if n = 0 then update_storage 0w 0w st
      else if m = 0 then update_storage 1w 0w (update_storage 0w 1w st)
      else update_storage 2w (lookup_storage 5w st)
             (update_storage 1w 1w (update_storage 0w 1w st))
    in storage_agree (storage_dead probe_word_context F live) live
      (update_storage 2w (lookup_storage 5w mt)
        (update_storage 1w (lookup_storage 4w mt)
          (update_storage 0w (lookup_storage 3w mt) mt)))
Proof
  rpt gen_tac >> strip_tac >>
  `n = 0 \/ n = 1` by decide_tac >> gvs[] >>
  Cases_on `m = 0` >> Cases_on `m = 1` >> gvs[] >>
  simp[storage_agree_def] >> rpt strip_tac >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  simp[storage_agree_def] >> strip_tac >>
  first_assum (qspecl_then [`k`,`b`] mp_tac) >>
  first_assum (qspecl_then [`3w`,`b`] mp_tac) >>
  first_assum (qspecl_then [`4w`,`b`] mp_tac) >>
  first_x_assum (qspecl_then [`5w`,`b`] mp_tac) >>
  simp[probe_word_dead_bytes, dimword_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> rpt strip_tac >>
  gvs[probe_word_dead_bytes] >>
  gvs[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM] >>
  gvs[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  Cases_on `k = 0w` >>
  gvs[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  Cases_on `k = 1w` >>
  gvs[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  Cases_on `k = 2w` >>
  gvs[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  `w2n k <> 1` by (strip_tac >>
    `k = 1w` by metis_tac[wordsTheory.n2w_w2n] >> gvs[]) >>
  gvs[] >>
  `w2n k <> 2` by (strip_tac >>
    `k = 2w` by metis_tac[wordsTheory.n2w_w2n] >> gvs[]) >>
  gvs[]
QED

Theorem probe_word_copy_pre_summary:
  !cenv env e0 es mt.
    expr_body_pre cenv probe_word_context env e0 es /\
    storage_agree
      (storage_dead probe_word_context F (get_storage probe_word_context es F))
      (get_storage probe_word_context es F) mt ==>
    ?es'. eval_expr probe_word_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
      (INL (Value (IntV 0)), es') /\ es'.scopes = es.scopes /\
      storage_agree
        (storage_dead probe_word_context F (get_storage probe_word_context es' F))
        (get_storage probe_word_context es' F)
        (update_storage 2w (lookup_storage 5w mt)
          (update_storage 1w (lookup_storage 4w mt)
            (update_storage 0w (lookup_storage 3w mt) mt)))
Proof
  rpt gen_tac >> strip_tac >>
  drule probe_word_pre_shapes >> strip_tac >>
  qspecl_then [`es`,
    `w2n (lookup_storage 3w (get_storage probe_word_context es F))`,
    `w2n (lookup_storage 4w (get_storage probe_word_context es F))`]
    mp_tac probe_word_copy_symbolic_success >>
  (impl_tac >- (simp[] >> strip_tac >>
    first_x_assum irule >>
    metis_tac[wordsTheory.n2w_w2n])) >>
  strip_tac >> qexists_tac `es'` >> simp[] >>
  simp[get_storage_def, set_storage_def] >>
  qspecl_then [`get_storage probe_word_context es F`, `mt`,
    `w2n (lookup_storage 3w (get_storage probe_word_context es F))`,
    `w2n (lookup_storage 4w (get_storage probe_word_context es F))`]
    mp_tac probe_word_copy_relational_agree >>
  (impl_tac >- (simp[] >> strip_tac >> first_x_assum irule >>
    metis_tac[wordsTheory.n2w_w2n])) >>
  simp[get_storage_def]
QED

(* Concrete compilation boundary only, not universal call simulation. *)
Definition probe_word_compiled_def:
  probe_word_compiled =
    let body =
      [Assign (BaseTarget (TopLevelNameTarget (NONE,"outer")))
         (TopLevelName probe_word_outer_type (NONE,"donor"));
       Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))] in
    let cenv = build_compile_env probe_word_copy_code
      Internal Nonpayable "shrink" [] (BaseT (UintT 256)) body F in
    SND (compile_internal_function cenv [] F F 0 F F F 0 body
      (SOME (BaseT (UintT 256))) (initial_compile_state "entry"))
End

Theorem probe_word_compiled_block_count:
  LENGTH probe_word_compiled.cs_blocks = 9
Proof
  EVAL_TAC
QED

Theorem probe_word_compiled_entry:
  EL 8 probe_word_compiled.cs_blocks =
    <| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 RETPC_PARAM [Lit 0w] ["%0"];
       mk_inst 1 ALLOCA [Lit 32w] ["%1"];
       mk_inst 2 ALLOCA [Lit 96w] ["%2"];
       mk_inst 3 ASSIGN [Lit 0w] ["%3"];
       mk_inst 4 JMP [Label "@wcopy_cond_0"] []] |>
Proof
  EVAL_TAC
QED

Theorem probe_word_compiled_load_cond:
  EL 7 probe_word_compiled.cs_blocks =
    <| bb_label := "@wcopy_cond_0"; bb_instructions :=
      [mk_inst 5 EQ [Var "%3"; Lit 3w] ["%4"];
       mk_inst 6 JNZ [Var "%4"; Label "@wcopy_exit_2";
         Label "@wcopy_body_1"] []] |>
Proof
  EVAL_TAC
QED

Theorem probe_word_compiled_load_body:
  EL 6 probe_word_compiled.cs_blocks =
    <| bb_label := "@wcopy_body_1"; bb_instructions :=
      [mk_inst 7 ADD [Lit 3w; Var "%3"] ["%5"];
       mk_inst 8 SLOAD [Var "%5"] ["%6"];
       mk_inst 9 MUL [Var "%3"; Lit 32w] ["%7"];
       mk_inst 10 ADD [Var "%2"; Var "%7"] ["%8"];
       mk_inst 11 MSTORE [Var "%8"; Var "%6"] [];
       mk_inst 12 ADD [Var "%3"; Lit 1w] ["%9"];
       mk_inst 13 ASSIGN [Var "%9"] ["%3"];
       mk_inst 14 JMP [Label "@wcopy_cond_0"] []] |>
Proof
  EVAL_TAC
QED

Theorem probe_word_compiled_load_exit:
  EL 5 probe_word_compiled.cs_blocks =
    <| bb_label := "@wcopy_exit_2"; bb_instructions :=
      [mk_inst 15 MLOAD [Var "%2"] ["%10"];
       mk_inst 16 ASSIGN [Lit 0w] ["%11"];
       mk_inst 17 JMP [Label "@dyn_cond_3"] []] |>
Proof
  EVAL_TAC
QED

Theorem probe_word_compiled_copy_cond:
  EL 4 probe_word_compiled.cs_blocks =
    <| bb_label := "@dyn_cond_3"; bb_instructions :=
      [mk_inst 18 LT [Var "%11"; Var "%10"] ["%12"];
       mk_inst 19 ISZERO [Var "%12"] ["%13"];
       mk_inst 20 JNZ [Var "%13"; Label "@dyn_exit_5";
         Label "@dyn_body_4"] []] |>
Proof
  EVAL_TAC
QED

Theorem probe_word_compiled_copy_body:
  EL 3 probe_word_compiled.cs_blocks =
    <| bb_label := "@dyn_body_4"; bb_instructions :=
      [mk_inst 21 MUL [Var "%11"; Lit 64w] ["%14"];
       mk_inst 22 ADD [Lit 32w; Var "%14"] ["%15"];
       mk_inst 23 ADD [Var "%2"; Var "%15"] ["%16"];
       mk_inst 24 MUL [Var "%11"; Lit 2w] ["%17"];
       mk_inst 25 ADD [Lit 1w; Var "%17"] ["%18"];
       mk_inst 26 ADD [Lit 0w; Var "%18"] ["%19"];
       mk_inst 27 ASSIGN [Lit 0w] ["%20"];
       mk_inst 28 JMP [Label "@wcopy_cond_6"] []] |>
Proof
  EVAL_TAC
QED

Theorem probe_word_compiled_elem_cond:
  EL 2 probe_word_compiled.cs_blocks =
    <| bb_label := "@wcopy_cond_6"; bb_instructions :=
      [mk_inst 29 EQ [Var "%20"; Lit 2w] ["%21"];
       mk_inst 30 JNZ [Var "%21"; Label "@wcopy_exit_8";
         Label "@wcopy_body_7"] []] |>
Proof
  EVAL_TAC
QED

Theorem probe_word_compiled_elem_body:
  EL 1 probe_word_compiled.cs_blocks =
    <| bb_label := "@wcopy_body_7"; bb_instructions :=
      [mk_inst 31 MUL [Var "%20"; Lit 32w] ["%22"];
       mk_inst 32 ADD [Var "%16"; Var "%22"] ["%23"];
       mk_inst 33 MLOAD [Var "%23"] ["%24"];
       mk_inst 34 ADD [Var "%19"; Var "%20"] ["%25"];
       mk_inst 35 SSTORE [Var "%25"; Var "%24"] [];
       mk_inst 36 ADD [Var "%20"; Lit 1w] ["%26"];
       mk_inst 37 ASSIGN [Var "%26"] ["%20"];
       mk_inst 38 JMP [Label "@wcopy_cond_6"] []] |>
Proof
  EVAL_TAC
QED

Theorem probe_word_compiled_elem_exit:
  EL 0 probe_word_compiled.cs_blocks =
    <| bb_label := "@wcopy_exit_8"; bb_instructions :=
      [mk_inst 39 ADD [Var "%11"; Lit 1w] ["%27"];
       mk_inst 40 ASSIGN [Var "%27"] ["%11"];
       mk_inst 41 JMP [Label "@dyn_cond_3"] []] |>
Proof
  EVAL_TAC
QED

Theorem probe_word_compiled_return:
  (probe_word_compiled.cs_current_bb,
   probe_word_compiled.cs_current_insts) =
    ("@dyn_exit_5",
     [mk_inst 42 SSTORE [Lit 0w; Var "%10"] [];
      mk_inst 43 RET [Lit 0w; Var "%0"] []])
Proof
  EVAL_TAC >> simp[]
QED

(* Checked artifact interface:
   - %0 is the return PC; %1 is an unused 32-byte return-value allocation.
   - %2 is a fresh 96-byte buffer. The first wcopy loop unconditionally
     SLOADs donor slots 3,4,5 into that buffer (counter %3, bound 3).
   - %10 is the donor outer length loaded from %2; counter %11 is tested
     against it by @dyn_cond_3. For each live outer element, the second
     wcopy loop copies TWO words, including the possibly dead child word,
     from %2+32+64*%11 to slots 1+2*%11 and 2+2*%11.
   - @dyn_exit_5 always stores %10 to slot 0 and returns stack value 0
     through %0. Thus destination writes are length-dependent, not an
     unconditional three-slot copy. The accepted relational full-copy
     theorem is not itself an execution theorem for this compiled code.
   These concrete equations do not establish either universal expression
   case judgment or an inhabited statement-state relation. *)

Theorem probe_word_conditional_copy_relational_agree:
  !st mt n m.
    n <= 1 /\ (n = 1 ==> m <= 1) /\
    lookup_storage 3w st = n2w n /\ lookup_storage 4w st = n2w m /\
    storage_agree (storage_dead probe_word_context F st) st mt ==>
    let live =
      if n = 0 then update_storage 0w 0w st
      else if m = 0 then update_storage 1w 0w (update_storage 0w 1w st)
      else update_storage 2w (lookup_storage 5w st)
             (update_storage 1w 1w (update_storage 0w 1w st))
    in storage_agree (storage_dead probe_word_context F live) live
      (if n = 0 then update_storage 0w 0w mt
       else update_storage 0w (lookup_storage 3w mt)
         (update_storage 2w (lookup_storage 5w mt)
           (update_storage 1w (lookup_storage 4w mt) mt)))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n = 0`
  >- (gvs[] >> simp[storage_agree_def] >> rpt strip_tac >>
      qpat_x_assum `storage_agree _ _ _` mp_tac >>
      simp[storage_agree_def] >> strip_tac >>
      first_x_assum (qspecl_then [`k`,`b`] mp_tac) >>
      simp[probe_word_dead_bytes] >>
      gvs[probe_word_dead_bytes, lookup_storage_def, update_storage_def,
          APPLY_UPDATE_THM] >>
      Cases_on `k = 0w` >>
      gvs[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  drule_all probe_word_copy_relational_agree >>
  simp[update_storage_def, UPDATE_COMMUTES,
       dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem probe_word_conditional_copy_pre_summary:
  !cenv env e0 es mt.
    expr_body_pre cenv probe_word_context env e0 es /\
    storage_agree
      (storage_dead probe_word_context F (get_storage probe_word_context es F))
      (get_storage probe_word_context es F) mt ==>
    ?es'. eval_expr probe_word_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
      (INL (Value (IntV 0)), es') /\ es'.scopes = es.scopes /\
      storage_agree
        (storage_dead probe_word_context F (get_storage probe_word_context es' F))
        (get_storage probe_word_context es' F)
        (if w2n (lookup_storage 3w (get_storage probe_word_context es F)) = 0
         then update_storage 0w 0w mt
         else update_storage 0w (lookup_storage 3w mt)
           (update_storage 2w (lookup_storage 5w mt)
             (update_storage 1w (lookup_storage 4w mt) mt)))
Proof
  rpt gen_tac >> strip_tac >>
  drule probe_word_pre_shapes >> strip_tac >>
  qspecl_then [`es`,
    `w2n (lookup_storage 3w (get_storage probe_word_context es F))`,
    `w2n (lookup_storage 4w (get_storage probe_word_context es F))`]
    mp_tac probe_word_copy_symbolic_success >>
  (impl_tac >- (simp[] >> strip_tac >>
    first_x_assum irule >> metis_tac[wordsTheory.n2w_w2n])) >>
  strip_tac >> qexists_tac `es'` >> simp[] >>
  simp[get_storage_def, set_storage_def] >>
  qspecl_then [`get_storage probe_word_context es F`, `mt`,
    `w2n (lookup_storage 3w (get_storage probe_word_context es F))`,
    `w2n (lookup_storage 4w (get_storage probe_word_context es F))`]
    mp_tac probe_word_conditional_copy_relational_agree >>
  (impl_tac >- (simp[] >> strip_tac >> first_x_assum irule >>
    metis_tac[wordsTheory.n2w_w2n])) >>
  simp[get_storage_def]
QED

(* Entry-first wrapper for the actual compiled artifact, including its open
   return block. No independently handwritten callee is substituted here. *)
Definition probe_word_function_def:
  probe_word_function = mk_raw_function "shrink"
    (REVERSE probe_word_compiled.cs_blocks ++
     [<| bb_label := probe_word_compiled.cs_current_bb;
         bb_instructions := probe_word_compiled.cs_current_insts |>])
End

Definition probe_word_entry_state_def:
  probe_word_entry_state s =
    update_var "%3" 0w
      (update_var "%2" (n2w (s.vs_alloca_next + 32))
        (update_var "%1" (n2w s.vs_alloca_next)
          (update_var "%0" s.vs_return_pc_token
            (s with <|
              vs_allocas := s.vs_allocas |+
                (1, (s.vs_alloca_next, 32)) |+
                (2, (s.vs_alloca_next + 32, 96));
              vs_alloca_next := s.vs_alloca_next + 128 |>))))
End

Theorem probe_word_entry_sequence:
  !s.
    FLOOKUP s.vs_allocas 1 = NONE /\
    FLOOKUP s.vs_allocas 2 = NONE ==>
    run_inst_seq (TAKE 4 (EL 8 probe_word_compiled.cs_blocks).bb_instructions) s =
      OK (probe_word_entry_state s)
Proof
  rpt strip_tac >>
  `32 MOD dimword (:256) = 32 /\ 96 MOD dimword (:256) = 96` by
    simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  simp[probe_word_compiled_entry] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, mk_inst_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_alloca_def, eval_operands_def, eval_operand_def, update_var_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_alloca_def, eval_operands_def, eval_operand_def,
       FLOOKUP_UPDATE, update_var_def] >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
       eval_operands_def, eval_operand_def, probe_word_entry_state_def,
       update_var_def]
QED

Theorem probe_word_entry_block:
  !s fuel ctx.
    FLOOKUP s.vs_allocas 1 = NONE /\
    FLOOKUP s.vs_allocas 2 = NONE /\ ~s.vs_halted ==>
    exec_block fuel ctx (EL 8 probe_word_compiled.cs_blocks)
      (s with vs_inst_idx := 0) =
    OK (jump_to "@wcopy_cond_0" (probe_word_entry_state s))
Proof
  rpt strip_tac >>
  irule exec_block_inst_seq_jmp >>
  conj_tac >- simp[probe_word_entry_state_def, update_var_def] >>
  qexists_tac `TAKE 4 (EL 8 probe_word_compiled.cs_blocks).bb_instructions` >>
  simp[probe_word_entry_sequence, probe_word_compiled_entry,
       mk_inst_def, is_terminator_def, get_instruction_def,
       probe_word_entry_state_def, update_var_def] >>
  rpt strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >>
  gvs[]
QED

Theorem probe_word_function_blocks:
  probe_word_function.fn_blocks =
    [EL 8 probe_word_compiled.cs_blocks;
     EL 7 probe_word_compiled.cs_blocks;
     EL 6 probe_word_compiled.cs_blocks;
     EL 5 probe_word_compiled.cs_blocks;
     EL 4 probe_word_compiled.cs_blocks;
     EL 3 probe_word_compiled.cs_blocks;
     EL 2 probe_word_compiled.cs_blocks;
     EL 1 probe_word_compiled.cs_blocks;
     EL 0 probe_word_compiled.cs_blocks;
     <| bb_label := "@dyn_exit_5";
        bb_instructions :=
          [mk_inst 42 SSTORE [Lit 0w; Var "%10"] [];
           mk_inst 43 RET [Lit 0w; Var "%0"] []] |>]
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_word_run_entry:
  !s fuel ctx.
    FLOOKUP s.vs_allocas 1 = NONE /\
    FLOOKUP s.vs_allocas 2 = NONE /\ ~s.vs_halted /\
    s.vs_current_bb = "entry" ==>
    run_blocks (SUC fuel) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function
      (jump_to "@wcopy_cond_0" (probe_word_entry_state s))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_unfold, probe_word_function_blocks,
       lookup_block_def, probe_word_compiled_entry, listTheory.FIND_thm] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  rewrite_tac[GSYM (SRULE [mk_inst_def] probe_word_compiled_entry)] >>
  simp[probe_word_entry_block, jump_to_def, probe_word_entry_state_def,
       update_var_def]
QED

Definition probe_word_load_state_def:
  probe_word_load_state s (i:bytes32) (bufaddr:bytes32) =
    let slot = 3w + i in
    let value = sload slot s in
    let offset = i * 32w in
    let addr = bufaddr + offset in
    let t = update_var "%8" addr
      (update_var "%7" offset
        (update_var "%6" value (update_var "%5" slot s))) in
    update_var "%3" (i + 1w)
      (update_var "%9" (i + 1w) (mstore (w2n addr) value t))
End

Theorem probe_word_load_sequence:
  !s i bufaddr.
    lookup_var "%3" s = SOME i /\ lookup_var "%2" s = SOME bufaddr ==>
    run_inst_seq
      (TAKE 7 (EL 6 probe_word_compiled.cs_blocks).bb_instructions) s =
      OK (probe_word_load_state s i bufaddr)
Proof
  rpt strip_tac >>
  simp[probe_word_compiled_load_body] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_read1_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_write2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def, eval_operand_def,
       lookup_var_update_var, probe_word_load_state_def]
QED

Theorem probe_word_load_block:
  !s i bufaddr fuel ctx.
    lookup_var "%3" s = SOME i /\ lookup_var "%2" s = SOME bufaddr /\
    ~s.vs_halted ==>
    exec_block fuel ctx (EL 6 probe_word_compiled.cs_blocks)
      (s with vs_inst_idx := 0) =
    OK (jump_to "@wcopy_cond_0" (probe_word_load_state s i bufaddr))
Proof
  rpt strip_tac >> irule exec_block_inst_seq_jmp >>
  conj_tac >- simp[probe_word_load_state_def, update_var_def, mstore_def] >>
  qexists_tac `TAKE 7 (EL 6 probe_word_compiled.cs_blocks).bb_instructions` >>
  simp[probe_word_load_sequence, probe_word_compiled_load_body,
       mk_inst_def, is_terminator_def, get_instruction_def] >>
  rpt strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6`
    by decide_tac >> gvs[]
QED

Definition probe_word_load_cond_state_def:
  probe_word_load_cond_state s i = update_var "%4" (bool_to_word (i = 3w)) s
End

Theorem probe_word_load_cond_sequence:
  !s i.
    lookup_var "%3" s = SOME i ==>
    run_inst_seq
      (TAKE 1 (EL 7 probe_word_compiled.cs_blocks).bb_instructions) s =
    OK (probe_word_load_cond_state s i)
Proof
  rpt strip_tac >> simp[probe_word_compiled_load_cond] >>
  simp[run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def,
       probe_word_load_cond_state_def]
QED

Theorem probe_word_load_cond_block:
  !s i fuel ctx.
    lookup_var "%3" s = SOME i /\ ~s.vs_halted ==>
    exec_block fuel ctx (EL 7 probe_word_compiled.cs_blocks)
      (s with vs_inst_idx := 0) =
    OK (jump_to (if i = 3w then "@wcopy_exit_2" else "@wcopy_body_1")
      (probe_word_load_cond_state s i))
Proof
  rpt strip_tac >>
  simp[Once exec_block_def, probe_word_compiled_load_cond,
       get_instruction_def, mk_inst_def] >>
  simp[Once step_inst_def] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operands_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, Once step_inst_def,
       Once step_inst_base_def, eval_operand_def, lookup_var_update_var,
       update_var_def, probe_word_load_cond_state_def, jump_to_def,
       bool_to_word_def] >>
  Cases_on `i = 3w` >>
  gvs[lookup_var_def, FLOOKUP_UPDATE, is_terminator_def, bool_to_word_def]
QED

Theorem probe_word_run_load_cond:
  !s i fuel ctx.
    lookup_var "%3" s = SOME i /\ ~s.vs_halted /\
    s.vs_current_bb = "@wcopy_cond_0" ==>
    run_blocks (SUC fuel) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function
      (jump_to (if i = 3w then "@wcopy_exit_2" else "@wcopy_body_1")
        (probe_word_load_cond_state s i))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_unfold, probe_word_function_blocks,
       lookup_block_def, probe_word_compiled_entry,
       probe_word_compiled_load_cond, listTheory.FIND_thm] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  rewrite_tac[GSYM (SRULE [mk_inst_def] probe_word_compiled_load_cond)] >>
  drule_all probe_word_load_cond_block >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[jump_to_def, probe_word_load_cond_state_def, update_var_def]
QED

Theorem probe_word_run_load_body:
  !s i bufaddr fuel ctx.
    lookup_var "%3" s = SOME i /\ lookup_var "%2" s = SOME bufaddr /\
    ~s.vs_halted /\ s.vs_current_bb = "@wcopy_body_1" ==>
    run_blocks (SUC fuel) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function
      (jump_to "@wcopy_cond_0" (probe_word_load_state s i bufaddr))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_unfold, probe_word_function_blocks,
       lookup_block_def, probe_word_compiled_entry,
       probe_word_compiled_load_cond, probe_word_compiled_load_body,
       listTheory.FIND_thm] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  rewrite_tac[GSYM (SRULE [mk_inst_def] probe_word_compiled_load_body)] >>
  drule_all probe_word_load_block >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[jump_to_def, probe_word_load_state_def, update_var_def, mstore_def]
QED


Theorem probe_word_load_state_vars:
  !s i bufaddr v.
    lookup_var v (probe_word_load_state s i bufaddr) =
      if v = "%3" \/ v = "%9" then SOME (i + 1w)
      else if v = "%8" then SOME (bufaddr + i * 32w)
      else if v = "%7" then SOME (i * 32w)
      else if v = "%6" then SOME (sload (3w + i) s)
      else if v = "%5" then SOME (3w + i)
      else lookup_var v s
Proof
  simp[probe_word_load_state_def, lookup_var_update_var] >>
  rpt gen_tac >> Cases_on `v = "%3"` >> simp[] >>
  Cases_on `v = "%9"` >> simp[]
QED

Theorem probe_word_load_state_halted:
  !s i bufaddr. (probe_word_load_state s i bufaddr).vs_halted = s.vs_halted
Proof
  simp[probe_word_load_state_def]
QED

Theorem probe_word_load_cond_state_vars:
  !s i v.
    lookup_var v (probe_word_load_cond_state s i) =
      if v = "%4" then SOME (bool_to_word (i = 3w)) else lookup_var v s
Proof
  simp[probe_word_load_cond_state_def, lookup_var_update_var]
QED

Theorem probe_word_load_cond_state_halted:
  !s i. (probe_word_load_cond_state s i).vs_halted = s.vs_halted
Proof
  simp[probe_word_load_cond_state_def]
QED

Definition probe_word_load_round_def:
  probe_word_load_round s i bufaddr =
    jump_to "@wcopy_cond_0"
      (probe_word_load_state
        (jump_to "@wcopy_body_1" (probe_word_load_cond_state s i)) i bufaddr)
End

Theorem probe_word_load_round_observations:
  !s i bufaddr.
    lookup_var "%2" (probe_word_load_round s i bufaddr) = lookup_var "%2" s /\
    lookup_var "%3" (probe_word_load_round s i bufaddr) = SOME (i + 1w) /\
    (probe_word_load_round s i bufaddr).vs_halted = s.vs_halted /\
    (probe_word_load_round s i bufaddr).vs_current_bb = "@wcopy_cond_0"
Proof
  simp[probe_word_load_round_def, control_moves_keep_vars,
       probe_word_load_state_vars, probe_word_load_state_halted,
       probe_word_load_cond_state_vars, probe_word_load_cond_state_halted] >>
  simp[jump_to_def]
QED

Theorem probe_word_run_load_round:
  !s i bufaddr fuel ctx.
    lookup_var "%3" s = SOME i /\ lookup_var "%2" s = SOME bufaddr /\
    ~s.vs_halted /\ s.vs_current_bb = "@wcopy_cond_0" /\ i <> 3w ==>
    run_blocks (SUC (SUC fuel)) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function (probe_word_load_round s i bufaddr)
Proof
  rpt strip_tac >>
  drule_all probe_word_run_load_cond >>
  disch_then (fn th => rewrite_tac[th]) >> simp[] >>
  qmatch_goalsub_abbrev_tac `run_blocks (SUC fuel) ctx probe_word_function t` >>
  `lookup_var "%3" t = SOME i /\ lookup_var "%2" t = SOME bufaddr /\
   ~t.vs_halted /\ t.vs_current_bb = "@wcopy_body_1"` by
    (simp[Abbr `t`, control_moves_keep_vars, probe_word_load_cond_state_vars,
          probe_word_load_cond_state_halted] >> simp[jump_to_def]) >>
  drule_all probe_word_run_load_body >>
  simp[Abbr `t`, probe_word_load_round_def]
QED

Definition probe_word_loaded_state_def:
  probe_word_loaded_state s bufaddr =
    let t = probe_word_load_round
      (probe_word_load_round (probe_word_load_round s 0w bufaddr) 1w bufaddr)
      2w bufaddr in
    jump_to "@wcopy_exit_2" (probe_word_load_cond_state t (3w:bytes32))
End

Theorem probe_word_run_load_loop:
  !s bufaddr fuel ctx.
    lookup_var "%3" s = SOME 0w /\ lookup_var "%2" s = SOME bufaddr /\
    ~s.vs_halted /\ s.vs_current_bb = "@wcopy_cond_0" ==>
    run_blocks (SUC (SUC (SUC (SUC (SUC (SUC (SUC fuel)))))))
      ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function (probe_word_loaded_state s bufaddr)
Proof
  rpt strip_tac >>
  `(0w:bytes32) <> 3w /\ (1w:bytes32) <> 3w /\ (2w:bytes32) <> 3w` by
    simp[wordsTheory.n2w_11, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  drule_all probe_word_run_load_round >> simp[] >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks _ ctx probe_word_function t` >>
  `lookup_var "%3" t = SOME 1w /\ lookup_var "%2" t = SOME bufaddr /\
   ~t.vs_halted /\ t.vs_current_bb = "@wcopy_cond_0"` by
    simp[Abbr `t`, probe_word_load_round_observations] >>
  drule_all probe_word_run_load_round >> simp[] >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks _ ctx probe_word_function u` >>
  `lookup_var "%3" u = SOME 2w /\ lookup_var "%2" u = SOME bufaddr /\
   ~u.vs_halted /\ u.vs_current_bb = "@wcopy_cond_0"` by
    simp[Abbr `u`, probe_word_load_round_observations, word_add_n2w] >>
  drule_all probe_word_run_load_round >> simp[] >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks _ ctx probe_word_function v` >>
  `lookup_var "%3" v = SOME 3w /\ ~v.vs_halted /\
   v.vs_current_bb = "@wcopy_cond_0"` by
    simp[Abbr `v`, probe_word_load_round_observations, word_add_n2w] >>
  drule_all probe_word_run_load_cond >>
  simp[Abbr `v`, Abbr `u`, Abbr `t`, probe_word_loaded_state_def]
QED

Definition probe_word_load_exit_state_def:
  probe_word_load_exit_state s bufaddr =
    update_var "%11" 0w (update_var "%10" (mload (w2n bufaddr) s) s)
End

Theorem probe_word_load_exit_sequence:
  !s bufaddr.
    lookup_var "%2" s = SOME bufaddr ==>
    run_inst_seq
      (TAKE 2 (EL 5 probe_word_compiled.cs_blocks).bb_instructions) s =
    OK (probe_word_load_exit_state s bufaddr)
Proof
  rpt strip_tac >> simp[probe_word_compiled_load_exit] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_read1_def,
       mk_inst_def, eval_operands_def, eval_operand_def] >>
  simp[run_inst_seq_def, Once step_inst_base_def, eval_operand_def,
       probe_word_load_exit_state_def]
QED

Theorem probe_word_load_exit_block:
  !s bufaddr fuel ctx.
    lookup_var "%2" s = SOME bufaddr /\ ~s.vs_halted ==>
    exec_block fuel ctx (EL 5 probe_word_compiled.cs_blocks)
      (s with vs_inst_idx := 0) =
    OK (jump_to "@dyn_cond_3" (probe_word_load_exit_state s bufaddr))
Proof
  rpt strip_tac >> irule exec_block_inst_seq_jmp >>
  conj_tac >- simp[probe_word_load_exit_state_def] >>
  qexists_tac `TAKE 2 (EL 5 probe_word_compiled.cs_blocks).bb_instructions` >>
  simp[probe_word_load_exit_sequence, probe_word_compiled_load_exit,
       mk_inst_def, is_terminator_def, get_instruction_def] >>
  rpt strip_tac >> `k = 0 \/ k = 1` by decide_tac >> gvs[]
QED

Theorem probe_word_run_load_exit:
  !s bufaddr fuel ctx.
    lookup_var "%2" s = SOME bufaddr /\ ~s.vs_halted /\
    s.vs_current_bb = "@wcopy_exit_2" ==>
    run_blocks (SUC fuel) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function
      (jump_to "@dyn_cond_3" (probe_word_load_exit_state s bufaddr))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_unfold, probe_word_function_blocks,
       lookup_block_def, probe_word_compiled_entry,
       probe_word_compiled_load_cond, probe_word_compiled_load_body,
       probe_word_compiled_load_exit, listTheory.FIND_thm] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  rewrite_tac[GSYM (SRULE [mk_inst_def] probe_word_compiled_load_exit)] >>
  drule_all probe_word_load_exit_block >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[jump_to_def, probe_word_load_exit_state_def]
QED

Theorem probe_word_load_storage_frame:
  !s i bufaddr.
    contract_storage (probe_word_load_round s i bufaddr) = contract_storage s
Proof
  rewrite_tac[probe_word_load_round_def, probe_word_load_state_def,
       probe_word_load_cond_state_def, LET_THM, contract_storage_def,
       jump_to_def, update_var_def, mstore_def] >> simp[]
QED

Theorem probe_word_load_round_memory:
  !s i bufaddr.
    (probe_word_load_round s i bufaddr).vs_memory =
      (mstore (w2n (bufaddr + i * 32w)) (sload (3w + i) s) s).vs_memory
Proof
  simp[probe_word_load_round_def, probe_word_load_state_def,
       probe_word_load_cond_state_def, sload_def, contract_storage_def,
       jump_to_def, update_var_def, mstore_def]
QED

Theorem probe_word_load_cond_storage_frame:
  !s i lbl.
    contract_storage (jump_to lbl (probe_word_load_cond_state s i)) =
      contract_storage s
Proof
  simp[contract_storage_def, jump_to_def,
       probe_word_load_cond_state_def, update_var_def]
QED

Theorem probe_word_loaded_storage_frame:
  !s bufaddr.
    contract_storage (probe_word_loaded_state s bufaddr) = contract_storage s
Proof
  simp[probe_word_loaded_state_def, probe_word_load_cond_storage_frame,
       probe_word_load_storage_frame]
QED

Theorem probe_word_load_round_mload:
  !s i bufaddr p.
    mload p (probe_word_load_round s i bufaddr) =
      mload p (mstore (w2n (bufaddr + i * 32w)) (sload (3w + i) s) s)
Proof
  rewrite_tac[mload_def, probe_word_load_round_memory]
QED

Theorem probe_word_load_cond_mload:
  !s i lbl p.
    mload p (jump_to lbl (probe_word_load_cond_state s i)) = mload p s
Proof
  simp[mload_def, jump_to_def, probe_word_load_cond_state_def, update_var_def]
QED

Theorem probe_word_loaded_header:
  !s bufaddr.
    regions_disjoint (w2n (bufaddr + 64w), 32) (w2n bufaddr, 32) /\
    regions_disjoint (w2n (bufaddr + 32w), 32) (w2n bufaddr, 32) ==>
    mload (w2n bufaddr) (probe_word_loaded_state s bufaddr) = sload 3w s
Proof
  rpt strip_tac >>
  simp[probe_word_loaded_state_def, probe_word_load_cond_mload] >>
  simp[Once probe_word_load_round_mload] >>
  simp[word_mul_n2w, word_add_n2w, mload_mstore_disjoint] >>
  simp[Once probe_word_load_round_mload] >>
  simp[word_mul_n2w, word_add_n2w, mload_mstore_disjoint] >>
  simp[probe_word_load_round_mload, word_mul_n2w, word_add_n2w,
       WORD_ADD_0, mload_mstore_same]
QED

Theorem probe_word_entry_observations:
  !s.
    lookup_var "%0" (probe_word_entry_state s) = SOME s.vs_return_pc_token /\
    lookup_var "%2" (probe_word_entry_state s) = SOME (n2w (s.vs_alloca_next + 32)) /\
    lookup_var "%3" (probe_word_entry_state s) = SOME 0w /\
    (probe_word_entry_state s).vs_halted = s.vs_halted /\
    (probe_word_entry_state s).vs_memory = s.vs_memory /\
    contract_storage (probe_word_entry_state s) = contract_storage s /\
    (probe_word_entry_state s).vs_alloca_next = s.vs_alloca_next + 128 /\
    (probe_word_entry_state s).vs_allocas = s.vs_allocas |+
      (1, (s.vs_alloca_next, 32)) |+ (2, (s.vs_alloca_next + 32, 96))
Proof
  simp[probe_word_entry_state_def, lookup_var_update_var,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, contract_storage_def]
QED

Theorem probe_word_loaded_observations:
  !s bufaddr.
    lookup_var "%2" (probe_word_loaded_state s bufaddr) = lookup_var "%2" s /\
    lookup_var "%0" (probe_word_loaded_state s bufaddr) = lookup_var "%0" s /\
    (probe_word_loaded_state s bufaddr).vs_halted = s.vs_halted /\
    (probe_word_loaded_state s bufaddr).vs_current_bb = "@wcopy_exit_2"
Proof
  simp[probe_word_loaded_state_def, control_moves_keep_vars,
       probe_word_load_cond_state_vars, probe_word_load_cond_state_halted,
       probe_word_load_round_def, probe_word_load_state_vars,
       probe_word_load_state_halted] >> simp[Once jump_to_def]
QED

Theorem probe_word_load_round_allocation_frame:
  !s i bufaddr.
    (probe_word_load_round s i bufaddr).vs_alloca_next = s.vs_alloca_next /\
    (probe_word_load_round s i bufaddr).vs_allocas = s.vs_allocas /\
    (probe_word_load_round s i bufaddr).vs_return_pc_token = s.vs_return_pc_token
Proof
  rewrite_tac[probe_word_load_round_def, probe_word_load_state_def,
       probe_word_load_cond_state_def, LET_THM, jump_to_def, update_var_def,
       mstore_def] >> simp[]
QED

Theorem probe_word_loaded_allocation_frame:
  !s bufaddr.
    (probe_word_loaded_state s bufaddr).vs_alloca_next = s.vs_alloca_next /\
    (probe_word_loaded_state s bufaddr).vs_allocas = s.vs_allocas /\
    (probe_word_loaded_state s bufaddr).vs_return_pc_token = s.vs_return_pc_token
Proof
  simp[probe_word_loaded_state_def, probe_word_load_cond_state_def,
       jump_to_def, update_var_def, probe_word_load_round_allocation_frame]
QED

Definition probe_word_copy_cond_state_def:
  probe_word_copy_cond_state s i n =
    update_var "%13" (bool_to_word (~(i <+ n)))
      (update_var "%12" (bool_to_word (i <+ n)) s)
End

Theorem probe_word_copy_cond_sequence:
  !s i n.
    lookup_var "%11" s = SOME i /\ lookup_var "%10" s = SOME n ==>
    run_inst_seq (TAKE 2 (EL 4 probe_word_compiled.cs_blocks).bb_instructions) s =
      OK (probe_word_copy_cond_state s i n)
Proof
  rpt strip_tac >> simp[probe_word_compiled_copy_cond] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def] >>
  simp[run_inst_seq_def, Once step_inst_base_def, exec_pure1_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var,
       probe_word_copy_cond_state_def, bool_to_word_def] >>
  Cases_on `i <+ n` >> gvs[WORD_LO, bool_to_word_def]
QED

Theorem probe_word_copy_cond_block:
  !s i n fuel ctx.
    lookup_var "%11" s = SOME i /\ lookup_var "%10" s = SOME n /\
    ~s.vs_halted ==>
    exec_block fuel ctx (EL 4 probe_word_compiled.cs_blocks)
      (s with vs_inst_idx := 0) =
    OK (jump_to (if i <+ n then "@dyn_body_4" else "@dyn_exit_5")
      (probe_word_copy_cond_state s i n))
Proof
  rpt strip_tac >>
  `jump_to (if i <+ n then "@dyn_body_4" else "@dyn_exit_5")
      (probe_word_copy_cond_state s i n) =
   jump_to (if bool_to_word (~(i <+ n)) <> 0w then "@dyn_exit_5" else "@dyn_body_4")
      (probe_word_copy_cond_state s i n)` by
    (Cases_on `i <+ n` >> simp[bool_to_word_def]) >>
  pop_assum SUBST1_TAC >> irule exec_block_inst_seq_jnz >>
  conj_tac >- simp[probe_word_copy_cond_state_def] >>
  qexistsl [`Var "%13"`,
    `TAKE 2 (EL 4 probe_word_compiled.cs_blocks).bb_instructions`, `20`] >>
  simp[probe_word_copy_cond_sequence, probe_word_compiled_copy_cond,
       probe_word_copy_cond_state_def, lookup_var_update_var,
       eval_operand_def, mk_inst_def, is_terminator_def, get_instruction_def] >>
  rpt strip_tac >> `k = 0 \/ k = 1` by decide_tac >> gvs[]
QED

Theorem probe_word_run_copy_cond:
  !s i n fuel ctx.
    lookup_var "%11" s = SOME i /\ lookup_var "%10" s = SOME n /\
    ~s.vs_halted /\ s.vs_current_bb = "@dyn_cond_3" ==>
    run_blocks (SUC fuel) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function
      (jump_to (if i <+ n then "@dyn_body_4" else "@dyn_exit_5")
        (probe_word_copy_cond_state s i n))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_unfold, probe_word_function_blocks,
       lookup_block_def, probe_word_compiled_entry,
       probe_word_compiled_load_cond, probe_word_compiled_load_body,
       probe_word_compiled_load_exit, probe_word_compiled_copy_cond,
       listTheory.FIND_thm] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  rewrite_tac[GSYM (SRULE [mk_inst_def] probe_word_compiled_copy_cond)] >>
  drule_all probe_word_copy_cond_block >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[jump_to_def, probe_word_copy_cond_state_def]
QED

Definition probe_word_copy_body_state_def:
  probe_word_copy_body_state s i bufaddr =
    update_var "%20" 0w
      (update_var "%19" (0w + (1w + i * 2w))
        (update_var "%18" (1w + i * 2w)
          (update_var "%17" (i * 2w)
            (update_var "%16" (bufaddr + (32w + i * 64w))
              (update_var "%15" (32w + i * 64w)
                (update_var "%14" (i * 64w) s))))))
End

Theorem probe_word_copy_body_sequence:
  !s i bufaddr.
    lookup_var "%11" s = SOME i /\ lookup_var "%2" s = SOME bufaddr ==>
    run_inst_seq (TAKE 7 (EL 3 probe_word_compiled.cs_blocks).bb_instructions) s =
      OK (probe_word_copy_body_state s i bufaddr)
Proof
  rpt strip_tac >> simp[probe_word_compiled_copy_body] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[run_inst_seq_def, Once step_inst_base_def, eval_operand_def,
       mk_inst_def, probe_word_copy_body_state_def]
QED

Theorem probe_word_copy_body_block:
  !s i bufaddr fuel ctx.
    lookup_var "%11" s = SOME i /\ lookup_var "%2" s = SOME bufaddr /\
    ~s.vs_halted ==>
    exec_block fuel ctx (EL 3 probe_word_compiled.cs_blocks)
      (s with vs_inst_idx := 0) =
    OK (jump_to "@wcopy_cond_6" (probe_word_copy_body_state s i bufaddr))
Proof
  rpt strip_tac >> irule exec_block_inst_seq_jmp >>
  conj_tac >- simp[probe_word_copy_body_state_def] >>
  qexists_tac `TAKE 7 (EL 3 probe_word_compiled.cs_blocks).bb_instructions` >>
  simp[probe_word_copy_body_sequence, probe_word_compiled_copy_body,
       mk_inst_def, is_terminator_def, get_instruction_def] >>
  rpt strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6`
    by decide_tac >> gvs[]
QED

Definition probe_word_elem_cond_state_def:
  probe_word_elem_cond_state s i = update_var "%21" (bool_to_word (i = 2w)) s
End

Theorem probe_word_elem_cond_block:
  !s i fuel ctx.
    lookup_var "%20" s = SOME i /\ ~s.vs_halted ==>
    exec_block fuel ctx (EL 2 probe_word_compiled.cs_blocks)
      (s with vs_inst_idx := 0) =
    OK (jump_to (if i = 2w then "@wcopy_exit_8" else "@wcopy_body_7")
      (probe_word_elem_cond_state s i))
Proof
  rpt strip_tac >>
  simp[Once exec_block_def, probe_word_compiled_elem_cond,
       get_instruction_def, mk_inst_def] >>
  simp[Once step_inst_def] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operands_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, Once step_inst_def,
       Once step_inst_base_def, eval_operand_def, lookup_var_update_var,
       update_var_def, probe_word_elem_cond_state_def, jump_to_def,
       bool_to_word_def] >>
  Cases_on `i = 2w` >>
  gvs[lookup_var_def, FLOOKUP_UPDATE, is_terminator_def, bool_to_word_def]
QED

Definition probe_word_elem_body_state_def:
  probe_word_elem_body_state s i src dst =
    let offset = i * 32w in
    let addr = src + offset in
    let value = mload (w2n addr) s in
    let t = update_var "%25" (dst + i)
      (update_var "%24" value
        (update_var "%23" addr (update_var "%22" offset s))) in
    update_var "%20" (i + 1w)
      (update_var "%26" (i + 1w) (sstore (dst + i) value t))
End

Theorem probe_word_elem_body_sequence:
  !s i src dst.
    lookup_var "%20" s = SOME i /\ lookup_var "%16" s = SOME src /\
    lookup_var "%19" s = SOME dst ==>
    run_inst_seq (TAKE 7 (EL 1 probe_word_compiled.cs_blocks).bb_instructions) s =
      OK (probe_word_elem_body_state s i src dst)
Proof
  rpt strip_tac >> simp[probe_word_compiled_elem_body] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_read1_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var,
       mload_def, update_var_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_write2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_update_var,
       lookup_var_def, sstore_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[run_inst_seq_def, Once step_inst_base_def, eval_operand_def,
       mk_inst_def, probe_word_elem_body_state_def, mload_def, update_var_def,
       sstore_def] >> gvs[lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem probe_word_elem_body_block:
  !s i src dst fuel ctx.
    lookup_var "%20" s = SOME i /\ lookup_var "%16" s = SOME src /\
    lookup_var "%19" s = SOME dst /\ ~s.vs_halted ==>
    exec_block fuel ctx (EL 1 probe_word_compiled.cs_blocks)
      (s with vs_inst_idx := 0) =
    OK (jump_to "@wcopy_cond_6" (probe_word_elem_body_state s i src dst))
Proof
  rpt strip_tac >> irule exec_block_inst_seq_jmp >>
  conj_tac >- simp[probe_word_elem_body_state_def, sstore_def] >>
  qexists_tac `TAKE 7 (EL 1 probe_word_compiled.cs_blocks).bb_instructions` >>
  simp[probe_word_elem_body_sequence, probe_word_compiled_elem_body,
       mk_inst_def, is_terminator_def, get_instruction_def] >>
  rpt strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6`
    by decide_tac >> gvs[]
QED

Definition probe_word_elem_exit_state_def:
  probe_word_elem_exit_state s i =
    update_var "%11" (i + 1w) (update_var "%27" (i + 1w) s)
End

Theorem probe_word_elem_exit_sequence:
  !s i.
    lookup_var "%11" s = SOME i ==>
    run_inst_seq (TAKE 2 (EL 0 probe_word_compiled.cs_blocks).bb_instructions) s =
      OK (probe_word_elem_exit_state s i)
Proof
  rpt strip_tac >> simp[probe_word_compiled_elem_exit] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
       mk_inst_def, eval_operands_def, eval_operand_def] >>
  simp[run_inst_seq_def, Once step_inst_base_def, eval_operand_def,
       mk_inst_def, lookup_var_update_var, probe_word_elem_exit_state_def]
QED

Theorem probe_word_elem_exit_block:
  !s i fuel ctx.
    lookup_var "%11" s = SOME i /\ ~s.vs_halted ==>
    exec_block fuel ctx (EL 0 probe_word_compiled.cs_blocks)
      (s with vs_inst_idx := 0) =
    OK (jump_to "@dyn_cond_3" (probe_word_elem_exit_state s i))
Proof
  rpt strip_tac >> irule exec_block_inst_seq_jmp >>
  conj_tac >- simp[probe_word_elem_exit_state_def] >>
  qexists_tac `TAKE 2 (EL 0 probe_word_compiled.cs_blocks).bb_instructions` >>
  simp[probe_word_elem_exit_sequence, probe_word_compiled_elem_exit,
       mk_inst_def, is_terminator_def, get_instruction_def] >>
  rpt strip_tac >> `k = 0 \/ k = 1` by decide_tac >> gvs[]
QED

Theorem probe_word_run_copy_body:
  !s i bufaddr fuel ctx.
    lookup_var "%11" s = SOME i /\ lookup_var "%2" s = SOME bufaddr /\
    ~s.vs_halted /\ s.vs_current_bb = "@dyn_body_4" ==>
    run_blocks (SUC fuel) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function
      (jump_to "@wcopy_cond_6" (probe_word_copy_body_state s i bufaddr))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_unfold, probe_word_function_blocks,
       lookup_block_def, probe_word_compiled_entry,
       probe_word_compiled_load_cond, probe_word_compiled_load_body,
       probe_word_compiled_load_exit, probe_word_compiled_copy_cond,
       probe_word_compiled_copy_body, listTheory.FIND_thm] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  rewrite_tac[GSYM (SRULE [mk_inst_def] probe_word_compiled_copy_body)] >>
  drule_all probe_word_copy_body_block >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[jump_to_def, probe_word_copy_body_state_def]
QED

Theorem probe_word_run_elem_cond:
  !s i fuel ctx.
    lookup_var "%20" s = SOME i /\ ~s.vs_halted /\
    s.vs_current_bb = "@wcopy_cond_6" ==>
    run_blocks (SUC fuel) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function
      (jump_to (if i = 2w then "@wcopy_exit_8" else "@wcopy_body_7")
        (probe_word_elem_cond_state s i))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_unfold, probe_word_function_blocks,
       lookup_block_def, probe_word_compiled_entry,
       probe_word_compiled_load_cond, probe_word_compiled_load_body,
       probe_word_compiled_load_exit, probe_word_compiled_copy_cond,
       probe_word_compiled_copy_body, probe_word_compiled_elem_cond,
       listTheory.FIND_thm] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  rewrite_tac[GSYM (SRULE [mk_inst_def] probe_word_compiled_elem_cond)] >>
  drule_all probe_word_elem_cond_block >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[jump_to_def, probe_word_elem_cond_state_def]
QED

Theorem probe_word_run_elem_body:
  !s i src dst fuel ctx.
    lookup_var "%20" s = SOME i /\ lookup_var "%16" s = SOME src /\
    lookup_var "%19" s = SOME dst /\ ~s.vs_halted /\
    s.vs_current_bb = "@wcopy_body_7" ==>
    run_blocks (SUC fuel) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function
      (jump_to "@wcopy_cond_6" (probe_word_elem_body_state s i src dst))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_unfold, probe_word_function_blocks,
       lookup_block_def, probe_word_compiled_entry,
       probe_word_compiled_load_cond, probe_word_compiled_load_body,
       probe_word_compiled_load_exit, probe_word_compiled_copy_cond,
       probe_word_compiled_copy_body, probe_word_compiled_elem_cond,
       probe_word_compiled_elem_body, listTheory.FIND_thm] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  rewrite_tac[GSYM (SRULE [mk_inst_def] probe_word_compiled_elem_body)] >>
  drule_all probe_word_elem_body_block >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[jump_to_def, probe_word_elem_body_state_def, sstore_def]
QED

Theorem probe_word_run_elem_exit:
  !s i fuel ctx.
    lookup_var "%11" s = SOME i /\ ~s.vs_halted /\
    s.vs_current_bb = "@wcopy_exit_8" ==>
    run_blocks (SUC fuel) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function
      (jump_to "@dyn_cond_3" (probe_word_elem_exit_state s i))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_unfold, probe_word_function_blocks,
       lookup_block_def, probe_word_compiled_entry,
       probe_word_compiled_load_cond, probe_word_compiled_load_body,
       probe_word_compiled_load_exit, probe_word_compiled_copy_cond,
       probe_word_compiled_copy_body, probe_word_compiled_elem_cond,
       probe_word_compiled_elem_body, probe_word_compiled_elem_exit,
       PURE_REWRITE_RULE [CONJUNCT1 listTheory.EL] probe_word_compiled_elem_exit,
       listTheory.FIND_thm] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  rewrite_tac[GSYM (SRULE [mk_inst_def] probe_word_compiled_elem_exit)] >>
  drule_all probe_word_elem_exit_block >>
  disch_then (fn th => rewrite_tac[th,
    PURE_REWRITE_RULE [CONJUNCT1 listTheory.EL] th]) >>
  simp[jump_to_def, probe_word_elem_exit_state_def]
QED

Theorem probe_word_return_block:
  !s n retpc fuel ctx.
    lookup_var "%10" s = SOME n /\ lookup_var "%0" s = SOME retpc /\
    ~s.vs_halted ==>
    exec_block fuel ctx
      <| bb_label := "@dyn_exit_5"; bb_instructions :=
        [mk_inst 42 SSTORE [Lit 0w; Var "%10"] [];
         mk_inst 43 RET [Lit 0w; Var "%0"] []] |>
      (s with vs_inst_idx := 0) =
    IntRet <| iret_values := [0w]; iret_adopt_fmp := NONE |>
      (sstore 0w n (s with vs_inst_idx := 1))
Proof
  rpt strip_tac >>
  simp[Once exec_block_def, get_instruction_def, mk_inst_def] >>
  simp[Once step_inst_def, Once step_inst_base_def, exec_write2_def,
       eval_operands_def, eval_operand_def, lookup_var_def] >>
  gvs[lookup_var_def] >>
  simp[Once exec_block_def, get_instruction_def, mk_inst_def, sstore_def] >>
  simp[Once step_inst_def, Once step_inst_base_def, eval_operands_def,
       eval_operand_def, lookup_var_def, is_terminator_def, sstore_def]
QED

Theorem probe_word_run_return:
  !s n retpc fuel ctx.
    lookup_var "%10" s = SOME n /\ lookup_var "%0" s = SOME retpc /\
    ~s.vs_halted /\ s.vs_current_bb = "@dyn_exit_5" ==>
    run_blocks (SUC fuel) ctx probe_word_function s =
    IntRet <| iret_values := [0w]; iret_adopt_fmp := NONE |>
      (sstore 0w n (s with vs_inst_idx := 1))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_unfold, probe_word_function_blocks,
       lookup_block_def, probe_word_compiled_entry,
       probe_word_compiled_load_cond, probe_word_compiled_load_body,
       probe_word_compiled_load_exit, probe_word_compiled_copy_cond,
       probe_word_compiled_copy_body, probe_word_compiled_elem_cond,
       probe_word_compiled_elem_body, probe_word_compiled_elem_exit,
       listTheory.FIND_thm] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  drule_all probe_word_return_block >>
  simp[mk_inst_def]
QED

Theorem probe_word_elem_body_vars:
  !s i src dst v.
    lookup_var v (probe_word_elem_body_state s i src dst) =
      if v = "%20" \/ v = "%26" then SOME (i + 1w)
      else if v = "%25" then SOME (dst + i)
      else if v = "%24" then SOME (mload (w2n (src + i * 32w)) s)
      else if v = "%23" then SOME (src + i * 32w)
      else if v = "%22" then SOME (i * 32w)
      else lookup_var v s
Proof
  simp[probe_word_elem_body_state_def, lookup_var_update_var,
       lookup_var_def, update_var_def, sstore_def, FLOOKUP_UPDATE] >>
  rpt gen_tac >> Cases_on `v = "%20"` >> simp[] >>
  Cases_on `v = "%26"` >> simp[]
QED

Theorem probe_word_elem_body_halted:
  !s i src dst.
    (probe_word_elem_body_state s i src dst).vs_halted = s.vs_halted
Proof
  simp[probe_word_elem_body_state_def, sstore_def]
QED

Definition probe_word_elem_round_def:
  probe_word_elem_round s i src dst =
    jump_to "@wcopy_cond_6"
      (probe_word_elem_body_state
        (jump_to "@wcopy_body_7" (probe_word_elem_cond_state s i)) i src dst)
End

Theorem probe_word_elem_round_observations:
  !s i src dst v.
    (v = "%0" \/ v = "%2" \/ v = "%10" \/ v = "%11" \/
     v = "%16" \/ v = "%19" ==> lookup_var v (probe_word_elem_round s i src dst) = lookup_var v s) /\
    lookup_var "%20" (probe_word_elem_round s i src dst) = SOME (i + 1w) /\
    (probe_word_elem_round s i src dst).vs_halted = s.vs_halted /\
    (probe_word_elem_round s i src dst).vs_current_bb = "@wcopy_cond_6"
Proof
  simp[probe_word_elem_round_def, control_moves_keep_vars,
       probe_word_elem_body_vars, probe_word_elem_body_halted,
       probe_word_elem_cond_state_def, lookup_var_update_var] >>
  rpt gen_tac >> conj_tac >- (strip_tac >> gvs[]) >>
  simp[Once jump_to_def]
QED

Theorem probe_word_run_elem_round:
  !s i src dst fuel ctx.
    lookup_var "%20" s = SOME i /\ lookup_var "%16" s = SOME src /\
    lookup_var "%19" s = SOME dst /\ ~s.vs_halted /\
    s.vs_current_bb = "@wcopy_cond_6" /\ i <> 2w ==>
    run_blocks (SUC (SUC fuel)) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function (probe_word_elem_round s i src dst)
Proof
  rpt strip_tac >> drule_all probe_word_run_elem_cond >> simp[] >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks (SUC fuel) ctx probe_word_function t` >>
  `lookup_var "%20" t = SOME i /\ lookup_var "%16" t = SOME src /\
   lookup_var "%19" t = SOME dst /\ ~t.vs_halted /\
   t.vs_current_bb = "@wcopy_body_7"` by
    (simp[Abbr `t`, control_moves_keep_vars, probe_word_elem_cond_state_def,
          lookup_var_update_var] >> simp[Once jump_to_def]) >>
  drule_all probe_word_run_elem_body >>
  simp[Abbr `t`, probe_word_elem_round_def]
QED

Definition probe_word_elems_copied_state_def:
  probe_word_elems_copied_state s src dst =
    jump_to "@wcopy_exit_8"
      (probe_word_elem_cond_state
        (probe_word_elem_round (probe_word_elem_round s 0w src dst) 1w src dst) (2w:bytes32))
End

Theorem probe_word_run_elem_loop:
  !s src dst fuel ctx.
    lookup_var "%20" s = SOME 0w /\ lookup_var "%16" s = SOME src /\
    lookup_var "%19" s = SOME dst /\ ~s.vs_halted /\
    s.vs_current_bb = "@wcopy_cond_6" ==>
    run_blocks (SUC (SUC (SUC (SUC (SUC fuel))))) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function (probe_word_elems_copied_state s src dst)
Proof
  rpt strip_tac >>
  `(0w:bytes32) <> 2w /\ (1w:bytes32) <> 2w` by
    simp[n2w_11, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  drule_all probe_word_run_elem_round >> simp[] >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks _ ctx probe_word_function t` >>
  `lookup_var "%20" t = SOME 1w /\ lookup_var "%16" t = SOME src /\
   lookup_var "%19" t = SOME dst /\ ~t.vs_halted /\
   t.vs_current_bb = "@wcopy_cond_6"` by
    simp[Abbr `t`, probe_word_elem_round_observations] >>
  drule_all probe_word_run_elem_round >> simp[] >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks _ ctx probe_word_function u` >>
  `lookup_var "%20" u = SOME 2w /\ ~u.vs_halted /\
   u.vs_current_bb = "@wcopy_cond_6"` by
    simp[Abbr `u`, probe_word_elem_round_observations, word_add_n2w] >>
  drule_all probe_word_run_elem_cond >>
  simp[Abbr `u`, Abbr `t`, probe_word_elems_copied_state_def]
QED

Theorem probe_word_copy_cond_observations:
  !s i n v lbl.
    (v <> "%12" /\ v <> "%13" ==>
      lookup_var v (probe_word_copy_cond_state s i n) = lookup_var v s) /\
    (probe_word_copy_cond_state s i n).vs_halted = s.vs_halted /\
    (jump_to lbl (probe_word_copy_cond_state s i n)).vs_current_bb = lbl
Proof
  simp[probe_word_copy_cond_state_def, lookup_var_update_var] >>
  simp[Once jump_to_def]
QED

Theorem probe_word_copy_body_observations:
  !s i bufaddr v.
    (v = "%0" \/ v = "%2" \/ v = "%10" \/ v = "%11" ==>
      lookup_var v (probe_word_copy_body_state s i bufaddr) = lookup_var v s) /\
    lookup_var "%16" (probe_word_copy_body_state s i bufaddr) =
      SOME (bufaddr + (32w + i * 64w)) /\
    lookup_var "%19" (probe_word_copy_body_state s i bufaddr) =
      SOME (0w + (1w + i * 2w)) /\
    lookup_var "%20" (probe_word_copy_body_state s i bufaddr) = SOME 0w /\
    (probe_word_copy_body_state s i bufaddr).vs_halted = s.vs_halted
Proof
  simp[probe_word_copy_body_state_def, lookup_var_update_var] >>
  rpt strip_tac >> gvs[]
QED

Theorem probe_word_elems_copied_observations:
  !s src dst v.
    (v = "%0" \/ v = "%2" \/ v = "%10" \/ v = "%11" ==>
      lookup_var v (probe_word_elems_copied_state s src dst) = lookup_var v s) /\
    (probe_word_elems_copied_state s src dst).vs_halted = s.vs_halted /\
    (probe_word_elems_copied_state s src dst).vs_current_bb = "@wcopy_exit_8"
Proof
  simp[probe_word_elems_copied_state_def, control_moves_keep_vars,
       probe_word_elem_cond_state_def, lookup_var_update_var] >>
  rpt gen_tac >> conj_tac
  >- (strip_tac >> gvs[probe_word_elem_round_observations]) >>
  simp[probe_word_elem_round_observations, Once jump_to_def]
QED

Definition probe_word_copy_setup_state_def:
  probe_word_copy_setup_state s i n bufaddr =
    jump_to "@wcopy_cond_6"
      (probe_word_copy_body_state
        (jump_to "@dyn_body_4" (probe_word_copy_cond_state s i n)) i bufaddr)
End

Theorem probe_word_run_copy_setup:
  !s i n bufaddr fuel ctx.
    lookup_var "%11" s = SOME i /\ lookup_var "%10" s = SOME n /\
    lookup_var "%2" s = SOME bufaddr /\ ~s.vs_halted /\
    s.vs_current_bb = "@dyn_cond_3" /\ i <+ n ==>
    run_blocks (SUC (SUC fuel)) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function (probe_word_copy_setup_state s i n bufaddr)
Proof
  rpt strip_tac >> drule_all probe_word_run_copy_cond >> simp[] >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks (SUC fuel) ctx probe_word_function t` >>
  `lookup_var "%11" t = SOME i /\ lookup_var "%2" t = SOME bufaddr /\
   ~t.vs_halted /\ t.vs_current_bb = "@dyn_body_4"` by
    simp[Abbr `t`, control_moves_keep_vars, probe_word_copy_cond_observations] >>
  drule_all probe_word_run_copy_body >>
  simp[Abbr `t`, probe_word_copy_setup_state_def]
QED

Theorem probe_word_copy_setup_observations:
  !s i n bufaddr v.
    (v = "%0" \/ v = "%2" \/ v = "%10" \/ v = "%11" ==>
      lookup_var v (probe_word_copy_setup_state s i n bufaddr) = lookup_var v s) /\
    lookup_var "%16" (probe_word_copy_setup_state s i n bufaddr) =
      SOME (bufaddr + (32w + i * 64w)) /\
    lookup_var "%19" (probe_word_copy_setup_state s i n bufaddr) =
      SOME (0w + (1w + i * 2w)) /\
    lookup_var "%20" (probe_word_copy_setup_state s i n bufaddr) = SOME 0w /\
    (probe_word_copy_setup_state s i n bufaddr).vs_halted = s.vs_halted /\
    (probe_word_copy_setup_state s i n bufaddr).vs_current_bb = "@wcopy_cond_6"
Proof
  simp[probe_word_copy_setup_state_def, control_moves_keep_vars,
       probe_word_copy_body_observations] >>
  rpt gen_tac >> conj_tac
  >- (strip_tac >> gvs[probe_word_copy_body_observations,
       probe_word_copy_cond_observations, control_moves_keep_vars]) >>
  simp[probe_word_copy_body_observations, probe_word_copy_cond_observations,
       control_moves_keep_vars, Once jump_to_def]
QED

Definition probe_word_copy_round_def:
  probe_word_copy_round s i n bufaddr =
    jump_to "@dyn_cond_3"
      (probe_word_elem_exit_state
        (probe_word_elems_copied_state (probe_word_copy_setup_state s i n bufaddr)
          (bufaddr + (32w + i * 64w)) (0w + (1w + i * 2w))) i)
End

Theorem probe_word_run_copy_round:
  !s i n bufaddr fuel ctx.
    lookup_var "%11" s = SOME i /\ lookup_var "%10" s = SOME n /\
    lookup_var "%2" s = SOME bufaddr /\ ~s.vs_halted /\
    s.vs_current_bb = "@dyn_cond_3" /\ i <+ n ==>
    run_blocks (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC fuel))))))))
      ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function (probe_word_copy_round s i n bufaddr)
Proof
  rpt strip_tac >> drule_all probe_word_run_copy_setup >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks _ ctx probe_word_function t` >>
  `lookup_var "%20" t = SOME 0w /\
   lookup_var "%16" t = SOME (bufaddr + (32w + i * 64w)) /\
   lookup_var "%19" t = SOME (0w + (1w + i * 2w)) /\
   ~t.vs_halted /\ t.vs_current_bb = "@wcopy_cond_6"` by
    simp[Abbr `t`, probe_word_copy_setup_observations] >>
  drule_all probe_word_run_elem_loop >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks _ ctx probe_word_function u` >>
  `lookup_var "%11" u = SOME i /\ ~u.vs_halted /\
   u.vs_current_bb = "@wcopy_exit_8"` by
    simp[Abbr `u`, Abbr `t`, probe_word_elems_copied_observations,
         probe_word_copy_setup_observations] >>
  drule_all probe_word_run_elem_exit >>
  simp[Abbr `u`, Abbr `t`, probe_word_copy_round_def]
QED

Theorem probe_word_copy_round_observations:
  !s i n bufaddr v.
    (v = "%0" \/ v = "%2" \/ v = "%10" ==>
      lookup_var v (probe_word_copy_round s i n bufaddr) = lookup_var v s) /\
    lookup_var "%11" (probe_word_copy_round s i n bufaddr) = SOME (i + 1w) /\
    (probe_word_copy_round s i n bufaddr).vs_halted = s.vs_halted /\
    (probe_word_copy_round s i n bufaddr).vs_current_bb = "@dyn_cond_3"
Proof
  simp[probe_word_copy_round_def, control_moves_keep_vars,
       probe_word_elem_exit_state_def, lookup_var_update_var] >>
  rpt gen_tac >> conj_tac
  >- (strip_tac >> gvs[probe_word_elems_copied_observations,
       probe_word_copy_setup_observations]) >>
  simp[probe_word_elems_copied_observations, probe_word_copy_setup_observations,
       Once jump_to_def]
QED

Definition probe_word_copied_state_def:
  probe_word_copied_state s n bufaddr =
    if n = 0w then jump_to "@dyn_exit_5" (probe_word_copy_cond_state s 0w n)
    else jump_to "@dyn_exit_5"
      (probe_word_copy_cond_state (probe_word_copy_round s 0w n bufaddr) 1w n)
End

Theorem probe_word_run_copy_loop:
  !s n bufaddr fuel ctx.
    lookup_var "%11" s = SOME 0w /\ lookup_var "%10" s = SOME n /\
    lookup_var "%2" s = SOME bufaddr /\ ~s.vs_halted /\
    s.vs_current_bb = "@dyn_cond_3" /\ (n = 0w \/ n = 1w) ==>
    run_blocks ((if n = 0w then 1 else 9) + fuel) ctx probe_word_function s =
    run_blocks fuel ctx probe_word_function (probe_word_copied_state s n bufaddr)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n = 0w`
  >- (gvs[probe_word_copied_state_def] >>
      drule_all probe_word_run_copy_cond >> simp[WORD_LO, arithmeticTheory.ADD1]) >>
  `n = 1w` by gvs[] >> gvs[] >>
  `(0w:bytes32) <+ 1w /\ ~((1w:bytes32) <+ 1w)` by
    simp[WORD_LO, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  `fuel + 9 = SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC fuel))))))))`
    by decide_tac >>
  pure_asm_rewrite_tac [] >> drule_all probe_word_run_copy_round >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks (SUC fuel) ctx probe_word_function t` >>
  `lookup_var "%11" t = SOME 1w /\ lookup_var "%10" t = SOME 1w /\
   ~t.vs_halted /\ t.vs_current_bb = "@dyn_cond_3"` by
    simp[Abbr `t`, probe_word_copy_round_observations] >>
  drule_all probe_word_run_copy_cond >>
  simp[Abbr `t`, probe_word_copied_state_def, n2w_11,
       dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem probe_word_load_exit_observations:
  !s bufaddr v.
    (v <> "%10" /\ v <> "%11" ==>
      lookup_var v (probe_word_load_exit_state s bufaddr) = lookup_var v s) /\
    lookup_var "%10" (probe_word_load_exit_state s bufaddr) =
      SOME (mload (w2n bufaddr) s) /\
    lookup_var "%11" (probe_word_load_exit_state s bufaddr) = SOME 0w /\
    (probe_word_load_exit_state s bufaddr).vs_halted = s.vs_halted
Proof
  simp[probe_word_load_exit_state_def, lookup_var_update_var]
QED

Theorem probe_word_copied_observations:
  !s n bufaddr.
    lookup_var "%10" s = SOME n ==>
    lookup_var "%10" (probe_word_copied_state s n bufaddr) = SOME n /\
    lookup_var "%0" (probe_word_copied_state s n bufaddr) = lookup_var "%0" s /\
    (probe_word_copied_state s n bufaddr).vs_halted = s.vs_halted /\
    (probe_word_copied_state s n bufaddr).vs_current_bb = "@dyn_exit_5"
Proof
  rpt strip_tac >> Cases_on `n = 0w` >>
  simp[probe_word_copied_state_def, control_moves_keep_vars,
       probe_word_copy_cond_observations, probe_word_copy_round_observations]
QED

Theorem probe_word_run_copy_return:
  !s n bufaddr retpc fuel ctx.
    lookup_var "%11" s = SOME 0w /\ lookup_var "%10" s = SOME n /\
    lookup_var "%2" s = SOME bufaddr /\ lookup_var "%0" s = SOME retpc /\
    ~s.vs_halted /\ s.vs_current_bb = "@dyn_cond_3" /\
    (n = 0w \/ n = 1w) ==>
    run_blocks ((if n = 0w then 1 else 9) + SUC fuel)
      ctx probe_word_function s =
    IntRet <| iret_values := [0w]; iret_adopt_fmp := NONE |>
      (sstore 0w n ((probe_word_copied_state s n bufaddr) with vs_inst_idx := 1))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all probe_word_run_copy_loop >>
  disch_then (fn th => rewrite_tac[th]) >>
  irule probe_word_run_return >>
  simp[probe_word_copied_observations]
QED

Theorem probe_word_buffer_disjoint:
  !a. a + 128 <= dimword (:256) ==>
    regions_disjoint (w2n ((n2w (a+32):bytes32) + 64w),32)
      (w2n (n2w (a+32):bytes32),32) /\
    regions_disjoint (w2n ((n2w (a+32):bytes32) + 32w),32)
      (w2n (n2w (a+32):bytes32),32)
Proof
  rpt strip_tac >>
  `a+32 < dimword (:256) /\ a+64 < dimword (:256) /\
   a+96 < dimword (:256)` by decide_tac >>
  simp[word_add_n2w, w2n_n2w, arithmeticTheory.ADD_ASSOC,
       venomMemDefsTheory.regions_disjoint_def]
QED

Definition probe_word_final_state_def:
  probe_word_final_state s =
    let b = n2w (s.vs_alloca_next + 32);
        e = jump_to "@wcopy_cond_0" (probe_word_entry_state s);
        l = probe_word_loaded_state e b;
        c = jump_to "@dyn_cond_3" (probe_word_load_exit_state l b) in
    sstore 0w (sload 3w s)
      ((probe_word_copied_state c (sload 3w s) b) with vs_inst_idx := 1)
End

Theorem probe_word_run_function:
  !s fuel ctx.
    FLOOKUP s.vs_allocas 1 = NONE /\ FLOOKUP s.vs_allocas 2 = NONE /\
    ~s.vs_halted /\ s.vs_current_bb = "entry" /\
    s.vs_alloca_next + 128 <= dimword (:256) /\
    (sload 3w s = 0w \/ sload 3w s = 1w) ==>
    run_blocks ((if sload 3w s = 0w then 11 else 19) + fuel)
      ctx probe_word_function s =
    IntRet <| iret_values := [0w]; iret_adopt_fmp := NONE |>
      (probe_word_final_state s)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `((if sload 3w s = 0w then 11 else 19) + fuel) =
    SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC
      ((if sload 3w s = 0w then 1 else 9) + SUC fuel)))))))))`
    by (Cases_on `sload 3w s = 0w` >> simp[]) >>
  pure_asm_rewrite_tac [] >> drule_all probe_word_run_entry >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks _ ctx probe_word_function e` >>
  qabbrev_tac `b = (n2w (s.vs_alloca_next + 32):bytes32)` >>
  `lookup_var "%3" e = SOME 0w /\ lookup_var "%2" e = SOME b /\
   ~e.vs_halted /\ e.vs_current_bb = "@wcopy_cond_0"` by
    (simp[Abbr `e`, Abbr `b`, control_moves_keep_vars, probe_word_entry_observations] >>
     simp[Once jump_to_def, probe_word_entry_observations]) >>
  drule_all probe_word_run_load_loop >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks _ ctx probe_word_function l` >>
  `lookup_var "%2" l = SOME b /\ ~l.vs_halted /\
   l.vs_current_bb = "@wcopy_exit_2"` by
    simp[Abbr `l`, probe_word_loaded_observations] >>
  drule_all probe_word_run_load_exit >>
  disch_then (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `run_blocks _ ctx probe_word_function c` >>
  `contract_storage e = contract_storage s` by
    simp[Abbr `e`, contract_storage_def, jump_to_def,
         probe_word_entry_state_def, update_var_def] >>
  `mload (w2n b) l = sload 3w s` by
    (simp[Abbr `l`] >>
     dep_rewrite.DEP_REWRITE_TAC [probe_word_loaded_header] >>
     simp[Abbr `b`, probe_word_buffer_disjoint, sload_def]) >>
  `probe_word_final_state s = sstore 0w (sload 3w s)
    ((probe_word_copied_state c (sload 3w s) b) with vs_inst_idx := 1)` by
    simp[probe_word_final_state_def, Abbr `c`, Abbr `l`, Abbr `e`, Abbr `b`] >>
  asm_rewrite_tac [] >> irule probe_word_run_copy_return >>
  simp[Abbr `c`, control_moves_keep_vars, probe_word_load_exit_observations,
       Abbr `l`, probe_word_loaded_observations, Abbr `e`,
       probe_word_entry_observations] >>
  simp[Once jump_to_def, probe_word_load_exit_observations]
QED

Theorem probe_word_elem_body_scratch_frame:
  !s i src dst.
    (probe_word_elem_body_state s i src dst).vs_memory = s.vs_memory /\
    (probe_word_elem_body_state s i src dst).vs_allocas = s.vs_allocas /\
    (probe_word_elem_body_state s i src dst).vs_alloca_next = s.vs_alloca_next /\
    (probe_word_elem_body_state s i src dst).vs_return_pc_token = s.vs_return_pc_token
Proof
  simp[probe_word_elem_body_state_def, update_var_def, sstore_def]
QED

Theorem probe_word_elem_round_scratch_frame:
  !s i src dst.
    (probe_word_elem_round s i src dst).vs_memory = s.vs_memory /\
    (probe_word_elem_round s i src dst).vs_allocas = s.vs_allocas /\
    (probe_word_elem_round s i src dst).vs_alloca_next = s.vs_alloca_next /\
    (probe_word_elem_round s i src dst).vs_return_pc_token = s.vs_return_pc_token
Proof
  simp[probe_word_elem_round_def, jump_to_def, probe_word_elem_body_scratch_frame,
       probe_word_elem_cond_state_def, update_var_def]
QED

Theorem probe_word_elems_copied_scratch_frame:
  !s src dst.
    (probe_word_elems_copied_state s src dst).vs_memory = s.vs_memory /\
    (probe_word_elems_copied_state s src dst).vs_allocas = s.vs_allocas /\
    (probe_word_elems_copied_state s src dst).vs_alloca_next = s.vs_alloca_next /\
    (probe_word_elems_copied_state s src dst).vs_return_pc_token = s.vs_return_pc_token
Proof
  simp[probe_word_elems_copied_state_def, jump_to_def,
       probe_word_elem_cond_state_def, update_var_def, probe_word_elem_round_scratch_frame]
QED

Theorem probe_word_copy_body_scratch_frame:
  !s i b.
    (probe_word_copy_body_state s i b).vs_memory = s.vs_memory /\
    (probe_word_copy_body_state s i b).vs_allocas = s.vs_allocas /\
    (probe_word_copy_body_state s i b).vs_alloca_next = s.vs_alloca_next /\
    (probe_word_copy_body_state s i b).vs_return_pc_token = s.vs_return_pc_token
Proof
  simp[probe_word_copy_body_state_def, update_var_def]
QED

Theorem probe_word_copy_setup_scratch_frame:
  !s i n b.
    (probe_word_copy_setup_state s i n b).vs_memory = s.vs_memory /\
    (probe_word_copy_setup_state s i n b).vs_allocas = s.vs_allocas /\
    (probe_word_copy_setup_state s i n b).vs_alloca_next = s.vs_alloca_next /\
    (probe_word_copy_setup_state s i n b).vs_return_pc_token = s.vs_return_pc_token
Proof
  simp[probe_word_copy_setup_state_def, jump_to_def, probe_word_copy_body_scratch_frame,
       probe_word_copy_cond_state_def, update_var_def]
QED

Theorem probe_word_copy_round_scratch_frame:
  !s i n b.
    (probe_word_copy_round s i n b).vs_memory = s.vs_memory /\
    (probe_word_copy_round s i n b).vs_allocas = s.vs_allocas /\
    (probe_word_copy_round s i n b).vs_alloca_next = s.vs_alloca_next /\
    (probe_word_copy_round s i n b).vs_return_pc_token = s.vs_return_pc_token
Proof
  simp[probe_word_copy_round_def, jump_to_def, probe_word_elem_exit_state_def,
       update_var_def, probe_word_elems_copied_scratch_frame,
       probe_word_copy_setup_scratch_frame]
QED

Theorem probe_word_copied_scratch_frame:
  !s n b.
    (probe_word_copied_state s n b).vs_memory = s.vs_memory /\
    (probe_word_copied_state s n b).vs_allocas = s.vs_allocas /\
    (probe_word_copied_state s n b).vs_alloca_next = s.vs_alloca_next /\
    (probe_word_copied_state s n b).vs_return_pc_token = s.vs_return_pc_token
Proof
  rpt gen_tac >> Cases_on `n = 0w` >>
  simp[probe_word_copied_state_def, jump_to_def, probe_word_copy_cond_state_def,
       update_var_def, probe_word_copy_round_scratch_frame]
QED

Theorem probe_word_final_allocation_frame:
  !s.
    (probe_word_final_state s).vs_alloca_next = s.vs_alloca_next + 128 /\
    (probe_word_final_state s).vs_allocas = s.vs_allocas |+
      (1,(s.vs_alloca_next,32)) |+ (2,(s.vs_alloca_next+32,96)) /\
    (probe_word_final_state s).vs_return_pc_token = s.vs_return_pc_token
Proof
  simp[probe_word_final_state_def, sstore_def, probe_word_copied_scratch_frame,
       jump_to_def, probe_word_load_exit_state_def, update_var_def,
       probe_word_loaded_allocation_frame, probe_word_entry_observations] >>
  simp[probe_word_entry_state_def, update_var_def]
QED

Theorem probe_word_final_memory:
  !s.
    (probe_word_final_state s).vs_memory =
    (probe_word_loaded_state
      (jump_to "@wcopy_cond_0" (probe_word_entry_state s))
      (n2w (s.vs_alloca_next + 32))).vs_memory
Proof
  simp[probe_word_final_state_def, sstore_def, probe_word_copied_scratch_frame,
       jump_to_def, probe_word_load_exit_state_def, update_var_def]
QED

Theorem probe_word_loaded_memory:
  !s b.
    (probe_word_loaded_state s b).vs_memory =
    (mstore (w2n (b+64w)) (sload 5w s)
      (mstore (w2n (b+32w)) (sload 4w s)
        (mstore (w2n b) (sload 3w s) s))).vs_memory
Proof
  rpt gen_tac >>
  qabbrev_tac `t = probe_word_load_round s 0w b` >>
  qabbrev_tac `u = probe_word_load_round t 1w b` >>
  qabbrev_tac `t' = mstore (w2n b) (sload 3w s) s` >>
  qabbrev_tac `u' = mstore (w2n (b+32w)) (sload 4w s) t'` >>
  `contract_storage t = contract_storage s /\
   contract_storage u = contract_storage s` by
    simp[Abbr `u`, Abbr `t`, probe_word_load_storage_frame] >>
  `t.vs_memory = t'.vs_memory` by
    simp[Abbr `t`, Abbr `t'`, probe_word_load_round_memory,
         word_mul_n2w, word_add_n2w, WORD_ADD_0] >>
  `u.vs_memory = (mstore (w2n (b+32w)) (sload 4w s) t).vs_memory` by
    simp[Abbr `u`, probe_word_load_round_memory, sload_def,
         word_mul_n2w, word_add_n2w] >>
  `u.vs_memory = u'.vs_memory` by
    simp[Abbr `u'`, mstore_def] >>
  `(probe_word_loaded_state s b).vs_memory =
    (mstore (w2n (b+64w)) (sload 5w s) u).vs_memory` by
    simp[probe_word_loaded_state_def, jump_to_def,
         probe_word_load_cond_state_def, update_var_def,
         probe_word_load_round_memory, Abbr `u`, Abbr `t`,
         sload_def, probe_word_load_storage_frame, word_mul_n2w, word_add_n2w] >>
  `(mstore (w2n (b+64w)) (sload 5w s) u).vs_memory =
   (mstore (w2n (b+64w)) (sload 5w s) u').vs_memory` by simp[mstore_def] >>
  metis_tac[]
QED

Theorem probe_word_final_memory_footprint:
  !s. s.vs_alloca_next + 128 <= dimword (:256) ==>
    (probe_word_final_state s).vs_memory =
    (mstore (s.vs_alloca_next+96) (sload 5w s)
      (mstore (s.vs_alloca_next+64) (sload 4w s)
        (mstore (s.vs_alloca_next+32) (sload 3w s) s))).vs_memory
Proof
  rpt strip_tac >>
  `s.vs_alloca_next+32 < dimword (:256) /\
   s.vs_alloca_next+64 < dimword (:256) /\
   s.vs_alloca_next+96 < dimword (:256)` by decide_tac >>
  rewrite_tac[probe_word_final_memory, probe_word_loaded_memory] >>
  qabbrev_tac `e = jump_to "@wcopy_cond_0" (probe_word_entry_state s)` >>
  `contract_storage e = contract_storage s /\ e.vs_memory = s.vs_memory` by
    simp[Abbr `e`, contract_storage_def, jump_to_def,
         probe_word_entry_state_def, update_var_def] >>
  simp[word_add_n2w, w2n_n2w, arithmeticTheory.ADD_ASSOC, sload_def] >>
  qabbrev_tac `t = mstore (s.vs_alloca_next+32)
    (lookup_storage 3w (contract_storage s)) e` >>
  qabbrev_tac `t' = mstore (s.vs_alloca_next+32)
    (lookup_storage 3w (contract_storage s)) s` >>
  `t.vs_memory = t'.vs_memory` by simp[Abbr `t`, Abbr `t'`, mstore_def] >>
  qabbrev_tac `u = mstore (s.vs_alloca_next+64)
    (lookup_storage 4w (contract_storage s)) t` >>
  qabbrev_tac `u' = mstore (s.vs_alloca_next+64)
    (lookup_storage 4w (contract_storage s)) t'` >>
  `u.vs_memory = u'.vs_memory` by simp[Abbr `u`, Abbr `u'`, mstore_def] >>
  simp[mstore_def]
QED

Theorem probe_word_elem_round_storage:
  !s i src dst.
    contract_storage (probe_word_elem_round s i src dst) =
      update_storage (dst+i) (mload (w2n (src+i*32w)) s) (contract_storage s)
Proof
  simp[probe_word_elem_round_def, probe_word_elem_body_state_def,
       probe_word_elem_cond_state_def, jump_to_def, update_var_def,
       mload_def, sstore_def, contract_storage_def, lookup_account_def]
QED

Theorem probe_word_elem_cond_storage_frame:
  !s i lbl.
    contract_storage (jump_to lbl (probe_word_elem_cond_state s i)) =
      contract_storage s
Proof
  simp[contract_storage_def, jump_to_def, probe_word_elem_cond_state_def,
       update_var_def]
QED

Theorem probe_word_elems_copied_storage:
  !s src dst.
    contract_storage (probe_word_elems_copied_state s src dst) =
      update_storage (dst+1w) (mload (w2n (src+32w)) s)
        (update_storage dst (mload (w2n src) s) (contract_storage s))
Proof
  simp[probe_word_elems_copied_state_def, probe_word_elem_cond_storage_frame,
       probe_word_elem_round_storage] >>
  simp[word_mul_n2w, word_add_n2w, WORD_ADD_0,
       mload_def, probe_word_elem_round_scratch_frame]
QED

Theorem probe_word_copy_body_storage_frame:
  !s i b lbl.
    contract_storage (jump_to lbl (probe_word_copy_body_state s i b)) =
      contract_storage s
Proof
  simp[contract_storage_def, jump_to_def, probe_word_copy_body_state_def,
       update_var_def]
QED

Theorem probe_word_copy_cond_storage_frame:
  !s i n lbl.
    contract_storage (jump_to lbl (probe_word_copy_cond_state s i n)) =
      contract_storage s
Proof
  simp[contract_storage_def, jump_to_def, probe_word_copy_cond_state_def,
       update_var_def]
QED

Theorem probe_word_copy_setup_storage:
  !s i n b.
    contract_storage (probe_word_copy_setup_state s i n b) = contract_storage s /\
    mload (w2n (b+32w)) (probe_word_copy_setup_state s i n b) =
      mload (w2n (b+32w)) s /\
    mload (w2n (b+64w)) (probe_word_copy_setup_state s i n b) =
      mload (w2n (b+64w)) s
Proof
  rpt gen_tac >> conj_tac
  >- simp[probe_word_copy_setup_state_def, probe_word_copy_body_storage_frame,
          probe_word_copy_cond_storage_frame] >>
  simp[mload_def, probe_word_copy_setup_scratch_frame]
QED

Theorem probe_word_elem_exit_storage_frame:
  !s i lbl.
    contract_storage (jump_to lbl (probe_word_elem_exit_state s i)) =
      contract_storage s
Proof
  simp[contract_storage_def, jump_to_def, probe_word_elem_exit_state_def,
       update_var_def]
QED

Theorem probe_word_copy_round_storage:
  !s n b.
    contract_storage (probe_word_copy_round s 0w n b) =
      update_storage 2w (mload (w2n (b+64w)) s)
        (update_storage 1w (mload (w2n (b+32w)) s) (contract_storage s))
Proof
  simp[probe_word_copy_round_def, probe_word_elem_exit_storage_frame,
       probe_word_elems_copied_storage] >>
  simp[word_mul_n2w, word_add_n2w, WORD_ADD_0] >>
  simp[GSYM WORD_ADD_ASSOC, word_add_n2w, probe_word_copy_setup_storage]
QED

Theorem probe_word_copied_storage:
  !s n b.
    contract_storage (probe_word_copied_state s n b) =
      if n = 0w then contract_storage s
      else update_storage 2w (mload (w2n (b+64w)) s)
        (update_storage 1w (mload (w2n (b+32w)) s) (contract_storage s))
Proof
  rpt gen_tac >> Cases_on `n = 0w` >>
  simp[probe_word_copied_state_def, probe_word_copy_cond_storage_frame,
       probe_word_copy_round_storage]
QED

Theorem probe_word_loaded_words:
  !s b.
    regions_disjoint (w2n (b+64w),32) (w2n (b+32w),32) ==>
    mload (w2n (b+32w)) (probe_word_loaded_state s b) = sload 4w s /\
    mload (w2n (b+64w)) (probe_word_loaded_state s b) = sload 5w s
Proof
  rpt strip_tac >>
  `!p. mload p (probe_word_loaded_state s b) =
    mload p (mstore (w2n (b+64w)) (sload 5w s)
      (mstore (w2n (b+32w)) (sload 4w s)
        (mstore (w2n b) (sload 3w s) s)))` by
    simp[mload_def, probe_word_loaded_memory] >>
  simp[mload_mstore_same, mload_mstore_disjoint]
QED

Theorem probe_word_load_exit_storage_frame:
  !s b lbl p.
    contract_storage (jump_to lbl (probe_word_load_exit_state s b)) =
      contract_storage s /\
    mload p (jump_to lbl (probe_word_load_exit_state s b)) = mload p s
Proof
  simp[contract_storage_def, mload_def, jump_to_def,
       probe_word_load_exit_state_def, update_var_def]
QED

Theorem probe_word_final_storage:
  !s. s.vs_alloca_next + 128 <= dimword (:256) ==>
    contract_storage (probe_word_final_state s) =
      if sload 3w s = 0w then update_storage 0w 0w (contract_storage s)
      else update_storage 0w (sload 3w s)
        (update_storage 2w (sload 5w s)
          (update_storage 1w (sload 4w s) (contract_storage s)))
Proof
  rpt strip_tac >>
  qabbrev_tac `b = (n2w (s.vs_alloca_next+32):bytes32)` >>
  qabbrev_tac `e = jump_to "@wcopy_cond_0" (probe_word_entry_state s)` >>
  qabbrev_tac `l = probe_word_loaded_state e b` >>
  qabbrev_tac `c = jump_to "@dyn_cond_3" (probe_word_load_exit_state l b)` >>
  qabbrev_tac `d = probe_word_copied_state c (sload 3w s) b` >>
  `probe_word_final_state s = sstore 0w (sload 3w s) (d with vs_inst_idx := 1)` by
    simp[probe_word_final_state_def, Abbr `d`, Abbr `c`, Abbr `l`, Abbr `e`, Abbr `b`] >>
  `contract_storage (probe_word_final_state s) =
    update_storage 0w (sload 3w s) (contract_storage d)` by
    simp[sstore_def, contract_storage_def, lookup_account_def] >>
  `contract_storage e = contract_storage s` by
    simp[Abbr `e`, contract_storage_def, jump_to_def,
         probe_word_entry_state_def, update_var_def] >>
  `regions_disjoint (w2n (b+64w),32) (w2n (b+32w),32)` by
    (`s.vs_alloca_next+64 < dimword (:256) /\
      s.vs_alloca_next+96 < dimword (:256)` by decide_tac >>
     simp[Abbr `b`, word_add_n2w, w2n_n2w, arithmeticTheory.ADD_ASSOC,
          venomMemDefsTheory.regions_disjoint_def]) >>
  `mload (w2n (b+32w)) l = sload 4w s /\
   mload (w2n (b+64w)) l = sload 5w s` by
    (drule probe_word_loaded_words >>
     disch_then (qspec_then `e` mp_tac) >> simp[Abbr `l`, sload_def]) >>
  simp[Abbr `d`, probe_word_copied_storage, Abbr `c`,
       probe_word_load_exit_storage_frame, Abbr `l`, probe_word_loaded_storage_frame] >>
  Cases_on `sload 3w s = 0w` >> simp[]
QED

Theorem probe_word_final_memory_frame:
  !s off len.
    s.vs_alloca_next + 128 <= dimword (:256) /\
    (off+len <= s.vs_alloca_next+32 \/ s.vs_alloca_next+128 <= off) ==>
    mem_bytes_at off len (probe_word_final_state s).vs_memory =
      mem_bytes_at off len s.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `off+len <= s.vs_alloca_next+32 \/ s.vs_alloca_next+64 <= off` by decide_tac >>
  `off+len <= s.vs_alloca_next+64 \/ s.vs_alloca_next+96 <= off` by decide_tac >>
  `off+len <= s.vs_alloca_next+96 \/ s.vs_alloca_next+128 <= off` by decide_tac >>
  simp[probe_word_final_memory_footprint,
       valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]
QED

(* Only mutable runtime fields propagated by INVOKE, excluding accounts and
   memory, which have separate (non-identity) footprints above. *)
Theorem probe_word_entry_runtime_frame[local]:
  !s.
    (probe_word_entry_state s).vs_transient = s.vs_transient /\
    (probe_word_entry_state s).vs_returndata = s.vs_returndata /\
    (probe_word_entry_state s).vs_logs = s.vs_logs /\
    (probe_word_entry_state s).vs_outcomes = s.vs_outcomes /\
    (probe_word_entry_state s).vs_requests = s.vs_requests /\
    (probe_word_entry_state s).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_entry_state s).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_entry_state_def, update_var_def]
QED

Theorem probe_word_load_runtime_frame[local]:
  !s i b.
    (probe_word_load_state s i b).vs_transient = s.vs_transient /\
    (probe_word_load_state s i b).vs_returndata = s.vs_returndata /\
    (probe_word_load_state s i b).vs_logs = s.vs_logs /\
    (probe_word_load_state s i b).vs_outcomes = s.vs_outcomes /\
    (probe_word_load_state s i b).vs_requests = s.vs_requests /\
    (probe_word_load_state s i b).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_load_state s i b).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_load_state_def, update_var_def, mstore_def]
QED

Theorem probe_word_load_round_runtime_frame[local]:
  !s i b.
    (probe_word_load_round s i b).vs_transient = s.vs_transient /\
    (probe_word_load_round s i b).vs_returndata = s.vs_returndata /\
    (probe_word_load_round s i b).vs_logs = s.vs_logs /\
    (probe_word_load_round s i b).vs_outcomes = s.vs_outcomes /\
    (probe_word_load_round s i b).vs_requests = s.vs_requests /\
    (probe_word_load_round s i b).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_load_round s i b).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_load_round_def, jump_to_def, probe_word_load_runtime_frame,
       probe_word_load_cond_state_def, update_var_def]
QED

Theorem probe_word_loaded_runtime_frame[local]:
  !s b.
    (probe_word_loaded_state s b).vs_transient = s.vs_transient /\
    (probe_word_loaded_state s b).vs_returndata = s.vs_returndata /\
    (probe_word_loaded_state s b).vs_logs = s.vs_logs /\
    (probe_word_loaded_state s b).vs_outcomes = s.vs_outcomes /\
    (probe_word_loaded_state s b).vs_requests = s.vs_requests /\
    (probe_word_loaded_state s b).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_loaded_state s b).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_loaded_state_def, jump_to_def,
       probe_word_load_cond_state_def, update_var_def,
       probe_word_load_round_runtime_frame]
QED

Theorem probe_word_elem_body_runtime_frame[local]:
  !s i src dst.
    (probe_word_elem_body_state s i src dst).vs_transient = s.vs_transient /\
    (probe_word_elem_body_state s i src dst).vs_returndata = s.vs_returndata /\
    (probe_word_elem_body_state s i src dst).vs_logs = s.vs_logs /\
    (probe_word_elem_body_state s i src dst).vs_outcomes = s.vs_outcomes /\
    (probe_word_elem_body_state s i src dst).vs_requests = s.vs_requests /\
    (probe_word_elem_body_state s i src dst).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_elem_body_state s i src dst).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_elem_body_state_def, update_var_def, sstore_def]
QED

Theorem probe_word_elem_round_runtime_frame[local]:
  !s i src dst.
    (probe_word_elem_round s i src dst).vs_transient = s.vs_transient /\
    (probe_word_elem_round s i src dst).vs_returndata = s.vs_returndata /\
    (probe_word_elem_round s i src dst).vs_logs = s.vs_logs /\
    (probe_word_elem_round s i src dst).vs_outcomes = s.vs_outcomes /\
    (probe_word_elem_round s i src dst).vs_requests = s.vs_requests /\
    (probe_word_elem_round s i src dst).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_elem_round s i src dst).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_elem_round_def, jump_to_def, probe_word_elem_body_runtime_frame,
       probe_word_elem_cond_state_def, update_var_def]
QED

Theorem probe_word_elems_copied_runtime_frame[local]:
  !s src dst.
    (probe_word_elems_copied_state s src dst).vs_transient = s.vs_transient /\
    (probe_word_elems_copied_state s src dst).vs_returndata = s.vs_returndata /\
    (probe_word_elems_copied_state s src dst).vs_logs = s.vs_logs /\
    (probe_word_elems_copied_state s src dst).vs_outcomes = s.vs_outcomes /\
    (probe_word_elems_copied_state s src dst).vs_requests = s.vs_requests /\
    (probe_word_elems_copied_state s src dst).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_elems_copied_state s src dst).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_elems_copied_state_def, jump_to_def,
       probe_word_elem_cond_state_def, update_var_def, probe_word_elem_round_runtime_frame]
QED

Theorem probe_word_copy_body_runtime_frame[local]:
  !s i b.
    (probe_word_copy_body_state s i b).vs_transient = s.vs_transient /\
    (probe_word_copy_body_state s i b).vs_returndata = s.vs_returndata /\
    (probe_word_copy_body_state s i b).vs_logs = s.vs_logs /\
    (probe_word_copy_body_state s i b).vs_outcomes = s.vs_outcomes /\
    (probe_word_copy_body_state s i b).vs_requests = s.vs_requests /\
    (probe_word_copy_body_state s i b).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_copy_body_state s i b).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_copy_body_state_def, update_var_def]
QED

Theorem probe_word_copy_setup_runtime_frame[local]:
  !s i n b.
    (probe_word_copy_setup_state s i n b).vs_transient = s.vs_transient /\
    (probe_word_copy_setup_state s i n b).vs_returndata = s.vs_returndata /\
    (probe_word_copy_setup_state s i n b).vs_logs = s.vs_logs /\
    (probe_word_copy_setup_state s i n b).vs_outcomes = s.vs_outcomes /\
    (probe_word_copy_setup_state s i n b).vs_requests = s.vs_requests /\
    (probe_word_copy_setup_state s i n b).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_copy_setup_state s i n b).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_copy_setup_state_def, jump_to_def, probe_word_copy_body_runtime_frame,
       probe_word_copy_cond_state_def, update_var_def]
QED

Theorem probe_word_copy_round_runtime_frame[local]:
  !s i n b.
    (probe_word_copy_round s i n b).vs_transient = s.vs_transient /\
    (probe_word_copy_round s i n b).vs_returndata = s.vs_returndata /\
    (probe_word_copy_round s i n b).vs_logs = s.vs_logs /\
    (probe_word_copy_round s i n b).vs_outcomes = s.vs_outcomes /\
    (probe_word_copy_round s i n b).vs_requests = s.vs_requests /\
    (probe_word_copy_round s i n b).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_copy_round s i n b).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_copy_round_def, jump_to_def, probe_word_elem_exit_state_def,
       update_var_def, probe_word_elems_copied_runtime_frame,
       probe_word_copy_setup_runtime_frame]
QED

Theorem probe_word_copied_runtime_frame[local]:
  !s n b.
    (probe_word_copied_state s n b).vs_transient = s.vs_transient /\
    (probe_word_copied_state s n b).vs_returndata = s.vs_returndata /\
    (probe_word_copied_state s n b).vs_logs = s.vs_logs /\
    (probe_word_copied_state s n b).vs_outcomes = s.vs_outcomes /\
    (probe_word_copied_state s n b).vs_requests = s.vs_requests /\
    (probe_word_copied_state s n b).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_copied_state s n b).vs_immutables = s.vs_immutables
Proof
  rpt gen_tac >> Cases_on `n = 0w` >>
  simp[probe_word_copied_state_def, jump_to_def, probe_word_copy_cond_state_def,
       update_var_def, probe_word_copy_round_runtime_frame]
QED

Theorem probe_word_final_runtime_frame:
  !s.
    (probe_word_final_state s).vs_transient = s.vs_transient /\
    (probe_word_final_state s).vs_returndata = s.vs_returndata /\
    (probe_word_final_state s).vs_logs = s.vs_logs /\
    (probe_word_final_state s).vs_outcomes = s.vs_outcomes /\
    (probe_word_final_state s).vs_requests = s.vs_requests /\
    (probe_word_final_state s).vs_pending_deletions = s.vs_pending_deletions /\
    (probe_word_final_state s).vs_immutables = s.vs_immutables
Proof
  simp[probe_word_final_state_def, sstore_def, probe_word_copied_runtime_frame,
       jump_to_def, probe_word_load_exit_state_def, update_var_def,
       probe_word_loaded_runtime_frame, probe_word_entry_runtime_frame]
QED

Theorem probe_word_function_entry:
  ~NULL probe_word_function.fn_blocks /\
  (HD probe_word_function.fn_blocks).bb_label = "entry"
Proof
  EVAL_TAC
QED

Theorem probe_word_setup_exists:
  !args s. ?cs. setup_callee probe_word_function args s = SOME cs
Proof
  simp[setup_callee_def, probe_word_function_entry]
QED

Theorem probe_word_setup_observations:
  !args s cs.
    setup_callee probe_word_function args s = SOME cs ==>
    cs.vs_current_bb = "entry" /\ ~cs.vs_halted /\
    cs.vs_allocas = FEMPTY /\ cs.vs_alloca_next = s.vs_alloca_next /\
    contract_storage cs = contract_storage s
Proof
  simp[setup_callee_def, probe_word_function_entry] >>
  rpt strip_tac >> simp[contract_storage_def]
QED

Theorem probe_word_invoke:
  !name ctx ops s args cs fuel id out.
    lookup_function name ctx.ctx_functions = SOME probe_word_function /\
    eval_operands ops s = SOME args /\
    s.vs_alloca_next + 128 <= dimword (:256) /\
    (sload 3w s = 0w \/ sload 3w s = 1w) /\
    setup_callee probe_word_function args s = SOME cs ==>
    step_inst ((if sload 3w s = 0w then 11 else 19) + fuel) ctx
      (mk_inst id INVOKE (Label name :: ops) [out]) s =
    OK (update_var out 0w
      (merge_callee_state s (probe_word_final_state cs)))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule probe_word_setup_observations >> strip_tac >>
  `sload 3w cs = sload 3w s` by simp[sload_def] >>
  `run_blocks ((if sload 3w s = 0w then 11 else 19) + fuel)
      ctx probe_word_function cs =
    IntRet <| iret_values := [0w]; iret_adopt_fmp := NONE |>
      (probe_word_final_state cs)` by
    (qspecl_then [`cs`, `fuel`, `ctx`] mp_tac probe_word_run_function >> simp[]) >>
  gvs[] >>
  simp[Once step_inst_def, decode_invoke_def, bind_outputs_def, adopt_return_fmp_def]
QED

Theorem probe_word_invoke_caller_frame:
  !s cs out.
    (update_var out 0w (merge_callee_state s (probe_word_final_state cs))).vs_allocas =
      s.vs_allocas /\
    (update_var out 0w (merge_callee_state s (probe_word_final_state cs))).vs_alloca_next =
      s.vs_alloca_next /\
    (update_var out 0w (merge_callee_state s (probe_word_final_state cs))).vs_current_bb =
      s.vs_current_bb /\
    (update_var out 0w (merge_callee_state s (probe_word_final_state cs))).vs_inst_idx =
      s.vs_inst_idx /\
    (update_var out 0w (merge_callee_state s (probe_word_final_state cs))).vs_fmp =
      s.vs_fmp /\
    (update_var out 0w (merge_callee_state s (probe_word_final_state cs))).vs_call_entry_fmp =
      s.vs_call_entry_fmp /\
    (update_var out 0w (merge_callee_state s (probe_word_final_state cs))).vs_return_pc_token =
      s.vs_return_pc_token /\
    (!v. lookup_var v (update_var out 0w (merge_callee_state s (probe_word_final_state cs))) =
      lookup_var v (update_var out 0w s))
Proof
  simp[update_var_def, lookup_var_def, merge_callee_local_fields]
QED

Theorem probe_word_agree_donor_header:
  !st mt.
    storage_agree (storage_dead probe_word_context F st) st mt ==>
    lookup_storage 3w mt = lookup_storage 3w st
Proof
  rpt strip_tac >> sym_tac >>
  irule accountsRelPropsTheory.word_to_bytes_EL_eq >> rpt strip_tac >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  simp[storage_agree_def] >> strip_tac >>
  first_x_assum (qspecl_then [`3w`, `b`] mp_tac) >>
  simp[probe_word_dead_bytes, dimword_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem probe_word_pre_machine_header:
  !cenv env e0 es s.
    expr_body_pre cenv probe_word_context env e0 es /\
    storage_agree
      (storage_dead probe_word_context F (get_storage probe_word_context es F))
      (get_storage probe_word_context es F) (contract_storage s) ==>
    (sload 3w s = 0w \/ sload 3w s = 1w)
Proof
  rpt gen_tac >> strip_tac >>
  drule probe_word_pre_shapes >> strip_tac >>
  drule probe_word_agree_donor_header >> strip_tac >>
  `w2n (sload 3w s) <= 1` by simp[sload_def] >>
  `w2n (sload 3w s) = 0 \/ w2n (sload 3w s) = 1` by decide_tac >>
  metis_tac[wordsTheory.n2w_w2n]
QED

Theorem probe_word_load_round_call_ctx[local]:
  !s i b. (probe_word_load_round s i b).vs_call_ctx = s.vs_call_ctx
Proof
  simp[probe_word_load_round_def, jump_to_def, probe_word_load_cond_state_def,
       probe_word_load_state_def, update_var_def, mstore_def]
QED

Theorem probe_word_loaded_call_ctx[local]:
  !s b. (probe_word_loaded_state s b).vs_call_ctx = s.vs_call_ctx
Proof
  simp[probe_word_loaded_state_def, jump_to_def,
       probe_word_load_cond_state_def, update_var_def, probe_word_load_round_call_ctx]
QED

Theorem probe_word_elem_round_call_ctx[local]:
  !s i src dst. (probe_word_elem_round s i src dst).vs_call_ctx = s.vs_call_ctx
Proof
  simp[probe_word_elem_round_def, jump_to_def, probe_word_elem_body_state_def,
       probe_word_elem_cond_state_def, update_var_def, sstore_def]
QED

Theorem probe_word_elems_copied_call_ctx[local]:
  !s src dst. (probe_word_elems_copied_state s src dst).vs_call_ctx = s.vs_call_ctx
Proof
  simp[probe_word_elems_copied_state_def, jump_to_def,
       probe_word_elem_cond_state_def, update_var_def, probe_word_elem_round_call_ctx]
QED

Theorem probe_word_copy_body_call_ctx[local]:
  !s i b. (probe_word_copy_body_state s i b).vs_call_ctx = s.vs_call_ctx
Proof
  simp[probe_word_copy_body_state_def, update_var_def]
QED

Theorem probe_word_copy_setup_call_ctx[local]:
  !s i n b. (probe_word_copy_setup_state s i n b).vs_call_ctx = s.vs_call_ctx
Proof
  simp[probe_word_copy_setup_state_def, jump_to_def, probe_word_copy_body_call_ctx,
       probe_word_copy_cond_state_def, update_var_def]
QED

Theorem probe_word_copy_round_call_ctx[local]:
  !s i n b. (probe_word_copy_round s i n b).vs_call_ctx = s.vs_call_ctx
Proof
  simp[probe_word_copy_round_def, jump_to_def, probe_word_elem_exit_state_def,
       update_var_def, probe_word_elems_copied_call_ctx, probe_word_copy_setup_call_ctx]
QED

Theorem probe_word_copied_call_ctx[local]:
  !s n b. (probe_word_copied_state s n b).vs_call_ctx = s.vs_call_ctx
Proof
  rpt gen_tac >> Cases_on `n = 0w` >>
  simp[probe_word_copied_state_def, jump_to_def, probe_word_copy_cond_state_def,
       update_var_def, probe_word_copy_round_call_ctx]
QED

Theorem probe_word_final_call_ctx:
  !s. (probe_word_final_state s).vs_call_ctx = s.vs_call_ctx
Proof
  simp[probe_word_final_state_def, sstore_def, probe_word_copied_call_ctx,
       jump_to_def, probe_word_load_exit_state_def, update_var_def,
       probe_word_loaded_call_ctx, probe_word_entry_state_def]
QED

Theorem probe_word_merged_storage:
  !s args cs out.
    setup_callee probe_word_function args s = SOME cs /\
    s.vs_alloca_next + 128 <= dimword (:256) ==>
    contract_storage (update_var out 0w
      (merge_callee_state s (probe_word_final_state cs))) =
      if sload 3w s = 0w then update_storage 0w 0w (contract_storage s)
      else update_storage 0w (sload 3w s)
        (update_storage 2w (sload 5w s)
          (update_storage 1w (sload 4w s) (contract_storage s)))
Proof
  rpt gen_tac >> strip_tac >>
  drule probe_word_setup_observations >> strip_tac >>
  drule setup_callee_shared_fields >> strip_tac >>
  `contract_storage (update_var out 0w
      (merge_callee_state s (probe_word_final_state cs))) =
    contract_storage (probe_word_final_state cs)` by
    simp[contract_storage_def, update_var_def, probe_word_final_call_ctx] >>
  simp[probe_word_final_storage, sload_def]
QED

Theorem probe_word_invoke_storage_summary:
  !cenv env e0 es s args cs out.
    expr_body_pre cenv probe_word_context env e0 es /\
    storage_agree
      (storage_dead probe_word_context F (get_storage probe_word_context es F))
      (get_storage probe_word_context es F) (contract_storage s) /\
    s.vs_alloca_next + 128 <= dimword (:256) /\
    setup_callee probe_word_function args s = SOME cs ==>
    ?es'. eval_expr probe_word_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
      (INL (Value (IntV 0)), es') /\ es'.scopes = es.scopes /\
      storage_agree
        (storage_dead probe_word_context F (get_storage probe_word_context es' F))
        (get_storage probe_word_context es' F)
        (contract_storage (update_var out 0w
          (merge_callee_state s (probe_word_final_state cs))))
Proof
  rpt gen_tac >> strip_tac >>
  drule probe_word_agree_donor_header >> strip_tac >>
  drule_all probe_word_conditional_copy_pre_summary >> strip_tac >>
  qexists_tac `es'` >> simp[] >>
  drule_all probe_word_merged_storage >> disch_then (fn th => rewrite_tac[th]) >>
  gvs[sload_def, wordsTheory.w2n_eq_0]
QED

Theorem probe_word_load_round_accounts[local]:
  !s i b. (probe_word_load_round s i b).vs_accounts = s.vs_accounts
Proof
  simp[probe_word_load_round_def, jump_to_def, probe_word_load_cond_state_def,
       probe_word_load_state_def, update_var_def, mstore_def]
QED

Theorem probe_word_loaded_accounts[local]:
  !s b. (probe_word_loaded_state s b).vs_accounts = s.vs_accounts
Proof
  simp[probe_word_loaded_state_def, jump_to_def, probe_word_load_cond_state_def,
       update_var_def, probe_word_load_round_accounts]
QED

(* Overwriting the active account's storage erases precisely the effect
   of a copy round; all other addresses and account metadata are retained. *)
Theorem probe_word_elem_round_accounts_overwrite[local]:
  !s i src dst a stor.
    s.vs_call_ctx.cc_address = a ==>
    (a =+ (lookup_account a (probe_word_elem_round s i src dst).vs_accounts
      with storage := stor)) (probe_word_elem_round s i src dst).vs_accounts =
       (a =+ (lookup_account a s.vs_accounts with storage := stor)) s.vs_accounts
Proof
  rpt strip_tac >>
  simp[probe_word_elem_round_def, jump_to_def, probe_word_elem_cond_state_def,
       probe_word_elem_body_state_def, update_var_def, sstore_def, lookup_account_def]
QED

Theorem probe_word_elems_copied_accounts_overwrite[local]:
  !s src dst a stor.
    s.vs_call_ctx.cc_address = a ==>
    (a =+ (lookup_account a (probe_word_elems_copied_state s src dst).vs_accounts
      with storage := stor)) (probe_word_elems_copied_state s src dst).vs_accounts =
       (a =+ (lookup_account a s.vs_accounts with storage := stor)) s.vs_accounts
Proof
  rpt strip_tac >>
  simp[probe_word_elems_copied_state_def, jump_to_def,
       probe_word_elem_cond_state_def, update_var_def,
       probe_word_elem_round_accounts_overwrite, probe_word_elem_round_call_ctx]
QED

Theorem probe_word_copy_body_accounts[local]:
  !s i b. (probe_word_copy_body_state s i b).vs_accounts = s.vs_accounts
Proof
  simp[probe_word_copy_body_state_def, update_var_def]
QED

Theorem probe_word_copy_setup_accounts[local]:
  !s i n b. (probe_word_copy_setup_state s i n b).vs_accounts = s.vs_accounts
Proof
  simp[probe_word_copy_setup_state_def, jump_to_def, probe_word_copy_body_accounts,
       probe_word_copy_cond_state_def, update_var_def]
QED

Theorem probe_word_copy_round_accounts_overwrite[local]:
  !s i n b a stor.
    s.vs_call_ctx.cc_address = a ==>
    (a =+ (lookup_account a (probe_word_copy_round s i n b).vs_accounts
      with storage := stor)) (probe_word_copy_round s i n b).vs_accounts =
       (a =+ (lookup_account a s.vs_accounts with storage := stor)) s.vs_accounts
Proof
  rpt strip_tac >>
  simp[probe_word_copy_round_def, jump_to_def, probe_word_elem_exit_state_def,
       update_var_def, probe_word_elems_copied_accounts_overwrite,
       probe_word_copy_setup_call_ctx, probe_word_copy_setup_accounts]
QED

Theorem probe_word_copied_accounts_overwrite[local]:
  !s n b a stor.
    s.vs_call_ctx.cc_address = a ==>
    (a =+ (lookup_account a (probe_word_copied_state s n b).vs_accounts
      with storage := stor)) (probe_word_copied_state s n b).vs_accounts =
       (a =+ (lookup_account a s.vs_accounts with storage := stor)) s.vs_accounts
Proof
  rpt strip_tac >> Cases_on `n = 0w` >>
  simp[probe_word_copied_state_def, jump_to_def, probe_word_copy_cond_state_def,
       update_var_def, probe_word_copy_round_accounts_overwrite]
QED

Theorem probe_word_final_accounts:
  !s.
    (probe_word_final_state s).vs_accounts =
      (s.vs_call_ctx.cc_address =+
        (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with
          storage := contract_storage (probe_word_final_state s))) s.vs_accounts
Proof
  gen_tac >>
  qabbrev_tac `b = (n2w (s.vs_alloca_next+32):bytes32)` >>
  qabbrev_tac `e = jump_to "@wcopy_cond_0" (probe_word_entry_state s)` >>
  qabbrev_tac `l = probe_word_loaded_state e b` >>
  qabbrev_tac `c = jump_to "@dyn_cond_3" (probe_word_load_exit_state l b)` >>
  qabbrev_tac `d = probe_word_copied_state c (sload 3w s) b` >>
  `e.vs_call_ctx = s.vs_call_ctx /\ e.vs_accounts = s.vs_accounts` by
    simp[Abbr `e`, jump_to_def, probe_word_entry_state_def, update_var_def] >>
  `l.vs_call_ctx = s.vs_call_ctx /\ l.vs_accounts = s.vs_accounts` by
    simp[Abbr `l`, probe_word_loaded_accounts, probe_word_loaded_call_ctx] >>
  `c.vs_call_ctx = s.vs_call_ctx /\ c.vs_accounts = s.vs_accounts` by
    simp[Abbr `c`, jump_to_def, probe_word_load_exit_state_def, update_var_def] >>
  `d.vs_call_ctx = s.vs_call_ctx` by simp[Abbr `d`, probe_word_copied_call_ctx] >>
  `probe_word_final_state s = sstore 0w (sload 3w s) (d with vs_inst_idx := 1)` by
    simp[probe_word_final_state_def, Abbr `d`, Abbr `c`, Abbr `l`, Abbr `e`, Abbr `b`] >>
  asm_rewrite_tac[] >>
  simp[sstore_def, contract_storage_def, lookup_account_def] >>
  simp[GSYM lookup_account_def, Abbr `d`, probe_word_copied_accounts_overwrite]
QED

Theorem probe_word_merged_accounts:
  !s args cs out.
    setup_callee probe_word_function args s = SOME cs /\
    s.vs_call_ctx.cc_address = probe_word_context.txn.target ==>
    let t = update_var out 0w (merge_callee_state s (probe_word_final_state cs)) in
    t.vs_accounts = (probe_word_context.txn.target =+
      (lookup_account probe_word_context.txn.target s.vs_accounts with
        storage := contract_storage t)) s.vs_accounts /\
    t.vs_transient = s.vs_transient
Proof
  rpt gen_tac >> strip_tac >>
  drule setup_callee_shared_fields >> strip_tac >>
  `contract_storage (update_var out 0w (merge_callee_state s (probe_word_final_state cs))) =
    contract_storage (probe_word_final_state cs)` by
    simp[contract_storage_def, update_var_def, probe_word_final_call_ctx] >>
  gs[update_var_def, probe_word_final_runtime_frame] >>
  once_rewrite_tac[probe_word_final_accounts] >> simp[]
QED

Theorem probe_word_invoke_accounts_summary:
  !cenv env e0 es s args cs out.
    expr_body_pre cenv probe_word_context env e0 es /\
    storage_agree
      (storage_dead probe_word_context F (get_storage probe_word_context es F))
      (get_storage probe_word_context es F) (contract_storage s) /\
    s.vs_alloca_next + 128 <= dimword (:256) /\
    setup_callee probe_word_function args s = SOME cs /\
    accounts_rel probe_word_context es s /\
    s.vs_call_ctx.cc_address = probe_word_context.txn.target ==>
    ?es'. eval_expr probe_word_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
      (INL (Value (IntV 0)), es') /\ es'.scopes = es.scopes /\
      accounts_rel probe_word_context es'
        (update_var out 0w (merge_callee_state s (probe_word_final_state cs)))
Proof
  rpt gen_tac >> strip_tac >>
  drule probe_word_pre_shapes >> strip_tac >>
  qspecl_then [`es`,
    `w2n (lookup_storage 3w (get_storage probe_word_context es F))`,
    `w2n (lookup_storage 4w (get_storage probe_word_context es F))`]
    mp_tac probe_word_copy_symbolic_success >>
  simp[wordsTheory.n2w_w2n] >>
  (impl_tac >- metis_tac[wordsTheory.n2w_w2n]) >>
  strip_tac >>
  drule_all probe_word_invoke_storage_summary >> strip_tac >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `set_storage _ _ F stor` >>
  irule accountsRelPropsTheory.accounts_rel_set_storage >>
  qexistsl [`es`, `s`, `stor`,
    `contract_storage (merge_callee_state s (probe_word_final_state cs))`] >>
  simp[set_storage_backend_eq] >>
  drule_all probe_word_merged_accounts >>
  disch_then (qspec_then `out` mp_tac) >>
  gvs[get_storage_after_set, update_var_def, contract_storage_def]
QED

Theorem probe_word_invoke_local_memory:
  !func cenv scopes s args cs out name lo sz.
    local_ptrs_rel func cenv scopes s /\
    setup_callee probe_word_function args s = SOME cs /\
    s.vs_alloca_next + 128 <= dimword (:256) /\
    local_region cenv scopes s name lo sz ==>
    mem_bytes_at lo sz
      (update_var out 0w (merge_callee_state s (probe_word_final_state cs))).vs_memory =
    mem_bytes_at lo sz s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule setup_callee_shared_fields >> strip_tac >>
  drule probe_word_setup_observations >> strip_tac >>
  `regions_disjoint lo sz s.vs_alloca_next 128` by
    (irule localPtrsPropsTheory.local_ptrs_rel_above_frontier >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `sz = 0` >- simp[valueEncodingTheory.mem_bytes_at_def] >>
  `lo + sz <= cs.vs_alloca_next + 32 \/ cs.vs_alloca_next + 128 <= lo` by
    (gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at lo sz (probe_word_final_state cs).vs_memory =
   mem_bytes_at lo sz cs.vs_memory` by
    (irule probe_word_final_memory_frame >> simp[]) >>
  simp[update_var_def]
QED

Theorem probe_word_invoke_local_ptrs:
  !func cenv scopes s args cs out.
    local_ptrs_rel func cenv scopes s /\
    setup_callee probe_word_function args s = SOME cs /\
    s.vs_alloca_next + 128 <= dimword (:256) /\
    not_local_ptr cenv scopes out ==>
    local_ptrs_rel func cenv scopes
      (update_var out 0w (merge_callee_state s (probe_word_final_state cs)))
Proof
  rpt gen_tac >> strip_tac >>
  irule localPtrsPropsTheory.local_ptrs_rel_update_var >> simp[] >>
  irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >>
  qexists_tac `s` >>
  simp[merge_callee_local_fields, lookup_var_def] >>
  rpt strip_tac >> gvs[] >> sym_tac >>
  drule_all probe_word_invoke_local_memory >>
  disch_then (qspec_then `out` mp_tac) >> simp[update_var_def]
QED

Theorem probe_word_invoke_locals_kept:
  !func cenv es s args cs out.
    local_ptrs_rel func cenv es.scopes s /\
    setup_callee probe_word_function args s = SOME cs /\
    s.vs_alloca_next + 128 <= dimword (:256) ==>
    locals_kept cenv es s
      (update_var out 0w (merge_callee_state s (probe_word_final_state cs)))
Proof
  rpt gen_tac >> strip_tac >>
  irule exprSimTheory.locals_kept_regions >> rpt strip_tac >>
  irule probe_word_invoke_local_memory >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem probe_word_invoke_immutables[local]:
  !ctx func cenv es s args cs out.
    stmt_state_rel ctx func cenv probe_word_context es s /\
    setup_callee probe_word_function args s = SOME cs /\
    s.vs_alloca_next + 128 <= dimword (:256) ==>
    immutables_rel cenv probe_word_context.txn.target
      cenv.ce_module cenv.ce_is_ctor es
      (update_var out 0w (merge_callee_state s (probe_word_final_state cs)))
Proof
  rpt gen_tac >> strip_tac >>
  drule setup_callee_shared_fields >> strip_tac >>
  drule probe_word_setup_observations >> strip_tac >>
  irule loweringSliceTheory.immutables_rel_mem_agree >>
  qexists_tac `s` >>
  simp[update_var_def] >>
  conj_tac
  >- (simp[probe_word_final_memory_footprint,
           immutableMemoryFrameTheory.immutable_mstore_capacity] >>
      decide_tac) >>
  reverse conj_tac >- gvs[stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >>
  `off + type_memory_size tv <= s.vs_alloca_next` by
    (gvs[stmt_state_rel_def, immutable_alloca_sep_def] >> metis_tac[]) >>
  `mem_bytes_at off (type_memory_size tv) (probe_word_final_state cs).vs_memory =
   mem_bytes_at off (type_memory_size tv) cs.vs_memory` by
    (irule probe_word_final_memory_frame >> simp[] >> decide_tac) >>
  simp[]
QED

Theorem probe_word_invoke_immutable_sep[local]:
  !func cenv es s cs out.
    immutable_alloca_sep func cenv probe_word_context es s /\
    not_local_ptr cenv es.scopes out ==>
    immutable_alloca_sep func cenv probe_word_context es
      (update_var out 0w (merge_callee_state s (probe_word_final_state cs)))
Proof
  rpt gen_tac >> strip_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
  simp[probe_word_invoke_caller_frame] >>
  rpt strip_tac >> qexists_tac `id` >>
  gvs[local_region_def, not_local_ptr_def, probe_word_invoke_caller_frame,
      lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem probe_word_invoke_stmt_state_summary:
  !ctx func cenv env e0 es s args cs out.
    expr_body_pre cenv probe_word_context env e0 es /\
    stmt_state_rel ctx func cenv probe_word_context es s /\
    s.vs_alloca_next + 128 <= dimword (:256) /\
    setup_callee probe_word_function args s = SOME cs /\
    not_local_ptr cenv es.scopes out ==>
    ?es'. eval_expr probe_word_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
      (INL (Value (IntV 0)), es') /\ es'.scopes = es.scopes /\
      stmt_state_rel ctx func cenv probe_word_context es'
        (update_var out 0w (merge_callee_state s (probe_word_final_state cs)))
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\
   accounts_rel probe_word_context es s /\
   s.vs_call_ctx.cc_address = probe_word_context.txn.target /\
   storage_agree
     (storage_dead probe_word_context F (get_storage probe_word_context es F))
     (get_storage probe_word_context es F) (contract_storage s)` by
    gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
        storage_rel_def, get_storage_def, lookup_account_def] >>
  drule_all probe_word_invoke_accounts_summary >> strip_tac >>
  drule probe_word_pre_shapes >> strip_tac >>
  qspecl_then [`es`,
    `w2n (lookup_storage 3w (get_storage probe_word_context es F))`,
    `w2n (lookup_storage 4w (get_storage probe_word_context es F))`]
    mp_tac probe_word_copy_symbolic_success >>
  simp[wordsTheory.n2w_w2n] >>
  (impl_tac >- metis_tac[wordsTheory.n2w_w2n]) >> strip_tac >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel _ _ _ _ (set_storage _ _ F stor)` >>
  drule_all probe_word_invoke_local_ptrs >> strip_tac >>
  drule_all probe_word_invoke_immutables >> strip_tac >>
  `immutable_alloca_sep func cenv probe_word_context es s` by
    gvs[stmt_state_rel_def] >>
  drule_all probe_word_invoke_immutable_sep >>
  disch_then (qspec_then `cs` assume_tac) >>
  irule stmt_state_rel_allocas_frame >>
  conj_tac
  >- (qpat_x_assum `immutable_alloca_sep _ _ _ es (update_var _ _ _)` mp_tac >>
      simp[immutable_alloca_sep_def, set_storage_def]) >>
  reverse conj_tac
  >- (qexistsl_tac [`es`, `s`] >> simp[probe_word_invoke_caller_frame]) >>
  drule setup_callee_shared_fields >> strip_tac >>
  qpat_assum `accounts_rel _ (set_storage _ _ _ _) _`
    (mp_then Any mp_tac accountsRelPropsTheory.accounts_rel_storage_transient) >>
  simp[probe_word_final_call_ctx] >> strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  simp[stmt_state_rel_def, state_rel_def] >> strip_tac >>
  drule setup_callee_oracle >> strip_tac >>
  `immutables_rel cenv probe_word_context.txn.target cenv.ce_module cenv.ce_is_ctor
     (set_storage probe_word_context es F stor)
     (update_var out 0w (merge_callee_state s (probe_word_final_state cs)))` by
    (qpat_assum `!out. immutables_rel _ _ _ _ _ _`
       (qspec_then `out` mp_tac) >> simp[NoAsms, immutables_rel_def, set_storage_def]) >>
  simp[state_rel_def] >>
  gvs[storage_rel_def, transient_rel_def, contract_storage_def,
      contract_transient_def, update_var_def] >>
  simp[logs_rel_def, set_storage_def, probe_word_final_runtime_frame,
       probe_word_final_call_ctx] >>
  gvs[logs_rel_def]
QED

(* The actual caller allocates a return buffer even for a single word. *)
Theorem probe_word_shrink_lower_value:
  !cenv sa bufsz flags ty.
    cenv.ce_func_info "shrink" = (1,bufsz,flags) ==>
    lower_value compile_expr cenv ty
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) sa =
    (Var ("%" ++ toString (sa.cs_next_var + 3)),
     sa with <| cs_next_var := sa.cs_next_var + 4;
                cs_next_id := sa.cs_next_id + 5;
                cs_current_insts := sa.cs_current_insts ++
       [mk_inst sa.cs_next_id ALLOCA [Lit 32w]
          ["%" ++ toString sa.cs_next_var];
        mk_inst (sa.cs_next_id + 1) INVOKE
          [Label (internal_fn_label (cenv.ce_func_ids "shrink") "shrink"
             (cenv.ce_func_param_types "shrink") cenv.ce_is_ctor)]
          ["%" ++ toString (sa.cs_next_var + 1)];
        mk_inst (sa.cs_next_id + 2) ADD
          [Var ("%" ++ toString sa.cs_next_var); Lit 0w]
          ["%" ++ toString (sa.cs_next_var + 2)];
        mk_inst (sa.cs_next_id + 3) MSTORE
          [Var ("%" ++ toString (sa.cs_next_var + 2));
           Var ("%" ++ toString (sa.cs_next_var + 1))] [];
        mk_inst (sa.cs_next_id + 4) MLOAD
          [Var ("%" ++ toString sa.cs_next_var)]
          ["%" ++ toString (sa.cs_next_var + 3)]] |>)
Proof
  rpt strip_tac >>
  simp[exprLoweringTheory.lower_value_def, comp_bind_def,
       Once exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_call_def,
       exprLoweringTheory.compile_multi_vvs_def, comp_return_def,
       exprLoweringTheory.compile_stage_intcall_args_def, nsid_to_string_def,
       contextTheory.compile_alloc_buffer_def, emit_op_def, emit_multi_op_def,
       emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
       comp_ignore_bind_def, contextTheory.base_ptr_def,
       vyperASTTheory.expr_type_def] >>
  pure_rewrite_tac[numLib.num_CONV ``1``, fresh_vars_def] >>
  simp[comp_bind_def, comp_return_def, fresh_var_def,
       exprLoweringTheory.store_multi_results_def,
       emit_op_def, emit_void_def, fresh_id_def, emit_def,
       comp_ignore_bind_def, exprLoweringTheory.unwrap_value_def,
       contextTheory.mk_ptr_def, is_word_type_def,
       contextTheory.compile_ptr_load_def] >>
  rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
QED

(* C0.25 caller-boundary audit (not a simulation certificate).
   probe_word_shrink_lower_value needs only the function-info arity = 1;
   the buffer-size and stack flags are irrelevant for the empty argument list.
   The emitted label must additionally look up probe_word_function in ctx.
   Its value is internal_fn_label (cenv.ce_func_ids "shrink") "shrink"
      (cenv.ce_func_param_types "shrink") cenv.ce_is_ctor.

   Let A = s0.vs_alloca_next.  The caller first allocates 32 bytes, so the
   s supplied to probe_word_invoke is NOT s0: s.vs_alloca_next = A + 32.
   Its required headroom is consequently A + 160 <= dimword (:256).
   alloca_room includes pending_alloca_size plus reachable-function budget;
   stmt_state_rel therefore supplies a route, but the code-membership and
   reachability arithmetic yielding this concrete 160 bound is still unproved.
   setup_callee probe_word_function [] s = SOME cs and the emitted-label
   lookup also remain to be connected to that state.  The donor shape follows
   from probe_word_pre_shapes and storage_agree as in the accepted INVOKE
   summary, once the initial ALLOCA is transported through stmt_state_rel.

   Freshness is not a new semantic premise: all four writes use counters
   sa.cs_next_var + k, k = 0,1,2,3. local_ptrs_reserved_fresh proves each
   not_local_ptr from local_ptrs_reserved cenv sa. not_fresh_at_def excludes
   each from the old-register clause of expr_post. The INVOKE-only register
   equation is probe_word_invoke_caller_frame; frame transport through the
   ALLOCA, ADD, MSTORE and MLOAD is still required.

   Old allocation separation DOES have an invariant: stmt_state_rel includes
   alloca_inv, whose alloca_next_valid conjunct says
     FLOOKUP s0.vs_allocas aid = SOME (off,sz) ==> off + sz <= A.
   Thus old recorded regions miss BOTH caller buffer [A,A+32) and callee
   scratch [A+32,A+160). No extra nonlocal-region hypothesis is needed for
   this numeric separation. Applying the memory frame to all five caller
   instructions and preserving old allocation entries remains unproved;
   distinct instruction ids and pending ALLOCA membership must be used.
   probe_word_invoke_locals_kept and probe_word_invoke_stmt_state_summary
   cover only INVOKE, not the buffer setup and final load/store wrapper.

   expr_vv_case needs the prefix ending after MSTORE and a LocatedValue
   witness for the return buffer, whereas expr_sim_case needs all five
   instructions and the final MLOAD value. Neither universal judgment follows
   merely from this lowering equation or the conditional INVOKE summaries.
*)

Theorem probe_word_internal_label_mismatch:
  !fid tys ctor.
    internal_fn_label fid "shrink" tys ctor <>
      probe_word_function.fn_name
Proof
  simp[internal_fn_label_def, probe_word_function_def, mk_raw_function_def]
QED

Theorem probe_word_emitted_label_lookup_impossible:
  !fns fid tys ctor.
    lookup_function (internal_fn_label fid "shrink" tys ctor) fns <>
      SOME probe_word_function
Proof
  Induct_on `fns` >- simp[venomInstTheory.lookup_function_def, listTheory.FIND_thm] >>
  rpt gen_tac >>
  simp[venomInstTheory.lookup_function_def, listTheory.FIND_thm] >>
  IF_CASES_TAC >- (strip_tac >> gvs[probe_word_internal_label_mismatch]) >>
  gvs[venomInstTheory.lookup_function_def]
QED

Theorem setup_callee_blocks_cong:
  !f g args s. f.fn_blocks = g.fn_blocks ==>
    setup_callee f args s = setup_callee g args s
Proof
  simp[setup_callee_def]
QED

Theorem probe_word_renamed_lookup:
  !name.
    lookup_function name [probe_word_function with fn_name := name] =
      SOME (probe_word_function with fn_name := name)
Proof
  simp[venomInstTheory.lookup_function_def, listTheory.FIND_thm]
QED

Theorem probe_word_renamed_invoke:
  !name ctx ops s args cs fuel id out.
    lookup_function name ctx.ctx_functions =
      SOME (probe_word_function with fn_name := name) /\
    eval_operands ops s = SOME args /\
    s.vs_alloca_next + 128 <= dimword (:256) /\
    (sload 3w s = 0w \/ sload 3w s = 1w) /\
    setup_callee probe_word_function args s = SOME cs ==>
    step_inst ((if sload 3w s = 0w then 11 else 19) + fuel) ctx
      (mk_inst id INVOKE (Label name :: ops) [out]) s =
    OK (update_var out 0w
      (merge_callee_state s (probe_word_final_state cs)))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule probe_word_setup_observations >> strip_tac >>
  `sload 3w cs = sload 3w s` by simp[sload_def] >>
  `!n. run_blocks n ctx (probe_word_function with fn_name := name) cs =
        run_blocks n ctx probe_word_function cs` by
    (gen_tac >> irule venomExecProofsTheory.run_blocks_eq_from_run_block_eq >> simp[]) >>
  qspecl_then [`cs`, `fuel`, `ctx`] mp_tac probe_word_run_function >>
  simp[] >> strip_tac >>
  `setup_callee (probe_word_function with fn_name := name) args s = SOME cs` by
    (qpat_x_assum `setup_callee _ _ _ = SOME cs` mp_tac >>
     simp[setup_callee_def]) >>
  simp[Once step_inst_def, decode_invoke_def, bind_outputs_def, adopt_return_fmp_def]
QED


(* Consumer retest after name transport:
   Both expr_sim_case and expr_vv_case unfold to frag_exec with arbitrary
   env, ty, es, sa, s0; the former has the five-instruction lower_value
   fragment and expr_post, the latter compile_expr's four-instruction
   prefix and vv_post. The name constraint is now inhabited by the singleton
   in probe_word_renamed_lookup, and the state equation is unchanged in
   probe_word_renamed_invoke. setup exists by probe_word_setup_exists.

   Important remaining allocation branch: the earlier A+160 accounting is
   only for a fresh caller ALLOCA. exec_alloca_def explicitly reuses a
   recorded allocation if FLOOKUP s0.vs_allocas sa.cs_next_id = SOME (off,sz).
   Neither fn_inst_ids_distinct nor local_ptrs_reserved asserts this lookup
   is NONE. alloca_room_fresh requires inst.inst_id NOTIN FDOM s0.vs_allocas;
   its freshness premise has not been derived at these consumers. The
   existing-allocation branch must be handled rather than assuming a bump
   of 32 unconditionally. stmt_state_rel does force sz=32 for that recorded
   ALLOCA once membership in fn_insts func is established. Its separation
   from live local regions still needs the appropriate configuration/frame
   interface before the caller's MSTORE can establish locals_kept.
   These are residual integration obligations, not checked impossibility.
*)
