(* Relation-level probes only: not a counterexample to target_case. *)
Theory targetSubscriptProbe
Ancestors
  compileEnv vyperStoragePlaceRegion vyperStorageLayoutSafety vfmState
  words finite_map combin vyperValue targetSubscriptSim
  emitHelperProps emitHelper exprLoweringProps venomExecSemantics venomState venomInst
  fragExec vyperInterpreter vyperContext vyperState vyperStorageBackend exprSimHyps

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
