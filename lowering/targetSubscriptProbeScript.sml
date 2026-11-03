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
