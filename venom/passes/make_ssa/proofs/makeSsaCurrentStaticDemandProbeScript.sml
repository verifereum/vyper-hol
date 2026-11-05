(* Static-demand design probe. The bounded checks below are not closure. *)
Theory makeSsaCurrentStaticDemandProbe
Ancestors makeSsaCurrentHistoryProbe makeSsaCurrentSimDefs makeSsaCurrentDefs
  makeSsaCurrentCleanupRuntime venomExecSemantics venomState venomWf cfgWf
  unitShapeDefs o1PassContract list finite_map
  makeSsaCurrentSourceCuts makeSsaCurrentTokens

Theorem current_static_probe_admissible:
  !fn. fn = current_probe_loop \/ fn = history_probe_backedges ==>
    fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
    fn_phis_cover_preds fn /\ fn_phi_outputs_single_def fn /\
    fn_phis_non_degenerate fn /\ all_reachable fn /\ fn_inst_wf fn /\
    wf_function fn /\ first_block_no_preds fn /\ first_block_no_phi fn /\
    ir_supply_covers_fn history_probe_supply fn /\ ir_supply_inst_ok history_probe_supply
Proof
  metis_tac[history_probe_admissible, MEM]
QED

(* This re-placed PHI selects its own output on first arrival. Cleanup
   replaces it by a read of the retained original PHI's renamed output.
   Thus backwards demand transport must pass through the retained batch,
   not require the selected pre-cleanup self-name on the first arrival. *)
Theorem current_static_probe_selected_self:
  resolve_phi "E" [Label "E";Var "v";Label "D";Var "formal_var_0"] = SOME (Var "v") /\
  simplify_current_phi_prefix
    [current_probe_inst 10 PHI
       [Label "E";Var "v";Label "D";Var "formal_var_0"] ["v"];
     current_probe_inst 2 PHI
       [Label "E";Var "a";Label "D";Var "b"] ["formal_var_0"]] =
    [current_probe_inst 10 PHI
       [Label "E";Var "a";Label "D";Var "b"] ["formal_var_0"];
     current_probe_inst 2 ASSIGN [Var "formal_var_0"] ["v"]] /\
  (EL 1 (FST (make_ssa_current_fn current_probe_supply current_probe_loop)).fn_blocks).bb_instructions =
    [current_probe_inst 10 PHI [Label "E";Var "a";Label "D";Var "b"] ["formal_var_0"];
     current_probe_inst 2 ASSIGN [Var "formal_var_0"] ["v"];
     current_probe_inst 3 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 4 JNZ [Var "formal_var_0";Label "D";Label "X"] []]
Proof
  EVAL_TAC
QED

Theorem current_static_probe_first_and_return:
  !prev. prev = "E" \/ prev = "D" ==>
  ?post ready.
    eval_phis (history_probe_state [("a",1w);("b",2w)] prev "D")
      (EL 1 (FST (make_ssa_current_fn current_probe_supply current_probe_loop)).fn_blocks).bb_instructions = OK post /\
    current_copies_run
      [EL 1 (EL 1 (FST (make_ssa_current_fn current_probe_supply current_probe_loop)).fn_blocks).bb_instructions]
      post = OK ready /\ lookup_var "v" ready = SOME (if prev = "E" then 1w else 2w)
Proof
  rpt strip_tac >> gvs[] >> EVAL_TAC >> simp[FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]
QED

Theorem current_static_probe_surviving_insertion:
  !prev. prev = "E" \/ prev = "D" \/ prev = "S" ==>
  ?post. eval_phis
    (history_probe_state [("a",1w);("b",2w);("x",3w);
       ("formal_var_0",5w);("formal_var_2",4w)] prev "H")
    (EL 1 (FST (make_ssa_current_fn history_probe_supply history_probe_backedges)).fn_blocks).bb_instructions = OK post /\
    lookup_var "formal_var_0" post = SOME
      (if prev = "E" then 3w else if prev = "D" then 4w else 5w)
Proof
  rpt strip_tac >> gvs[] >> EVAL_TAC >> simp[FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]
QED

(* Candidate static interface, not a compiler-closure theorem.
   Cuts contain predecessor, block, source cursor and target cursor.  The
   target ordinary suffix has the same length as the source ordinary suffix;
   that alignment is a proof obligation, NOT a premise hidden in a seed table.
   The difference before this suffix is the actual sequential cleanup region. *)
Datatype:
  current_static_cut = CurrentStaticCut string string num num
End

Datatype:
  current_static_expr = CurrentStaticRead operand | CurrentStaticProduced num
End

Definition current_static_body_start_def:
  current_static_body_start old out =
    LENGTH out - (LENGTH old - phi_prefix_length old)
End

(* A PHI batch substitutes from the incoming snapshot, never from another
   substitution's result. A missing selector remains NONE (a static blocker). *)
Definition current_static_phi_subst_def:
  current_static_phi_subst p phis op =
    case op of
      Var v => (case ALOOKUP
        (MAP (\j. (HD j.inst_outputs, resolve_phi p j.inst_operands)) phis) v of
          NONE => SOME (CurrentStaticRead op)
        | SOME selected => OPTION_MAP CurrentStaticRead selected)
    | _ => SOME (CurrentStaticRead op)
End

Definition current_static_inst_subst_def:
  current_static_inst_subst inst op =
    case op of
      Var v => (case ALOOKUP (ZIP (inst.inst_outputs,
                      GENLIST I (LENGTH inst.inst_outputs))) v of
          NONE => CurrentStaticRead op
        | SOME k => CurrentStaticProduced k)
    | _ => CurrentStaticRead op
End

Definition current_static_copy_subst_def:
  current_static_copy_subst inst op =
    if inst.inst_opcode = ASSIGN then
      case op of
        Var v => if MEM v inst.inst_outputs then
          (case inst.inst_operands of [rhs] => SOME (CurrentStaticRead rhs) | _ => NONE)
          else SOME (CurrentStaticRead op)
      | _ => SOME (CurrentStaticRead op)
    else if inst.inst_opcode = NOP then SOME (CurrentStaticRead op) else NONE
End

(* These edges are extracted from fn/fn', not supplied by a caller.  kind=0
   is simultaneous dispatch; kind=1 cleanup; kind=2 paired ordinary code;
   kind=3 CFG transfer. The ordinary equations are syntactic candidates only. *)
Definition current_static_edge_def:
  current_static_edge fn fn' c d kind <=>
    (?p h old out. lookup_block h fn.fn_blocks = SOME old /\
      lookup_block h fn'.fn_blocks = SOME out /\
      c = CurrentStaticCut p h 0 0 /\
      d = CurrentStaticCut p h (phi_prefix_length old.bb_instructions)
                                (phi_prefix_length out.bb_instructions) /\ kind = 0) \/
    (?p h old out j. lookup_block h fn.fn_blocks = SOME old /\
      lookup_block h fn'.fn_blocks = SOME out /\
      phi_prefix_length out.bb_instructions <= j /\
      j < current_static_body_start old.bb_instructions out.bb_instructions /\
      c = CurrentStaticCut p h (phi_prefix_length old.bb_instructions) j /\
      d = CurrentStaticCut p h (phi_prefix_length old.bb_instructions) (SUC j) /\ kind = 1) \/
    (?p h old out i j. lookup_block h fn.fn_blocks = SOME old /\
      lookup_block h fn'.fn_blocks = SOME out /\
      phi_prefix_length old.bb_instructions <= i /\ i < LENGTH old.bb_instructions /\
      j = current_static_body_start old.bb_instructions out.bb_instructions +
          (i - phi_prefix_length old.bb_instructions) /\ j < LENGTH out.bb_instructions /\
      c = CurrentStaticCut p h i j /\ d = CurrentStaticCut p h (SUC i) (SUC j) /\ kind = 2) \/
    (?p h q old out. lookup_block h fn.fn_blocks = SOME old /\
      lookup_block h fn'.fn_blocks = SOME out /\ fn_cfg_edge fn h q /\
      c = CurrentStaticCut p h (LENGTH old.bb_instructions) (LENGTH out.bb_instructions) /\
      d = CurrentStaticCut h q 0 0 /\ kind = 3)
End

(* Inverse substitution returns expressions, including paired production
   markers. Equal production markers discharge a demand at this step;
   unequal markers or NONE must be excluded by the eventual static theorem. *)
Definition current_static_back_def:
  current_static_back fn fn' c kind x y a b <=>
    ?p h i j old out. c = CurrentStaticCut p h i j /\
      lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
      ((kind = 0 /\
        current_static_phi_subst p
          (TAKE (phi_prefix_length old.bb_instructions) old.bb_instructions) x = SOME a /\
        current_static_phi_subst p
          (TAKE (phi_prefix_length out.bb_instructions) out.bb_instructions) y = SOME b) \/
       (kind = 1 /\ a = CurrentStaticRead x /\
        current_static_copy_subst (EL j out.bb_instructions) y = SOME b) \/
       (kind = 2 /\ a = current_static_inst_subst (EL i old.bb_instructions) x /\
                    b = current_static_inst_subst (EL j out.bb_instructions) y) \/
       (kind = 3 /\ a = CurrentStaticRead x /\ b = CurrentStaticRead y))
End

(* Copy ownership uses certificate provenance, not the spelling of its read.
   This is crucial when the inserted PHI selected its own spelling. *)
Definition current_static_owner_def:
  current_static_owner fn H h n v <=>
    (current_actual_inserted fn v h /\ current_token_name H (CurrentInserted v h) = SOME n) \/
    (?old i k. lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
      k < LENGTH (EL i old.bb_instructions).inst_outputs /\
      EL k (EL i old.bb_instructions).inst_outputs = v /\
      current_token_name H (CurrentOriginal h i k) = SOME n)
End

Definition current_static_seed_def:
  current_static_seed fn fn' H c x y <=>
    (?d. current_static_edge fn fn' c d 2 /\
      ?p h i j old out. c = CurrentStaticCut p h i j /\
        lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
        MEM (x,y) (ZIP ((EL i old.bb_instructions).inst_operands,
                       (EL j out.bb_instructions).inst_operands))) \/
    (?d p h i j out n v. current_static_edge fn fn' c d 1 /\
      c = CurrentStaticCut p h i j /\ lookup_block h fn'.fn_blocks = SOME out /\
      (EL j out.bb_instructions).inst_opcode = ASSIGN /\
      (EL j out.bb_instructions).inst_outputs = [n] /\
      (EL j out.bb_instructions).inst_operands = [y] /\
      current_static_owner fn H h n v /\ x = Var v) \/
    (?p h old out inst n v. c = CurrentStaticCut p h 0 0 /\
      lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
      MEM inst (TAKE (phi_prefix_length out.bb_instructions) out.bb_instructions) /\
      inst.inst_outputs = [n] /\ resolve_phi p inst.inst_operands = SOME y /\
      ((current_actual_inserted fn v h /\
        current_token_name H (CurrentInserted v h) = SOME n /\ x = Var v) \/
       (?i. i < phi_prefix_length old.bb_instructions /\
        current_token_name H (CurrentOriginal h i 0) = SOME n /\
        resolve_phi p (EL i old.bb_instructions).inst_operands = SOME x)))
End

Inductive current_static_demand:
  (!fn fn' H c x y. current_static_seed fn fn' H c x y ==>
    current_static_demand fn fn' H c x y) /\
  (!fn fn' H c d kind x y u v.
    current_static_demand fn fn' H d x y /\ current_static_edge fn fn' c d kind /\
    current_static_back fn fn' c kind x y (CurrentStaticRead u) (CurrentStaticRead v) ==>
    current_static_demand fn fn' H c u v)
End

(* Certificate-indexed demands. No executions, replays, or agreement occur
   in this definition. The guard is the actual compiler certificate. *)
Definition current_certificate_static_demand_def:
  current_certificate_static_demand s fn fn' s' A H events c x y <=>
    current_structural_certificate s fn fn' s' A H events /\
    current_static_demand fn fn' H c x y
End

(* Exact outstanding totality/producer-compatibility obligation. It is a
   proposition to be proved from the frozen premises and certificate, not an
   assumption of any simulation theorem in this probe. *)
Definition current_static_transfer_safe_def:
  current_static_transfer_safe fn fn' H <=>
    !c d kind x y. current_static_edge fn fn' c d kind /\
      current_static_demand fn fn' H d x y ==>
      ?a b. current_static_back fn fn' c kind x y a b /\
        ((?u v. a = CurrentStaticRead u /\ b = CurrentStaticRead v) \/
         (?k. a = CurrentStaticProduced k /\ b = CurrentStaticProduced k))
End

Theorem current_static_probe_copy_pullback:
  current_static_copy_subst
    (current_probe_inst 2 ASSIGN [Var "formal_var_0"] ["v"]) (Var "v") =
      SOME (CurrentStaticRead (Var "formal_var_0")) /\
  (!p. p = "E" \/ p = "D" ==>
    current_static_phi_subst p
      [current_probe_inst 2 PHI [Label "E";Var "a";Label "D";Var "b"] ["v"]]
      (Var "v") = SOME (CurrentStaticRead (Var (if p = "E" then "a" else "b"))) /\
    current_static_phi_subst p
      [current_probe_inst 10 PHI [Label "E";Var "a";Label "D";Var "b"] ["formal_var_0"]]
      (Var "formal_var_0") =
        SOME (CurrentStaticRead (Var (if p = "E" then "a" else "b"))))
Proof
  conj_tac >- EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem current_static_probe_ordinary_pullback:
  current_static_inst_subst (current_probe_inst 0 ASSIGN [Lit 1w] ["x"]) (Var "x") =
    CurrentStaticProduced 0 /\
  current_static_inst_subst (current_probe_inst 0 ASSIGN [Lit 1w] ["fresh"]) (Var "fresh") =
    CurrentStaticProduced 0 /\
  current_static_inst_subst (current_probe_inst 0 ASSIGN [Lit 1w] ["x"]) (Var "live") =
    CurrentStaticRead (Var "live") /\
  current_static_inst_subst (current_probe_inst 0 ASSIGN [Lit 1w] ["fresh"]) (Var "live'") =
    CurrentStaticRead (Var "live'")
Proof
  EVAL_TAC
QED

(* Source-grounded case table / explicit proof gaps:

   Phase             Existing checked boundary                     Still missing
   -----             -------------------------                     -------------
   Retained PHI      current_certificate_leading_slot (original);   Static closure for
                     current_certificate_mixed_batch_ready          all outgoing pairs,
                     consumes permanent singleton agreement.        not just singletons.
   Surviving insert  current_certificate_leading_slot (inserted);   Derive its (v,selected
                     current_certificate_mixed_dispatch_continue    predecessor name) seed
                     lines 116-120 explicitly ASSUMES the read       and defined source v
                     agreement and definedness.                     from earlier producers.
   Retained->copy    current_actual_retained_copy_ready;             Transport v/retained
                     current_static_probe_copy_pullback checks      output across parallel
                     both E first arrival and D return.             batch and intervening
                                                                    copies, for ALL pairs.
   Other copy       current_certificate_reinserted_next_ready        Static nonclobber / prior
                     is conditional on cleanup segment readiness.   producer for its read.
   Ordinary write   current_static_inst_subst gives matching         Prove every demanded
                     output-position markers or unchanged reads.    pair avoids a one-sided
                                                                    write or unequal markers.
   Live-through     current_actual_demanded_cut_tokens requires      Demand closure includes
                     no insertion and phi-cut-clear;                 copy reads not covered
                     current_live_post_phi_unwritten_edge_demand     by ordinary liveness.
                     covers unwritten live post-PHI edge demand.     Connect these domains.
   Root producer    current_certificate_rooted_inserted_origin;     No dynamic completion
                     current_certificate_rooted_definition_nondefault statement follows from
                     invert tokens under their own liveness /       static token equality.
                     non-PHI-operand restrictions.                   Source-driven induction
                                                                    must supply completion.

   Smallest next static implication is current_static_transfer_safe for
   certificate-extracted demands at admissible cuts (p must be a CFG
   predecessor, except at entry). It excludes NONE selectors and mismatched
   production markers. The definition above deliberately quantifies all cuts;
   restricting to statically reachable admissible cuts is likely necessary.
   In addition, ordinary operand/output lengths and instruction alignment
   must be established, since ZIP itself silently truncates.

   Entry equality alone is insufficient for copy readiness: two missing
   variables can agree. Required extra fact: each target-only read seed has
   a source variable with a preceding source definition on EVERY path to
   that cut. At a retained PHI this definition is the completed source batch;
   for a surviving insert it must come from a predecessor source producer.
   No runtime premise has been added to manufacture that fact.

   The concrete selected-self case needs no header epoch in its local inverse
   substitution: the actual cleaned copy reads formal_var_0, not the selected
   precleanup self-name v. This does NOT establish that pair closure suffices
   on all loops, nor that the candidate totality/entry/definedness obligations
   follow from the frozen premises. This probe claims no global closure.
*)
