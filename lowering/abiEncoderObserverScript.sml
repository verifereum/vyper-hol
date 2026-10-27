(* Observation interface for extracting execution from continuation simulation.
   STOP hides haltedness and return data, but retains the encoder observations. *)
Theory abiEncoderObserver
Ancestors
  abiDecoderLoop fragExec venomState venomExecSemantics venomExecProofs emitHelper venomInst

Definition stop_view_def:
  stop_view s = halt_state (s with vs_returndata := [])
End

Theorem stop_view_fields:
  stop_view s = stop_view t ==>
  s.vs_memory = t.vs_memory /\ s.vs_vars = t.vs_vars /\
  s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_logs = t.vs_logs /\ s.vs_requests = t.vs_requests /\
  s.vs_labels = t.vs_labels
Proof
  simp[stop_view_def, halt_state_def, venom_state_component_equality]
QED

Theorem stop_view_operand:
  stop_view s = stop_view t ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule stop_view_fields >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem run_from_stop_view:
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id STOP [] []) ==>
  run_from 0 ctx fn t = Halt (stop_view t)
Proof
  strip_tac >> rewrite_tac[stop_view_def] >> irule run_from_halt >>
  qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
  simp[Once step_inst_base_def, mk_inst_def]
QED

Theorem abi_decode_sim_stop_run:
  abi_decode_sim ctx fn s t /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id STOP [] []) ==>
  ?fuel. run_from fuel ctx fn s = Halt (stop_view t)
Proof
  strip_tac >> drule_all run_from_stop_view >> strip_tac >>
  fs[abi_decode_sim_def] >>
  qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >> simp[]
QED

(* A cut is a block label and instruction index. A transition executes one
   non-INVOKE instruction, resolving parallel PHIs on terminator entry. *)
Definition abi_observer_step_def:
  abi_observer_step ctx fn cut s t <=>
    (s.vs_current_bb,s.vs_inst_idx) <> cut /\ ~s.vs_halted /\ ~t.vs_halted /\
    ?bb inst middle.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      inst.inst_opcode <> INVOKE /\ step_inst 0 ctx inst s = OK middle /\
      ((~is_terminator inst.inst_opcode /\
        t = middle with vs_inst_idx := SUC s.vs_inst_idx) \/
       (is_terminator inst.inst_opcode /\ ~middle.vs_halted /\
        ?target entered.
          lookup_block middle.vs_current_bb fn.fn_blocks = SOME target /\
          eval_phis middle target.bb_instructions = OK entered /\
          t = entered with vs_inst_idx := phi_prefix_length target.bb_instructions))
End

Inductive local_prefix:
  (!ctx fn cut s. ~s.vs_halted /\
    (s.vs_current_bb,s.vs_inst_idx) = cut ==> local_prefix ctx fn cut s s) /\
  (!ctx fn cut s middle t.
    abi_observer_step ctx fn cut s middle /\ local_prefix ctx fn cut middle t ==>
    local_prefix ctx fn cut s t)
End

Theorem abi_observer_step_sim:
  abi_observer_step ctx fn cut s t ==> abi_decode_sim ctx fn s t
Proof
  rw[abi_observer_step_def] >>
  gvs[step_inst_non_invoke]
  >- (simp[abi_decode_sim_def] >> rpt strip_tac >>
      qexists_tac `fuel` >> drule_all run_from_step >> simp[]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  simp[abi_decode_sim_def] >> rpt strip_tac >> qexists_tac `SUC fuel` >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke,
    Once run_blocks_def] >>
  gvs[run_from_def]
QED

Theorem local_prefix_sim:
  local_prefix ctx fn cut s t ==> abi_decode_sim ctx fn s t
Proof
  Induct_on `local_prefix` >> rpt strip_tac
  >- simp[abi_decode_sim_refl] >>
  drule abi_observer_step_sim >> strip_tac >>
  drule_all abi_decode_sim_trans >> simp[]
QED

(* Only the PHI prefix is consulted on entry. Instruction agreement below
   is currently global away from the cut; a region-aware adapter is still needed
   before arbitrary containing-function suffixes can be transported. *)
Theorem eval_phis_prefix:
  eval_phis s (TAKE (phi_prefix_length xs) xs) = eval_phis s xs
Proof
  Induct_on `xs` >> simp[phi_prefix_length_def, eval_phis_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def, eval_phis_def]
QED

Definition prefix_code_agrees_def:
  prefix_code_agrees fn fn' cut <=>
    (!lbl idx bb inst.
      (lbl,idx) <> cut /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb idx = SOME inst ==>
      ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
            get_instruction bb' idx = SOME inst) /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
        phi_prefix_length bb'.bb_instructions =
          phi_prefix_length bb.bb_instructions /\
        TAKE (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions =
          TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
End

Theorem abi_observer_step_transfer:
  prefix_code_agrees fn fn' cut /\ abi_observer_step ctx fn cut s t ==>
  abi_observer_step ctx fn' cut s t
Proof
  rw[abi_observer_step_def, prefix_code_agrees_def] >>
  qpat_assum `!lbl idx bb inst. _` (drule_all_then strip_assume_tac) >>
  simp[] >>
  qpat_x_assum `!lbl bb. _`
    (qspec_then `middle.vs_current_bb` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `lookup_block middle.vs_current_bb fn'.fn_blocks = SOME target'` >>
  qexistsl_tac [`target'`, `entered`] >>
  simp[] >>
  once_rewrite_tac[GSYM eval_phis_prefix] >>
  asm_rewrite_tac[] >> simp[eval_phis_prefix]
QED

Theorem local_prefix_transfer:
  local_prefix ctx fn cut s t ==>
  !fn'. prefix_code_agrees fn fn' cut ==> local_prefix ctx fn' cut s t
Proof
  Induct_on `local_prefix` >> rpt strip_tac
  >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
  rename1 `abi_observer_step ctx fn cut s middle` >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `middle` >> conj_tac
  >- (irule abi_observer_step_transfer >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Definition observer_closed_def:
  observer_closed fn cut <=>
    (!bb idx. lookup_block (FST cut) fn.fn_blocks = SOME bb /\
       idx = SND cut ==>
       ?id. get_instruction bb idx = SOME (mk_inst id STOP [] [])) /\
    (!lbl idx bb inst. (lbl,idx) <> cut /\
       lookup_block lbl fn.fn_blocks = SOME bb /\
       get_instruction bb idx = SOME inst ==>
       inst.inst_opcode <> INVOKE /\
       (!s h. step_inst_base inst s <> Halt h) /\
       (!s middle. step_inst_base inst s = OK middle ==> ~middle.vs_halted))
End

Theorem observer_run_prefix_aux:
  !fuel n s bb h.
    observer_closed fn cut /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    run_from fuel ctx fn s = Halt h ==>
    ?u. local_prefix ctx fn cut s u /\ stop_view u = h
Proof
  completeInduct_on `fuel` >> completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) = cut`
  >- (qexists_tac `s` >> conj_tac
      >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
      qpat_x_assum `observer_closed fn cut`
        (strip_assume_tac o REWRITE_RULE[observer_closed_def]) >>
      qpat_x_assum `!bb idx. _` (qspecl_then [`bb`, `s.vs_inst_idx`] mp_tac) >>
      impl_tac >- (Cases_on `cut` >> gvs[]) >> strip_tac >>
      `run_from fuel ctx fn s = Halt (stop_view s)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[Once step_inst_base_def, mk_inst_def]) >> gvs[]) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
      simp[Once run_from_def, Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE /\
    (!s h. step_inst_base inst s <> Halt h) /\
    (!s middle. step_inst_base inst s = OK middle ==> ~middle.vs_halted)` by
      metis_tac[observer_closed_def] >>
  Cases_on `step_inst_base inst s` >>
  qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  strip_tac >> gvs[] >>
  rename1 `step_inst_base inst s = OK middle` >>
  `~middle.vs_halted` by metis_tac[] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- suspend "jump" >>
  `middle.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  qpat_x_assum `!m. m < LENGTH _ - _ ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `h`] mp_tac) >>
  simp[] >>
  impl_tac >- gvs[run_from_def] >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `middle with vs_inst_idx := SUC s.vs_inst_idx` >> simp[] >>
  simp[abi_observer_step_def, step_inst_non_invoke] >>
  metis_tac[]
QED

Resume observer_run_prefix_aux[jump]:
  gvs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def] >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block middle.vs_current_bb fn.fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac >>
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  qpat_x_assum `!m. m < SUC n ==> _` (qspec_then `n` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`entered with vs_inst_idx := phi_prefix_length target.bb_instructions`,
     `target`, `h`] mp_tac) >>
  simp[] >> impl_tac >- gvs[run_from_def] >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `entered with vs_inst_idx := phi_prefix_length target.bb_instructions` >>
  simp[] >> simp[abi_observer_step_def, step_inst_non_invoke] >>
  qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]
QED

Finalise observer_run_prefix_aux

Theorem observer_run_prefix:
  observer_closed fn cut /\ ~s.vs_halted /\
  run_from fuel ctx fn s = Halt h ==>
  ?u. local_prefix ctx fn cut s u /\ stop_view u = h
Proof
  rpt strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- gvs[run_from_def] >>
  irule observer_run_prefix_aux >> metis_tac[]
QED

Theorem observer_same_block_probe:
  ~s.vs_halted /\ s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 ==>
  local_prefix ctx
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 SETFMP [Lit 7w] []; mk_inst 1 STOP [] []]|>])
    ("entry",1) s (s with <|vs_fmp := 7w; vs_inst_idx := 1|>)
Proof
  strip_tac >> irule (cj 2 local_prefix_rules) >>
  qexists_tac `s with <|vs_fmp := 7w; vs_inst_idx := 1|>` >> conj_tac
  >- (simp[abi_observer_step_def, lookup_block_def, get_instruction_def, listTheory.FIND_thm] >>
      qexists_tac `s with vs_fmp := 7w` >>
      simp[step_inst_non_invoke, Once step_inst_base_def, mk_inst_def,
           eval_operand_def, is_terminator_def]) >>
  irule (cj 1 local_prefix_rules) >> simp[]
QED

Theorem observer_jump_phi_probe:
  ~s.vs_halted /\ s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 ==>
  local_prefix ctx
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JMP [Label "exit"] []]|>;
       <|bb_label := "exit"; bb_instructions :=
        [mk_inst 1 PHI [Label "entry"; Lit 7w] ["x"];
         mk_inst 2 STOP [] []]|>])
    ("exit",1) s
    ((update_var "x" 7w (jump_to "exit" s)) with vs_inst_idx := 1)
Proof
  strip_tac >> irule (cj 2 local_prefix_rules) >>
  qexists_tac `(update_var "x" 7w (jump_to "exit" s)) with vs_inst_idx := 1` >>
  conj_tac
  >- (simp[abi_observer_step_def, lookup_block_def, get_instruction_def,
           listTheory.FIND_thm] >>
      conj_tac >- simp[update_var_def, jump_to_def] >>
      qexists_tac `jump_to "exit" s` >>
      simp[step_inst_non_invoke, Once step_inst_base_def, mk_inst_def,
           is_terminator_def, jump_to_def, update_var_def,
           listTheory.FIND_thm, eval_phis_def, eval_one_phi_def,
           resolve_phi_def, eval_operand_def, phi_prefix_length_def]) >>
  irule (cj 1 local_prefix_rules) >> simp[jump_to_def, update_var_def]
QED

Definition observer_region_closed_def:
  observer_region_closed ctx fn cut R <=>
    !s t. abi_observer_step ctx fn cut s t /\
      (s.vs_current_bb,s.vs_inst_idx) IN R ==>
      (t.vs_current_bb,t.vs_inst_idx) IN R
End

Definition region_code_agrees_def:
  region_code_agrees fn fn' cut R <=>
    (!lbl idx bb inst.
      (lbl,idx) IN R /\ (lbl,idx) <> cut /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb idx = SOME inst ==>
      ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
            get_instruction bb' idx = SOME inst) /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb /\
       (lbl,phi_prefix_length bb.bb_instructions) IN R ==>
      ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
        phi_prefix_length bb'.bb_instructions =
          phi_prefix_length bb.bb_instructions /\
        TAKE (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions =
          TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
End

Theorem abi_observer_step_region_transfer:
  abi_observer_step ctx fn cut s t /\
  (s.vs_current_bb,s.vs_inst_idx) IN R /\
  (t.vs_current_bb,t.vs_inst_idx) IN R /\
  region_code_agrees fn fn' cut R ==>
  abi_observer_step ctx fn' cut s t
Proof
  rw[abi_observer_step_def, region_code_agrees_def] >>
  qpat_assum `!lbl idx bb inst. _` (drule_all_then strip_assume_tac) >>
  simp[] >>
  drule eval_phis_preserves_current_bb >> strip_tac >> fs[] >>
  qpat_x_assum `!lbl bb. _`
    (qspec_then `middle.vs_current_bb` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `lookup_block middle.vs_current_bb fn'.fn_blocks = SOME target'` >>
  qexistsl_tac [`target'`, `entered`] >> simp[] >>
  once_rewrite_tac[GSYM eval_phis_prefix] >>
  asm_rewrite_tac[] >> simp[eval_phis_prefix]
QED

Theorem local_prefix_region_transfer:
  local_prefix ctx fn cut s t ==>
  !R fn'. (s.vs_current_bb,s.vs_inst_idx) IN R /\
    observer_region_closed ctx fn cut R /\
    region_code_agrees fn fn' cut R ==> local_prefix ctx fn' cut s t
Proof
  Induct_on `local_prefix` >> rpt strip_tac
  >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
  rename1 `abi_observer_step ctx fn cut s middle` >>
  `(middle.vs_current_bb,middle.vs_inst_idx) IN R` by
    metis_tac[observer_region_closed_def] >>
  irule (cj 2 local_prefix_rules) >> qexists_tac `middle` >> conj_tac
  >- (irule abi_observer_step_region_transfer >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem observer_run_prefix_transfer:
  observer_closed fn cut /\ ~s.vs_halted /\
  run_from fuel ctx fn s = Halt h /\
  (s.vs_current_bb,s.vs_inst_idx) IN R /\
  observer_region_closed ctx fn cut R /\
  region_code_agrees fn fn' cut R ==>
  ?u. local_prefix ctx fn' cut s u /\ stop_view u = h
Proof
  strip_tac >> drule_all observer_run_prefix >> strip_tac >>
  qexists_tac `u` >> simp[] >> irule local_prefix_region_transfer >> metis_tac[]
QED

Theorem observer_same_block_region_closed:
  observer_region_closed ctx
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 SETFMP [Lit 7w] []; mk_inst 1 STOP [] []]|>])
    ("entry",1) {("entry",0); ("entry",1)}
Proof
  rw[observer_region_closed_def, abi_observer_step_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def] >>
  gvs[step_inst_non_invoke, Once step_inst_base_def, mk_inst_def,
      is_terminator_def, eval_operand_def]
QED

Theorem observer_same_block_region_agrees:
  region_code_agrees
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 SETFMP [Lit 7w] []; mk_inst 1 STOP [] []]|>])
    (fn' with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        mk_inst 0 SETFMP [Lit 7w] [] :: suffix|>])
    ("entry",1) {("entry",0); ("entry",1)}
Proof
  rw[region_code_agrees_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def,
      phi_prefix_length_def, mk_inst_def]
QED

Theorem observer_same_block_suffix_transfer:
  ~s.vs_halted /\ s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 ==>
  local_prefix ctx
    (fn' with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        mk_inst 0 SETFMP [Lit 7w] [] :: suffix|>])
    ("entry",1) s (s with <|vs_fmp := 7w; vs_inst_idx := 1|>)
Proof
  strip_tac >> drule_all observer_same_block_probe >> strip_tac >>
  irule local_prefix_region_transfer >>
  qexists_tac `{("entry",0); ("entry",1)}` >>
  qexists_tac `fn with fn_blocks :=
    [<|bb_label := "entry"; bb_instructions :=
      [mk_inst 0 SETFMP [Lit 7w] []; mk_inst 1 STOP [] []]|>]` >>
  simp[observer_same_block_region_closed, observer_same_block_region_agrees]
QED

Theorem observer_jump_phi_region_closed:
  observer_region_closed ctx
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JMP [Label "exit"] []]|>;
       <|bb_label := "exit"; bb_instructions :=
        [mk_inst 1 PHI [Label "entry"; Lit 7w] ["x"];
         mk_inst 2 STOP [] []]|>])
    ("exit",1) {("entry",0); ("exit",1)}
Proof
  rw[observer_region_closed_def, abi_observer_step_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def] >>
  gvs[step_inst_non_invoke, Once step_inst_base_def, mk_inst_def,
      is_terminator_def, jump_to_def, listTheory.FIND_thm,
      eval_phis_def, eval_one_phi_def, resolve_phi_def,
      eval_operand_def, update_var_def, phi_prefix_length_def]
QED

Theorem observer_jump_phi_region_agrees:
  phi_prefix_length suffix = 0 ==>
  region_code_agrees
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JMP [Label "exit"] []]|>;
       <|bb_label := "exit"; bb_instructions :=
        [mk_inst 1 PHI [Label "entry"; Lit 7w] ["x"];
         mk_inst 2 STOP [] []]|>])
    (fn' with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JMP [Label "exit"] []]|>;
       <|bb_label := "exit"; bb_instructions :=
        mk_inst 1 PHI [Label "entry"; Lit 7w] ["x"] :: suffix|>])
    ("exit",1) {("entry",0); ("exit",1)}
Proof
  strip_tac >> rw[region_code_agrees_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def,
      phi_prefix_length_def, mk_inst_def]
QED

Theorem observer_jump_phi_suffix_transfer:
  ~s.vs_halted /\ s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 /\
  phi_prefix_length suffix = 0 ==>
  local_prefix ctx
    (fn' with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JMP [Label "exit"] []]|>;
       <|bb_label := "exit"; bb_instructions :=
        mk_inst 1 PHI [Label "entry"; Lit 7w] ["x"] :: suffix|>])
    ("exit",1) s
    ((update_var "x" 7w (jump_to "exit" s)) with vs_inst_idx := 1)
Proof
  strip_tac >> drule_all observer_jump_phi_probe >> strip_tac >>
  irule local_prefix_region_transfer >>
  qexists_tac `{("entry",0); ("exit",1)}` >>
  qexists_tac `fn with fn_blocks :=
    [<|bb_label := "entry"; bb_instructions :=
      [mk_inst 0 JMP [Label "exit"] []]|>;
     <|bb_label := "exit"; bb_instructions :=
      [mk_inst 1 PHI [Label "entry"; Lit 7w] ["x"]; mk_inst 2 STOP [] []]|>]` >>
  simp[observer_jump_phi_region_closed, observer_jump_phi_region_agrees]
QED

(* Safety is an invariant of reachable, nonhalted inputs, not of arbitrary
   states. Old instructions outside R impose no opcode restriction. *)
Definition observer_region_safe_def:
  observer_region_safe fn cut R <=>
    (!bb. lookup_block (FST cut) fn.fn_blocks = SOME bb ==>
       ?id. get_instruction bb (SND cut) = SOME (mk_inst id STOP [] [])) /\
    (!lbl idx bb inst.
      (lbl,idx) IN R /\ (lbl,idx) <> cut /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb idx = SOME inst ==>
      inst.inst_opcode <> INVOKE /\
      (!s h. ~s.vs_halted ==> step_inst_base inst s <> Halt h) /\
      (!s middle. ~s.vs_halted /\ step_inst_base inst s = OK middle ==>
         ~middle.vs_halted))
End

Theorem observer_setfmp_halted_probe:
  step_inst_base (mk_inst 0 SETFMP [Lit 7w] []) (s with vs_halted := T) =
  OK (s with <|vs_halted := T; vs_fmp := 7w|>)
Proof
  simp[Once step_inst_base_def, mk_inst_def, eval_operand_def]
QED

Theorem observer_same_block_not_closed:
  ~observer_closed
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 SETFMP [Lit 7w] []; mk_inst 1 STOP [] []]|>])
    ("entry",1)
Proof
  strip_tac >> fs[observer_closed_def] >>
  qpat_x_assum `!lbl idx bb inst. _`
    (qspecl_then [`"entry"`, `0`] mp_tac) >>
  simp[lookup_block_def, listTheory.FIND_thm, get_instruction_def] >>
  disj2_tac >> qexists_tac `ARB with vs_halted := T` >>
  simp[Once step_inst_base_def, mk_inst_def, eval_operand_def]
QED

Theorem observer_same_block_region_safe:
  observer_region_safe
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 SETFMP [Lit 7w] []; mk_inst 1 STOP [] []]|>])
    ("entry",1) {("entry",0); ("entry",1)}
Proof
  rw[observer_region_safe_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def] >>
  simp[Once step_inst_base_def, mk_inst_def, eval_operand_def] >>
  rpt strip_tac >> gvs[Once step_inst_base_def, mk_inst_def, eval_operand_def]
QED

Theorem observer_jump_phi_region_safe:
  observer_region_safe
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JMP [Label "exit"] []]|>;
       <|bb_label := "exit"; bb_instructions :=
        [mk_inst 1 PHI [Label "entry"; Lit 7w] ["x"];
         mk_inst 2 STOP [] []]|>])
    ("exit",1) {("entry",0); ("exit",1)}
Proof
  rw[observer_region_safe_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def] >>
  simp[Once step_inst_base_def, mk_inst_def, jump_to_def] >>
  rpt strip_tac >> gvs[Once step_inst_base_def, mk_inst_def, jump_to_def]
QED

Theorem observer_old_prefix_region_safe:
  observer_region_safe
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [old; mk_inst 0 SETFMP [Lit 7w] []; mk_inst 1 STOP [] []]|>])
    ("entry",2) {("entry",1); ("entry",2)}
Proof
  rw[observer_region_safe_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def] >>
  simp[Once step_inst_base_def, mk_inst_def, eval_operand_def] >>
  rpt strip_tac >> gvs[Once step_inst_base_def, mk_inst_def, eval_operand_def]
QED

Theorem observer_old_prefix_region_closed:
  observer_region_closed ctx
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [old; mk_inst 0 SETFMP [Lit 7w] []; mk_inst 1 STOP [] []]|>])
    ("entry",2) {("entry",1); ("entry",2)}
Proof
  rw[observer_region_closed_def, abi_observer_step_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def] >>
  gvs[step_inst_non_invoke, Once step_inst_base_def, mk_inst_def,
      is_terminator_def, eval_operand_def]
QED

Theorem observer_old_stop_or_invoke_not_closed:
  old = mk_inst 9 STOP [] [] \/ old.inst_opcode = INVOKE ==>
  ~observer_closed
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [old; mk_inst 0 SETFMP [Lit 7w] []; mk_inst 1 STOP [] []]|>])
    ("entry",2)
Proof
  rpt strip_tac >> fs[observer_closed_def] >>
  qpat_x_assum `!lbl idx bb inst. _`
    (qspecl_then [`"entry"`, `0`] mp_tac) >>
  simp[lookup_block_def, listTheory.FIND_thm, get_instruction_def] >>
  gvs[mk_inst_def] >>
  simp[Once step_inst_base_def]
QED

Theorem observer_old_stop_prefix_probe:
  observer_region_safe
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 9 STOP [] []; mk_inst 0 SETFMP [Lit 7w] [];
         mk_inst 1 STOP [] []]|>])
    ("entry",2) {("entry",1); ("entry",2)} /\
  observer_region_closed ctx
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 9 STOP [] []; mk_inst 0 SETFMP [Lit 7w] [];
         mk_inst 1 STOP [] []]|>])
    ("entry",2) {("entry",1); ("entry",2)}
Proof
  simp[observer_old_prefix_region_safe, observer_old_prefix_region_closed]
QED

Theorem observer_old_invoke_prefix_probe:
  observer_region_safe
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 9 INVOKE [] []; mk_inst 0 SETFMP [Lit 7w] [];
         mk_inst 1 STOP [] []]|>])
    ("entry",2) {("entry",1); ("entry",2)} /\
  observer_region_closed ctx
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 9 INVOKE [] []; mk_inst 0 SETFMP [Lit 7w] [];
         mk_inst 1 STOP [] []]|>])
    ("entry",2) {("entry",1); ("entry",2)}
Proof
  simp[observer_old_prefix_region_safe, observer_old_prefix_region_closed]
QED

Theorem observer_region_run_prefix_aux:
  !fuel n s bb h.
    observer_region_safe fn cut R /\ observer_region_closed ctx fn cut R /\
    (s.vs_current_bb,s.vs_inst_idx) IN R /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    run_from fuel ctx fn s = Halt h ==>
    ?u. local_prefix ctx fn cut s u /\ stop_view u = h
Proof
  completeInduct_on `fuel` >> completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) = cut`
  >- (qexists_tac `s` >> conj_tac
      >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
      qpat_x_assum `observer_region_safe fn cut R`
        (strip_assume_tac o REWRITE_RULE[observer_region_safe_def]) >>
      qpat_x_assum `!bb. _` (qspec_then `bb` mp_tac) >>
      impl_tac >- (Cases_on `cut` >> gvs[]) >> strip_tac >>
      `SND cut = s.vs_inst_idx` by (Cases_on `cut` >> gvs[]) >>
      gvs[] >>
      `run_from fuel ctx fn s = Halt (stop_view s)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[Once step_inst_base_def, mk_inst_def]) >> gvs[]) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
      simp[Once run_from_def, Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE /\
    (!h. step_inst_base inst s <> Halt h) /\
    (!middle. step_inst_base inst s = OK middle ==> ~middle.vs_halted)` by
      metis_tac[observer_region_safe_def] >>
  Cases_on `step_inst_base inst s` >>
  qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  strip_tac >> gvs[] >>
  rename1 `step_inst_base inst s = OK middle` >>
  `~middle.vs_halted` by metis_tac[] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- suspend "jump" >> suspend "ordinary"
QED

Resume observer_region_run_prefix_aux[ordinary]:
  `middle.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx fn cut s
     (middle with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  qpat_assum `observer_region_closed ctx fn cut R`
    (mp_tac o REWRITE_RULE[observer_region_closed_def]) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `!m. m < LENGTH _ - _ ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `h`] mp_tac) >>
  simp[] >> impl_tac >- gvs[run_from_def] >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `middle with vs_inst_idx := SUC s.vs_inst_idx` >> simp[]
QED

Resume observer_region_run_prefix_aux[jump]:
  gvs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def] >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block middle.vs_current_bb fn.fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac >>
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx fn cut s
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  qpat_assum `observer_region_closed ctx fn cut R`
    (mp_tac o REWRITE_RULE[observer_region_closed_def]) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `!m. m < SUC n ==> _` (qspec_then `n` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`entered with vs_inst_idx := phi_prefix_length target.bb_instructions`,
     `target`, `h`] mp_tac) >>
  simp[] >> impl_tac >- gvs[run_from_def] >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `entered with vs_inst_idx := phi_prefix_length target.bb_instructions` >>
  simp[]
QED

Finalise observer_region_run_prefix_aux

Theorem observer_region_run_prefix:
  observer_region_safe fn cut R /\ observer_region_closed ctx fn cut R /\
  (s.vs_current_bb,s.vs_inst_idx) IN R /\ ~s.vs_halted /\
  run_from fuel ctx fn s = Halt h ==>
  ?u. local_prefix ctx fn cut s u /\ stop_view u = h
Proof
  rpt strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- gvs[run_from_def] >>
  irule observer_region_run_prefix_aux >> metis_tac[]
QED

Theorem observer_region_run_prefix_transfer:
  observer_region_safe fn cut R /\ observer_region_closed ctx fn cut R /\
  (s.vs_current_bb,s.vs_inst_idx) IN R /\ ~s.vs_halted /\
  run_from fuel ctx fn s = Halt h /\
  region_code_agrees fn fn' cut R ==>
  ?u. local_prefix ctx fn' cut s u /\ stop_view u = h
Proof
  strip_tac >> drule_all observer_region_run_prefix >> strip_tac >>
  qexists_tac `u` >> simp[] >> irule local_prefix_region_transfer >> metis_tac[]
QED
