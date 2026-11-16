Theory dftPacketRootedAlignment
Ancestors
  dftPacketRowAlignment dftPacketCalleeAlignment dftPacketEntryReplay
  dftPacketFillingBoundary dftGasFromListReplayBoundary dftGasToListReplay
  dftIndexedExec dftRunRel venomInst venomExecSemantics venomExecProofs
  frameGasEvents finite_map list rich_list

Theorem dft_packet_rooted_last_success:
  FOLDL (\(prior,r) (sf,plan,call).
    case r of
      OK ent =>
        (prior ++ FST (plan_eval sf.fn_name plan ent),
         case SND (plan_eval sf.fn_name plan ent) of
           OK caller =>
             (case call of NONE => OK caller | SOME c => call_setup c caller)
         | other => other)
    | other => (prior,other)) ([],OK entry)
    (prefix ++ [(sf,plan,NONE)]) = (events,OK u) ==>
  ?prior ent es.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
          (prior ++ FST (plan_eval sf.fn_name plan ent),
           case SND (plan_eval sf.fn_name plan ent) of
             OK caller =>
               (case call of NONE => OK caller | SOME c => call_setup c caller)
           | other => other)
      | other => (prior,other)) ([],OK entry) prefix = (prior,OK ent) /\
    plan_eval sf.fn_name plan ent = (es,OK u) /\ events = prior ++ es
Proof
  simp[FOLDL_APPEND] >> pairarg_tac >>
  rename1 `_ = (prior,r0)` >> Cases_on `r0` >> gvs[] >>
  rename1 `plan_eval sf.fn_name plan ent` >>
  Cases_on `plan_eval sf.fn_name plan ent` >> gvs[] >>
  rename1 `plan_eval sf.fn_name plan ent = (es,r1)` >>
  Cases_on `r1` >> gvs[]
QED

(* One activation: closed rows identify the input of the final row. *)
Theorem dft_packet_level_row_alignment[local]:
  !(F:num) C7 C8 owner row_eval plan_eval entries rows slotss
    bb ps xs ys sp be e z q ms gs tail events u.
  row_eval = (\(bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
        (gas_events_block (F-e) C7 owner
           (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
         FOLDR (dft_exec_cons (F-e) C7) OK z
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\plan entry.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (row_eval row s), SND (row_eval row s))
      | other => (es,other)) ([],OK entry) plan) /\
  LENGTH entries = SUC (LENGTH rows) /\ LENGTH slotss = LENGTH rows /\
  (!i. i < LENGTH rows ==>
    ?bb e ps xs ys sp be.
      EL i rows = (bb,e,DROP (phi_prefix_length bb.bb_instructions)
                              bb.bb_instructions) /\
      bb.bb_instructions = ps ++ xs /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
      EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
      eval_phis (EL i entries) (ps ++ ys) = OK sp /\
      FOLDR (dft_exec_cons (F-e) C8) OK
        (DROP (phi_prefix_length (ps ++ ys)) ps)
        (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
      (!gs rest.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL i slotss) gs ==>
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
           (be with vs_gas_readings := gs ++ rest))) ==>
         residual_result rest (OK (EL (SUC i) entries))
           (FOLDR (dft_exec_cons (F-e) C7) OK xs
             (be with vs_gas_readings := gs ++ rest))))) /\
  bb.bb_instructions = ps ++ xs /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
  eval_phis (LAST entries) (ps ++ ys) = OK sp /\
  FOLDR (dft_exec_cons (F-e) C8) OK
    (DROP (phi_prefix_length (ps ++ ys)) ps)
    (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
  z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT slotss ++ FLAT (TAKE q ms)) gs /\
  plan_eval (rows ++ [(bb,e,z)])
    (HD entries with vs_gas_readings := gs ++ tail) = (events,OK u) ==>
  ?gpre kgss v.
    gs = gpre ++ FLAT kgss /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT slotss) gpre /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
    v = (LAST entries with vs_gas_readings := FLAT kgss ++ tail) /\
    SND (row_eval (bb,e,z) v) = OK u /\
    FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `LIST_REL _ (_ ++ _) gs` mp_tac >>
  simp[LIST_REL_SPLIT1] >> strip_tac >>
  drule dft_packet_flat_filling_split >> strip_tac >>
  rename1 `LIST_REL (LIST_REL _) (TAKE q ms) kgss` >>
  `?gss. ys1 = FLAT gss /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) slotss gss` by
    metis_tac[dft_packet_flat_filling_split] >>
  `?prior v es. plan_eval rows
      (HD entries with vs_gas_readings := gs ++ tail) = (prior,OK v) /\
      row_eval (bb,e,z) v = (es,OK u)` by
    (qpat_x_assum `plan_eval (_ ++ _) _ = _` mp_tac >>
     qpat_assum `plan_eval = _` (fn th => pure_rewrite_tac[th]) >>
     BETA_TAC >> metis_tac[dft_packet_plan_last_success]) >>
  `v = LAST entries with vs_gas_readings := FLAT kgss ++ tail` by
    (drule_all dft_packet_closed_plan_alignment >>
     disch_then (qspec_then `FLAT kgss ++ tail` mp_tac) >>
     strip_tac >> first_x_assum irule >> gvs[APPEND_ASSOC]) >>
  `(case eval_phis (LAST entries with vs_gas_readings := FLAT kgss ++ tail)
       (ps ++ xs) of
      OK sp' => FOLDR (dft_exec_cons (F'-e) C7) OK
        (DROP (phi_prefix_length (ps ++ xs)) ps ++ TAKE q xs)
        (sp' with vs_inst_idx := phi_prefix_length (ps ++ xs))
    | other => other) = OK u` by
    (qpat_x_assum `row_eval _ _ = _` mp_tac >>
     qpat_x_assum `row_eval = _` (fn th => pure_rewrite_tac[th]) >>
     simp[] >> Cases_on `eval_phis (LAST entries with vs_gas_readings :=
       FLAT kgss ++ tail) (ps ++ xs)` >> simp[]) >>
  `FOLDR (dft_exec_cons (F'-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u` by
    metis_tac[dft_packet_row_body_success] >>
  qexistsl_tac [`ys1`,`kgss`] >> simp[] >>
  Cases_on `eval_phis (LAST entries with vs_gas_readings :=
    FLAT kgss ++ tail) (ps ++ xs)` >> gvs[]
QED

Theorem dft_packet_rooted_step_success[local]:
  FOLDL (\(prior,r) (sf,plan,call).
    case r of
      OK ent =>
        (prior ++ FST (plan_eval sf.fn_name plan ent),
         case SND (plan_eval sf.fn_name plan ent) of
           OK caller =>
             (case call of NONE => OK caller | SOME c => call_setup c caller)
         | other => other)
    | other => (prior,other)) ([],OK entry)
    (prefix ++ [(sf,plan,call)]) = (events,OK u) ==>
  ?prior ent es caller.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
          (prior ++ FST (plan_eval sf.fn_name plan ent),
           case SND (plan_eval sf.fn_name plan ent) of
             OK caller =>
               (case call of NONE => OK caller | SOME c => call_setup c caller)
           | other => other)
      | other => (prior,other)) ([],OK entry) prefix = (prior,OK ent) /\
    plan_eval sf.fn_name plan ent = (es,OK caller) /\
    (case call of NONE => OK caller | SOME c => call_setup c caller) = OK u
Proof
  simp[FOLDL_APPEND] >> pairarg_tac >>
  rename1 `_ = (prior,r0)` >> Cases_on `r0` >> gvs[] >>
  rename1 `plan_eval sf.fn_name plan ent` >>
  Cases_on `plan_eval sf.fn_name plan ent` >> gvs[] >>
  rename1 `plan_eval sf.fn_name plan ent = (es,r1)` >>
  Cases_on `r1` >> gvs[]
QED

(* Successful intermediate callers use historical Q, not a new observation fact. *)
Theorem dft_packet_call_entry_alignment[local]:
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  call_setup = (\c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C7.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C8.ctx_functions = SOME ctf /\
  eval_operands ops b0 = SOME args /\
  setup_callee ctf args b0 = SOME child_entry /\
  (!op. MEM op c.inst_operands ==> eval_operand op caller = eval_operand op b0) /\
  (!callee argv.
    setup_callee callee argv (caller with vs_gas_readings := b0.vs_gas_readings) =
    setup_callee callee argv b0) /\
  caller.vs_gas_readings = rest /\ call_setup c caller = OK u ==>
  u = child_entry with vs_gas_readings := rest
Proof
  strip_tac >> drule_all dft_packet_callee_alignment >> strip_tac >> gvs[]
QED

(* The evaluator arguments below are the literal evaluators specialized to
   the displayed fuel and C7.  All indexing functions are bound data. *)
Theorem dft_packet_rooted_row_alignment:
  !(fuel:num) C7 C8 row_eval plan_eval call_setup rooted_eval
    cuts levels acts blocks W entries rows slotss bbs pss xss yss sps bes
    depths qs zs mss sfs segments root_entry Mcut gs tail events u.
  row_eval = (\owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
        (gas_events_block (fuel-e) C7 owner
           (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
         FOLDR (dft_exec_cons (fuel-e) C7) OK z
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\owner plan entry.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (row_eval owner row s), SND (row_eval owner row s))
      | other => (es,other)) ([],OK entry) plan) /\
  call_setup = (\c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C7.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  rooted_eval = (\levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
          (prior ++ FST (plan_eval sf.fn_name plan ent),
           case SND (plan_eval sf.fn_name plan ent) of
             OK caller => (case call of NONE => OK caller | SOME c => call_setup c caller)
           | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  cuts <> [] /\ LENGTH cuts = LENGTH levels /\
  HD (MAP (\(a,ds,e,q,z). a) cuts) = [] /\
  HD (entries 0) = root_entry /\
  (!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?tf inc ent order res nrest bt rho hin h0 hbe count front closed brest later.
      FLOOKUP acts ai = SOME (sfs i,tf,inc,ent,order,res,nrest) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbs i,bt,pss i,xss i,yss i,rho,hin,h0,SOME (bes i,hbe),
              count,front,closed,brest) /\
      HD (entries i) = ent /\ LAST (entries i) = hin /\
      order = ds ++ ei::later /\
      depths i = ei /\ qs i = qi /\ zs i = zi /\
      rows i = MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
        DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
          (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds /\
      slotss i = MAP (\f. FLAT (THE (FLOOKUP W (ai,f)))) ds /\
      mss i = THE (FLOOKUP W (ai,ei))) /\
  (!i. i < LENGTH cuts ==>
    EL i levels = (sfs i,rows i ++ [(bbs i,depths i,zs i)],
      if SUC i = LENGTH cuts then NONE else SOME (EL (qs i) (xss i))) /\
    LENGTH (entries i) = SUC (LENGTH (rows i)) /\
    LENGTH (slotss i) = LENGTH (rows i) /\
    (!r. r < LENGTH (rows i) ==>
      ?bb e ps xs ys sp be.
        EL r (rows i) = (bb,e,DROP (phi_prefix_length bb.bb_instructions)
                                bb.bb_instructions) /\
        bb.bb_instructions = ps ++ xs /\
        EVERY (\x. is_pseudo x.inst_opcode) ps /\
        EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
        EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
        eval_phis (EL r (entries i)) (ps ++ ys) = OK sp /\
        FOLDR (dft_exec_cons (fuel-e) C8) OK
          (DROP (phi_prefix_length (ps ++ ys)) ps)
          (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
        (!vs rest.
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL r (slotss i)) vs ==>
          ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
             (be with vs_gas_readings := vs ++ rest))) ==>
           residual_result rest (OK (EL (SUC r) (entries i)))
             (FOLDR (dft_exec_cons (fuel-e) C7) OK xs
               (be with vs_gas_readings := vs ++ rest))))) /\
    (bbs i).bb_instructions = pss i ++ xss i /\
    EVERY (\x. is_pseudo x.inst_opcode) (pss i) /\
    EVERY (\x. ~is_pseudo x.inst_opcode) (xss i) /\
    EVERY (\x. ~is_pseudo x.inst_opcode) (yss i) /\
    eval_phis (LAST (entries i)) (pss i ++ yss i) = OK (sps i) /\
    FOLDR (dft_exec_cons (fuel-depths i) C8) OK
      (DROP (phi_prefix_length (pss i ++ yss i)) (pss i))
      (sps i with vs_inst_idx := phi_prefix_length (pss i ++ yss i)) = OK (bes i) /\
    zs i = DROP (phi_prefix_length (bbs i).bb_instructions) (pss i) ++ TAKE (qs i) (xss i) /\
    qs i < LENGTH (xss i) /\ LENGTH (mss i) = LENGTH (xss i) /\
    segments i = FLAT (slotss i) ++ FLAT (TAKE (qs i) (mss i)) /\
    (SUC i < LENGTH cuts ==>
      EVERY (\x. ~is_terminator x.inst_opcode) (TAKE (qs i) (xss i)) /\
      ?b0 nm ops args ctf.
        (EL (qs i) (xss i)).inst_opcode = INVOKE /\
        decode_invoke (EL (qs i) (xss i)) = SOME (nm,ops) /\
        lookup_function nm C8.ctx_functions = SOME ctf /\
        eval_operands ops b0 = SOME args /\
        setup_callee ctf args b0 = SOME (HD (entries (SUC i))) /\
        (!kgss rest caller.
          LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
            (TAKE (qs i) (mss i)) kgss /\
          FOLDR (dft_exec_cons (fuel-depths i) C7) OK (TAKE (qs i) (xss i))
            (bes i with vs_gas_readings := FLAT kgss ++ rest) = OK caller ==>
          caller.vs_gas_readings = rest /\
          (!op. MEM op (EL (qs i) (xss i)).inst_operands ==>
            eval_operand op caller = eval_operand op b0) /\
          (!callee argv.
            setup_callee callee argv (caller with vs_gas_readings := b0.vs_gas_readings) =
            setup_callee callee argv b0)))) /\
  Mcut = FLAT (MAP segments (COUNT_LIST (LENGTH cuts))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP W (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP W (ai,ei))))) cuts) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  rooted_eval levels (root_entry with vs_gas_readings := gs ++ tail) = (events,OK u) ==>
  ?Mbefore gpre kgss v.
    Mbefore = FLAT (MAP segments (COUNT_LIST (LENGTH cuts - 1))) ++
      FLAT (slotss (LENGTH cuts - 1)) /\
    Mcut = Mbefore ++ FLAT (TAKE (qs (LENGTH cuts - 1)) (mss (LENGTH cuts - 1))) /\
    gs = gpre ++ FLAT kgss /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mbefore gpre /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE (qs (LENGTH cuts - 1)) (mss (LENGTH cuts - 1))) kgss /\
    v = (LAST (entries (LENGTH cuts - 1)) with vs_gas_readings := FLAT kgss ++ tail) /\
    SND (row_eval (sfs (LENGTH cuts - 1)).fn_name
      (bbs (LENGTH cuts - 1),depths (LENGTH cuts - 1),zs (LENGTH cuts - 1)) v) = OK u /\
    FOLDR (dft_exec_cons (fuel-depths (LENGTH cuts - 1)) C7) OK
      (TAKE (qs (LENGTH cuts - 1)) (xss (LENGTH cuts - 1)))
      (bes (LENGTH cuts - 1) with vs_gas_readings := FLAT kgss ++ tail) = OK u
Proof
  rpt gen_tac >> strip_tac >>
  `!i vals rest ev caller.
    i < LENGTH cuts /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (segments i) vals /\
    plan_eval (sfs i).fn_name (rows i ++ [(bbs i,depths i,zs i)])
      (HD (entries i) with vs_gas_readings := vals ++ rest) = (ev,OK caller) ==>
    ?gpre kgss v.
      vals = gpre ++ FLAT kgss /\
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (slotss i)) gpre /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE (qs i) (mss i)) kgss /\
      v = (LAST (entries i) with vs_gas_readings := FLAT kgss ++ rest) /\
      SND (row_eval (sfs i).fn_name (bbs i,depths i,zs i) v) = OK caller /\
      FOLDR (dft_exec_cons (fuel-depths i) C7) OK (TAKE (qs i) (xss i))
        (bes i with vs_gas_readings := FLAT kgss ++ rest) = OK caller` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH cuts ==> _` (drule_then strip_assume_tac) >>
     irule dft_packet_level_row_alignment >>
     conj_tac >- (qexists_tac `(sfs i).fn_name` >> simp[]) >>
     conj_tac >- simp[] >>
     reverse conj_tac >- metis_tac[] >>
     qexistsl_tac [`C8`,`ev`,`plan_eval (sfs i).fn_name`,`pss i`,`rows i`,`sps i`,`yss i`] >>
     simp[] >> metis_tac[]) >>
  `!k vals rest ev v.
    k < LENGTH cuts /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
      (FLAT (MAP segments (COUNT_LIST k))) vals /\
    rooted_eval (TAKE k levels)
      (root_entry with vs_gas_readings := vals ++ rest) = (ev,OK v) ==>
    v = (HD (entries k) with vs_gas_readings := rest)` by
    (Induct >> rpt gen_tac >> strip_tac
     >- (gvs[COUNT_LIST_SNOC] >>
         qpat_x_assum `rooted_eval _ _ = (ev,OK v)` mp_tac >> simp[]) >>
     `k < LENGTH levels /\ k < LENGTH cuts /\ SUC k <> LENGTH cuts` by decide_tac >>
     qpat_assum `!i. i < LENGTH cuts ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `LIST_REL _ _ vals` mp_tac >>
     pure_rewrite_tac[COUNT_LIST_SNOC, MAP_SNOC, FLAT_SNOC, LIST_REL_SPLIT1] >> strip_tac >>
     `TAKE (SUC k) levels = TAKE k levels ++ [EL k levels]` by
       simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
     qpat_x_assum `rooted_eval _ _ = (ev,OK v)` mp_tac >>
     qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
     qpat_x_assum `TAKE (SUC k) levels = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `EL k levels = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `SUC k <> LENGTH cuts` (fn th => pure_rewrite_tac[th]) >>
     disch_then (mp_then Any strip_assume_tac dft_packet_rooted_step_success) >>
     `ent = (HD (entries k) with vs_gas_readings := ys2 ++ rest)` by
       (first_x_assum irule >> conj_tac >- decide_tac >>
        qexistsl_tac [`prior`,`ys1`] >>
        reverse conj_tac >- first_assum MATCH_ACCEPT_TAC >>
        qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >>
        BETA_TAC >> metis_tac[APPEND_ASSOC]) >>
     qpat_assum `!i vals rest ev caller. _` (qspecl_then [`k`,`ys2`,`rest`,`es`,`caller`] mp_tac) >>
     impl_tac >- metis_tac[] >> strip_tac >>
     qpat_x_assum `SUC k < LENGTH cuts ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `!kgss rest caller. _` (drule_all_then strip_assume_tac) >>
     `call_setup (EL (qs k) (xss k)) caller = OK v` by
       (qpat_x_assum `(case _ of NONE => _ | SOME c => _) = OK v` mp_tac >>
        pure_rewrite_tac[COND_CLAUSES, optionTheory.option_case_def] >> simp[]) >>
     drule_all dft_packet_call_entry_alignment >> simp[]) >>
  qabbrev_tac `l = LENGTH cuts - 1` >>
  `SUC l = LENGTH cuts /\ l < LENGTH cuts /\ l < LENGTH levels` by
    (Cases_on `cuts` >> gvs[Abbr `l`]) >>
  qpat_assum `!i. i < LENGTH cuts ==> _`
    (qspec_then `l` mp_tac) >> impl_tac >- decide_tac >> strip_tac >>
  `Mcut = FLAT (MAP segments (COUNT_LIST l)) ++ segments l` by
    (qpat_x_assum `Mcut = FLAT (MAP segments (COUNT_LIST (LENGTH cuts)))` mp_tac >>
     qpat_assum `SUC l = LENGTH cuts` (fn th => pure_rewrite_tac[GSYM th]) >>
     pure_rewrite_tac[COUNT_LIST_SNOC, MAP_SNOC, FLAT_SNOC] >> simp[]) >>
  qpat_x_assum `LIST_REL _ Mcut gs` mp_tac >>
  qpat_assum `Mcut = _ ++ segments l` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[LIST_REL_SPLIT1] >> strip_tac >>
  `levels = TAKE l levels ++ [EL l levels]` by
    (`LENGTH levels = SUC l` by decide_tac >>
     metis_tac[TAKE_LENGTH_ID_rwt, TAKE_SUC_BY_TAKE, SNOC_APPEND]) >>
  qpat_x_assum `rooted_eval levels _ = _` mp_tac >>
  qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
  qpat_x_assum `levels = TAKE l levels ++ _` (fn th => pure_once_rewrite_tac[th]) >>
  qpat_assum `EL l levels = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `SUC l = LENGTH cuts` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[REFL_CLAUSE, COND_CLAUSES] >>
  disch_then (mp_then Any strip_assume_tac dft_packet_rooted_last_success) >>
  `ent = (HD (entries l) with vs_gas_readings := ys2 ++ tail)` by
    (qpat_x_assum `!k vals rest ev v. _`
       (qspecl_then [`l`,`ys1`,`ys2 ++ tail`,`prior`,`ent`] mp_tac) >>
     impl_tac >- (conj_tac >- decide_tac >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
       qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >>
       BETA_TAC >> metis_tac[APPEND_ASSOC]) >> simp[]) >>
  qpat_x_assum `!i vals rest ev caller.
    i < LENGTH cuts /\ LIST_REL _ (segments i) vals /\ _ ==> _`
    (qspecl_then [`l`,`ys2`,`tail`,`es`,`u`] mp_tac) >>
  impl_tac >- (conj_tac >- decide_tac >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
    qpat_x_assum `ent = _` (fn th => pure_rewrite_tac[GSYM th]) >>
    first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [`FLAT (MAP segments (COUNT_LIST l)) ++ FLAT (slotss l)`,
    `ys1 ++ gpre`,`kgss`,`v`] >>
  simp[LIST_REL_APPEND, APPEND_ASSOC] >>
  irule LIST_REL_APPEND_suff >> conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
