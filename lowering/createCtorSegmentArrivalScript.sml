(* Compare first arrivals without identifying raw jump edges with PHI entry
   at states from which successful execution cannot continue. *)
Theory createCtorSegmentArrival
Ancestors
  fragGasOrigin fragExec venomExecSemantics venomExecProofs venomInst
  venomState relation

Definition ctor_segment_fetch_def:
  ctor_segment_fetch fn s =
    OPTION_BIND (lookup_block s.vs_current_bb fn.fn_blocks)
      (\bb. get_instruction bb s.vs_inst_idx)
End

Definition ctor_segment_entry_def:
  ctor_segment_entry fn s =
    OPTION_MAP (\bb. (eval_phis s bb.bb_instructions,
                      phi_prefix_length bb.bb_instructions))
      (lookup_block s.vs_current_bb fn.fn_blocks)
End

Definition ctor_segment_next_def:
  ctor_segment_next fn s inst =
    case step_inst_base inst s of
      OK middle =>
        if is_terminator inst.inst_opcode then
          case ctor_segment_entry fn middle of
            SOME (OK entered,n) => SOME (entered with vs_inst_idx := n)
          | _ => NONE
        else SOME (middle with vs_inst_idx := SUC s.vs_inst_idx)
    | _ => NONE
End

Theorem ctor_segment_edge_fetch[local]:
  gas_origin_edge mem explicit ctx fn s marks (OK t) ==>
  ?inst. ctor_segment_fetch fn s = SOME inst /\ inst.inst_opcode <> PHI
Proof
  rw[gas_origin_edge_def, exit_result_def] >>
  simp[ctor_segment_fetch_def] >> metis_tac[step_inst_ok_imp_not_phi]
QED

Theorem ctor_segment_ready_next[local]:
  gas_origin_edge mem explicit ctx fn s marks (OK t) /\
  ctor_segment_fetch fn s = SOME inst /\ inst.inst_opcode <> INVOKE /\
  ctor_segment_fetch fn t = SOME next /\ next.inst_opcode <> PHI ==>
  ctor_segment_next fn s inst = SOME t
Proof
  rw[gas_origin_edge_def, exit_result_def] >>
  gvs[ctor_segment_fetch_def, step_inst_non_invoke, ctor_segment_next_def,
      ctor_segment_entry_def]
  >- (rename1 `get_instruction target (jump_to lbl s).vs_inst_idx = SOME next` >>
      Cases_on `target.bb_instructions` >>
      gvs[jump_to_def, get_instruction_def, phi_prefix_length_def, eval_phis_def]) >>
  qpat_assum `OK _ = step_inst_base _ _` (fs o single o SYM o REWRITE_RULE[]) >>
  fs[exit_result_def]
QED

Theorem ctor_segment_ok_cases[local]:
  gas_origin_path mem explicit ctx fn s marks (OK t) ==>
  s = t \/ ?mid left right. gas_origin_edge mem explicit ctx fn s left (OK mid) /\
                            gas_origin_path mem explicit ctx fn mid right (OK t)
Proof
  simp[Once gas_origin_path_cases, exit_result_def] >> metis_tac[]
QED

Theorem ctor_segment_path_fetch[local]:
  gas_origin_path mem explicit ctx fn s marks (OK t) /\
  ctor_segment_fetch fn t = SOME last /\ last.inst_opcode <> PHI ==>
  ?inst. ctor_segment_fetch fn s = SOME inst /\ inst.inst_opcode <> PHI
Proof
  strip_tac >> drule ctor_segment_ok_cases >> metis_tac[ctor_segment_edge_fetch]
QED

(* Both traversals use the registered function; only the chosen relations
   are restricted at the cut.  The next actual fetch proves productivity. *)
Theorem ctor_same_func_first_arrival:
  !ctx fn cut explicit R computed.
    (!u v. R u v ==>
       (u.vs_current_bb,u.vs_inst_idx) <> cut /\
       ?marks. gas_origin_edge F explicit ctx fn u marks (OK v)) /\
    (!u v. computed u v ==>
       (u.vs_current_bb,u.vs_inst_idx) <> cut /\
       ?inst. ctor_segment_fetch fn u = SOME inst /\
              inst.inst_opcode <> INVOKE /\
              ctor_segment_next fn u inst = SOME v) ==>
    !s t. RTC R s t ==>
    !w last. RTC computed s w /\
      (t.vs_current_bb,t.vs_inst_idx) = cut /\
      (w.vs_current_bb,w.vs_inst_idx) = cut /\
      ctor_segment_fetch fn t = SOME last /\ last.inst_opcode <> PHI ==>
      t = w
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac RTC_STRONG_INDUCT >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `RTC computed _ _` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
      metis_tac[]) >>
  rpt strip_tac >> rename1 `R s mid` >>
  qpat_assum `!u v. R u v ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `RTC computed s w` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1])
  >- metis_tac[] >>
  rename1 `computed s mid'` >>
  qpat_assum `!u v. computed u v ==> _` (drule_then strip_assume_tac) >>
  `?next. ctor_segment_fetch fn mid = SOME next /\ next.inst_opcode <> PHI` by
    (qpat_assum `RTC R mid t` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1])
     >- metis_tac[] >> metis_tac[ctor_segment_edge_fetch]) >>
  `ctor_segment_next fn s inst = SOME mid` by
    metis_tac[ctor_segment_ready_next] >>
  gvs[] >> metis_tac[]
QED

Theorem ctor_segment_invoke_ok[local]:
  gas_origin_edge mem explicit ctx fn s marks (OK t) /\
  ctor_segment_fetch fn s = SOME inst /\ inst.inst_opcode = INVOKE ==>
  ?fuel middle. step_inst fuel ctx inst s = OK middle /\
                t = (middle with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
  rw[gas_origin_edge_def, exit_result_def] >>
  gvs[ctor_segment_fetch_def]
  >- (qexists_tac `fuel` >> simp[]) >>
  qpat_assum `OK _ = step_inst _ _ _ _` (fs o single o SYM) >>
  fs[exit_result_def]
QED

(* Successful edges need only agree if both successors are ready to fetch.
   A returning INVOKE has one caller successor, independent of its fuel. *)
Theorem ctor_segment_ready_unique[local]:
  gas_origin_edge m1 e1 ctx fn s left (OK u) /\
  gas_origin_edge m2 e2 ctx fn s right (OK v) /\
  ctor_segment_fetch fn u = SOME i /\ i.inst_opcode <> PHI /\
  ctor_segment_fetch fn v = SOME j /\ j.inst_opcode <> PHI ==>
  u = v
Proof
  strip_tac >>
  drule ctor_segment_edge_fetch >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    `?k a. step_inst k ctx inst s = OK a /\
           u = (a with vs_inst_idx := SUC s.vs_inst_idx)` by
      metis_tac[ctor_segment_invoke_ok] >>
    `?l b. step_inst l ctx inst s = OK b /\
           v = (b with vs_inst_idx := SUC s.vs_inst_idx)` by
      metis_tac[ctor_segment_invoke_ok] >>
    `step_inst (MAX k l) ctx inst s = OK a` by
      (irule (cj 1 venomExecProofsTheory.fuel_mono) >> simp[] >>
       qexists_tac `k` >> simp[arithmeticTheory.MAX_LE]) >>
    `step_inst (MAX k l) ctx inst s = OK b` by
      (irule (cj 1 venomExecProofsTheory.fuel_mono) >> simp[] >>
       qexists_tac `l` >> simp[arithmeticTheory.MAX_LE]) >>
    gvs[]) >>
  `ctor_segment_next fn s inst = SOME u /\
   ctor_segment_next fn s inst = SOME v` by
    metis_tac[ctor_segment_ready_next] >>
  gvs[]
QED

Theorem ctor_segment_rtc_fetch[local]:
  RTC R s t /\
  (!u v. R u v ==> ?marks. gas_origin_edge F exp ctx fn u marks (OK v)) /\
  ctor_segment_fetch fn t = SOME last /\ last.inst_opcode <> PHI ==>
  ?inst. ctor_segment_fetch fn s = SOME inst /\ inst.inst_opcode <> PHI
Proof
  strip_tac >>
  qpat_x_assum `RTC R s t` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  metis_tac[ctor_segment_edge_fetch]
QED

Theorem ctor_segment_path_split[local]:
  !ctx fn exp mem exp' R.
    (!u v. R u v ==> ?marks. gas_origin_edge F exp ctx fn u marks (OK v)) ==>
    !s t. RTC R s t ==>
      !marks z last last'.
        gas_origin_path mem exp' ctx fn s marks (OK z) /\
        ctor_segment_fetch fn t = SOME last /\ last.inst_opcode <> PHI /\
        ctor_segment_fetch fn z = SOME last' /\ last'.inst_opcode <> PHI ==>
        (RTC R s z /\ RTC R z t) \/
        ?rest. gas_origin_path mem exp' ctx fn t rest (OK z)
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac RTC_STRONG_INDUCT >> conj_tac
  >- metis_tac[] >>
  rpt strip_tac >> rename1 `R s mid` >>
  qpat_x_assum `gas_origin_path _ _ _ _ s _ (OK z)`
    (strip_assume_tac o MATCH_MP ctor_segment_ok_cases)
  >- metis_tac[RTC_RULES] >>
  rename1 `gas_origin_path _ _ _ _ mid' _ (OK z)` >>
  `?i. ctor_segment_fetch fn mid = SOME i /\ i.inst_opcode <> PHI` by
    metis_tac[ctor_segment_rtc_fetch] >>
  `?j. ctor_segment_fetch fn mid' = SOME j /\ j.inst_opcode <> PHI` by
    metis_tac[ctor_segment_path_fetch] >>
  `mid = mid'` by metis_tac[ctor_segment_ready_unique] >>
  gvs[] >> metis_tac[RTC_RULES]
QED

Theorem ctor_path_split_at_sink:
  RTC A s t /\ RTC B t b /\
  (!p q. A p q \/ B p q ==> ?ms. gas_origin_edge F exp ctx fn p ms (OK q)) /\
  ctor_segment_fetch fn b = SOME last /\ last.inst_opcode <> PHI /\
  (!ms q. ~gas_origin_edge mem exp' ctx fn b ms (OK q)) /\
  gas_origin_path mem exp' ctx fn s marks (OK z) /\
  ctor_segment_fetch fn z = SOME last' /\ last'.inst_opcode <> PHI ==>
  (RTC A s z /\ RTC A z t) \/ (RTC B t z /\ RTC B z b)
Proof
  strip_tac >>
  `?i. ctor_segment_fetch fn t = SOME i /\ i.inst_opcode <> PHI` by
    metis_tac[ctor_segment_rtc_fetch] >>
  `(RTC A s z /\ RTC A z t) \/ ?rest. gas_origin_path mem exp' ctx fn t rest (OK z)` by
    metis_tac[ctor_segment_path_split] >- simp[] >>
  `(RTC B t z /\ RTC B z b) \/ ?rest. gas_origin_path mem exp' ctx fn b rest (OK z)` by
    metis_tac[ctor_segment_path_split] >- simp[] >>
  drule ctor_segment_ok_cases >> metis_tac[RTC_REFL]
QED
