Theory dftPacketPseudoHistory
Ancestors
  dftPacketTableSplice dftPacketCallEdgeClauses dftRunRel dftScheduleOrder
  dftWf venomExecProps venomInst list rich_list finite_map arithmetic

(* A live child with this parent suffix is unique, independently of the
   instruction schedule and of whether other children have returned. *)
Theorem dft_packet_history_suffix_child:
  !p:'a list. !i k x.
    i < LENGTH p /\ k <= LENGTH p /\
    x::DROP (SUC i) p = DROP k p ==>
    k = i /\ x = EL i p
Proof
  rpt strip_tac >>
  `LENGTH (x::DROP (SUC i) p) = LENGTH (DROP k p)` by metis_tac[] >>
  `k = i` by (fs[] >> decide_tac) >>
  gvs[DROP_CONS_EL]
QED

(* The immutable call clause requires a body-entry witness at the same
   block key.  Thus the current NONE row has no historical call records. *)
Theorem dft_packet_pseudo_no_recorded_call:
  !(blocks:(((num # num) list # num),
    basic_block # basic_block # instruction list # instruction list #
    instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool #
    bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p d bb bt ps xs ys rho hin h0 count front closed brest.
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,NONE,count,front,closed,brest) /\
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    ?bb bt ps xs ys rho hin h0 be hbe count front closed brest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest)) ==>
  !cid. FLOOKUP calls (p,d,cid) = NONE
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `FLOOKUP calls (p,d,cid)` >- simp[] >>
  PairCases_on `x` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem dft_packet_history_live_child_unique:
  !(p:(num # num) list) i a e cid livecid.
    i < LENGTH p /\ a = DROP (SUC i) p /\ (e,livecid) = EL i p /\
    MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p))) ==>
    cid = livecid
Proof
  rpt strip_tac >> gvs[MEM_GENLIST] >>
  `k <= LENGTH p` by decide_tac >>
  drule_all dft_packet_history_suffix_child >> strip_tac >>
  metis_tac[pairTheory.PAIR_EQ]
QED

(* This is the call-status part of the Q applicability check.  The second
   antecedent is precisely the return-status projection of the immutable
   call clause, so it applies also to retained, already returned children. *)
Theorem dft_packet_history_call_status:
  !(calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p i a e livecid liveq liveh liveb livedone liveentry rho count.
    i < LENGTH p /\ a = DROP (SUC i) p /\ (e,livecid) = EL i p /\
    FLOOKUP calls (a,e,livecid) =
      SOME (liveq,liveh,liveb,livedone,liveentry,NONE) /\
    (!cid q h b0 done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
      case ret of
        NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
      | SOME triple => MEM q (TAKE count rho)) ==>
    !cid q h b0 done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
      (cid = livecid /\ q = liveq /\ ret = NONE) \/ MEM q (TAKE count rho)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum drule >> Cases_on `ret` >> simp[] >> strip_tac >>
  `cid = livecid` by metis_tac[dft_packet_history_live_child_unique] >>
  gvs[]
QED

(* Only INVOKE/INVOKE ordering is used here.  This is insensitive to the
   exceptional-halt classification of external calls. *)
Theorem dft_packet_history_invoke_order:
  !sf tf bb bt ps xs ys.
    dft_fn_rel sf tf /\
    lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
    lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) xs ==>
    !r q. r < q /\ q < LENGTH xs /\
      (EL r xs).inst_opcode = INVOKE /\ (EL q xs).inst_opcode = INVOKE ==>
      id_before (MAP (\x. x.inst_id) ys)
        (EL r xs).inst_id (EL q xs).inst_id
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `FILTER (\x. is_pseudo x.inst_opcode) bb.bb_instructions = ps` by
    (`FILTER (\x. is_pseudo x.inst_opcode) ps = ps /\
      FILTER (\x. is_pseudo x.inst_opcode) xs = []` by
       simp[FILTER_EQ_ID,FILTER_EQ_NIL] >>
     simp[FILTER_APPEND_DISTRIB]) >>
  qpat_x_assum `dft_block_rel bb bt`
    (strip_assume_tac o REWRITE_RULE [dft_block_rel_def]) >>
  gvs[] >> rpt strip_tac >>
  `r < LENGTH xs` by decide_tac >>
  `MEM (EL r xs) (ps ++ xs) /\ MEM (EL q xs) (ps ++ xs)` by
    metis_tac[MEM_EL,MEM_APPEND] >>
  `~is_pseudo (EL r xs).inst_opcode /\ ~is_pseudo (EL q xs).inst_opcode` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `dft_must_order (EL r xs) (EL q xs)` by metis_tac[dft_must_order_invokes] >>
  `id_before (MAP (\x. x.inst_id) (ps ++ xs))
     (EL r xs).inst_id (EL q xs).inst_id` by
    (rewrite_tac[MAP_APPEND] >> irule id_before_append_right >>
     simp[id_before_def] >> qexistsl_tac [`r`,`q`] >> simp[EL_MAP]) >>
  fs[MAP_APPEND,MEM_APPEND] >> metis_tac[]
QED

Theorem dft_packet_history_invoke_prefix_bound:
  !xs ys rho pos liveq q.
    ALL_DISTINCT (MAP (\x. x.inst_id) xs) /\ ALL_DISTINCT rho /\
    LENGTH rho = LENGTH ys /\
    LIST_REL (\r y. r < LENGTH xs /\ y.inst_id = (EL r xs).inst_id) rho ys /\
    pos < LENGTH rho /\ liveq = EL pos rho /\
    (EL liveq xs).inst_opcode = INVOKE /\
    q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE pos rho) /\
    (!r t. r < t /\ t < LENGTH xs /\
      (EL r xs).inst_opcode = INVOKE /\ (EL t xs).inst_opcode = INVOKE ==>
      id_before (MAP (\x. x.inst_id) ys)
        (EL r xs).inst_id (EL t xs).inst_id) ==>
    q < liveq
Proof
  rpt gen_tac >> strip_tac >> rename1 `ALL_DISTINCT sched` >>
  `?k. k < pos /\ EL k sched = q` by
    (gvs[MEM_EL,LENGTH_TAKE,EL_TAKE] >> metis_tac[]) >>
  `k < LENGTH sched /\ k <> pos` by decide_tac >>
  `q <> liveq` by metis_tac[EL_ALL_DISTINCT_EL_EQ] >>
  Cases_on `q < liveq` >- simp[] >>
  `liveq < q` by decide_tac >>
  `id_before (MAP (\x. x.inst_id) ys)
    (EL liveq xs).inst_id (EL q xs).inst_id` by metis_tac[] >>
  qpat_x_assum `id_before _ _ _` mp_tac >>
  pure_rewrite_tac[id_before_def,LENGTH_MAP] >> rpt strip_tac >>
  `i < LENGTH ys` by decide_tac >>
  fs[EL_MAP,LIST_REL_EL_EQN] >>
  `i < LENGTH sched` by decide_tac >>
  `EL i sched = liveq /\ EL j sched = q` by
    (fs[EL_ALL_DISTINCT_EL_EQ] >> metis_tac[EL_MAP]) >>
  `i = pos /\ j = k` by metis_tac[EL_ALL_DISTINCT_EL_EQ] >>
  decide_tac
QED

Theorem dft_packet_history_suspended_schedule:
  !sf tf bb bt ps xs ys rho count liveq b0.
    dft_fn_rel sf tf /\
    lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
    lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
    PERM rho (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
      from_block [EL q xs] y) rho ys /\
    liveq < LENGTH xs /\ b0.vs_inst_idx = LENGTH ps + count /\
    get_instruction bt b0.vs_inst_idx = SOME (EL liveq xs) ==>
    ALL_DISTINCT (MAP (\x. x.inst_id) xs) /\ ALL_DISTINCT rho /\
    LENGTH rho = LENGTH ys /\ count < LENGTH ys /\ liveq = EL count rho
Proof
  rpt gen_tac >> strip_tac >> rename1 `PERM sched (COUNT_LIST (LENGTH xs))` >>
  rename1 `b0.vs_inst_idx = LENGTH ps + pos` >>
  `wf_function sf` by fs[dft_fn_rel_def] >>
  `MEM bb sf.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM,lookup_block_def] >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) xs)` by
    (qpat_x_assum `ALL_DISTINCT (MAP _ bb.bb_instructions)` mp_tac >>
     asm_rewrite_tac[MAP_APPEND,ALL_DISTINCT_APPEND] >> simp[]) >>
  `ALL_DISTINCT sched` by
    metis_tac[sortingTheory.ALL_DISTINCT_PERM,all_distinct_count_list] >>
  `LENGTH sched = LENGTH ys` by fs[LIST_REL_EL_EQN] >>
  `pos < LENGTH ys /\ EL pos ys = EL liveq xs` by
    gvs[get_instruction_def,EL_APPEND2] >>
  `EL pos sched < LENGTH xs /\
    (EL pos ys).inst_id = (EL (EL pos sched) xs).inst_id` by
    (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `liveq = EL pos sched` by
    (fs[EL_ALL_DISTINCT_EL_EQ] >> metis_tac[EL_MAP]) >> simp[]
QED

(* The actual bounded Q check: arbitrary old records in this suspended
   row are either its live call or an INVOKE already before that call.
   No native chronology or additional packet premise is necessary. *)
Theorem dft_packet_history_recorded_call_bound:
  !(calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p i a e livecid liveq liveh b0 livedone liveentry sf tf bb bt ps xs ys rho count.
    i < LENGTH p /\ a = DROP (SUC i) p /\ (e,livecid) = EL i p /\
    FLOOKUP calls (a,e,livecid) = SOME (liveq,liveh,b0,livedone,liveentry,NONE) /\
    dft_fn_rel sf tf /\
    lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
    lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
    PERM rho (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
      from_block [EL q xs] y) rho ys /\
    liveq < LENGTH xs /\ (EL liveq xs).inst_opcode = INVOKE /\
    b0.vs_inst_idx = LENGTH ps + count /\
    get_instruction bt b0.vs_inst_idx = SOME (EL liveq xs) /\
    (!cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      (case ret of
        NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
      | SOME triple => MEM q (TAKE count rho))) ==>
    !cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      q <= liveq /\ !rows v. TAKE q (LUPDATE v liveq rows) = TAKE q rows
Proof
  rpt gen_tac >> strip_tac >> rename1 `PERM sched (COUNT_LIST (LENGTH xs))` >>
  rename1 `b0.vs_inst_idx = LENGTH ps + pos` >>
  drule_all dft_packet_history_suspended_schedule >> strip_tac >>
  `!r t. r < t /\ t < LENGTH xs /\
    (EL r xs).inst_opcode = INVOKE /\ (EL t xs).inst_opcode = INVOKE ==>
    id_before (MAP (\x. x.inst_id) ys)
      (EL r xs).inst_id (EL t xs).inst_id` by
    (rpt strip_tac >> irule dft_packet_history_invoke_order >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  `!cid q h b done_at_call child_entry ret.
     FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
     (cid = livecid /\ q = liveq /\ ret = NONE) \/ MEM q (TAKE pos sched)` by
    (rpt strip_tac >> irule dft_packet_history_call_status >>
     rpt (first_assum (irule_at Any)) >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  `q <= liveq` by
    (first_x_assum drule >> strip_tac >- simp[] >>
     `q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE` by metis_tac[] >>
     `LIST_REL (\r y. r < LENGTH xs /\ y.inst_id = (EL r xs).inst_id) sched ys` by
       (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
     `q < liveq` suffices_by decide_tac >>
     irule dft_packet_history_invoke_prefix_bound >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  simp[dft_packet_row_prefix_splice]
QED
