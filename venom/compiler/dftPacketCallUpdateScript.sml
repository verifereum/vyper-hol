Theory dftPacketCallUpdate
Ancestors
  dftPacketExistingPathRows list rich_list finite_map arithmetic pred_set
  frameJointTransition dftGasFromListTraceDefs

Theorem dft_packet_path_rows:
  !b:((num # num) list). !L inds orders child_depth initial_rows
    (tab:(((num # num) list # num),'v list list) fmap).
    b <> [] /\ L = LENGTH b /\ LENGTH inds = L /\
    LENGTH orders = SUC L /\ orders <> [] /\ HD orders = [child_depth] /\
    (!i. i < L ==> ?rows.
      FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows /\
      EL i inds < LENGTH rows) ==>
    ?ts out.
      LENGTH ts = SUC L /\
      EL 0 ts = tab |+ ((b,child_depth),initial_rows) /\ out = EL L ts /\
      (!i. i < L ==>
        EL (SUC i) ts = EL i ts |+
          ((DROP (SUC i) b,FST (EL i b)),
           LUPDATE
             (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i ts) (DROP i b,f))))
               (EL i orders))) (EL i inds)
             (THE (FLOOKUP (EL i ts) (DROP (SUC i) b,FST (EL i b)))))) /\
      (!i. i < L ==>
        FLOOKUP (EL i ts) (DROP (SUC i) b,FST (EL i b)) =
        FLOOKUP tab (DROP (SUC i) b,FST (EL i b))) /\
      (!i a e. i <= L /\ (a,e) <> (b,child_depth) /\
        (!r. r < i ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
        FLOOKUP (EL i ts) (a,e) = FLOOKUP tab (a,e)) /\
      FLOOKUP out (b,child_depth) = SOME initial_rows /\
      (!i rows. i < L /\
        FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows ==>
        FLOOKUP out (DROP (SUC i) b,FST (EL i b)) =
          SOME (LUPDATE
            (FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i b,f))))
              (EL i orders))) (EL i inds) rows) /\
        (!k. k <= EL i inds ==>
          TAKE k (THE (FLOOKUP out (DROP (SUC i) b,FST (EL i b)))) =
          TAKE k rows) /\
        (!r. r < LENGTH rows /\ r <> EL i inds ==>
          EL r (THE (FLOOKUP out (DROP (SUC i) b,FST (EL i b)))) = EL r rows) /\
        LENGTH (THE (FLOOKUP out (DROP (SUC i) b,FST (EL i b)))) = LENGTH rows) /\
      FDOM out = FDOM tab UNION {(b,child_depth)}
Proof
  rpt strip_tac >> irule dft_packet_existing_path_rows >> simp[]
QED

(* This is construction algebra only.  In particular none of the inputs asserts
   that these updates already satisfy the semantic finite-packet relation. *)
Theorem dft_packet_call_tables:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab:(((num # num) list # num),bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num),(string # num) list list) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap)
    p d inst j s n_done src_order q csf ctf cs s1 cbb cbt cps cxs cys crho
    has_body b L inds orders cm ce ck cbe.
    b = (d,inst.inst_id)::p /\ L = LENGTH b /\ q = EL n_done src_order /\
    (has_body ==> s1.vs_inst_idx = LENGTH cps) /\
    (~has_body ==> s1.vs_inst_idx < LENGTH cps) /\
    cbe = (if has_body then SOME (s1,SUC j) else NONE) /\
    cm = (if has_body then GENLIST (\r.
      if (EL r cxs).inst_opcode = GAS then [NONE] else []) (LENGTH cxs) else []) /\
    ce = (if has_body then GENLIST (\r.
      if (EL r cxs).inst_opcode = GAS then [(csf.fn_name,(EL r cxs).inst_id)]
      else []) (LENGTH cxs) else []) /\
    ck = (if has_body then GENLIST (\r.
      if (EL r cxs).inst_opcode = GAS then [(b,SUC d,(EL r cxs).inst_id)]
      else []) (LENGTH cxs) else []) /\
    LENGTH inds = L /\ HD inds = q /\
    LENGTH orders = SUC L /\ HD orders = [SUC d] /\
    (!i. 0 < i /\ i <= L ==>
      ?sf tf inc entry res rest.
        FLOOKUP acts (DROP i b) =
          SOME (sf,tf,inc,entry,EL i orders,res,rest)) /\
    (!i. 0 < i /\ i < L ==>
      ?h b0 done_at_call child_entry.
        FLOOKUP calls (DROP (SUC i) b,FST (EL i b),SND (EL i b)) =
          SOME (EL i inds,h,b0,done_at_call,child_entry,NONE)) /\
    (!i. i < L ==> ?ms es ks.
      FLOOKUP ms_tab (DROP (SUC i) b,FST (EL i b)) = SOME ms /\
      FLOOKUP es_tab (DROP (SUC i) b,FST (EL i b)) = SOME es /\
      FLOOKUP ks_tab (DROP (SUC i) b,FST (EL i b)) = SOME ks /\
      EL i inds < LENGTH ms /\ EL i inds < LENGTH es /\ EL i inds < LENGTH ks) ==>
    ?acts' blocks' calls'.
      acts' = acts |+ (b,(csf,ctf,d,cs,[SUC d],NONE,NONE)) /\
      calls' = calls |+ ((p,d,inst.inst_id),(q,j,s,TAKE n_done src_order,cs,NONE)) /\
      blocks' = blocks |+ ((b,SUC d),
        (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)) /\
      (!a. a <> b ==> FLOOKUP acts' a = FLOOKUP acts a) /\
      (!key. key <> (p,d,inst.inst_id) ==> FLOOKUP calls' key = FLOOKUP calls key) /\
      (!a e. (a,e) <> (b,SUC d) ==> FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)) /\
      FLOOKUP blocks' (p,d) = FLOOKUP blocks (p,d) /\
      (?mts ms'.
        LENGTH mts = SUC L /\
        EL 0 mts = ms_tab |+ ((b,SUC d),cm) /\ ms' = EL L mts /\
        (!i. i < L ==>
          EL (SUC i) mts = EL i mts |+
            ((DROP (SUC i) b,FST (EL i b)),
             LUPDATE
               (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i mts) (DROP i b,f))))
                 (EL i orders))) (EL i inds)
               (THE (FLOOKUP (EL i mts) (DROP (SUC i) b,FST (EL i b)))))) /\
        (!i. i < L ==>
          FLOOKUP (EL i mts) (DROP (SUC i) b,FST (EL i b)) =
          FLOOKUP ms_tab (DROP (SUC i) b,FST (EL i b))) /\
        (!i a e. i <= L /\ (a,e) <> (b,SUC d) /\
          (!r. r < i ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
          FLOOKUP (EL i mts) (a,e) = FLOOKUP ms_tab (a,e)) /\
        FLOOKUP ms' (b,SUC d) = SOME cm /\
        (!i rows. i < L /\
          FLOOKUP ms_tab (DROP (SUC i) b,FST (EL i b)) = SOME rows ==>
          FLOOKUP ms' (DROP (SUC i) b,FST (EL i b)) =
            SOME (LUPDATE
              (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' (DROP i b,f))))
                (EL i orders))) (EL i inds) rows) /\
          (!k. k <= EL i inds ==>
            TAKE k (THE (FLOOKUP ms' (DROP (SUC i) b,FST (EL i b)))) = TAKE k rows) /\
          (!r. r < LENGTH rows /\ r <> EL i inds ==>
            EL r (THE (FLOOKUP ms' (DROP (SUC i) b,FST (EL i b)))) = EL r rows) /\
          LENGTH (THE (FLOOKUP ms' (DROP (SUC i) b,FST (EL i b)))) = LENGTH rows) /\
        FDOM ms' = FDOM ms_tab UNION {(b,SUC d)}) /\
      (?ets es'.
        LENGTH ets = SUC L /\
        EL 0 ets = es_tab |+ ((b,SUC d),ce) /\ es' = EL L ets /\
        (!i. i < L ==>
          EL (SUC i) ets = EL i ets |+
            ((DROP (SUC i) b,FST (EL i b)),
             LUPDATE
               (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i ets) (DROP i b,f))))
                 (EL i orders))) (EL i inds)
               (THE (FLOOKUP (EL i ets) (DROP (SUC i) b,FST (EL i b)))))) /\
        (!i. i < L ==>
          FLOOKUP (EL i ets) (DROP (SUC i) b,FST (EL i b)) =
          FLOOKUP es_tab (DROP (SUC i) b,FST (EL i b))) /\
        (!i a e. i <= L /\ (a,e) <> (b,SUC d) /\
          (!r. r < i ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
          FLOOKUP (EL i ets) (a,e) = FLOOKUP es_tab (a,e)) /\
        FLOOKUP es' (b,SUC d) = SOME ce /\
        (!i rows. i < L /\
          FLOOKUP es_tab (DROP (SUC i) b,FST (EL i b)) = SOME rows ==>
          FLOOKUP es' (DROP (SUC i) b,FST (EL i b)) =
            SOME (LUPDATE
              (FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (DROP i b,f))))
                (EL i orders))) (EL i inds) rows) /\
          (!k. k <= EL i inds ==>
            TAKE k (THE (FLOOKUP es' (DROP (SUC i) b,FST (EL i b)))) = TAKE k rows) /\
          (!r. r < LENGTH rows /\ r <> EL i inds ==>
            EL r (THE (FLOOKUP es' (DROP (SUC i) b,FST (EL i b)))) = EL r rows) /\
          LENGTH (THE (FLOOKUP es' (DROP (SUC i) b,FST (EL i b)))) = LENGTH rows) /\
        FDOM es' = FDOM es_tab UNION {(b,SUC d)}) /\
      (?kts ks'.
        LENGTH kts = SUC L /\
        EL 0 kts = ks_tab |+ ((b,SUC d),ck) /\ ks' = EL L kts /\
        (!i. i < L ==>
          EL (SUC i) kts = EL i kts |+
            ((DROP (SUC i) b,FST (EL i b)),
             LUPDATE
               (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i kts) (DROP i b,f))))
                 (EL i orders))) (EL i inds)
               (THE (FLOOKUP (EL i kts) (DROP (SUC i) b,FST (EL i b)))))) /\
        (!i. i < L ==>
          FLOOKUP (EL i kts) (DROP (SUC i) b,FST (EL i b)) =
          FLOOKUP ks_tab (DROP (SUC i) b,FST (EL i b))) /\
        (!i a e. i <= L /\ (a,e) <> (b,SUC d) /\
          (!r. r < i ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
          FLOOKUP (EL i kts) (a,e) = FLOOKUP ks_tab (a,e)) /\
        FLOOKUP ks' (b,SUC d) = SOME ck /\
        (!i rows. i < L /\
          FLOOKUP ks_tab (DROP (SUC i) b,FST (EL i b)) = SOME rows ==>
          FLOOKUP ks' (DROP (SUC i) b,FST (EL i b)) =
            SOME (LUPDATE
              (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (DROP i b,f))))
                (EL i orders))) (EL i inds) rows) /\
          (!k. k <= EL i inds ==>
            TAKE k (THE (FLOOKUP ks' (DROP (SUC i) b,FST (EL i b)))) = TAKE k rows) /\
          (!r. r < LENGTH rows /\ r <> EL i inds ==>
            EL r (THE (FLOOKUP ks' (DROP (SUC i) b,FST (EL i b)))) = EL r rows) /\
          LENGTH (THE (FLOOKUP ks' (DROP (SUC i) b,FST (EL i b)))) = LENGTH rows) /\
        FDOM ks' = FDOM ks_tab UNION {(b,SUC d)})
Proof
  rpt gen_tac >> strip_tac >>
  qexistsl [`acts |+ (b,(csf,ctf,d,cs,[SUC d],NONE,NONE))`,
    `blocks |+ ((b,SUC d),(cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE))`,
    `calls |+ ((p,d,inst.inst_id),(q,j,s,TAKE n_done src_order,cs,NONE))`] >>
  `b <> p` by (strip_tac >> gvs[]) >>
  pure_rewrite_tac[REFL_CLAUSE,AND_CLAUSES] >>
  conj_tac >- simp[FLOOKUP_UPDATE] >>
  conj_tac >- simp[FLOOKUP_UPDATE] >>
  conj_tac >- (rpt strip_tac >> simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac >- simp[FLOOKUP_UPDATE] >>
  conj_tac >- (irule dft_packet_path_rows >> gvs[] >> (reverse conj_tac >- (strip_tac >> gvs[]) >> metis_tac[])) >>
  conj_tac >- (irule dft_packet_path_rows >> gvs[] >> (reverse conj_tac >- (strip_tac >> gvs[]) >> metis_tac[])) >>
  irule dft_packet_path_rows >> gvs[] >> (reverse conj_tac >- (strip_tac >> gvs[]) >> metis_tac[])
QED
