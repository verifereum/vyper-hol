Theory requestCutPacketOrder
Ancestors
  dftFinitePacket venomExecSemantics venomState finite_map list rich_list arithmetic

(* A row before the selected cut closed at the next row's entry state. *)
Theorem request_cut_packet_predecessor:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a sf tf inc entry order res nrest i.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    SUC i < LENGTH order ==>
    ?bb bt ps xs ys row_order hin h0 be hbe count post rest ms ks.
      EL i order = inc + SUC i /\ EL (SUC i) order = inc + SUC (SUC i) /\
      FLOOKUP blocks (a,EL i order) =
        SOME (bb,bt,ps,xs,ys,row_order,hin,h0,SOME (be,hbe),count,OK post,T,SOME rest) /\
      FLOOKUP ms_tab (a,EL i order) = SOME ms /\
      FLOOKUP ks_tab (a,EL i order) = SOME ks /\
      ~post.vs_halted /\
      (i = 0 ==> hin = entry) /\
      post = (case THE (FLOOKUP blocks (a,EL (SUC i) order)) of
        (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf)
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (fn info => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
      (strip_assume_tac o MATCH_MP info)) >>
  `!r. r < LENGTH order ==> EL r order = inc + SUC r` by
    (rpt strip_tac >>
     qpat_assum `order = GENLIST _ _` (fn th => once_rewrite_tac[th]) >>
     simp[EL_GENLIST]) >>
  `EL i order = inc + SUC i /\ EL (SUC i) order = inc + SUC (SUC i)` by
    (conj_tac >> first_x_assum irule >> decide_tac) >>
  `MEM (inc + SUC i) order /\ MEM (inc + SUC (SUC i)) order` by
    (map_every (fn pat => qpat_assum pat mp_tac) [`EL i order = _`, `EL (SUC i) order = _`] >>
     rpt (disch_then (SUBST1_TAC o SYM)) >> simp[EL_MEM]) >>
  `?next. FLOOKUP blocks (a,inc + SUC (SUC i)) = SOME next` by
    (qpat_assum `!e. MEM e order <=> (a,e) IN FDOM blocks`
       (qspec_then `inc + SUC (SUC i)` mp_tac) >>
     qpat_assum `MEM (inc + SUC (SUC i)) order` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  PairCases_on `next` >>
  `?bb bt ps xs ys row_order hin h0 bentry count rest.
     FLOOKUP blocks (a,inc + SUC i) =
       SOME (bb,bt,ps,xs,ys,row_order,hin,h0,bentry,count,OK next6,T,SOME rest) /\
     ~next6.vs_halted` by suspend "previous" >>
  `(?be hbe. bentry = SOME (be,hbe)) /\ (i = 0 ==> hin = entry)` by
    suspend "input" >>
  `?ms ks. FLOOKUP ms_tab (a,inc+SUC i) = SOME ms /\
           FLOOKUP ks_tab (a,inc+SUC i) = SOME ks` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM ks_tab`,
        `FLOOKUP blocks (a,inc + SUC i) = _`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  qexistsl_tac [`bb'`,`bt'`,`ps'`,`xs'`,`ys'`,`row_order`,`hin`,`h0'`,
    `be`,`hbe`,`count''`,`next6`,`rest`,`ms`,`ks`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  map_every (fn pat => TRY (qpat_assum pat mp_tac))
    [`EL i order = _`, `EL (SUC i) order = _`, `bentry = _`,
     `FLOOKUP blocks (a,inc + SUC i) = _`, `FLOOKUP blocks (a,inc + SUC (SUC i)) = _`,
     `FLOOKUP ms_tab (a,inc + SUC i) = _`, `FLOOKUP ks_tab (a,inc + SUC i) = _`] >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED

Resume request_cut_packet_predecessor[previous]:
  qpat_assum `!a e bb bt ps xs ys order_row in_state h0 bentry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn row => qpat_assum `FLOOKUP blocks (a,inc + SUC (SUC i)) = SOME _`
      (strip_assume_tac o MATCH_MP row)) >>
  qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
    (fn lookup => qpat_x_assum `FLOOKUP acts a = SOME _`
      (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o
       REWRITE_RULE [lookup,optionTheory.SOME_11,pairTheory.PAIR_EQ])) >>
  qpat_x_assum `if _ then next6 = _ else _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
  `inc + SUC (SUC i) - 1 = inc + SUC i` by decide_tac >>
  metis_tac[]
QED

Resume request_cut_packet_predecessor[input]:
  qpat_assum `!a e bb bt ps xs ys order_row in_state h0 bentry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn row => qpat_assum `FLOOKUP blocks (a,inc + SUC i) = SOME _`
      (strip_assume_tac o MATCH_MP row)) >>
  qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
    (fn lookup => qpat_x_assum `FLOOKUP acts a = SOME _`
      (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o
       REWRITE_RULE [lookup,optionTheory.SOME_11,pairTheory.PAIR_EQ])) >>
  conj_tac
  >- (namedCases_on `bentry` ["", "body_pair"]
      >- (simp[NoAsms] >>
          qpat_x_assum `case NONE of NONE => _ | SOME (be',hbe') => _`
            (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
          map_every (fn pat => qpat_assum pat mp_tac)
            [`FLOOKUP blocks (p,d) = SOME _`,`FLOOKUP blocks (a,inc + SUC i) = SOME _`,
             `inc + SUC i = d`,`a = p`] >>
          POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[])
      >- (PairCases_on `body_pair` >> simp[NoAsms])) >>
  strip_tac >> qpat_x_assum `if inc + SUC i = _ then hin = _ else _` mp_tac >>
  qpat_assum `i = 0` (fn th => SUBST_ALL_TAC th) >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED

Finalise request_cut_packet_predecessor
