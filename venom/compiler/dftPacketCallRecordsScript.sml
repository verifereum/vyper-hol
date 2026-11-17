Theory dftPacketCallRecords
Ancestors
  dftPacketCallLocalPreservation dftPacketCalleeAlignment dftPacketCallNative
  dftGasSimInvariant dftRunRel frameJointTransition
  list rich_list finite_map arithmetic pred_set

Theorem dft_packet_call_stack_linkage:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (calls:(gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p d inst s sf fn inc entry order call_q j count rho cs csf ctf stk PG G tv.
    LENGTH stk = LENGTH p /\ inst.inst_opcode = INVOKE /\ active_inst fn inst s /\
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
    (!k. k < LENGTH p ==>
      ?sf tf inc entry order q h b0 done child e cid a.
        a = DROP (SUC k) p /\ (e,cid) = EL k p /\
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
        FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,NONE) /\
        (EL k stk).cf_fn = tf /\ (EL k stk).cf_state = b0 /\
        (EL k stk).cf_inst.inst_id = cid /\
        (EL k stk).cf_inst.inst_opcode = INVOKE /\
        active_inst tf (EL k stk).cf_inst b0) ==>
    LENGTH (<|cf_fn := fn; cf_inst := inst; cf_state := s;
      cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk) =
      LENGTH ((d,inst.inst_id)::p) /\
    (!k. k < LENGTH ((d,inst.inst_id)::p) ==>
      ?sf tf inc entry order q h b0 done child e cid a.
        a = DROP (SUC k) ((d,inst.inst_id)::p) /\
        (e,cid) = EL k ((d,inst.inst_id)::p) /\
        FLOOKUP (acts |+ ((d,inst.inst_id)::p,
          (csf,ctf,d,cs,[SUC d],NONE,NONE))) a =
          SOME (sf,tf,inc,entry,order,NONE,NONE) /\
        FLOOKUP (calls |+ ((p,d,inst.inst_id),(call_q,j,s,TAKE count rho,cs,NONE)))
          (a,e,cid) = SOME (q,h,b0,done,child,NONE) /\
        (EL k (<|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)).cf_fn = tf /\
        (EL k (<|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)).cf_state = b0 /\
        (EL k (<|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)).cf_inst.inst_id = cid /\
        (EL k (<|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)).cf_inst.inst_opcode = INVOKE /\
        active_inst tf
          (EL k (<|cf_fn := fn; cf_inst := inst; cf_state := s;
            cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)).cf_inst b0)
Proof
  rpt gen_tac >> strip_tac >> conj_tac >- simp[] >>
  gen_tac >> strip_tac >> Cases_on `k`
  >- (simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  `n < LENGTH p` by gvs[] >>
  `DROP (SUC n) p <> p` by
    (strip_tac >> pop_assum (mp_tac o AP_TERM ``LENGTH:(num # num) list -> num``) >> simp[]) >>
  `DROP (SUC n) p <> (d,inst.inst_id)::p` by
    (strip_tac >> pop_assum (mp_tac o AP_TERM ``LENGTH:(num # num) list -> num``) >> simp[]) >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem dft_packet_live_suffix_cons:
  !x p a.
    MEM a (GENLIST (\i. DROP i (x::p)) (SUC (SUC (LENGTH p)))) <=>
    a = x::p \/ MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
Proof
  simp[Once GENLIST_CONS,combinTheory.o_DEF]
QED

Theorem dft_packet_call_activation_linkage:
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
    C7 p d inst q j s count rho cs csf ctf cbb cbt cps cxs cys crho cbe s1.
    FLOOKUP acts ((d,inst.inst_id)::p) = NONE /\
    MEM csf C7.ctx_functions /\ ctf = dft_fn csf /\ dft_fn_rel csf ctf /\
    (!a sf tf inc entry order res rest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) ==>
      MEM sf C7.ctx_functions /\ tf = dft_fn sf /\ dft_fn_rel sf tf /\
      inc = (case a of [] => 0 | (e,cid)::parent => e) /\
      order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
      (!e. MEM e order <=> (a,e) IN FDOM blocks) /\
      (res = NONE <=> rest = NONE) /\
      (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))) /\
      (!e cid parent. a = (e,cid)::parent ==>
        ?q h b0 done ret.
          FLOOKUP calls (parent,e,cid) = SOME (q,h,b0,done,entry,ret))) /\
    (!a e. (a,e) IN FDOM blocks ==> a IN FDOM acts) ==>
    !a sf tf inc entry order res rest.
      FLOOKUP (acts |+ ((d,inst.inst_id)::p,
        (csf,ctf,d,cs,[SUC d],NONE,NONE))) a =
          SOME (sf,tf,inc,entry,order,res,rest) ==>
      MEM sf C7.ctx_functions /\ tf = dft_fn sf /\ dft_fn_rel sf tf /\
      inc = (case a of [] => 0 | (e,cid)::parent => e) /\
      order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
      (!e. MEM e order <=> (a,e) IN FDOM (blocks |+
        (((d,inst.inst_id)::p,SUC d),
          (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)))) /\
      (res = NONE <=> rest = NONE) /\
      (res = NONE <=> MEM a (GENLIST (\i. DROP i ((d,inst.inst_id)::p))
        (SUC (LENGTH ((d,inst.inst_id)::p))))) /\
      (!e cid parent. a = (e,cid)::parent ==>
        ?q' h b0 done ret.
          FLOOKUP (calls |+ ((p,d,inst.inst_id),(q,j,s,TAKE count rho,cs,NONE)))
            (parent,e,cid) = SOME (q',h,b0,done,entry,ret))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `a = (d,inst.inst_id)::p`
  >- (gvs[FLOOKUP_UPDATE,dft_packet_live_suffix_cons] >>
      `!e. ~(((d,inst.inst_id)::p,e) IN FDOM blocks)` by
        ((rpt strip_tac >> first_x_assum drule >> simp[FLOOKUP_DEF] >> (gvs[FLOOKUP_DEF]))) >>
      simp[FDOM_FUPDATE,GENLIST_CONS,GENLIST,FLOOKUP_UPDATE] >>
      strip_tac >> gvs[] >> simp[GENLIST_CONS,GENLIST]) >>
  simp[FLOOKUP_UPDATE] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[FDOM_FUPDATE,dft_packet_live_suffix_cons] >>
  rpt strip_tac >> gvs[] >> simp[FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> gvs[] >> metis_tac[]
QED
