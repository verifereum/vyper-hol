Theory dftPacketReturnLiveFrame
Ancestors
  dftPacketReturnTables frameJointTransition list rich_list arithmetic finite_map

Theorem dft_packet_return_suffixes:
  GENLIST (\i. DROP i (x::xs)) (SUC (LENGTH (x::xs))) =
    (x::xs)::GENLIST (\i. DROP i xs) (SUC (LENGTH xs)) /\
  ~MEM (x::xs) (GENLIST (\i. DROP i xs) (SUC (LENGTH xs)))
Proof
  simp[GENLIST_CONS, combinTheory.o_DEF, rich_listTheory.DROP, MEM_GENLIST] >>
  rpt strip_tac >> qpat_assum `x::xs = DROP _ xs`
    (mp_tac o AP_TERM ``LENGTH : 'a list -> num``) >>
  simp[LENGTH_DROP] >> decide_tac
QED

(* The surviving frames correspond to proper suffixes of the popped path.
   Neither block update and neither the activation nor call update touches them. *)
Theorem dft_packet_return_live_frames:
  p = ((e:num,cid:num)::a) /\ stk = f::rest /\ LENGTH stk = LENGTH p /\
  (!x. x <> p ==> FLOOKUP acts' x = FLOOKUP acts x) /\
  (!x v. (x,v) <> (p,d) /\ (x,v) <> (a,e) ==>
    FLOOKUP blocks' (x,v) = FLOOKUP blocks (x,v)) /\
  (!key. key <> (a,e,cid) ==> FLOOKUP calls' key = FLOOKUP calls key) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order q call_h b0 done child_entry v id x.
      x = DROP (SUC k) p /\ (v,id) = EL k p /\
      FLOOKUP acts x = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      FLOOKUP calls (x,v,id) = SOME (q,call_h,b0,done,child_entry,NONE) /\
      (EL k stk).cf_fn = tf /\ (EL k stk).cf_state = b0 /\
      (EL k stk).cf_inst.inst_id = id /\ (EL k stk).cf_inst.inst_opcode = INVOKE /\
      active_inst tf (EL k stk).cf_inst b0) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys rho ini h0 be hbe count
      q h b0 done child_entry id v x.
      x = DROP (SUC k) p /\ (v,id) = EL k p /\
      FLOOKUP acts x = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      LAST order = v /\
      FLOOKUP blocks (x,v) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls (x,v,id) = SOME (q,h,b0,done,child_entry,NONE) /\
      done = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) ==>
  LENGTH rest = LENGTH a /\
  (!k. k < LENGTH a ==>
    ?sf tf inc entry order q call_h b0 done child_entry v id x.
      x = DROP (SUC k) a /\ (v,id) = EL k a /\
      FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      FLOOKUP calls' (x,v,id) = SOME (q,call_h,b0,done,child_entry,NONE) /\
      (EL k rest).cf_fn = tf /\ (EL k rest).cf_state = b0 /\
      (EL k rest).cf_inst.inst_id = id /\ (EL k rest).cf_inst.inst_opcode = INVOKE /\
      active_inst tf (EL k rest).cf_inst b0) /\
  (!k. k < LENGTH a ==>
    ?sf tf inc entry order bb bt ps xs ys rho ini h0 be hbe count
      q h b0 done child_entry id v x.
      x = DROP (SUC k) a /\ (v,id) = EL k a /\
      FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      LAST order = v /\
      FLOOKUP blocks' (x,v) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls' (x,v,id) = SOME (q,h,b0,done,child_entry,NONE) /\
      done = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs))
Proof
  strip_tac >> gvs[] >>
  conj_tac >> qx_gen_tac `k` >> disch_tac >>
  `DROP (SUC k) a <> a /\ DROP (SUC k) a <> (e,cid)::a` by
    (conj_tac >> strip_tac >>
     pop_assum (mp_tac o AP_TERM ``LENGTH : (num # num) list -> num``) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  `SUC k < SUC (LENGTH a)` by simp[]
  >- (qpat_x_assum `!i. _ ==> ?sf inc entry order q call_h done child_entry v.
        _ /\ FLOOKUP acts _ = _ /\ FLOOKUP calls _ = _ /\ _`
        (qspec_then `SUC k` mp_tac) >>
      simp[EL_restricted])
  >> qpat_x_assum `!i. _ ==> ?sf tf inc entry order bb bt ps xs ys rho ini h0 be hbe count q h b0 child_entry id.
       _ /\ FLOOKUP acts _ = _ /\ FLOOKUP blocks _ = _ /\ _`
       (qspec_then `SUC k` mp_tac) >>
     simp[EL_restricted]
QED

(* Closing the popped path removes exactly the head of the live suffix list.
   Activation ownership, order, and links to an immutable call setup remain. *)
Theorem dft_packet_return_activation_frame:
  FLOOKUP (acts : ((num # num) list,
    ir_function # ir_function # num # venom_state # num list #
    exec_result option # bytes32 list option) fmap) ((e,cid)::a) =
    SOME (csf,ctf,e,child_entry,child_order,NONE,NONE) /\
  acts' = acts |+ (((e,cid)::a),(csf,ctf,e,child_entry,child_order,
    SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
  FDOM blocks' = FDOM blocks /\
  FLOOKUP (calls : (gas_event,
    num # num # venom_state # num list # venom_state #
    (internal_return # venom_state # venom_state) option) fmap)
    (a,e,cid) = SOME (q,h,b0,done,child_entry,NONE) /\
  calls' = calls |+ ((a,e,cid),(q,h,b0,done,child_entry,SOME (ir,out,post))) /\
  (!x sf tf inc entry order res nrest.
    FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    MEM sf C7.ctx_functions /\ tf = dft_fn sf /\ dft_fn_rel sf tf /\
    inc = (case x of [] => 0 | (e,cid)::parent => e) /\
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    (!v. MEM v order <=> (x,v) IN FDOM blocks) /\
    (res = NONE <=> nrest = NONE) /\
    (res = NONE <=> MEM x (GENLIST (\i. DROP i ((e,cid)::a))
      (SUC (LENGTH ((e,cid)::a))))) /\
    (!v id parent. x = (v,id)::parent ==>
      ?q h s done ret. FLOOKUP calls (parent,v,id) = SOME (q,h,s,done,entry,ret))) ==>
  (!x sf tf inc entry order res nrest.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    MEM sf C7.ctx_functions /\ tf = dft_fn sf /\ dft_fn_rel sf tf /\
    inc = (case x of [] => 0 | (e,cid)::parent => e) /\
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    (!v. MEM v order <=> (x,v) IN FDOM blocks') /\
    (res = NONE <=> nrest = NONE) /\
    (res = NONE <=> MEM x (GENLIST (\i. DROP i a) (SUC (LENGTH a)))) /\
    (!v id parent. x = (v,id)::parent ==>
      ?q h s done ret. FLOOKUP calls' (parent,v,id) = SOME (q,h,s,done,entry,ret)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> disch_tac >>
  `GENLIST (\i. DROP i ((e,cid)::a)) (SUC (LENGTH ((e,cid)::a))) =
     ((e,cid)::a)::GENLIST (\i. DROP i a) (SUC (LENGTH a)) /\
   ~MEM ((e,cid)::a) (GENLIST (\i. DROP i a) (SUC (LENGTH a)))` by
    simp[dft_packet_return_suffixes] >>
  Cases_on `x = (e,cid)::a`
  >- (qpat_assum `!x sf tf inc entry order res nrest. _`
        (fn th => qpat_assum `FLOOKUP acts ((e,cid)::a) = _`
          (mp_tac o MATCH_MP th)) >>
      simp[FLOOKUP_UPDATE] >> strip_tac >> gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  `FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest)` by gvs[FLOOKUP_UPDATE] >>
  qpat_x_assum `!x sf tf inc entry order res nrest. _` drule >>
  simp[] >> strip_tac >> simp[] >>
  rpt strip_tac >>
  `x <> (e,cid)::a` by simp[] >>
  gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED
