Theory dftPacketBlockInitializedStructure
Ancestors
  dftPacketFirstBodyObservation dftGasFromListTracePrefix dftPacketEntryReplay
  dftPacketBlockTerminatorCoverage
  dftIndexedExec dftRunRel venomExecProofs venomExecProps venomInst
  list rich_list finite_map arithmetic pred_set

Theorem visit_order_range[local]:
  order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
  LAST order = d ==>
  SUC inc <= d /\ (!e. MEM e order ==> e <= d)
Proof
  strip_tac >>
  `?k. LENGTH order = SUC k` by (Cases_on `order` >> gvs[]) >>
  `d = inc + SUC k` by
    (qpat_assum `order = GENLIST _ _` (mp_tac o AP_TERM ``LAST:num list -> num``) >>
     simp[GENLIST_LAST]) >>
  conj_tac >- decide_tac >>
  qpat_assum `order = GENLIST _ _` SUBST1_TAC >>
  simp[MEM_GENLIST] >> decide_tac
QED

Theorem prefix_visit_el[local]:
  TAKE (SUC j) xs = TAKE (SUC j) ys /\ h <= j ==> EL h xs = EL h ys
Proof
  strip_tac >>
  qpat_assum `TAKE _ _ = TAKE _ _` (mp_tac o AP_TERM ``EL h:'a list -> 'a``) >>
  simp[listTheory.EL_TAKE]
QED

Theorem ancestor_off_current[local]:
  i < LENGTH p ==> DROP (SUC i) p <> p
Proof
  strip_tac >> disch_then (mp_tac o AP_TERM ``LENGTH:'a list -> num``) >>
  simp[LENGTH_DROP]
QED

(* In a first-post-PHI visit, the body_ent is initialized precisely when the
   PHI prefix exhausts the pseudo prefix. *)
Theorem initialized_visit_cursor[local]:
  dft_fn_rel sf tf /\
  lookup_block post.vs_current_bb sf.fn_blocks = SOME bb /\
  lookup_block post.vs_current_bb tf.fn_blocks = SOME bt /\
  bt.bb_label = bb.bb_label /\ bb.bb_label = post.vs_current_bb /\
  eval_phis post bt.bb_instructions = OK sp /\
  s = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions /\
  get_instruction bt s.vs_inst_idx = SOME inst /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM sched (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\
    y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) sched ys /\
  s.vs_inst_idx <= LENGTH ps /\
  (if s.vs_inst_idx < LENGTH ps then body_ent = NONE else
     body_ent = SOME (s,h) /\ dft_remaining_inv sf bb xs s) ==>
  s.vs_current_bb = bb.bb_label /\
  inst = EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions /\
  (case body_ent of
    NONE => phi_prefix_length bt.bb_instructions <= s.vs_inst_idx /\
      s.vs_inst_idx < LENGTH ps /\
      (!f C. FOLDR (dft_exec_cons f C) OK
         (DROP (phi_prefix_length bt.bb_instructions) (TAKE s.vs_inst_idx ps))
         (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s)
  | SOME (be,hbe) => be = s /\ hbe = h /\ s.vs_inst_idx = LENGTH ps /\
      0 < LENGTH ys /\ inst = HD ys /\ dft_remaining_inv sf bb xs s /\
      (!f C. FOLDR (dft_exec_cons f C) OK
         (DROP (phi_prefix_length bt.bb_instructions) ps)
         (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s) /\
      (inv_memory_observation inst.inst_opcode ==>
        EL (EL 0 sched) xs = inst /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL 0 sched) xs) /\
        (!q. q < EL 0 sched /\ (EL q xs).inst_opcode = INVOKE ==>
          MEM q (TAKE 0 sched))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sp.vs_current_bb = post.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `s.vs_inst_idx = phi_prefix_length bt.bb_instructions /\
   s.vs_current_bb = bb.bb_label` by simp[] >>
  `inst = EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions` by
    fs[get_instruction_def,AllCaseEqs()] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Q_TAC ASM_CASES_TAC `s.vs_inst_idx < LENGTH ps`
  >- (`body_ent = NONE` by fs[] >>
      `DROP (phi_prefix_length bt.bb_instructions) (TAKE s.vs_inst_idx ps) = []` by
        simp[LENGTH_TAKE,DROP_LENGTH_TOO_LONG] >> simp[]) >>
  `s.vs_inst_idx = LENGTH ps` by decide_tac >>
  `body_ent = SOME (s,h) /\ dft_remaining_inv sf bb xs s` by fs[] >>
  `inst = HD ys /\ 0 < LENGTH ys` by
    (qpat_assum `get_instruction bt _ = _` mp_tac >>
     Cases_on `ys` >> gvs[get_instruction_def,EL_APPEND2] >>
     qpat_assum `LENGTH ps = phi_prefix_length _` (fn th => rewrite_tac[GSYM th]) >>
     pure_once_rewrite_tac[GSYM APPEND_ASSOC] >> simp[EL_APPEND2]) >>
  `DROP (phi_prefix_length bt.bb_instructions) ps = []` by
    (irule DROP_LENGTH_TOO_LONG >> decide_tac) >>
  `ys <> []` by (Cases_on `ys` >> fs[]) >>
  `lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
   lookup_block bb.bb_label tf.fn_blocks = SOME bt` by metis_tac[] >>
  `EL 0 sched = EL 0 sched` by ACCEPT_TAC (REFL ``EL 0 (sched:num list)``) >>
  simp[] >> disch_tac >>
  `inv_memory_observation (HD ys).inst_opcode` by metis_tac[] >>
  drule_all_then strip_assume_tac dft_packet_first_body_schedule >>
  gvs[EVERY_EL,listTheory.EL_TAKE,LENGTH_TAKE] >>
  rpt strip_tac >>
  qpat_assum `!n. n < HD sched ==> (EL n xs).inst_opcode <> INVOKE`
    (drule_then (fn th => fs[th]))
QED

(* Off the appended coordinate, any old visit that named a predecessor
   still names an unchanged record. A predecessor at the old last visit
   would force the new coordinate, which was absent. *)
Theorem initialized_splice_frame[local]:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    acts1 (blocks:(((num # num) list # num),'row) fmap) blocks1.
  FLOOKUP acts p = SOME (sf,tf,inc,entry,ord,NONE,NONE) /\
  FLOOKUP blocks (p,d) = SOME old /\
  (p,SUC d) NOTIN FDOM blocks /\
  (!e. (p,e) IN FDOM blocks ==> e <= d) /\
  acts1 = acts |+ (p,(sf,tf,inc,entry,ord ++ [SUC d],NONE,NONE)) /\
  blocks1 = (blocks |+ ((p,d),closing)) |+ ((p,SUC d),fresh) ==>
  FLOOKUP acts1 p = SOME (sf,tf,inc,entry,ord ++ [SUC d],NONE,NONE) /\
  FLOOKUP blocks1 (p,d) = SOME closing /\
  FLOOKUP blocks1 (p,SUC d) = SOME fresh /\
  (!a. a <> p ==> FLOOKUP acts1 a = FLOOKUP acts a) /\
  (!a e. (a,e) <> (p,d) /\ (a,e) <> (p,SUC d) ==>
     FLOOKUP blocks1 (a,e) = FLOOKUP blocks (a,e)) /\
  (!a f g ai ent seq r rest.
     FLOOKUP acts a = SOME (f,g,ai,ent,seq,r,rest) ==>
       FLOOKUP acts1 a = SOME (f,g,ai,ent,
         (if a = p then seq ++ [SUC d] else seq),r,rest)) /\
  (!a e. e <> 0 /\ (a,e) IN FDOM blocks ==>
     FLOOKUP blocks1 (a,e-1) = FLOOKUP blocks (a,e-1)) /\
  (!a e. a <> p ==> ((a,e) IN FDOM blocks1 <=> (a,e) IN FDOM blocks))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[FLOOKUP_UPDATE,FDOM_FUPDATE] >>
  conj_tac >- (rpt gen_tac >> Cases_on `a = p` >> simp[]) >>
  conj_tac >- (rpt gen_tac >> Cases_on `a = p` >> gvs[]) >>
  rpt gen_tac >> Cases_on `a = p` >> simp[] >> strip_tac >>
  `e <= d` by metis_tac[] >>
  `d <> e-1 /\ SUC d <> e-1` by decide_tac >> simp[]
QED

Theorem initialized_activation_frame[local]:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    acts1 (blocks:(((num # num) list # num),'row) fmap) blocks1
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap).
  FLOOKUP acts p = SOME (sf,tf,inc,entry,ord,NONE,NONE) /\
  acts1 = acts |+ (p,(sf,tf,inc,entry,ord ++ [SUC d],NONE,NONE)) /\
  ord ++ [SUC d] = GENLIST (\i. inc + SUC i) (LENGTH (ord ++ [SUC d])) /\
  (!e. MEM e (ord ++ [SUC d]) <=> (p,e) IN FDOM blocks1) /\
  (!a e. a <> p ==> ((a,e) IN FDOM blocks1 <=> (a,e) IN FDOM blocks)) /\
  (?seq. FLOOKUP acts [] = SOME (rsf,rtf,0,rentry,seq,NONE,NONE)) /\
  (!a f g ai ent seq r rest. FLOOKUP acts a = SOME (f,g,ai,ent,seq,r,rest) ==>
    MEM f C7.ctx_functions /\ g = dft_fn f /\ dft_fn_rel f g /\
    ai = (case a of [] => 0 | (e,cid)::parent => e) /\
    seq <> [] /\ seq = GENLIST (\i. ai + SUC i) (LENGTH seq) /\
    (!e. MEM e seq <=> (a,e) IN FDOM blocks) /\
    (r = NONE <=> rest = NONE) /\
    (r = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))) /\
    (!e cid parent. a = (e,cid)::parent ==>
      ?q h b0 done_at_call ret. FLOOKUP calls (parent,e,cid) =
        SOME (q,h,b0,done_at_call,ent,ret))) ==>
  (?seq. FLOOKUP acts1 [] = SOME (rsf,rtf,0,rentry,seq,NONE,NONE)) /\
  (!a f g ai ent seq r rest. FLOOKUP acts1 a = SOME (f,g,ai,ent,seq,r,rest) ==>
    MEM f C7.ctx_functions /\ g = dft_fn f /\ dft_fn_rel f g /\
    ai = (case a of [] => 0 | (e,cid)::parent => e) /\
    seq <> [] /\ seq = GENLIST (\i. ai + SUC i) (LENGTH seq) /\
    (!e. MEM e seq <=> (a,e) IN FDOM blocks1) /\
    (r = NONE <=> rest = NONE) /\
    (r = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))) /\
    (!e cid parent. a = (e,cid)::parent ==>
      ?q h b0 done_at_call ret. FLOOKUP calls (parent,e,cid) =
        SOME (q,h,b0,done_at_call,ent,ret)))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (Cases_on `p = []` >> gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `a = p`
  >- (simp[FLOOKUP_UPDATE, IgnAsm `ord ++ [SUC d] = _`] >> strip_tac >>
      qpat_assum `!a f g ai ent seq r rest. FLOOKUP acts _ = _ ==> _`
         (qspec_then `p` (drule_then strip_assume_tac)) >>
      gvs[IgnAsm `ord ++ [SUC d] = GENLIST _ _`] >>
      qpat_assum `ord ++ [SUC d] = GENLIST _ _`
        (fn th => once_rewrite_tac[GSYM th]) >>
      simp[IgnAsm `ord ++ [SUC d] = GENLIST _ _`] >>
      metis_tac[]) >>
  simp[FLOOKUP_UPDATE] >> disch_tac >>
  qpat_assum `!a f g ai ent seq r rest. FLOOKUP acts _ = _ ==> _`
     (qspec_then `a` (drule_then strip_assume_tac)) >> simp[] >> metis_tac[]
QED

(* Immutable call records retain their occurrence index and native setup.
   Their old return bound uses the stable trace of a successful child. *)
Theorem initialized_call_frame[local]:
  N <= N1 /\ TAKE (SUC j) tr1 = TAKE (SUC j) tr /\
  (!a f g ai ent ord r rest. FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,rest) ==>
    FLOOKUP acts1 a = SOME (f:ir_function,g,ai,ent,
      (if a = p then ord ++ [SUC d] else ord),r,rest:bytes32 list option)) /\
  (!a e bb bt ps xs ys sched hin h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb:basic_block,bt,ps:instruction list,xs,ys,sched,hin:venom_state,h0:num,SOME (be,hbe:num),count,
        front:exec_result,closed:bool,brest:bytes32 list option) ==>
    ?count1 (front1:exec_result) (closed1:bool) (brest1:bytes32 list option).
      FLOOKUP blocks1 (a,e) =
        SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count1,front1,closed1,brest1) /\
      count <= count1) /\
  (!a f g ai ent ord r rest.
    FLOOKUP acts a = SOME (f,g,ai,ent,ord,SOME r,SOME rest) ==>
    run_blocks (N-ai) C8 g ent = r) /\
  (!a f g ai ent ord r rest.
    FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,rest) ==> (r = NONE <=> rest = NONE)) /\
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    ?sf tf inc entry order res nrest bb bt ps xs ys sched hin h0
      be hbe count front closed brest csf ctf child_order child_res child_rest c nm ops args.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
    h < j /\ EL h tr = ((a,e,cid),tf,c,b0) /\ LENGTH ps <= b0.vs_inst_idx /\
    get_instruction bt b0.vs_inst_idx = SOME c /\
    (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK
      (TAKE (b0.vs_inst_idx - LENGTH ps) ys) be = OK b0) /\
    done_at_call = TAKE (b0.vs_inst_idx - LENGTH ps) sched /\ ~MEM q done_at_call /\
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
    decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
    (case ret of
      NONE => child_res = NONE /\ MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
    | SOME (ir,child_out,caller_post) =>
        child_res = SOME (IntRet ir child_out) /\
        bind_outputs c.inst_outputs ir.iret_values
          (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
        h + SUC (LENGTH (trace_blocks ((e,cid)::a) e (N-e) C8 ctf child_entry)) <= j /\
        MEM q (TAKE count sched))) ==>
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    ?sf tf inc entry order res nrest bb bt ps xs ys sched hin h0
      be hbe count front closed brest csf ctf child_order child_res child_rest c nm ops args.
    FLOOKUP acts1 a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks1 (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
    h < SUC j /\ EL h tr1 = ((a,e,cid),tf,c,b0) /\ LENGTH ps <= b0.vs_inst_idx /\
    get_instruction bt b0.vs_inst_idx = SOME c /\
    (!F. N1 <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK
      (TAKE (b0.vs_inst_idx - LENGTH ps) ys) be = OK b0) /\
    done_at_call = TAKE (b0.vs_inst_idx - LENGTH ps) sched /\ ~MEM q done_at_call /\
    FLOOKUP acts1 ((e,cid)::a) = SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
    decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
    (case ret of
      NONE => child_res = NONE /\ MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
    | SOME (ir,child_out,caller_post) =>
        child_res = SOME (IntRet ir child_out) /\
        bind_outputs c.inst_outputs ir.iret_values
          (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
        h + SUC (LENGTH (trace_blocks ((e,cid)::a) e (N1-e) C8 ctf child_entry)) <= SUC j /\
        MEM q (TAKE count sched)))
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  qpat_assum `!a e cid q h b0 done_at_call child_entry ret. FLOOKUP calls _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!a e bb bt ps xs ys sched hin h0 be hbe count front closed brest.
    FLOOKUP blocks _ = _ ==> _` (drule_then strip_assume_tac) >>
  `EL h tr1 = EL h tr` by (irule prefix_visit_el >> qexists `j` >> simp[]) >>
  qexistsl [`sf`,`tf`,`inc`,`entry`,`if a = p then order ++ [SUC d] else order`,
    `res`,`nrest`,`bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`hin`,`h0`,`be`,`hbe`,
    `count1`,`front1`,`closed1`,`brest1`,`csf`,`ctf`,
    `if (e,cid)::a = p then child_order ++ [SUC d] else child_order`,
    `child_res`,`child_rest`,`c`,`nm`,`ops`,`args`] >>
  simp[] >>
  `FLOOKUP acts1 a = SOME (sf,tf,inc,entry,
      (if a = p then order ++ [SUC d] else order),res,nrest)` by metis_tac[] >>
  `FLOOKUP acts1 ((e,cid)::a) = SOME (csf,ctf,e,child_entry,
      (if (e,cid)::a = p then child_order ++ [SUC d] else child_order),child_res,child_rest)`
    by metis_tac[] >>
  simp[] >> Cases_on `ret` >> gvs[] >> PairCases_on `x` >> gvs[] >>
  `?u. child_rest = SOME u` by
    (qpat_assum `!a f g ai ent ord r rest. FLOOKUP acts _ = _ ==> (_ <=> _)`
       (qspec_then `(e,(EL q xs).inst_id)::a` (drule_then assume_tac)) >>
     Cases_on `child_rest` >> fs[]) >>
  `run_blocks (N-e) C8 ctf child_entry = IntRet x0 x1` by metis_tac[] >>
  `trace_blocks ((e,(EL q xs).inst_id)::a) e (N1-e) C8 ctf child_entry =
    trace_blocks ((e,(EL q xs).inst_id)::a) e (N-e) C8 ctf child_entry` by
    (irule (cj 3 trace_stable) >> simp[] >> decide_tac) >>
  simp[] >>
  qmatch_asmsub_rename_tac `old_count <= count1` >>
  `TAKE old_count (TAKE count1 sched) = TAKE old_count sched` by simp[TAKE_TAKE_T] >>
  qpat_assum `MEM q (TAKE old_count sched)` mp_tac >>
  pop_assum (fn th => once_rewrite_tac[GSYM th]) >> metis_tac[MEM_TAKE]
QED

Theorem initialized_live_frames[local]:
  (!a. a <> (p : (num # num) list) ==> FLOOKUP acts1 a = FLOOKUP acts a) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order q call_h b0 done_at_call child_entry e cid a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts a = SOME (sf:ir_function,tf,inc:num,entry:venom_state,order:num list,
        NONE:exec_result option,NONE:bytes32 list option) /\
      FLOOKUP calls (a,e,cid) = SOME
        (q:num,call_h:num,b0,done_at_call:num list,child_entry:venom_state,
          NONE:(internal_return # venom_state # venom_state) option) /\
      (EL k stk).cf_fn = tf /\ (EL k stk).cf_state = b0 /\ (EL k stk).cf_inst.inst_id = cid /\
      (EL k stk).cf_inst.inst_opcode = INVOKE /\ active_inst tf (EL k stk).cf_inst b0) ==>
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order q call_h b0 done_at_call child_entry e cid a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts1 a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done_at_call,child_entry,NONE) /\
      (EL k stk).cf_fn = tf /\ (EL k stk).cf_state = b0 /\ (EL k stk).cf_inst.inst_id = cid /\
      (EL k stk).cf_inst.inst_opcode = INVOKE /\ active_inst tf (EL k stk).cf_inst b0)
Proof
  strip_tac >> rpt strip_tac >> drule_then strip_assume_tac ancestor_off_current >>
  qpat_assum `!k. k < LENGTH p ==> ?sf tf inc entry order q call_h b0 done_at_call child_entry e cid a. _`
    (drule_then strip_assume_tac) >> gvs[] >> metis_tac[]
QED

Theorem initialized_live_parents[local]:
  (!a. a <> (p : (num # num) list) ==> FLOOKUP acts1 a = FLOOKUP acts a) /\
  (!a e. (a,e) <> (p,d) /\ (a,e) <> (p,SUC d) ==>
    FLOOKUP blocks1 (a,e) = FLOOKUP blocks (a,e)) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys sched hin h0 be hbe count
      q h b0 done_at_call child_entry cid e a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts a = SOME (sf:ir_function,tf:ir_function,inc:num,entry:venom_state,order:num list,
        NONE:exec_result option,NONE:bytes32 list option) /\ LAST order = e /\
      FLOOKUP blocks (a,e) =
        SOME (bb:basic_block,bt,ps:instruction list,xs,ys:instruction list,sched:num list,
          hin:venom_state,h0:num,SOME (be:venom_state,hbe:num),count,OK b0,F,NONE:bytes32 list option) /\
      FLOOKUP calls (a,e,cid) = SOME
        (q,h:num,b0,done_at_call,child_entry:venom_state,
          NONE:(internal_return # venom_state # venom_state) option) /\
      done_at_call = TAKE count sched /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) ==>
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys sched hin h0 be hbe count
      q h b0 done_at_call child_entry cid e a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts1 a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\
      FLOOKUP blocks1 (a,e) =
        SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,NONE) /\
      done_at_call = TAKE count sched /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs))
Proof
  strip_tac >> rpt strip_tac >> drule_then strip_assume_tac ancestor_off_current >>
  qpat_assum `!k. k < LENGTH p ==> ?sf tf inc entry order bb bt ps xs ys sched hin h0 be hbe count
      q h b0 done_at_call child_entry cid e a. _` (drule_then strip_assume_tac) >>
  qmatch_asmsub_rename_tac `done_at_call = TAKE cnt sched` >>
  qexistsl [`sf`,`tf`,`inc`,`entry`,`order`,`bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`hin`,`h0`,`be`,
    `hbe`,`cnt`,`q`,`h`,`b0`,`done_at_call`,`child_entry`,`cid`,`e`,`a`] >>
  `a <> p` by metis_tac[] >> simp[]
QED

(* Closing the current row preserves all its visit fields and increases only
   its executed-prefix length. *)
Theorem initialized_body_lookup_frame[local]:
  !(blocks:(((num # num) list # num),basic_block # basic_block # instruction list #
    instruction list # instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap).
  FLOOKUP blocks (p,d) = SOME (bb0,bt0,ps0,xs0,ys0,sch0,in0,h00,SOME (be0,hbe0),cnt0,OK s,F,NONE) /\
  cnt0 <= LENGTH ys0 /\ (p,SUC d) NOTIN FDOM blocks /\
  blocks1 = (blocks |+ ((p,d),(bb0,bt0,ps0,xs0,ys0,sch0,in0,h00,SOME (be0,hbe0),
    LENGTH ys0,OK post,T,SOME post.vs_gas_readings))) |+ ((p,SUC d),fresh) ==>
  !a e bb bt ps xs ys sched hin h0 be hbe cnt front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,front,closed,brest) ==>
    ?cnt1 front1 closed1 brest1.
      FLOOKUP blocks1 (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt1,front1,closed1,brest1) /\
      cnt <= cnt1
Proof
  gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `FLOOKUP blocks (p,SUC d) = NONE` by simp[FLOOKUP_DEF] >>
  Cases_on `(a,e) = (p,SUC d)` >- gvs[] >>
  Cases_on `(a,e) = (p,d)`
  >- (qexistsl [`LENGTH ys0`,`OK post`,`T`,`SOME post.vs_gas_readings`] >>
      gvs[FLOOKUP_UPDATE]) >>
  qexistsl [`cnt`,`front`,`closed`,`brest`] >> simp[FLOOKUP_UPDATE]
QED

Theorem initialized_pseudo_fold_fuel[local]:
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  FOLDR (dft_exec_cons f C) OK (DROP k ps) u = OK v ==>
  FOLDR (dft_exec_cons g C) OK (DROP k ps) u = OK v
Proof
  strip_tac >>
  `EVERY (\i. is_pseudo i.inst_opcode) (DROP k ps)` by simp[EVERY_DROP] >>
  drule_all_then mp_tac (Q.INST [`g` |-> `f`, `D` |-> `C`, `gs` |-> `u.vs_gas_readings`]
    dft_packet_pseudo_fold_gas) >>
  disch_then (qspec_then `u` mp_tac) >>
  simp[venomStateTheory.venom_state_fupdselfid] >> disch_tac >>
  drule_all_then mp_tac (Q.INST [`D` |-> `C`, `gs` |-> `u.vs_gas_readings`]
    dft_packet_pseudo_fold_gas) >>
  disch_then (qspecl_then [`u`,`g`] mp_tac) >>
  simp[venomStateTheory.venom_state_fupdselfid]
QED

Theorem initialized_block_rows[local]:
  N <= N1 /\ TAKE (SUC j) tr1 = TAKE (SUC j) tr /\ SUC d <= N1 /\
  EL (SUC j) tr1 = (((p:(num # num) list),SUC d,next.inst_id),tf0,next,s1) /\
  FLOOKUP acts p = SOME (sf0,tf0,inc0,entry0,ord0,NONE,NONE) /\ LAST ord0 = d /\
  FLOOKUP blocks (p,d) = SOME (bb0,bt0,ps0,xs0,ys0,sch0,in0,h00,SOME (be0,hbe0),cnt0,OK s,F,NONE) /\
  FLOOKUP acts1 p = SOME (sf0,tf0,inc0,entry0,ord0 ++ [SUC d],NONE,NONE) /\
  blocks1 = (blocks |+ ((p,d),(bb0,bt0,ps0,xs0,ys0,sch0,in0,h00,SOME (be0,hbe0),
    LENGTH ys0,OK post,T,SOME post.vs_gas_readings))) |+ ((p,SUC d),
    (bb1,bt1,ps1,xs1,ys1,sch1,post,SUC j,body1,0,OK s1,F,NONE)) /\
  (p,SUC d) NOTIN FDOM blocks /\
  (!a e. e <> 0 /\ (a,e) IN FDOM blocks ==>
    FLOOKUP blocks1 (a,e-1) = FLOOKUP blocks (a,e-1)) /\
  (!a f g ai ent ord r rest. FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,rest) ==>
    FLOOKUP acts1 a = SOME (f,g,ai,ent,(if a = p then ord ++ [SUC d] else ord),r,rest) /\
    ord <> [] /\ ord = GENLIST (\i. ai + SUC i) (LENGTH ord)) /\
  (!F. N1 <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys0 be0 = OK post) /\
  ~post.vs_halted /\
  lookup_block post.vs_current_bb sf0.fn_blocks = SOME bb1 /\
  lookup_block post.vs_current_bb tf0.fn_blocks = SOME bt1 /\
  bb1.bb_label = post.vs_current_bb /\ bt1.bb_label = bb1.bb_label /\
  eval_phis post bt1.bb_instructions = OK sp1 /\
  bt1.bb_instructions = ps1 ++ ys1 /\ bb1.bb_instructions = ps1 ++ xs1 /\
  EVERY (\i. is_pseudo i.inst_opcode) ps1 /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs1 /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys1 /\
  EVERY inst_shape_ok bb1.bb_instructions /\ LENGTH xs1 = LENGTH ys1 /\
  PERM sch1 (COUNT_LIST (LENGTH xs1)) /\
  LIST_REL (\q y. q < LENGTH xs1 /\ y.inst_id = (EL q xs1).inst_id /\ from_block [EL q xs1] y) sch1 ys1 /\
  strict_dom_vars_defined sf0 post /\ fn_reachable sf0 post.vs_current_bb /\
  ctx_labels_bound C7 post.vs_labels /\ ctx_labels_bound C8 post.vs_labels /\
  s1 = sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions /\
  next = EL (phi_prefix_length bt1.bb_instructions) bt1.bb_instructions /\
  (case body1 of NONE => FLOOKUP m1 (p,SUC d) = SOME [] /\ FLOOKUP es1 (p,SUC d) = SOME [] /\
      FLOOKUP ks1 (p,SUC d) = SOME []
    | SOME (be,hbe) => be = s1 /\ hbe = SUC j /\ s1.vs_inst_idx = LENGTH ps1 /\
      next = HD ys1 /\ s1.vs_current_bb = bb1.bb_label /\ dft_remaining_inv sf0 bb1 xs1 s1 /\
      FOLDR (dft_exec_cons (N1-SUC d) C8) OK (DROP (phi_prefix_length bt1.bb_instructions) ps1)
        (sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions) = OK s1) /\
  (!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body_ent,cnt,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\ MEM e order /\ e <= N /\ h0 <= j /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\ lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\ bt.bb_label = bb.bb_label /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      EVERY inst_shape_ok bb.bb_instructions /\ LENGTH xs = LENGTH ys /\
      PERM sched (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) sched ys /\
      strict_dom_vars_defined sf hin /\ fn_reachable sf hin.vs_current_bb /\
      ctx_labels_bound C7 hin.vs_labels /\ ctx_labels_bound C8 hin.vs_labels /\ eval_phis hin bt.bb_instructions = OK sp /\
      EL h0 tr = ((a,e,(EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions).inst_id),tf,
        EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
        sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
      (if e = SUC inc then hin = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks (a,e-1) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
          ~hin.vs_halted) /\
      cnt <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
      (case body_ent of NONE => a = p /\ e = d /\ cnt = 0 /\ front = OK s /\
          FLOOKUP m (a,e) = SOME [] /\ FLOOKUP es (a,e) = SOME [] /\ FLOOKUP ks (a,e) = SOME []
        | SOME (be,hbe) => hbe <= j /\ be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
          dft_remaining_inv sf bb xs be /\ EL hbe tr = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
          FOLDR (dft_exec_cons (N-e) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
            (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
          (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE cnt ys) be = front) /\
          (closed ==> cnt = LENGTH ys /\ terminates front /\
            (!v. (front = OK v \/ (?ir. front = IntRet ir v)) ==> brest = SOME v.vs_gas_readings))) /\
      (e <> LAST order ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
      (e = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest)) ==>
  (!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks1 (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body_ent,cnt,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts1 a = SOME (sf,tf,inc,entry,order,res,nrest) /\ MEM e order /\ e <= N1 /\ h0 <= SUC j /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\ lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\ bt.bb_label = bb.bb_label /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      EVERY inst_shape_ok bb.bb_instructions /\ LENGTH xs = LENGTH ys /\
      PERM sched (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) sched ys /\
      strict_dom_vars_defined sf hin /\ fn_reachable sf hin.vs_current_bb /\
      ctx_labels_bound C7 hin.vs_labels /\ ctx_labels_bound C8 hin.vs_labels /\ eval_phis hin bt.bb_instructions = OK sp /\
      EL h0 tr1 = ((a,e,(EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions).inst_id),tf,
        EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
        sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
      (if e = SUC inc then hin = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks1 (a,e-1) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
          ~hin.vs_halted) /\
      cnt <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
      (case body_ent of NONE => a = p /\ e = SUC d /\ cnt = 0 /\ front = OK s1 /\
          FLOOKUP m1 (a,e) = SOME [] /\ FLOOKUP es1 (a,e) = SOME [] /\ FLOOKUP ks1 (a,e) = SOME []
        | SOME (be,hbe) => hbe <= SUC j /\ be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
          dft_remaining_inv sf bb xs be /\ EL hbe tr1 = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
          FOLDR (dft_exec_cons (N1-e) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
            (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
          (!F. N1 <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE cnt ys) be = front) /\
          (closed ==> cnt = LENGTH ys /\ terminates front /\
            (!v. (front = OK v \/ (?ir. front = IntRet ir v)) ==> brest = SOME v.vs_gas_readings))) /\
      (e <> LAST order ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
      (e = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest))
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  Cases_on `(a,e) = (p,SUC d)` >- suspend "fresh" >>
  Cases_on `(a,e) = (p,d)` >- suspend "close" >>
  suspend "retain"
QED

Resume initialized_block_rows[fresh]:
  qexistsl [`sf0`,`tf0`,`inc0`,`entry0`,`ord0 ++ [SUC d]`,`NONE`,`NONE`,`sp1`] >>
  `SUC inc0 <= d` by
    (qpat_assum `!a f g ai ent ord r rest. FLOOKUP acts a = _ ==> _`
       (qspec_then `p` (drule_then strip_assume_tac)) >>
     drule_all_then strip_assume_tac visit_order_range >> simp[]) >>
  gvs[FLOOKUP_UPDATE,LAST_APPEND_NOT_NIL] >>
  Cases_on `body1` >- gvs[] >> PairCases_on `x` >> gvs[]
QED

Resume initialized_block_rows[close]:
  qpat_x_assum `!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (qspecl_then [`p`,`d`] (drule_then (strip_assume_tac o SRULE []))) >>
  `EL h00 tr1 = EL h00 tr /\ EL hbe0 tr1 = EL hbe0 tr` by
    (conj_tac >> irule prefix_visit_el >> qexists `j` >> simp[]) >>
  `d <> 0` by
    (qpat_assum `!a f g ai ent ord r rest. FLOOKUP acts a = _ ==> _`
       (qspec_then `p` (drule_then strip_assume_tac)) >>
     metis_tac[visit_order_range,numTheory.NOT_SUC,LESS_EQ_0]) >>
  `FLOOKUP blocks1 (p,d-1) = FLOOKUP blocks (p,d-1)` by
    (qpat_assum `!a e. e <> 0 /\ _ ==> FLOOKUP blocks1 _ = _`
       (qspecl_then [`p`,`d`] irule) >> simp[FDOM_FLOOKUP]) >>
  `FOLDR (dft_exec_cons (N1-d) C8) OK (DROP (phi_prefix_length bt0.bb_instructions) ps0)
    (sp with vs_inst_idx := phi_prefix_length bt0.bb_instructions) = OK be0` by
    (irule initialized_pseudo_fold_fuel >> (metis_tac[])) >>
  qexistsl [`sf0`,`tf0`,`inc0`,`entry0`,`ord0 ++ [SUC d]`,`NONE`,`NONE`,`sp`] >>
  gvs[FLOOKUP_UPDATE,LAST_APPEND_NOT_NIL,TAKE_LENGTH_ID_rwt,passSimulationDefsTheory.terminates_def]
QED

Resume initialized_block_rows[retain]:
  `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body_ent,cnt,front,closed,brest)` by
    gvs[FLOOKUP_UPDATE] >>
  qpat_x_assum `!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (qspecl_then [`a`,`e`] (drule_then strip_assume_tac)) >>
  `e <> 0` by
    (qpat_assum `!a f g ai ent ord r rest. FLOOKUP acts a = _ ==> _`
       (qspec_then `a` (drule_then strip_assume_tac)) >>
     qpat_assum `order = GENLIST _ _` (mp_tac o AP_TERM ``MEM (e:num)``) >>
     simp[MEM_GENLIST]) >>
  `FLOOKUP blocks1 (a,e-1) = FLOOKUP blocks (a,e-1)` by
    (qpat_assum `!a e. e <> 0 /\ _ ==> FLOOKUP blocks1 _ = _`
       (qspecl_then [`a`,`e`] irule) >> simp[FDOM_FLOOKUP]) >>
  `EL h0 tr1 = EL h0 tr` by (irule prefix_visit_el >> qexists `j` >> simp[]) >>
  `?be hbe. body_ent = SOME (be,hbe)` by
    (Cases_on `body_ent` >- gvs[] >> PairCases_on `x` >> metis_tac[]) >>
  qpat_assum `body_ent = SOME (be,hbe)`
    (fn th => qpat_x_assum `case body_ent of NONE => _ | SOME z => _`
      (strip_assume_tac o SRULE [th])) >>
  `EL hbe tr1 = EL hbe tr` by (irule prefix_visit_el >> qexists `j` >> simp[]) >>
  `FOLDR (dft_exec_cons (N1-e) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
    (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be` by
    (irule initialized_pseudo_fold_fuel >> metis_tac[]) >>
  qpat_assum `!a f g ai ent ord r rest. FLOOKUP acts a = _ ==> _`
    (qspec_then `a` (drule_then strip_assume_tac)) >>
  qexistsl [`sf`,`tf`,`inc`,`entry`,`if a = p then order ++ [SUC d] else order`,`res`,`nrest`,`sp`] >>
  `e <= N1 /\ h0 <= SUC j /\ hbe <= SUC j` by decide_tac >>
  `!F. N1 <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE cnt ys) be = front` by
    (qx_gen_tac `fuel` >> strip_tac >>
     qpat_assum `!F. N <= F ==> FOLDR _ _ (TAKE cnt ys) _ = _`
       (qspec_then `fuel` irule) >> decide_tac) >>
  `a = p ==> e <> LAST order` by
    ((strip_tac >>
     qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)` mp_tac >>
     simp[] >> (gvs[]))) >>
  `a = p ==> e <> SUC d` by (strip_tac >> gvs[]) >>
  Cases_on `a = p` >> gvs[LAST_APPEND_NOT_NIL] >>
  disch_tac >> qpat_assum `IS_SOME brest ==> _` drule >> simp[]
QED

Finalise initialized_block_rows

(* Coverage at the closed row uses the pre-terminator schedule, while the
   fresh row has no executed body instruction. *)
Theorem initialized_return_coverage[local]:
  FLOOKUP blocks ((p:(num # num) list),d) =
    SOME (bb0:basic_block,bt0:basic_block,ps0:instruction list,xs0,ys0:instruction list,
      sch0,in0:venom_state,h00:num,SOME (be0:venom_state,hbe0:num),cnt0,OK s,F,NONE) /\
  (p,SUC d) NOTIN FDOM blocks /\
  blocks1 = (blocks |+ ((p,d),(bb0,bt0,ps0,xs0,ys0,sch0,in0,h00,SOME (be0,hbe0),
    LENGTH ys0,OK post,T,SOME post.vs_gas_readings))) |+ ((p,SUC d),
    (bb1,bt1,ps1,xs1,ys1,sch1,post,SUC j,body1,0,OK s1,F,NONE)) /\
  (!q. q < LENGTH xs0 /\ (EL q xs0).inst_opcode = INVOKE ==> MEM q (TAKE cnt0 sch0)) /\
  (!a e bb bt ps xs ys sched hin h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count sched) ==>
      ?h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,h:num,b0:venom_state,done_at_call:num list,child_entry:venom_state,
            SOME (ir:internal_return,child_out:venom_state,caller_post:venom_state))) ==>
  (!a e bb bt ps xs ys sched hin h0 be hbe count front closed brest.
    FLOOKUP blocks1 (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count sched) ==>
      ?h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post)))
Proof
  strip_tac >> rpt gen_tac >> disch_tac >> qx_gen_tac `q` >> strip_tac >>
  Cases_on `(a,e) = (p,SUC d)` >- gvs[FLOOKUP_UPDATE] >>
  Cases_on `(a,e) = (p,d)`
  >- (gvs[FLOOKUP_UPDATE] >>
      qpat_assum `!a e bb bt ps xs ys sched hin h0 be hbe count front closed brest.
        FLOOKUP blocks _ = _ ==> _` (drule_then (qspec_then `q` irule)) >> simp[]) >>
  qmatch_asmsub_rename_tac `MEM q (TAKE cnt sched)` >>
  `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,front,closed,brest)`
    by gvs[FLOOKUP_UPDATE] >>
  qpat_assum `!a e bb bt ps xs ys sched hin h0 be hbe count front closed brest.
    FLOOKUP blocks _ = _ ==> _` (drule_then (qspec_then `q` irule)) >> simp[]
QED

Theorem initialized_fresh_cursor[local]:
  FLOOKUP acts1 (p:(num # num) list) =
    SOME (sf0,tf0,inc0:num,entry0:venom_state,ord0 ++ [SUC d],NONE:exec_result option,NONE:bytes32 list option) /\
  FLOOKUP blocks1 (p,SUC d) = SOME (bb1:basic_block,bt1,ps1:instruction list,xs1,ys1:instruction list,
    sch1:num list,post:venom_state,SUC j,body1,0,OK s1,F,NONE:bytes32 list option) /\
  lookup_block s1.vs_current_bb tf0.fn_blocks = SOME bt1 /\
  get_instruction bt1 s1.vs_inst_idx = SOME next /\
  eval_phis post bt1.bb_instructions = OK sp1 /\
  (case body1 of NONE => phi_prefix_length bt1.bb_instructions <= s1.vs_inst_idx /\
      s1.vs_inst_idx < LENGTH ps1 /\
      (!f C. FOLDR (dft_exec_cons f C) OK
        (DROP (phi_prefix_length bt1.bb_instructions) (TAKE s1.vs_inst_idx ps1))
          (sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions) = OK s1)
    | SOME (be,hbe) => be = s1 /\ hbe = SUC j /\ s1.vs_inst_idx = LENGTH ps1 /\
      0 < LENGTH ys1 /\ next = HD ys1 /\ dft_remaining_inv sf0 bb1 xs1 s1 /\
      (!f C. FOLDR (dft_exec_cons f C) OK (DROP (phi_prefix_length bt1.bb_instructions) ps1)
        (sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions) = OK s1) /\
      (inv_memory_observation next.inst_opcode ==>
        EL (EL 0 sch1) xs1 = next /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL 0 sch1) xs1) /\
        (!q. q < EL 0 sch1 /\ (EL q xs1).inst_opcode = INVOKE ==> MEM q (TAKE 0 sch1)))) ==>
  (?sf inc entry order bb bt ps xs ys sched hin h0 body_ent count.
    FLOOKUP acts1 p = SOME (sf,tf0,inc,entry,order,NONE,NONE) /\ LAST order = SUC d /\
    FLOOKUP blocks1 (p,SUC d) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body_ent,count,OK s1,F,NONE) /\
    lookup_block s1.vs_current_bb tf0.fn_blocks = SOME bt /\
    get_instruction bt s1.vs_inst_idx = SOME next /\
    (case body_ent of NONE => phi_prefix_length bt.bb_instructions <= s1.vs_inst_idx /\
      s1.vs_inst_idx < LENGTH ps /\ count = 0 /\
      FOLDR (dft_exec_cons (N1-SUC d) C8) OK
        (DROP (phi_prefix_length bt.bb_instructions) (TAKE s1.vs_inst_idx ps))
        ((case eval_phis hin bt.bb_instructions of OK sp => sp | other => hin)
         with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s1
    | SOME (be,hbe) => s1.vs_inst_idx = LENGTH ps + count /\ count < LENGTH ys /\ next = EL count ys)) /\
  (!bb bt ps xs ys sched hin h0 be hbe count sf inc entry order.
    FLOOKUP acts1 p = SOME (sf,tf0,inc,entry,order,NONE,NONE) /\
    FLOOKUP blocks1 (p,SUC d) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,OK s1,F,NONE) /\
    inv_memory_observation next.inst_opcode ==>
    EL (EL count sched) xs = next /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL count sched) xs) /\
    (!q. q < EL count sched /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count sched)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (qexistsl [`sf0`,`inc0`,`entry0`,`ord0 ++ [SUC d]`,`bb1`,`bt1`,`ps1`,`xs1`,`ys1`,
       `sch1`,`post`,`SUC j`,`body1`,`0`] >>
      simp[LAST_APPEND_NOT_NIL] >> Cases_on `body1` >> gvs[] >>
      PairCases_on `x` >> gvs[listTheory.EL]) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED

(* Frame old structure and install the new first-post-PHI cursor on the
   exact splice chosen by the block-edge initializer. *)
Theorem block_initialized_structure:
  N <= N1 /\ TAKE (SUC j) tr1 = TAKE (SUC j) tr /\ SUC d <= N1 /\
  EL (SUC j) tr1 = ((p,SUC d,next.inst_id),tf0,next,s1) /\
  FLOOKUP acts p = SOME (sf0,tf0,inc0,entry0,ord0,NONE,NONE) /\ LAST ord0 = d /\
  FLOOKUP blocks (p,d) = SOME (bb0,bt0,ps0,xs0,ys0,sch0,in0,h00,SOME (be0,hbe0),cnt0,OK s,F,NONE) /\
  acts1 = acts |+ (p,(sf0,tf0,inc0,entry0,ord0 ++ [SUC d],NONE,NONE)) /\
  blocks1 = (blocks |+ ((p,d),(bb0,bt0,ps0,xs0,ys0,sch0,in0,h00,SOME (be0,hbe0),
    LENGTH ys0,OK post,T,SOME post.vs_gas_readings))) |+ ((p,SUC d),
    (bb1,bt1,ps1,xs1,ys1,sch1,post,SUC j,body1,0,OK s1,F,NONE)) /\
  (p,SUC d) NOTIN FDOM blocks /\
  ord0 ++ [SUC d] = GENLIST (\i. inc0 + SUC i) (LENGTH (ord0 ++ [SUC d])) /\
  (!e. MEM e (ord0 ++ [SUC d]) <=> (p,e) IN FDOM blocks1) /\
  (!F. N1 <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys0 be0 = OK post) /\
  ~post.vs_halted /\
  cnt0 < LENGTH ys0 /\ inst0 = EL cnt0 ys0 /\ is_terminator inst0.inst_opcode /\
  lookup_block post.vs_current_bb sf0.fn_blocks = SOME bb1 /\
  lookup_block post.vs_current_bb tf0.fn_blocks = SOME bt1 /\
  bb1.bb_label = post.vs_current_bb /\ bt1.bb_label = bb1.bb_label /\
  eval_phis post bt1.bb_instructions = OK sp1 /\
  s1 = sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions /\
  lookup_block s1.vs_current_bb tf0.fn_blocks = SOME bt1 /\
  get_instruction bt1 s1.vs_inst_idx = SOME next /\
  bt1.bb_instructions = ps1 ++ ys1 /\ bb1.bb_instructions = ps1 ++ xs1 /\
  EVERY (\i. is_pseudo i.inst_opcode) ps1 /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs1 /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys1 /\
  EVERY inst_shape_ok bb1.bb_instructions /\ LENGTH xs1 = LENGTH ys1 /\
  PERM sch1 (COUNT_LIST (LENGTH xs1)) /\
  LIST_REL (\q y. q < LENGTH xs1 /\ y.inst_id = (EL q xs1).inst_id /\ from_block [EL q xs1] y) sch1 ys1 /\
  strict_dom_vars_defined sf0 post /\ fn_reachable sf0 post.vs_current_bb /\
  ctx_labels_bound C7 post.vs_labels /\ ctx_labels_bound C8 post.vs_labels /\
  s1.vs_inst_idx <= LENGTH ps1 /\
  (if s1.vs_inst_idx < LENGTH ps1 then
    body1 = NONE /\ FLOOKUP m1 (p,SUC d) = SOME [] /\
    FLOOKUP es1 (p,SUC d) = SOME [] /\ FLOOKUP ks1 (p,SUC d) = SOME []
   else body1 = SOME (s1,SUC j) /\ dft_remaining_inv sf0 bb1 xs1 s1) /\
  (?seq. FLOOKUP acts [] = SOME (rsf,rtf,0,rentry,seq,NONE,NONE)) /\
  (!a f g ai ent seq r rest. FLOOKUP acts a = SOME (f,g,ai,ent,seq,r,rest) ==>
    MEM f C7.ctx_functions /\ g = dft_fn f /\ dft_fn_rel f g /\
    ai = (case a of [] => 0 | (e,cid)::parent => e) /\
    seq <> [] /\ seq = GENLIST (\i. ai + SUC i) (LENGTH seq) /\
    (!e. MEM e seq <=> (a,e) IN FDOM blocks) /\
    (r = NONE <=> rest = NONE) /\
    (r = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))) /\
    (!e cid parent. a = (e,cid)::parent ==>
      ?q h b0 done_at_call ret. FLOOKUP calls (parent,e,cid) =
        SOME (q,h,b0,done_at_call,ent,ret))) /\
  (!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body_ent,cnt,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\ MEM e order /\ e <= N /\ h0 <= j /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\ lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\ bt.bb_label = bb.bb_label /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      EVERY inst_shape_ok bb.bb_instructions /\ LENGTH xs = LENGTH ys /\
      PERM sched (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) sched ys /\
      strict_dom_vars_defined sf hin /\ fn_reachable sf hin.vs_current_bb /\
      ctx_labels_bound C7 hin.vs_labels /\ ctx_labels_bound C8 hin.vs_labels /\ eval_phis hin bt.bb_instructions = OK sp /\
      EL h0 tr = ((a,e,(EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions).inst_id),tf,
        EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
        sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
      (if e = SUC inc then hin = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks (a,e-1) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
          ~hin.vs_halted) /\
      cnt <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
      (case body_ent of NONE => a = p /\ e = d /\ cnt = 0 /\ front = OK s /\
          FLOOKUP m (a,e) = SOME [] /\ FLOOKUP es (a,e) = SOME [] /\ FLOOKUP ks (a,e) = SOME []
        | SOME (be,hbe) => hbe <= j /\ be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
          dft_remaining_inv sf bb xs be /\ EL hbe tr = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
          FOLDR (dft_exec_cons (N-e) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
            (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
          (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE cnt ys) be = front) /\
          (closed ==> cnt = LENGTH ys /\ terminates front /\
            (!v. (front = OK v \/ (?ir. front = IntRet ir v)) ==> brest = SOME v.vs_gas_readings))) /\
      (e <> LAST order ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
      (e = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest)) /\
  (!a f g ai ent ord r rest.
    FLOOKUP acts a = SOME (f,g,ai,ent,ord,SOME r,SOME rest) ==>
    run_blocks (N-ai) C8 g ent = r) /\
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    ?sf tf inc entry order res nrest bb bt ps xs ys sched hin h0
      be hbe count front closed brest csf ctf child_order child_res child_rest c nm ops args.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
    h < j /\ EL h tr = ((a,e,cid),tf,c,b0) /\ LENGTH ps <= b0.vs_inst_idx /\
    get_instruction bt b0.vs_inst_idx = SOME c /\
    (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK
      (TAKE (b0.vs_inst_idx - LENGTH ps) ys) be = OK b0) /\
    done_at_call = TAKE (b0.vs_inst_idx - LENGTH ps) sched /\ ~MEM q done_at_call /\
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
    decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
    (case ret of
      NONE => child_res = NONE /\ MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
    | SOME (ir,child_out,caller_post) =>
        child_res = SOME (IntRet ir child_out) /\
        bind_outputs c.inst_outputs ir.iret_values
          (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
        h + SUC (LENGTH (trace_blocks ((e,cid)::a) e (N-e) C8 ctf child_entry)) <= j /\
        MEM q (TAKE count sched))) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order q call_h b0 done_at_call child_entry e cid a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done_at_call,child_entry,NONE) /\
      (EL k stk).cf_fn = tf /\ (EL k stk).cf_state = b0 /\ (EL k stk).cf_inst.inst_id = cid /\
      (EL k stk).cf_inst.inst_opcode = INVOKE /\ active_inst tf (EL k stk).cf_inst b0) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys sched hin h0 be hbe count
      q h b0 done_at_call child_entry cid e a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,NONE) /\
      done_at_call = TAKE count sched /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) /\
  (!a e bb bt ps xs ys sched hin h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count sched) ==>
      ?h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) ==>
  (?seq. FLOOKUP acts1 [] = SOME (rsf,rtf,0,rentry,seq,NONE,NONE)) /\
  (!a f g ai ent seq r rest. FLOOKUP acts1 a = SOME (f,g,ai,ent,seq,r,rest) ==>
    MEM f C7.ctx_functions /\ g = dft_fn f /\ dft_fn_rel f g /\
    ai = (case a of [] => 0 | (e,cid)::parent => e) /\
    seq <> [] /\ seq = GENLIST (\i. ai + SUC i) (LENGTH seq) /\
    (!e. MEM e seq <=> (a,e) IN FDOM blocks1) /\
    (r = NONE <=> rest = NONE) /\
    (r = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))) /\
    (!e cid parent. a = (e,cid)::parent ==>
      ?q h b0 done_at_call ret. FLOOKUP calls (parent,e,cid) =
        SOME (q,h,b0,done_at_call,ent,ret))) /\
  (!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks1 (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body_ent,cnt,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts1 a = SOME (sf,tf,inc,entry,order,res,nrest) /\ MEM e order /\ e <= N1 /\ h0 <= SUC j /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\ lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\ bt.bb_label = bb.bb_label /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      EVERY inst_shape_ok bb.bb_instructions /\ LENGTH xs = LENGTH ys /\
      PERM sched (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) sched ys /\
      strict_dom_vars_defined sf hin /\ fn_reachable sf hin.vs_current_bb /\
      ctx_labels_bound C7 hin.vs_labels /\ ctx_labels_bound C8 hin.vs_labels /\ eval_phis hin bt.bb_instructions = OK sp /\
      EL h0 tr1 = ((a,e,(EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions).inst_id),tf,
        EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
        sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
      (if e = SUC inc then hin = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks1 (a,e-1) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
          ~hin.vs_halted) /\
      cnt <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
      (case body_ent of NONE => a = p /\ e = SUC d /\ cnt = 0 /\ front = OK s1 /\
          FLOOKUP m1 (a,e) = SOME [] /\ FLOOKUP es1 (a,e) = SOME [] /\ FLOOKUP ks1 (a,e) = SOME []
        | SOME (be,hbe) => hbe <= SUC j /\ be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
          dft_remaining_inv sf bb xs be /\ EL hbe tr1 = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
          FOLDR (dft_exec_cons (N1-e) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
            (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
          (!F. N1 <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE cnt ys) be = front) /\
          (closed ==> cnt = LENGTH ys /\ terminates front /\
            (!v. (front = OK v \/ (?ir. front = IntRet ir v)) ==> brest = SOME v.vs_gas_readings))) /\
      (e <> LAST order ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
      (e = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest)) /\
  (?sf inc entry order bb bt ps xs ys sched hin h0 body_ent count.
    FLOOKUP acts1 p = SOME (sf,tf0,inc,entry,order,NONE,NONE) /\ LAST order = SUC d /\
    FLOOKUP blocks1 (p,SUC d) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body_ent,count,OK s1,F,NONE) /\
    lookup_block s1.vs_current_bb tf0.fn_blocks = SOME bt /\
    get_instruction bt s1.vs_inst_idx = SOME next /\
    (case body_ent of NONE => phi_prefix_length bt.bb_instructions <= s1.vs_inst_idx /\
      s1.vs_inst_idx < LENGTH ps /\ count = 0 /\
      FOLDR (dft_exec_cons (N1-SUC d) C8) OK
        (DROP (phi_prefix_length bt.bb_instructions) (TAKE s1.vs_inst_idx ps))
        ((case eval_phis hin bt.bb_instructions of OK sp => sp | other => hin)
         with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s1
    | SOME (be,hbe) => s1.vs_inst_idx = LENGTH ps + count /\ count < LENGTH ys /\ next = EL count ys)) /\
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    ?sf tf inc entry order res nrest bb bt ps xs ys sched hin h0
      be hbe count front closed brest csf ctf child_order child_res child_rest c nm ops args.
    FLOOKUP acts1 a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks1 (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
    h < SUC j /\ EL h tr1 = ((a,e,cid),tf,c,b0) /\ LENGTH ps <= b0.vs_inst_idx /\
    get_instruction bt b0.vs_inst_idx = SOME c /\
    (!F. N1 <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK
      (TAKE (b0.vs_inst_idx - LENGTH ps) ys) be = OK b0) /\
    done_at_call = TAKE (b0.vs_inst_idx - LENGTH ps) sched /\ ~MEM q done_at_call /\
    FLOOKUP acts1 ((e,cid)::a) = SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
    decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
    (case ret of
      NONE => child_res = NONE /\ MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
    | SOME (ir,child_out,caller_post) =>
        child_res = SOME (IntRet ir child_out) /\
        bind_outputs c.inst_outputs ir.iret_values
          (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
        h + SUC (LENGTH (trace_blocks ((e,cid)::a) e (N1-e) C8 ctf child_entry)) <= SUC j /\
        MEM q (TAKE count sched))) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order q call_h b0 done_at_call child_entry e cid a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts1 a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done_at_call,child_entry,NONE) /\
      (EL k stk).cf_fn = tf /\ (EL k stk).cf_state = b0 /\ (EL k stk).cf_inst.inst_id = cid /\
      (EL k stk).cf_inst.inst_opcode = INVOKE /\ active_inst tf (EL k stk).cf_inst b0) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys sched hin h0 be hbe count
      q h b0 done_at_call child_entry cid e a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts1 a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\
      FLOOKUP blocks1 (a,e) =
        SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,NONE) /\
      done_at_call = TAKE count sched /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) /\
  (!a e bb bt ps xs ys sched hin h0 be hbe count front closed brest.
    FLOOKUP blocks1 (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count sched) ==>
      ?h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) /\
  (!bb bt ps xs ys sched hin h0 be hbe count sf inc entry order.
    FLOOKUP acts1 p = SOME (sf,tf0,inc,entry,order,NONE,NONE) /\
    FLOOKUP blocks1 (p,SUC d) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,OK s1,F,NONE) /\
    inv_memory_observation next.inst_opcode ==>
    EL (EL count sched) xs = next /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL count sched) xs) /\
    (!q. q < EL count sched /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count sched)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!a f g ai ent seq r rest. FLOOKUP acts a = _ ==> _`
    (qspec_then `p` (drule_then strip_assume_tac)) >>
  `!e. (p,e) IN FDOM blocks ==> e <= d` by
    (drule_all_then strip_assume_tac visit_order_range >> simp[]) >>
  drule_all_then strip_assume_tac initialized_splice_frame >>
  `!a f g ai ent ord r rest. FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,rest) ==>
    FLOOKUP acts1 a = SOME (f,g,ai,ent,(if a = p then ord ++ [SUC d] else ord),r,rest) /\
    ord <> [] /\ ord = GENLIST (\i. ai + SUC i) (LENGTH ord)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!a f g ai ent seq r rest. FLOOKUP acts a = _ ==> MEM _ _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- (first_assum (drule_then ACCEPT_TAC)) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `cnt0 <= LENGTH ys0` by decide_tac >>
  `!a e bb bt ps xs ys sched hin h0 be hbe cnt front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,front,closed,brest) ==>
    ?cnt1 front1 closed1 brest1.
      FLOOKUP blocks1 (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt1,front1,closed1,brest1) /\
      cnt <= cnt1` by
    (rpt gen_tac >> disch_tac >>
     drule_all_then ACCEPT_TAC (Q.INST [`fresh` |->
       `(bb1,bt1,ps1,xs1,ys1,sch1,post,SUC j,body1,0,OK s1,F,NONE)`]
       (SPEC_ALL initialized_body_lookup_frame))) >>
  `!q. q < LENGTH xs0 /\ (EL q xs0).inst_opcode = INVOKE ==> MEM q (TAKE cnt0 sch0)` by
    (qpat_assum `!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
       FLOOKUP blocks _ = _ ==> _`
       (qspecl_then [`p`,`d`] (drule_then strip_assume_tac)) >>
     `sf = sf0 /\ tf = tf0` by
       (qpat_assum `FLOOKUP acts p = SOME (sf,tf,inc,entry,order,res,nrest)` mp_tac >>
        qpat_assum `FLOOKUP acts p = SOME (sf0,tf0,inc0,entry0,ord0,NONE,NONE)`
          (fn th => rewrite_tac[th,optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
        strip_tac >> simp[]) >>
     qpat_assum `sf = sf0` SUBST_ALL_TAC >>
     qpat_assum `tf = tf0` SUBST_ALL_TAC >>
     rpt gen_tac >> strip_tac >>
     drule_all_then ACCEPT_TAC (cj 2 dft_packet_block_terminator_invoke_coverage)) >>
  `(if s1.vs_inst_idx < LENGTH ps1 then body1 = NONE else
      body1 = SOME (s1,SUC j) /\ dft_remaining_inv sf0 bb1 xs1 s1)` by
    (qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then _ else _` mp_tac >>
     Cases_on `s1.vs_inst_idx < LENGTH ps1` >> gvs[]) >>
  drule_all_then strip_assume_tac initialized_visit_cursor >>
  drule_all_then (map_every assume_tac o CONJUNCTS) initialized_activation_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "rows" >>
  conj_tac >- suspend "cursor" >>
  conj_tac >- suspend "calls" >>
  conj_tac >- (
    mp_tac initialized_live_frames >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  conj_tac >- (
    mp_tac initialized_live_parents >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  conj_tac >- (
    mp_tac initialized_return_coverage >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  suspend "observation"
QED

Resume block_initialized_structure[rows]:
  mp_tac initialized_block_rows >> (impl_tac >- (
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac >- (
      Cases_on `body1` >- (
        simp[NoAsms] >>
        qpat_assum `case NONE of NONE => _ | SOME z => _`
          (strip_assume_tac o SRULE []) >>
        qpat_assum `s1.vs_inst_idx < LENGTH ps1` (fn lt =>
          qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then _ else _`
            (ACCEPT_TAC o SRULE [lt]))) >>
      PairCases_on `x` >> simp[NoAsms] >>
      qpat_assum `case SOME (x0,x1) of NONE => _ | SOME z => _`
        (strip_assume_tac o SRULE []) >>
      rpt conj_tac >> first_assum (fn th =>
        if is_forall (concl th) then qspecl_then [`N1-SUC d`,`C8`] ACCEPT_TAC th
        else ACCEPT_TAC th)) >>
    first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume block_initialized_structure[cursor]:
  mp_tac (cj 1 initialized_fresh_cursor) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume block_initialized_structure[calls]:
  mp_tac initialized_call_frame >> (impl_tac >- (
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac >- (
      rpt gen_tac >> disch_tac >>
      qpat_assum `!a f g ai ent seq r rest. FLOOKUP acts a = _ ==> MEM _ _ /\ _`
        (drule_then (fn th => ACCEPT_TAC (List.nth (CONJUNCTS th,7))))) >>
    first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume block_initialized_structure[observation]:
  mp_tac (cj 2 initialized_fresh_cursor) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Finalise block_initialized_structure
