Theory dftPacketReturnAnchorState
Ancestors
  dftPacketReturnAnchorEntries dftPacketReturnAnchorCalls dftPacketRootedAlignment
  dftGasFromListTraceDefs finite_map list rich_list arithmetic

(* The inputs below are literal projections of the retained tables and the
   fixed old cut.  No aligned family or successful-source premise is assumed. *)
Theorem dft_packet_return_anchor_state:
  !(N:num) C7 C8 root_sf root_tf root_entry
    (acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab:(((num # num) list # num),bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num),(string # num) list list) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap)
    row_eval plan_eval call_setup rooted_eval p d cb ct cp cx cy cr ci ch cbody cc st
    a e bb bt ps xs ys rho hin h0 be hbe count front closed brest
    z0 cuts0 levels0 M0 E0.
  row_eval = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
       (gas_events_block (F-e) C owner
         (bb with bb_instructions :=
           TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
        FOLDR (dft_exec_cons (F-e) C) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\F C owner plan entry.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
      | other => (es,other)) ([],OK entry) plan) /\
  call_setup = (\C c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  rooted_eval = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (plan_eval F C sf.fn_name plan ent),
          case SND (plan_eval F C sf.fn_name plan ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => call_setup C c caller)
          | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  (?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)) /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    (!e. MEM e order <=> (a,e) IN FDOM blocks)) /\
  (!a e bb bt ps xs ys rho hin h0 body count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      MEM e order /\ bb.bb_instructions = ps ++ xs /\
      bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
      EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      eval_phis hin bt.bb_instructions = OK sp /\
      (if e = SUC inc then hin = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks (a,e-1) =
            SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
          ~hin.vs_halted) /\
      (closed <=> IS_SOME brest) /\
      (case body of NONE => a = p /\ e = d
       | SOME (be,hbe) =>
           FOLDR (dft_exec_cons (N-e) C8) OK
             (DROP (phi_prefix_length bt.bb_instructions) ps)
             (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be) /\
      (e <> LAST order ==> closed)) /\
  FLOOKUP blocks (p,d) =
    SOME (cb,ct,cp,cx,cy,cr,ci,ch,cbody,cc,OK st,F,NONE) /\
  FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM es_tab /\
  FDOM blocks = FDOM ks_tab /\
  (!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
    LENGTH ms = LENGTH xs /\
    (!sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      !F k kgss tail.
        N <= F /\ k <= LENGTH xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
        (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
        (?extra. FLAT (TAKE k ess) =
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
        (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
          u.vs_gas_readings = tail /\
          trace_gas (trace_block a e (F-e) C7 sf
            (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
            (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
          (!tail'.
            FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
              (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
              (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess))))) /\
  (!a e sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe count r8 u0 ms ess ks.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,r8,T,SOME u0) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
    !F. N <= F ==> !gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
      (?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
        (be with vs_gas_readings := gs ++ tail))) ==>
      (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
        residual_result tail r8 (FOLDR (dft_exec_cons (F-e) C7) OK xs
          (be with vs_gas_readings := gs ++ tail)))) /\
  (!a e cid q h b0 done child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) ==>
    ?sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe count front closed brest
      csf ctf child_order child_res child_rest nm ops args.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
      done = TAKE (b0.vs_inst_idx - LENGTH ps) rho /\ ~MEM q done /\
      FLOOKUP acts ((e,cid)::a) =
        SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
      decode_invoke (EL q xs) = SOME (nm,ops) /\
      lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
      (case ret of NONE => MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
       | SOME triple => MEM q (TAKE count rho))) /\
  (!k. k < LENGTH p ==>
    ?bb' bt' ps' xs' ys' rho' hin' h0' be' hbe' cnt'
      q' h' b0' done' child_entry' cid' e' a'.
      a' = DROP (SUC k) p /\ (e',cid') = EL k p /\
      FLOOKUP blocks (a',e') =
        SOME (bb',bt',ps',xs',ys',rho',hin',h0',SOME (be',hbe'),cnt',OK b0',F,NONE) /\
      FLOOKUP calls (a',e',cid') = SOME (q',h',b0',done',child_entry',NONE) /\
      done' = TAKE cnt' rho') /\
  (!a e cid q h b0 done child_entry ret bb bt ps xs ys rho hin h0 be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms ==>
    !F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
      (!callee argv. setup_callee callee argv (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee argv b0)) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  0 < LENGTH xs /\ z0 = DROP (phi_prefix_length bb.bb_instructions) ps /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts0 =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts0 = LENGTH levels0 /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts0 /\ EL i cuts0 = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts0 then ai = a /\ ei = e /\ qi = 0 /\ zi = z0
       else ?cid h b0 done child_entry ret.
         EL (SUC i) (MAP (\(aj,dj,ej,qj,zj). aj) cuts0) = (ei,cid)::ai /\
         FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done,child_entry,ret) /\
         qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
         zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
         EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
         (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done)) /\
      EL i levels0 =
        (sfi,MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],
         if SUC i = LENGTH cuts0 then NONE else SOME (EL qi xsi))) /\
  M0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts0) /\
  (!F gs tail ev v. N <= F /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs /\
    rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail) = (ev,OK v) ==>
    ev = E0) ==>
  !F g0 t ev v. N <= F /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 g0 /\
    rooted_eval F C7 levels0 (root_entry with vs_gas_readings := g0 ++ t) = (ev,OK v) ==>
    ev = E0 /\ v = (be with vs_gas_readings := t)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[] >>
  rename1 `N <= fuel` >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
    _ ==> LENGTH ms = LENGTH xs /\ _`
    (assume_tac o cj 1) >>
  `!i. ?entries rows slotss bb ps xs ys sp be depth q z ms sf.
    i < LENGTH cuts0 ==>
    (!ai ds ei qi zi. EL i cuts0 = (ai,ds,ei,qi,zi) ==>
      ?tf inc ent order res nrest bt rho hin h0 hbe count front closed brest later.
        FLOOKUP acts ai = SOME (sf,tf,inc,ent,order,res,nrest) /\
        FLOOKUP blocks (ai,ei) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
        HD entries = ent /\ LAST entries = hin /\ order = ds ++ ei::later /\
        depth = ei /\ q = qi /\ z = zi /\
        rows = MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds /\
        slotss = MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds /\
        ms = THE (FLOOKUP ms_tab (ai,ei))) /\
    EL i levels0 = (sf,rows ++ [(bb,depth,z)],
      if SUC i = LENGTH cuts0 then NONE else SOME (EL q xs)) /\
    LENGTH entries = SUC (LENGTH rows) /\ LENGTH slotss = LENGTH rows /\
    (!r. r < LENGTH rows ==>
      ?br er pr xr yr sr ber.
        EL r rows = (br,er,DROP (phi_prefix_length br.bb_instructions) br.bb_instructions) /\
        br.bb_instructions = pr ++ xr /\ EVERY (\x. is_pseudo x.inst_opcode) pr /\
        EVERY (\x. ~is_pseudo x.inst_opcode) xr /\ EVERY (\x. ~is_pseudo x.inst_opcode) yr /\
        eval_phis (EL r entries) (pr ++ yr) = OK sr /\
        FOLDR (dft_exec_cons (fuel-er) C8) OK (DROP (phi_prefix_length (pr ++ yr)) pr)
          (sr with vs_inst_idx := phi_prefix_length (pr ++ yr)) = OK ber /\
        (!vs rest. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL r slotss) vs ==>
          ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xr
            (ber with vs_gas_readings := vs ++ rest))) ==>
           residual_result rest (OK (EL (SUC r) entries))
            (FOLDR (dft_exec_cons (fuel-er) C7) OK xr
              (ber with vs_gas_readings := vs ++ rest))))) /\
    bb.bb_instructions = ps ++ xs /\ EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
    eval_phis (LAST entries) (ps ++ ys) = OK sp /\
    FOLDR (dft_exec_cons (fuel-depth) C8) OK (DROP (phi_prefix_length (ps ++ ys)) ps)
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    q < LENGTH xs /\ LENGTH ms = LENGTH xs /\
    (SUC i < LENGTH cuts0 ==>
      EVERY (\x. ~is_terminator x.inst_opcode) (TAKE q xs) /\
      ?b0 nm ops args ctf child_entry csf ctf' cinc corder cres crest.
        FLOOKUP acts (EL (SUC i) (MAP (\(ai,ds,ei,qi,zi). ai) cuts0)) =
          SOME (csf,ctf',cinc,child_entry,corder,cres,crest) /\
        (EL q xs).inst_opcode = INVOKE /\ decode_invoke (EL q xs) = SOME (nm,ops) /\
        lookup_function nm C8.ctx_functions = SOME ctf /\
        eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
        (!kgss rest caller.
          LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
          FOLDR (dft_exec_cons (fuel-depth) C7) OK (TAKE q xs)
            (be with vs_gas_readings := FLAT kgss ++ rest) = OK caller ==>
          caller.vs_gas_readings = rest /\
          (!op. MEM op (EL q xs).inst_operands ==> eval_operand op caller = eval_operand op b0) /\
          (!callee argv. setup_callee callee argv (caller with vs_gas_readings := b0.vs_gas_readings) =
            setup_callee callee argv b0)))` by
    (gen_tac >> Cases_on `i < LENGTH cuts0`
     >- (qabbrev_tac `ci0 = EL i cuts0` >> PairCases_on `ci0` >>
         `EL i cuts0 = (ci00,ci01,ci02,ci03,ci04)` by metis_tac[Abbr `ci0`] >>
         qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts0 /\ _ ==> _`
           (drule_all_then strip_assume_tac) >>
         `?bei0 bei1. bei = SOME (bei0,bei1)` by
           (Cases_on `SUC i = LENGTH cuts0`
            >- (qpat_x_assum `if SUC i = LENGTH cuts0 then _ else _` mp_tac >>
                asm_rewrite_tac[] >> disch_then strip_assume_tac >>
                qpat_x_assum `FLOOKUP blocks (ci00,ci02) = _` mp_tac >>
                qpat_x_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
                qpat_x_assum `ci00 = a` mp_tac >>
                qpat_x_assum `ci02 = e` mp_tac >>
                POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
            qpat_x_assum `if SUC i = LENGTH cuts0 then _ else _` mp_tac >>
            simp[] >> strip_tac >>
            qpat_assum `!a e cid q h b0 done child_entry ret. _ ==> _`
              (drule_then strip_assume_tac) >>
            qpat_x_assum `FLOOKUP blocks (ci00,ci02) = SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti)` mp_tac >>
            qpat_x_assum `FLOOKUP blocks (ci00,ci02) = _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
         qpat_x_assum `bei = SOME _` SUBST_ALL_TAC >>
         drule_all dft_packet_return_anchor_entries >>
         strip_tac >>
         qexistsl_tac [`entries`,`rows`,`slotss`,`bbi`,`psi`,`xsi`,`ysi`,`sp`,
           `bei0`,`ci02`,`ci03`,`ci04`,`THE (FLOOKUP ms_tab (ci00,ci02))`,`sfi`] >>
         asm_rewrite_tac[] >>
         conj_tac >- (rpt gen_tac >> pure_rewrite_tac[pairTheory.PAIR_EQ] >>
           disch_then (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) >>
           qexistsl_tac [`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bti`,`rhoi`,
             `ini`,`hi`,`bei1`,`counti`,`fronti`,`closedi`,`resti`,`later`] >> simp[]) >>
         `ci04 = DROP (phi_prefix_length (psi ++ xsi)) psi ++ TAKE ci03 xsi /\
          ci03 < LENGTH xsi` by
           (Cases_on `SUC i = LENGTH cuts0`
            >- (qpat_x_assum `if SUC i = LENGTH cuts0 then _ else _` mp_tac >>
                qpat_assum `SUC i = LENGTH cuts0` (fn th => rewrite_tac[th]) >> strip_tac >>
                map_every (fn pat => qpat_x_assum pat mp_tac)
                  [`FLOOKUP blocks (ci00,ci02) = _`,`FLOOKUP blocks (a,e) = _`,
                   `ci00 = a`,`ci02 = e`,`ci03 = 0`,`ci04 = z0`,
                   `z0 = _`,`0 < LENGTH xs`,`bbi.bb_instructions = psi ++ xsi`] >>
                POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
            qpat_x_assum `if SUC i = LENGTH cuts0 then _ else _` mp_tac >>
            asm_rewrite_tac[] >> strip_tac >> simp[]) >>
         asm_rewrite_tac[] >> strip_tac >>
         `SUC i <> LENGTH cuts0` by decide_tac >>
         qpat_x_assum `if SUC i = LENGTH cuts0 then _ else _` mp_tac >>
         asm_rewrite_tac[] >> strip_tac >>
         conj_tac >- (first_assum ACCEPT_TAC) >>
         qpat_assum `!a e cid q h b0 done child_entry ret. _ ==> _`
           (drule_then strip_assume_tac) >>
         qpat_x_assum `FLOOKUP blocks (ci00,ci02) = _` mp_tac >>
         asm_rewrite_tac[] >>
         pure_rewrite_tac[optionTheory.SOME_11,pairTheory.PAIR_EQ] >>
         disch_then (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) >>
         `?ms ess ks. FLOOKUP ms_tab (ci00,ci02) = SOME ms /\
           FLOOKUP es_tab (ci00,ci02) = SOME ess /\
           FLOOKUP ks_tab (ci00,ci02) = SOME ks` by
           (map_every (fn pat => qpat_x_assum pat mp_tac)
             [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,
              `FDOM blocks = FDOM ks_tab`,`FLOOKUP blocks (ci00,ci02) = _`] >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            gvs[flookup_thm]) >>
         qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks. _ ==> LENGTH ms = LENGTH xs /\ _`
           (qspecl_then [`ci00`,`ci02`] (drule_all_then strip_assume_tac)) >>
         qpat_x_assum `!sf tf inc entry order res nrest. _`
           (drule_then assume_tac) >>
         qpat_assum `!a e cid q h b0 done child_entry ret bb bt ps xs ys rho hin h0 be hbe count front closed brest ms. _`
           (qspecl_then [`ci00`,`ci02`,`cid`] (drule_then mp_tac)) >>
         disch_then drule >> disch_then drule >>
         disch_then assume_tac >>
         `!r. MEM r done ==> MEM r (TAKE count'' rho'')` by
           (drule dft_packet_return_anchor_done >> disch_then drule >>
            disch_then (qspec_then `p` mp_tac) >> simp[]) >>
         qexistsl_tac [`b0`,`nm`,`ops`,`args`,`ctf`,`child_entry`,`csf`,`ctf`,
           `ci02`,`child_order`,`child_res`,`child_rest`] >>
         asm_rewrite_tac[] >>
         rpt gen_tac >> strip_tac >>
         qpat_x_assum `LIST_REL _ (TAKE _ (THE _)) _`
           (assume_tac o REWRITE_RULE [optionTheory.THE_DEF]) >>
         reverse conj_tac
         >- (qpat_x_assum `!F kgss tail u. _` (drule_all_then strip_assume_tac) >> simp[]) >>
         qpat_x_assum `!F k kgss tail. _`
           (qspecl_then [`fuel`,`ci03`,`kgss`,`rest`] mp_tac) >>
         (impl_tac >- (simp[] >> metis_tac[])) >>
         strip_tac >> first_x_assum drule >>
         disch_then strip_assume_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum `!i. ?entries rows slotss bb ps xs ys sp be depth q z ms sf. _`
    mp_tac >>
  map_every (fn v => disch_then (qx_choose_then v mp_tac o CONV_RULE SKOLEM_CONV))
    [`entries`,`rows`,`slotss`,`bbs`,`pss`,`xss`,`yss`,`sps`,`bes`,`depths`,`qs`,`zs`,`mss`,`sfs`] >>
  disch_then (mk_asm "family") >>
  qabbrev_tac `segments = \i. FLAT (slotss i) ++ FLAT (TAKE (qs i) (mss i))` >>
  `cuts0 <> []` by
    (qpat_assum `MAP _ cuts0 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     `LENGTH cuts0 = SUC (LENGTH a)` by metis_tac[LENGTH_MAP,LENGTH_REVERSE,LENGTH_GENLIST] >>
     Cases_on `cuts0` >> gvs[]) >>
  asm "family" (assume_tac o cj 1) >>
  `HD (MAP (\(ai,ds,ei,qi,zi). ai) cuts0) = []` by
    (qpat_assum `MAP _ cuts0 = _` (fn th => pure_rewrite_tac[th]) >>
     simp[GENLIST,REVERSE_SNOC]) >>
  `HD (entries 0) = root_entry` by
    (qabbrev_tac `firstcut = EL 0 cuts0` >> PairCases_on `firstcut` >>
     `EL 0 cuts0 = (firstcut0,firstcut1,firstcut2,firstcut3,firstcut4)` by metis_tac[Abbr `firstcut`] >>
     `0 < LENGTH cuts0` by
       (qpat_assum `cuts0 <> []` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
        Cases_on `cuts0` >> simp[]) >>
     qpat_assum `!i. i < LENGTH cuts0 ==> !ai ds ei qi zi. _`
       (drule_then (drule_then strip_assume_tac)) >>
     `firstcut0 = []` by
       (qpat_x_assum `HD (MAP _ cuts0) = []` mp_tac >>
        qpat_x_assum `EL 0 cuts0 = _` mp_tac >>
        qpat_x_assum `0 < LENGTH cuts0` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `cuts0` >> simp[] >> metis_tac[pairTheory.FST]) >>
     qpat_x_assum `FLOOKUP acts firstcut0 = _` mp_tac >>
     qpat_x_assum `FLOOKUP acts [] = _` mp_tac >>
     qpat_x_assum `HD (entries 0) = _` mp_tac >>
     qpat_x_assum `firstcut0 = []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  `!i. SUC i < LENGTH cuts0 ==>
    ?b0 nm ops args ctf.
      (EL (qs i) (xss i)).inst_opcode = INVOKE /\
      decode_invoke (EL (qs i) (xss i)) = SOME (nm,ops) /\
      lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\
      setup_callee ctf args b0 = SOME (HD (entries (SUC i))) /\
      (!kgss rest caller.
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE (qs i) (mss i)) kgss /\
        FOLDR (dft_exec_cons (fuel-depths i) C7) OK (TAKE (qs i) (xss i))
          (bes i with vs_gas_readings := FLAT kgss ++ rest) = OK caller ==>
        caller.vs_gas_readings = rest /\
        (!op. MEM op (EL (qs i) (xss i)).inst_operands ==> eval_operand op caller = eval_operand op b0) /\
        (!callee argv. setup_callee callee argv (caller with vs_gas_readings := b0.vs_gas_readings) =
          setup_callee callee argv b0))` by
    (gen_tac >> strip_tac >>
     `i < LENGTH cuts0` by decide_tac >>
     asm "family" (qspec_then `i` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_x_assum `SUC i < LENGTH cuts0 ==> _` (drule_then strip_assume_tac) >>
     qabbrev_tac `nextcut = EL (SUC i) cuts0` >> PairCases_on `nextcut` >>
     `EL (SUC i) cuts0 = (nextcut0,nextcut1,nextcut2,nextcut3,nextcut4)` by metis_tac[Abbr `nextcut`] >>
     qpat_assum `!i. i < LENGTH cuts0 ==> !ai ds ei qi zi. _`
       (drule_then (drule_then strip_assume_tac)) >>
     `child_entry = HD (entries (SUC i))` by
       (map_every (fn pat => qpat_x_assum pat mp_tac)
         [`FLOOKUP acts (EL (SUC i) (MAP _ cuts0)) = _`,
          `FLOOKUP acts nextcut0 = _`,`HD (entries (SUC i)) = _`,
          `EL (SUC i) cuts0 = _`,`SUC i < LENGTH cuts0`] >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        gvs[EL_MAP]) >>
     qexistsl_tac [`b0`,`nm`,`ops`,`args`,`ctf`] >> asm_rewrite_tac[]) >>
  `MAP segments (COUNT_LIST (LENGTH cuts0)) =
    MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts0` by
    (irule LIST_EQ >> pure_rewrite_tac[LENGTH_MAP,LENGTH_COUNT_LIST] >>
     reverse conj_tac >- REFL_TAC >>
     gen_tac >> strip_tac >>
     qabbrev_tac `cut = EL x cuts0` >> PairCases_on `cut` >>
     `EL x cuts0 = (cut0,cut1,cut2,cut3,cut4)` by metis_tac[Abbr `cut`] >>
     qpat_assum `!i. i < LENGTH cuts0 ==> !ai ds ei qi zi. _`
       (drule_then (drule_then strip_assume_tac)) >>
     qpat_x_assum `Abbrev (segments = _)` mp_tac >>
     map_every (fn pat => qpat_x_assum pat mp_tac)
       [`slotss x = _`,`mss x = _`,`qs x = _`,`EL x cuts0 = _`,`x < LENGTH cuts0`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> simp[EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST,Abbr `segments`]) >>
  `M0 = FLAT (MAP segments (COUNT_LIST (LENGTH cuts0)))` by metis_tac[] >>
  qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = (ai,ds,ei,qi,zi) ==> _` (mk_asm "original_cuts") >>
  `!i ai ds ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = (ai,ds,ei,qi,zi) ==>
    ?tf inc ent order res nrest bt rho hin h0 hbe count front closed brest later.
      FLOOKUP acts ai = SOME (sfs i,tf,inc,ent,order,res,nrest) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbs i,bt,pss i,xss i,yss i,rho,hin,h0,SOME (bes i,hbe),count,front,closed,brest) /\
      HD (entries i) = ent /\ LAST (entries i) = hin /\ order = ds ++ ei::later /\
      depths i = ei /\ qs i = qi /\ zs i = zi /\
      rows i = MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
        DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
          (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds /\
      slotss i = MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds /\
      mss i = THE (FLOOKUP ms_tab (ai,ei))` by
    (rpt strip_tac >> qpat_assum `!i. i < LENGTH cuts0 ==> !ai ds ei qi zi. _`
      (drule_then (drule_then strip_assume_tac)) >> metis_tac[]) >>
  `?Mbefore gpre kgss anchor_input.
    Mbefore = FLAT (MAP segments (COUNT_LIST (LENGTH cuts0 - 1))) ++
      FLAT (slotss (LENGTH cuts0 - 1)) /\
    M0 = Mbefore ++ FLAT (TAKE (qs (LENGTH cuts0 - 1)) (mss (LENGTH cuts0 - 1))) /\
    g0 = gpre ++ FLAT kgss /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mbefore gpre /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE (qs (LENGTH cuts0 - 1)) (mss (LENGTH cuts0 - 1))) kgss /\
    anchor_input = (LAST (entries (LENGTH cuts0 - 1)) with vs_gas_readings := FLAT kgss ++ t) /\
    SND (row_eval fuel C7 (sfs (LENGTH cuts0 - 1)).fn_name
      (bbs (LENGTH cuts0 - 1),depths (LENGTH cuts0 - 1),zs (LENGTH cuts0 - 1)) anchor_input) = OK v /\
    FOLDR (dft_exec_cons (fuel-depths (LENGTH cuts0 - 1)) C7) OK
      (TAKE (qs (LENGTH cuts0 - 1)) (xss (LENGTH cuts0 - 1)))
      (bes (LENGTH cuts0 - 1) with vs_gas_readings := FLAT kgss ++ t) = OK v` by
    (irule (dft_packet_rooted_row_alignment |> Q.INST_TYPE
       [`:'b` |-> `:ir_function`, `:'c` |-> `:num`,
        `:'d` |-> `:exec_result option`, `:'e` |-> `:bytes32 list option`,
        `:'f` |-> `:basic_block`, `:'g` |-> `:num list`, `:'h` |-> `:num`,
        `:'i` |-> `:num`, `:'j` |-> `:num`, `:'k` |-> `:exec_result`,
        `:'l` |-> `:bool`, `:'m` |-> `:bytes32 list option`]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `row_eval = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> REFL_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`C8`,`ms_tab`,`acts`,`blocks`,`call_setup C7`,`ev`,`levels0`,
       `plan_eval fuel C7`,`pss`,`root_entry`,`rooted_eval fuel C7`,`rows`,`sps`,`yss`] >>
     conj_tac >- (qpat_assum `call_setup = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> REFL_TAC) >>
     conj_tac >- (qpat_assum `plan_eval = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> REFL_TAC) >>
     conj_tac >- (qpat_assum `rooted_eval = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> REFL_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (gen_tac >> strip_tac >>
         asm "family" (qspec_then `i` mp_tac) >>
         qpat_assum `!i. SUC i < LENGTH cuts0 ==> ?b0 nm ops args ctf. _`
           (qspec_then `i` mp_tac) >>
         simp[Abbr `segments`] >>
         qpat_x_assum `i < LENGTH cuts0` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `l = LENGTH cuts0 - 1` >>
  `l < LENGTH cuts0 /\ SUC l = LENGTH cuts0` by
    (simp[Abbr `l`, NoAsms] >>
     qpat_x_assum `cuts0 <> []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `cuts0` >> simp[]) >>
  qabbrev_tac `lastcut = EL l cuts0` >> PairCases_on `lastcut` >>
  `EL l cuts0 = (lastcut0,lastcut1,lastcut2,lastcut3,lastcut4)` by
    metis_tac[Abbr `lastcut`] >>
  asm "original_cuts" (drule_then (drule_then strip_assume_tac)) >>
  `lastcut0 = a /\ lastcut2 = e /\ lastcut3 = 0` by
    (qpat_assum `if SUC l = LENGTH cuts0 then _ else _` mp_tac >>
     qpat_assum `SUC l = LENGTH cuts0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = (ai,ds,ei,qi,zi) ==> _`
    (drule_then (drule_then strip_assume_tac)) >>
  `qs l = 0` by
    (qpat_assum `qs l = _` mp_tac >> qpat_assum `lastcut3 = 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `bes l = be` by
    (qpat_assum `FLOOKUP blocks (lastcut0,lastcut2) = SOME (bbs l,_)` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,_)` mp_tac >>
     qpat_assum `lastcut0 = a` mp_tac >> qpat_assum `lastcut2 = e` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `FOLDR _ OK (TAKE (qs l) _) _ = OK v` mp_tac >>
  qpat_x_assum `LIST_REL (LIST_REL _) (TAKE (qs l) _) kgss` mp_tac >>
  qpat_assum `qs l = 0` mp_tac >>
  qpat_assum `bes l = be` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  rpt strip_tac >> gvs[]
QED
