Theory dftPacketReturnAnchorEntries
Ancestors
  dftPacketEntryReplay dftIndexedExec dftGasFromListRestore dftGasToListReplay
  venomExecSemantics venomInst venomState finite_map list rich_list arithmetic

(* Only projections of the literal retained clauses are needed here. In
   particular the predecessor and NONE-body branches are retained, rather
   than assuming the existence of an already aligned entry sequence. *)
Theorem dft_packet_return_anchor_entries:
  !(N:num) C7 C8
    (acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (ms_tab:(((num # num) list # num),bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num),(string # num) list list) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap)
    p d cb ct cp cx cy cr ci ch cbody cc st
    fuel a sf tf inc entry order res nrest ds e later
    bb bt ps xs ys rho hin h0 be hbe count front closed brest.
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
    LENGTH ms = LENGTH xs) /\
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
  N <= fuel /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  order = ds ++ e::later /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) ==>
  ?entries rows slotss sp.
    entries = MAP (\f. case THE (FLOOKUP blocks (a,f)) of
      (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf) ds ++ [hin] /\
    rows = MAP (\f. (FST (THE (FLOOKUP blocks (a,f))),f,
      DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
        (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds /\
    slotss = MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds /\
    HD entries = entry /\ LAST entries = hin /\
    LENGTH entries = SUC (LENGTH rows) /\ LENGTH slotss = LENGTH rows /\
    (!r. r < LENGTH rows ==>
      ?br er pr xr yr sr ber.
        EL r rows = (br,er,DROP (phi_prefix_length br.bb_instructions) br.bb_instructions) /\
        br.bb_instructions = pr ++ xr /\
        EVERY (\i. is_pseudo i.inst_opcode) pr /\
        EVERY (\i. ~is_pseudo i.inst_opcode) xr /\
        EVERY (\i. ~is_pseudo i.inst_opcode) yr /\
        eval_phis (EL r entries) (pr ++ yr) = OK sr /\
        FOLDR (dft_exec_cons (fuel-er) C8) OK
          (DROP (phi_prefix_length (pr ++ yr)) pr)
          (sr with vs_inst_idx := phi_prefix_length (pr ++ yr)) = OK ber /\
        (!vs rest.
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL r slotss) vs ==>
          ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xr
             (ber with vs_gas_readings := vs ++ rest))) ==>
           residual_result rest (OK (EL (SUC r) entries))
             (FOLDR (dft_exec_cons (fuel-er) C7) OK xr
               (ber with vs_gas_readings := vs ++ rest))))) /\
    bb.bb_instructions = ps ++ xs /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    eval_phis hin (ps ++ ys) = OK sp /\
    FOLDR (dft_exec_cons (fuel-e) C8) OK (DROP (phi_prefix_length (ps ++ ys)) ps)
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
    LENGTH (THE (FLOOKUP ms_tab (a,e))) = LENGTH xs
Proof
  rpt gen_tac >> strip_tac >>
  `order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
   (!f. MEM f order <=> (a,f) IN FDOM blocks)` by
    (qpat_x_assum `!a sf tf inc entry order res nrest. _ ==> _` drule >> simp[]) >>
  `!f bf btf psf xsf ysf rhof inf hf bef cf rf closedf restf.
    FLOOKUP blocks (a,f) = SOME (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) ==>
    MEM f order /\ (f = SUC inc ==> inf = entry) /\
    (f <> SUC inc ==> ?pb pt pps pxs pys prho pin ph pbe pc pu.
      FLOOKUP blocks (a,f-1) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK inf,T,SOME pu)) /\
    (bef = NONE ==> ~closedf)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!a e bb bt ps xs ys rho hin h0 body count front closed brest. _ ==> _`
       (fn th => qpat_assum `FLOOKUP blocks (a,f) = _`
         (mp_then Any strip_assume_tac th)) >>
     qpat_x_assum `!a e bb bt ps xs ys rho hin h0 body count front closed brest. _ ==> _` kall_tac >>
     qpat_x_assum `!a sf tf inc entry order res nrest. _ ==> _` kall_tac >>
     qpat_x_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks. _ ==> _` kall_tac >>
     qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe count r8 u0 ms ess ks. _ ==> _` kall_tac >>
     gvs[] >> Cases_on `f = SUC inc` >> gvs[] >>
     Cases_on `bef` >> gvs[] >> metis_tac[flookup_thm]) >>
  `!f bf btf psf xsf ysf rhof inf hf bef hbef cf rf closedf restf.
    FLOOKUP blocks (a,f) = SOME (bf,btf,psf,xsf,ysf,rhof,inf,hf,SOME(bef,hbef),cf,rf,closedf,restf) ==>
    ?sp. bf.bb_instructions = psf ++ xsf /\
      EVERY (\i. is_pseudo i.inst_opcode) psf /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xsf /\
      EVERY (\i. ~is_pseudo i.inst_opcode) ysf /\
      eval_phis inf (psf ++ ysf) = OK sp /\
      (!F. FOLDR (dft_exec_cons (F-f) C8) OK (DROP (phi_prefix_length (psf ++ ysf)) psf)
        (sp with vs_inst_idx := phi_prefix_length (psf ++ ysf)) = OK bef) /\
      LENGTH (THE (FLOOKUP ms_tab (a,f))) = LENGTH xsf` by
    (rpt strip_tac >>
     qpat_assum `!a e bb bt ps xs ys rho hin h0 body count front closed brest. _ ==> _`
       (drule_then strip_assume_tac) >> gvs[] >>
     `?ms. FLOOKUP ms_tab (a,f) = SOME ms` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
     `?ess. FLOOKUP es_tab (a,f) = SOME ess` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
     `?ks. FLOOKUP ks_tab (a,f) = SOME ks` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
     qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks. _ ==> _`
       (drule_all_then assume_tac) >>
     simp[] >> gen_tac >>
     qpat_x_assum `FOLDR _ _ _ _ = OK bef` mp_tac >>
     `EVERY (\i. is_pseudo i.inst_opcode) (DROP (phi_prefix_length (psf ++ ysf)) psf)` by simp[EVERY_DROP] >>
     pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     metis_tac[dft_packet_pseudo_fuel]) >>
  `!f bf btf psf xsf ysf rhof inf hf bentry cf post rest.
    FLOOKUP blocks (a,f) = SOME (bf,btf,psf,xsf,ysf,rhof,inf,hf,bentry,cf,OK post,T,SOME rest) ==>
    ?bef hbef sp. bentry = SOME(bef,hbef) /\
      bf.bb_instructions = psf ++ xsf /\
      EVERY (\i. is_pseudo i.inst_opcode) psf /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xsf /\
      EVERY (\i. ~is_pseudo i.inst_opcode) ysf /\
      eval_phis inf (psf ++ ysf) = OK sp /\
      FOLDR (dft_exec_cons (fuel-f) C8) OK (DROP (phi_prefix_length (psf ++ ysf)) psf)
        (sp with vs_inst_idx := phi_prefix_length (psf ++ ysf)) = OK bef /\
      (!vs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
         (FLAT (THE (FLOOKUP ms_tab (a,f)))) vs ==>
       (?g. terminates (FOLDR (dft_exec_cons g C7) OK xsf (bef with vs_gas_readings := vs ++ tail))) ==>
       residual_result tail (OK post) (FOLDR (dft_exec_cons (fuel-f) C7) OK xsf
         (bef with vs_gas_readings := vs ++ tail)))` by
    (rpt strip_tac >>
     `bentry <> NONE` by metis_tac[] >>
     Cases_on `bentry` >> gvs[] >> PairCases_on `x` >>
     qpat_assum `!f bf btf psf xsf ysf rhof inf hf bef hbef cf rf closedf restf. _ ==> _`
       (drule_then strip_assume_tac) >>
     `?ms. FLOOKUP ms_tab (a,f) = SOME ms` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
     `?ess. FLOOKUP es_tab (a,f) = SOME ess` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
     `?ks. FLOOKUP ks_tab (a,f) = SOME ks` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
     qpat_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe count r8 u0 ms ess ks. _ ==> _`
       (fn th => qpat_assum `FLOOKUP blocks (a,f) = _`
         (mp_then Any mp_tac th)) >>
     disch_tac >> qexistsl [`x0`,`x1`,`sp`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!sf tf inc entry order res nrest ms ess ks F' gs tail. _ ==> residual_result _ _ _`
       (irule o SRULE []) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!r. r <= LENGTH ds ==>
    EL r (ds ++ [e]) = inc + SUC r /\ MEM (inc + SUC r) order` by
    (rpt strip_tac >>
     `r < LENGTH order` by gvs[] >>
     `EL r order = inc + SUC r` by
       (qpat_assum `order = GENLIST _ _` (fn th => once_rewrite_tac[th]) >> simp[EL_GENLIST]) >>
     `EL r (ds ++ [e]) = EL r order` by
       (gvs[EL_APPEND_EQN] >> Cases_on `r < LENGTH ds` >> gvs[]) >>
     metis_tac[EL_MEM]) >>
  qabbrev_tac `gin = (\f. case THE (FLOOKUP blocks (a,f)) of
    (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf)` >>
  `gin e = hin` by simp[Abbr `gin`] >>
  `!r. r <= LENGTH ds ==>
    EL r (MAP gin ds ++ [hin]) = gin (inc + SUC r)` by
    (rpt strip_tac >>
     `MAP gin ds ++ [hin] = MAP gin (ds ++ [e])` by simp[] >>
     qpat_x_assum `MAP gin ds ++ [hin] = _` (fn th => pure_once_rewrite_tac[th]) >> simp[EL_MAP]) >>
  `!f. MEM f order ==>
    ?bf btf psf xsf ysf rhof inf hf bef cf rf closedf restf.
      FLOOKUP blocks (a,f) = SOME (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) /\
      gin f = inf` by
    (rpt strip_tac >>
     `?v. FLOOKUP blocks (a,f) = SOME v` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
     PairCases_on `v` >> simp[Abbr `gin`] >> metis_tac[]) >>
  `gin (SUC inc) = entry` by
    (`MEM (SUC inc) order` by
       (qpat_x_assum `!r. r <= LENGTH ds ==> _ /\ _` (qspec_then `0` mp_tac) >> simp[ADD1]) >>
     qpat_x_assum `!f. MEM f order ==> _` drule >> strip_tac >>
     qpat_assum `!f bf btf psf xsf ysf rhof inf hf bef cf rf closedf restf. _ ==> _`
       (drule_then mp_tac) >> simp[]) >>
  qpat_assum `!f bf btf psf xsf ysf rhof inf hf bef hbef cf rf closedf restf. _ ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `!r. r <= LENGTH ds ==> EL r _ = gin _` (qspec_then `0` mp_tac) >> gvs[ADD1]) >>
  rpt strip_tac >>
  `SUC r <= LENGTH ds` by simp[] >>
  `MEM (inc + SUC (SUC r)) order` by metis_tac[] >>
  qpat_x_assum `!f. MEM f order ==> _` drule >> strip_tac >>
  qpat_x_assum `!f bf btf psf xsf ysf rhof inf hf bef cf rf closedf restf. _ ==> _`
    (fn th => qpat_assum `FLOOKUP blocks (a,inc + SUC (SUC r)) = _`
      (mp_then Any mp_tac th)) >> simp[] >> strip_tac >>
  `inc + SUC (SUC r) - 1 = inc + SUC r` by simp[] >>
  qpat_x_assum `FLOOKUP blocks (a,_ - 1) = _` mp_tac >> simp[] >> strip_tac >>
  qpat_assum `!f bf btf psf xsf ysf rhof inf hf bentry cf post rest. _ ==> _`
    (drule_then strip_assume_tac) >>
  `gin (inc + SUC r) = pin` by simp[Abbr `gin`] >>
  `EL r ds = inc + SUC r` by
    (qpat_x_assum `!r. r <= LENGTH ds ==> _ /\ _` (qspec_then `r` mp_tac) >> simp[EL_APPEND_EQN]) >>
  qexistsl [`pb`,`inc + SUC r`,`pps`,`pxs`,`pys`,`sp'`,`bef'`] >>
  simp[EL_MAP] >>
  qpat_x_assum `!vs tail. LIST_REL _ _ _ ==> _` mp_tac >> simp[]
QED
