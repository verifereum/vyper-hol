Theory dftPacketReturnOrderEnumeration
Ancestors
  venomExecSemantics venomState venomInst finite_map list rich_list arithmetic

(* Enumeration is fixed by the retained table, not by a choice of row witnesses. *)
Theorem dft_packet_return_order_enumerate:
  !(blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap) blocks' b order inc d entry N
    cbb cbt cps cxs cys crho cin ch0 cbe chbe cn s ir out.
  order <> [] /\ d = LAST order /\
  (!i. i < LENGTH order ==>
    EL i order = inc + SUC i /\
    (EL i order = d <=> SUC i = LENGTH order) /\
    (SUC i < LENGTH order ==> EL (SUC i) order - 1 = EL i order)) /\
  (!f. MEM f order ==>
    ?bb bt ps xs ys rho ini h0 body count front closed brest.
      FLOOKUP blocks (b,f) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,front,closed,brest) /\
      f <= N /\
      (if f = SUC inc then ini = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks (b,f-1) =
            SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK ini,T,SOME pu) /\
          ~ini.vs_halted) /\
      (f <> d ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
      (body = NONE ==> f = d) /\ (closed <=> IS_SOME brest)) /\
  FLOOKUP blocks (b,d) =
    SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks' (b,d) =
    SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings) /\
  (!f. MEM f order /\ f <> d ==> FLOOKUP blocks' (b,f) = FLOOKUP blocks (b,f)) ==>
  ?bbs bts entries.
    bbs = MAP (\f. FST (THE (FLOOKUP blocks' (b,f)))) order /\
    bts = MAP (\f. case THE (FLOOKUP blocks' (b,f)) of
      (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => btf) order /\
    entries = MAP (\f. case THE (FLOOKUP blocks' (b,f)) of
      (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf) order /\
    LENGTH bbs = LENGTH order /\ LENGTH bts = LENGTH order /\
    LENGTH entries = LENGTH order /\ HD entries = entry /\ LAST order <= N /\
    (!i. i < LENGTH order ==>
      (SUC i < LENGTH order ==> ~(EL (SUC i) entries).vs_halted) /\
      ?ps xs ys rho h0 be hbe count r8 rest.
        FLOOKUP blocks' (b,EL i order) =
          SOME (EL i bbs,EL i bts,ps,xs,ys,rho,EL i entries,h0,
            SOME (be,hbe),count,r8,T,SOME rest) /\
        r8 = (if SUC i < LENGTH order then OK (EL (SUC i) entries)
              else IntRet ir out) /\
        (SUC i = LENGTH order ==> rest = out.vs_gas_readings))
Proof
  rpt gen_tac >> strip_tac >>
  `0 < LENGTH order` by (Cases_on `order` >> gvs[]) >>
  `HD order = SUC inc` by
    (qpat_assum `!i. i < LENGTH order ==> _` (qspec_then `0` mp_tac) >> simp[EL] >> decide_tac) >>
  `MEM (HD order) order` by (Cases_on `order` >> gvs[]) >>
  simp[LENGTH_MAP, NoAsms] >>
  conj_tac
  >- (ASM_SIMP_TAC bool_ss [GSYM (cj 1 EL), EL_MAP, LENGTH_MAP] >>
      qpat_x_assum `!f. MEM f order ==> ?bb. _`
        (qspec_then `HD order` mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `HD order = d` >> gvs[] >>
      gvs[ADD1]) >>
  conj_tac
  >- (qpat_assum `!f. MEM f order ==> ?bb. _`
        (qspec_then `LAST order` mp_tac) >>
      (impl_tac >- simp[MEM_LAST_NOT_NIL]) >> strip_tac >> simp[]) >>
  qx_gen_tac `i` >> strip_tac >>
  `MEM (EL i order) order` by metis_tac[MEM_EL] >>
  qpat_assum `!i. i < LENGTH order ==> _`
    (qspec_then `i` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!f. MEM f order ==> ?bb. _`
    (qspec_then `EL i order` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `SUC i < LENGTH order`
  >- (`EL i order <> d` by decide_tac >>
      qpat_x_assum `if EL i order = SUC inc then _ else _` kall_tac >>
      qpat_assum `!i. i < LENGTH order ==> _`
        (qspec_then `SUC i` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
      `EL (SUC i) order <> SUC inc` by decide_tac >>
      `MEM (EL (SUC i) order) order` by metis_tac[MEM_EL] >>
      qpat_assum `!f. MEM f order ==> ?bb. _`
        (qspec_then `EL (SUC i) order` mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `!i. i < LENGTH order ==> _` kall_tac >>
      qpat_x_assum `!f. MEM f order ==> ?bb. _` kall_tac >>
      gvs[ADD1] >>
      `i < LENGTH order` by decide_tac >>
      `MEM (EL i order) order` by metis_tac[MEM_EL] >>
      rename1 `bdy <> NONE` >> Cases_on `bdy` >> gvs[] >>
      rename1 `FLOOKUP blocks (b,_) =
        SOME (_,_,_,_,_,_,_,_,SOME bp,_,OK _,T,_)` >>
      PairCases_on `bp` >>
      Cases_on `EL (SUC i) order = LAST order` >>
      gvs[EL_MAP,ADD1]) >>
  `SUC i = LENGTH order` by decide_tac >>
  `EL i order = d` by metis_tac[] >>
  qpat_x_assum `!i. i < LENGTH order ==> _` kall_tac >>
  qpat_x_assum `!f. MEM f order ==> ?bb. _` kall_tac >>
  gvs[EL_MAP]
QED
