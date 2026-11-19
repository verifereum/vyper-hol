Theory dftPacketCallKeyFreshness
Ancestors
  dftGasOracleDefs venomInst venomState frameGasEvents
  list rich_list finite_map arithmetic pred_set

(* Only the retained row equations are used.  Completed children are not
   removed from acts, so descent is bounded by the finite domain, not by the
   current live stack. *)
Theorem dft_packet_retained_key_domain:
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
    (ks_tab:(((num # num) list # num),gas_event list list) fmap).
    (!a sf tf inc entry order res rest f.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\ MEM f order ==>
      (a,f) IN FDOM blocks) /\
    (!a f bb bt ps xs ys rho hin h0 body count front closed brest.
      FLOOKUP blocks (a,f) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) ==>
      (case body of
        NONE => FLOOKUP ks_tab (a,f) = SOME []
      | SOME be => ?ks.
          FLOOKUP ks_tab (a,f) = SOME ks /\ LENGTH ks = LENGTH xs /\
          (!q. q < LENGTH xs ==>
            ((EL q xs).inst_opcode = GAS ==>
              EL q ks = [(a,f,(EL q xs).inst_id)]) /\
            ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
              EL q ks = []) /\
            ((EL q xs).inst_opcode = INVOKE ==>
              (case FLOOKUP calls (a,f,(EL q xs).inst_id) of
                NONE => EL q ks = []
              | SOME call => ?csf ctf cinc centry corder cres crest.
                  FLOOKUP acts ((f,(EL q xs).inst_id)::a) =
                    SOME (csf,ctf,cinc,centry,corder,cres,crest) /\
                  EL q ks = FLAT (MAP (\g. FLAT
                    (THE (FLOOKUP ks_tab (((f,(EL q xs).inst_id)::a),g)))) corder)))))) ==>
    !a sf tf inc entry order res rest b e cid.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\
      MEM (b,e,cid) (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) order)) ==>
      b IN FDOM acts
Proof
  rpt gen_tac >> strip_tac >>
  `!a sf tf inc entry order res rest b e cid.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\
    MEM (b,e,cid) (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) order)) ==>
    b = a \/ ?a' sf' tf' inc' entry' order' res' rest'.
      LENGTH a' = SUC (LENGTH a) /\
      FLOOKUP acts a' = SOME (sf',tf',inc',entry',order',res',rest') /\
      MEM (b,e,cid) (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a',f)))) order'))`
    by (rpt gen_tac >> strip_tac >> suspend "step") >>
  qabbrev_tac `B = SUC (MAX_SET (IMAGE LENGTH (FDOM acts)))` >>
  `!a v. FLOOKUP acts a = SOME v ==> LENGTH a < B` by
    (rpt strip_tac >>
     `LENGTH a <= MAX_SET (IMAGE LENGTH (FDOM acts))` by
       (irule in_max_set >> simp[] >>
        metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >> simp[Abbr `B`]) >>
  gen_tac >> measureInduct_on `B - LENGTH a` >> rpt strip_tac >>
  qpat_x_assum `!a sf tf inc entry order res rest b e cid. _`
    (drule_all_then strip_assume_tac)
  >- metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  `LENGTH a' < B` by metis_tac[] >> decide_tac
QED

Resume dft_packet_retained_key_domain[step]:
  qpat_x_assum `MEM (b,e,cid) _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_FLAT,MEM_MAP]) >>
  rename1 `MEM f order` >>
  `(a,f) IN FDOM blocks` by metis_tac[] >>
  `?bv. FLOOKUP blocks (a,f) = SOME bv` by
    metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
  PairCases_on `bv` >>
  qpat_x_assum `!a f bb bt ps xs ys rho hin h0 body count front closed brest. _`
    (drule_then mp_tac) >>
  Cases_on `bv8` >- (simp[] >> strip_tac >> gvs[]) >>
  simp[] >> strip_tac >> gvs[] >>
  `?q. q < LENGTH ks /\ MEM (b,e,cid) (EL q ks)` by
    metis_tac[MEM_FLAT,MEM_EL] >>
  qpat_x_assum `!q. q < LENGTH _ ==> _` (qspec_then `q` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `(EL q bv3).inst_opcode = GAS` >- gvs[] >>
  Cases_on `(EL q bv3).inst_opcode = INVOKE` >- (
    Cases_on `FLOOKUP calls (a,f,(EL q bv3).inst_id)` >- gvs[] >>
    gvs[] >> disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[]
QED

Finalise dft_packet_retained_key_domain

Theorem fresh_gas_keys_distinct:
  !xs b e. ALL_DISTINCT (MAP (\i. i.inst_id) xs) ==>
    ALL_DISTINCT (FLAT (MAP (\i.
      if i.inst_opcode = GAS then [(b,e,i.inst_id)] else []) xs))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = GAS` >> simp[] >>
  gvs[MEM_FLAT,MEM_MAP] >> gen_tac >> CCONTR_TAC >> gvs[] >>
  Cases_on `i.inst_opcode = GAS` >> gvs[]
QED

(* The provenance antecedent is precisely the conclusion of the domain
   boundary above.  It also gives row freshness by inclusion in its owning
   activation; root distinctness alone would not justify this projection. *)
Theorem dft_packet_call_key_freshness:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap) p d inst b xs.
    (!a sf tf inc entry order res rest c e cid.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\
      MEM (c,e,cid) (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) order)) ==>
      c IN FDOM acts) /\
    FLOOKUP acts b = NONE /\ b = (d,inst.inst_id)::p /\
    ALL_DISTINCT (MAP (\i. i.inst_id) xs) ==>
    ALL_DISTINCT (FLAT (MAP (\i.
      if i.inst_opcode = GAS then [(b,SUC d,i.inst_id)] else []) xs)) /\
    (!a sf tf inc entry order res rest cid.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) ==>
      ~MEM (b,SUC d,cid)
        (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) order))) /\
    (!a sf tf inc entry order res rest key.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\
      MEM key (FLAT (MAP (\i.
        if i.inst_opcode = GAS then [(b,SUC d,i.inst_id)] else []) xs)) ==>
      ~MEM key (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) order))) /\
    (!a sf tf inc entry order res rest f ks key.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\ MEM f order /\
      FLOOKUP ks_tab (a,f) = SOME ks /\
      MEM key (FLAT (MAP (\i.
        if i.inst_opcode = GAS then [(b,SUC d,i.inst_id)] else []) xs)) ==>
      ~MEM key (FLAT ks))
Proof
  rpt gen_tac >> strip_tac >>
  `!a sf tf inc entry order res rest cid.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) ==>
    ~MEM (b,SUC d,cid)
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) order))` by
    (rpt strip_tac >>
     `b IN FDOM acts` by metis_tac[] >>
     gvs[FLOOKUP_DEF]) >>
  conj_tac >- metis_tac[fresh_gas_keys_distinct] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `MEM key (FLAT (MAP _ xs))`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_FLAT,MEM_MAP]) >>
      Cases_on `i.inst_opcode = GAS` >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM key (FLAT (MAP (\g. FLAT (THE (FLOOKUP ks_tab (a,g)))) order))` by
    (simp[MEM_FLAT,MEM_MAP] >> qexists_tac `FLAT ks` >> simp[] >>
     qexists_tac `f` >> simp[]) >>
  qpat_x_assum `MEM key (FLAT (MAP _ xs))`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_FLAT,MEM_MAP]) >>
  Cases_on `i.inst_opcode = GAS` >> gvs[] >> metis_tac[]
QED

(* Insert the new keys into the FINAL aggregate of the replaced child.
   Existing keys of that child may occur in the replaced cell, but not in
   any surviving cell.  Only the inserted keys must be foreign to the old
   row. *)
Theorem dft_packet_call_key_row_replace:
  !rows q pre post fresh final.
    q < LENGTH rows /\ ALL_DISTINCT (FLAT rows) /\
    EL q rows = pre ++ post /\ final = pre ++ fresh ++ post /\
    ALL_DISTINCT fresh /\
    (!key. MEM key fresh ==> ~MEM key (FLAT rows)) ==>
    ALL_DISTINCT (FLAT (LUPDATE final q rows)) /\
    EL q (LUPDATE final q rows) = final /\
    (!r. r < LENGTH rows /\ r <> q ==>
      EL r (LUPDATE final q rows) = EL r rows /\
      (!key. MEM key final ==> ~MEM key (EL r rows)))
Proof
  Induct_on `rows` >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `q`
  >- (gvs[ALL_DISTINCT_APPEND,LUPDATE_def] >>
      conj_tac >- (simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
      qpat_x_assum `!q pre' post' fresh'. _` kall_tac >>
      rpt strip_tac >> Cases_on `r` >> gvs[] >> rpt strip_tac >>
      metis_tac[MEM_FLAT,MEM_EL]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  first_x_assum (qspecl_then [`n`,`pre`,`post`,`fresh`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  conj_tac
  >- (simp[LUPDATE_def,ALL_DISTINCT_APPEND] >> rpt strip_tac >>
      gvs[MEM_FLAT,MEM_LUPDATE] >> metis_tac[MEM_EL,MEM_APPEND]) >>
  simp[EL_LUPDATE] >> rpt strip_tac >> Cases_on `r` >> gvs[] >>
  metis_tac[MEM_FLAT,MEM_EL,MEM_APPEND]
QED
