Theory dftPacketPseudoKeyFreshness
Ancestors
  dftGasOracleDefs venomInst venomState frameGasEvents
  list rich_list finite_map arithmetic pred_set alist sorting

(* Retained key provenance is independent of the live stack.  The row
   equations below are the key projections of the retained table clauses. *)
Theorem dft_packet_retained_key_origin_clauses:
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
    (ks_tab:(((num # num) list # num),gas_event list list) fmap) AK.
    AK = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
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
      MEM (b,e,cid) (AK a) ==>
      ?bb bt ps xs ys rho hin h0 be hbe count front closed brest q.
        FLOOKUP blocks (b,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
        q < LENGTH xs /\ (EL q xs).inst_opcode = GAS /\ (EL q xs).inst_id = cid
Proof
  rpt gen_tac >> strip_tac >>
  `!a sf tf inc entry order res rest b e cid.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\
    MEM (b,e,cid) (AK a) ==>
    (?bb bt ps xs ys rho hin h0 be hbe count front closed brest q.
      FLOOKUP blocks (b,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ (EL q xs).inst_opcode = GAS /\ (EL q xs).inst_id = cid) \/
    (?a' sf' tf' inc' entry' order' res' rest'.
      LENGTH a' = SUC (LENGTH a) /\
      FLOOKUP acts a' = SOME (sf',tf',inc',entry',order',res',rest') /\
      MEM (b,e,cid) (AK a'))` by
    (rpt gen_tac >> strip_tac >> suspend "step") >>
  qabbrev_tac `B = SUC (MAX_SET (IMAGE LENGTH (FDOM acts)))` >>
  `!a v. FLOOKUP acts a = SOME v ==> LENGTH a < B` by
    (rpt strip_tac >>
     `LENGTH a <= MAX_SET (IMAGE LENGTH (FDOM acts))` by
       (irule in_max_set >> simp[] >>
        metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >> simp[Abbr `B`]) >>
  gen_tac >> measureInduct_on `B - LENGTH a` >> rpt strip_tac >>
  qpat_x_assum `!a sf tf inc entry order res rest b e cid. _`
    (drule_all_then strip_assume_tac)
  >- (goal_assum (drule_at Any) >> simp[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  `LENGTH a' < B` by metis_tac[] >> decide_tac
QED

Resume dft_packet_retained_key_origin_clauses[step]:
  `AK a = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) order)` by simp[] >>
  qpat_assum `AK a = _` (fn th =>
    qpat_x_assum `MEM (b,e,cid) _`
      (strip_assume_tac o SRULE [th,MEM_FLAT,MEM_MAP])) >>
  rename1 `MEM f order` >>
  `(a,f) IN FDOM blocks` by metis_tac[] >>
  `?bv. FLOOKUP blocks (a,f) = SOME bv` by
    metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
  PairCases_on `bv` >>
  qpat_x_assum `!a f bb bt ps xs ys rho hin h0 body count front closed brest. _`
    (drule_then mp_tac) >>
  Cases_on `bv8` >- (simp[] >> strip_tac >> gvs[]) >>
  PairCases_on `x` >> simp[] >> strip_tac >> gvs[] >>
  `?q. q < LENGTH ks /\ MEM (b,e,cid) (EL q ks)` by
    metis_tac[MEM_FLAT,MEM_EL] >>
  qpat_x_assum `!q. q < LENGTH _ ==> _` (qspec_then `q` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `(EL q bv3).inst_opcode = GAS`
  >- (gvs[] >> disj1_tac >> goal_assum (drule_at Any) >> metis_tac[]) >>
  Cases_on `(EL q bv3).inst_opcode = INVOKE`
  >- ((Cases_on `FLOOKUP calls (a,f,(EL q bv3).inst_id)` >- gvs[] >>
      gvs[] >> disj2_tac >> goal_assum (drule_at Any) >>
      gvs[MEM_FLAT,MEM_MAP] >> (metis_tac[MEM_FLAT, MEM_MAP]))) >>
  gvs[]
QED

Finalise dft_packet_retained_key_origin_clauses
