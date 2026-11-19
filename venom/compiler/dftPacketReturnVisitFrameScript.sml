Theory dftPacketReturnVisitFrame
Ancestors
  dftPacketReturnLiveFrame dftIndexedExec dftGasFromListTraceDefs
  venomExecSemantics finite_map list rich_list arithmetic

(* The pending call for the popped activation has a unique key. All other
   call visits keep the setup, visit, and (where present) return certificate. *)
Theorem dft_packet_return_call_suffix[local]:
  ((v,id)::parent) <> (e,cid)::a ==>
  (MEM ((v,id)::parent) (GENLIST (\i. DROP i ((e,cid)::a))
    (SUC (SUC (LENGTH a)))) <=>
   MEM ((v,id)::parent) (GENLIST (\i. DROP i a) (SUC (LENGTH a))))
Proof
  simp[SRULE [] dft_packet_return_suffixes] >> metis_tac[]
QED

Theorem mem_take_bound_mono[local]:
  n <= m /\ MEM x (TAKE n xs) ==> MEM x (TAKE m xs)
Proof
  metis_tac[MEM_TAKE,TAKE_TAKE_T]
QED

Theorem dft_packet_return_visit_frame:
  b = (e,cid)::a /\
  FLOOKUP (acts : ((num # num) list,
    ir_function # ir_function # num # venom_state # num list #
    exec_result option # bytes32 list option) fmap) b =
    SOME (csf,ctf,e,ent,ord,NONE,NONE) /\
  FLOOKUP (blocks : (((num # num) list # num),
    basic_block # basic_block # instruction list # instruction list #
    instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (b,d) = SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME (pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),pn,OK b0,F,NONE) /\
  FLOOKUP (calls : (gas_event, num # num # venom_state # num list # venom_state #
    (internal_return # venom_state # venom_state) option) fmap) (a,e,cid) =
    SOME (q,h,b0,done,ent,NONE) /\
  acts' = acts |+ (b,(csf,ctf,e,ent,ord,SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
  blocks' = blocks |+
    ((b,d),(cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings)) |+
    ((a,e),(pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
      OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  calls' = calls |+ ((a,e,cid),(q,h,b0,done,ent,SOME (ir,out,post))) /\
  cn <= LENGTH cys /\
  q = EL pn prho /\ pn < LENGTH prho /\
  bind_outputs (EL q pxs).inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state b0 out)) = SOME post /\
  h + SUC (LENGTH (trace_blocks b e (N-e) C8 ctf ent)) <= SUC j /\
  (!x v id k t z done entry ret.
    FLOOKUP calls (x,v,id) = SOME (k,t,z,done,entry,ret) ==>
    ?sf tf inc inp order res nrest bb bt ps xs ys rho ini h0
     be hbe count front closed brest csf ctf cord cres crest c nm ops args.
      FLOOKUP acts x = SOME (sf,tf,inc,inp,order,res,nrest) /\
      FLOOKUP blocks (x,v) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
      k < LENGTH xs /\ c = EL k xs /\ c.inst_id = id /\ c.inst_opcode = INVOKE /\
      t < j /\ EL t (trace_blocks [] 0 N C8 root_tf root_entry) = ((x,v,id),tf,c,z) /\
      LENGTH ps <= z.vs_inst_idx /\ get_instruction bt z.vs_inst_idx = SOME c /\
      (!F. N <= F ==> FOLDR (dft_exec_cons (F-v) C8) OK
        (TAKE (z.vs_inst_idx - LENGTH ps) ys) be = OK z) /\
      done = TAKE (z.vs_inst_idx - LENGTH ps) rho /\ ~MEM k done /\
      FLOOKUP acts ((v,id)::x) = SOME (csf,ctf,v,entry,cord,cres,crest) /\
      decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops z = SOME args /\ setup_callee ctf args z = SOME entry /\
      (case ret of
        NONE => cres = NONE /\ MEM ((v,id)::x) (GENLIST (\i. DROP i b) (SUC (LENGTH b)))
      | SOME (r,u,post) => cres = SOME (IntRet r u) /\
          bind_outputs c.inst_outputs r.iret_values
            (adopt_return_fmp r (merge_callee_state z u)) = SOME post /\
          t + SUC (LENGTH (trace_blocks ((v,id)::x) v (N-v) C8 ctf entry)) <= j /\
          MEM k (TAKE count rho))) ==>
  (!x v id k t z done entry ret.
    FLOOKUP calls' (x,v,id) = SOME (k,t,z,done,entry,ret) ==>
    ?sf tf inc inp order res nrest bb bt ps xs ys rho ini h0
     be hbe count front closed brest csf ctf cord cres crest c nm ops args.
      FLOOKUP acts' x = SOME (sf,tf,inc,inp,order,res,nrest) /\
      FLOOKUP blocks' (x,v) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
      k < LENGTH xs /\ c = EL k xs /\ c.inst_id = id /\ c.inst_opcode = INVOKE /\
      t < SUC j /\ EL t (trace_blocks [] 0 N C8 root_tf root_entry) = ((x,v,id),tf,c,z) /\
      LENGTH ps <= z.vs_inst_idx /\ get_instruction bt z.vs_inst_idx = SOME c /\
      (!F. N <= F ==> FOLDR (dft_exec_cons (F-v) C8) OK
        (TAKE (z.vs_inst_idx - LENGTH ps) ys) be = OK z) /\
      done = TAKE (z.vs_inst_idx - LENGTH ps) rho /\ ~MEM k done /\
      FLOOKUP acts' ((v,id)::x) = SOME (csf,ctf,v,entry,cord,cres,crest) /\
      decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops z = SOME args /\ setup_callee ctf args z = SOME entry /\
      (case ret of
        NONE => cres = NONE /\ MEM ((v,id)::x) (GENLIST (\i. DROP i a) (SUC (LENGTH a)))
      | SOME (r,u,post) => cres = SOME (IntRet r u) /\
          bind_outputs c.inst_outputs r.iret_values
            (adopt_return_fmp r (merge_callee_state z u)) = SOME post /\
          t + SUC (LENGTH (trace_blocks ((v,id)::x) v (N-v) C8 ctf entry)) <= SUC j /\
          MEM k (TAKE count rho)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> disch_tac >>
  rename1 `FLOOKUP calls' (x,v,id) = SOME (k,t,z,ds,en,ret)` >>
  `a <> b` by (strip_tac >> gvs[]) >>
  Cases_on `(x,v,id) = (a,e,cid)`
  >- (gvs[FLOOKUP_UPDATE] >>
      qpat_x_assum `!x v id k t z done entry ret. _` drule >>
      strip_tac >> gvs[] >>
      rpt (goal_assum $ drule_at Any) >>
      simp[TAKE_SUC_BY_TAKE,MEM_SNOC] >> decide_tac) >>
  `FLOOKUP calls (x,v,id) = SOME (k,t,z,ds,en,ret)` by gvs[FLOOKUP_UPDATE] >>
  qpat_x_assum `!x v id k t z done entry ret. _` drule >> strip_tac >>
  `((v,id)::x) <> b` by gvs[] >>
  Cases_on `(x,v) = (a,e)`
  >- (gvs[FLOOKUP_UPDATE] >> Cases_on `ret` >>
      gvs[dft_packet_return_call_suffix, AllCaseEqs()] >>
      rpt (goal_assum $ drule_at Any) >>
      rpt (split_pair_case_tac >> gvs[]) >>
      simp[TAKE_SUC_BY_TAKE,MEM_SNOC] >> decide_tac) >>
  Cases_on `(x,v) = (b,d)`
  >- (gvs[FLOOKUP_UPDATE] >> Cases_on `ret` >>
      gvs[dft_packet_return_call_suffix, AllCaseEqs()] >>
      rpt (goal_assum $ drule_at Any) >>
      rpt (split_pair_case_tac >> gvs[]) >>
      irule mem_take_bound_mono >> qexists_tac `cn` >> simp[]) >>
  Cases_on `x = b` >> gvs[FLOOKUP_UPDATE] >> Cases_on `ret` >>
  gvs[dft_packet_return_call_suffix, AllCaseEqs()] >>
  rpt (goal_assum $ drule_at Any) >>
  rpt (split_pair_case_tac >> gvs[]) >> simp[] >> metis_tac[]
QED
