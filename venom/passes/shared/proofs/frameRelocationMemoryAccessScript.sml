Theory frameRelocationMemoryAccess
Ancestors ptrDiscipline venomExecSemantics finite_map

(* Classify both read and write ranges before choosing target geometry. *)
Theorem resolved_memory_access:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  SND o_f rv = G /\ len <> 0 /\
  ((MEM (off,len) (source_memory_write_ranges inst s) /\
    mem_write_ops inst = SOME ops) \/
   (MEM (off,len) (source_memory_read_ranges inst s) /\
    mem_read_ops inst = SOME ops)) ==>
  ((off + len <= lo /\
    (!v. ops.iao_ofst = Var v ==> FLOOKUP rv v = NONE)) \/
   (?v token b sz. ops.iao_ofst = Var v /\
     FLOOKUP rv v = SOME (token,(b,sz)) /\
     b <= off /\ off + len <= b + sz))
Proof
  strip_tac >> (
  `lo < off + len \/ op_prov G ops.iao_ofst <> NONE ==>
   ?v b sz. ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (b,sz) /\
            b <= off /\ off + len <= b + sz` by
    (gvs[access_ok_def] >> metis_tac[]) >>
  Cases_on `lo < off + len \/ op_prov G ops.iao_ofst <> NONE`
  >- (first_x_assum drule >> strip_tac >> disj2_tac >>
      Cases_on `FLOOKUP rv v` >> gvs[FLOOKUP_o_f] >>
      PairCases_on `x` >> gvs[] >> metis_tac[]) >>
  disj1_tac >> gvs[] >> rpt strip_tac >>
  Cases_on `FLOOKUP rv v` >> gvs[op_prov_def, FLOOKUP_o_f])
QED
