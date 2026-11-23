(* Classify visits along the executed finish, not the compiler's ID range. *)
Theory entryCreateIfExpFinishVisit
Ancestors
  entryCreateFocusSpec dftGasFromListTraceDefs venomInst relation pair

Triviality ifexp_finish_native_not_at_exit:
  create_operand_native_step sx z E ctx fn p (d,k,u,left) (d',k',v,right) ==>
  ~create_operand_at z u
Proof
  rw[create_operand_native_step_def,create_operand_fetch_def,LET_THM]
QED

Triviality ifexp_finish_native_positions:
  (!d k u left d' k' v right.
    create_operand_native_step sx z E ctx fn p (d,k,u,left) (d',k',v,right) ==>
    (create_operand_at sx u ==> create_operand_at sy v) /\
    (create_operand_at sy u ==> create_operand_at z v)) ==>
  !x y. RTC (create_operand_native_step sx z E ctx fn p) x y ==>
    create_operand_at sx (FST (SND (SND x))) ==>
    create_operand_at sx (FST (SND (SND y))) \/
    create_operand_at sy (FST (SND (SND y))) \/
    create_operand_at z (FST (SND (SND y)))
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> conj_tac
  >- simp[] >>
  simp_tac bool_ss [FORALL_PROD,FST,SND] >> rpt strip_tac >>
  metis_tac[ifexp_finish_native_not_at_exit]
QED

Theorem ifexp_two_pc_finish_visit:
  (!u inst. create_operand_fetch sx z fn u inst ==>
    (create_operand_at sx u ==> inst.inst_opcode = ASSIGN) /\
    (create_operand_at sy u ==> inst.inst_opcode = JMP)) /\
  (!d0 k0 u left d1 k1 v right.
    create_operand_native_step sx z E ctx fn p (d0,k0,u,left) (d1,k1,v,right) ==>
    (create_operand_at sx u ==> create_operand_at sy v) /\
    (create_operand_at sy u ==> create_operand_at z v)) /\
  create_interior_visit sx z E ctx fn (p,d,k) s (before,hit,after) ==>
  ?d' k' u inst.
    RTC (create_operand_native_step sx z E ctx fn p) (d,k,s,[]) (d',k',u,before) /\
    create_operand_fetch sx z fn u inst /\
    hit = ((p,d',inst.inst_id),fn,inst,u) /\
    ((create_operand_at sx u /\ inst.inst_opcode = ASSIGN) \/
     (create_operand_at sy u /\ inst.inst_opcode = JMP))
Proof
  simp_tac bool_ss [create_interior_visit_def,LET_THM] >>
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (REPEAT_TCL CHOOSE_THEN mp_tac) >>
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >> disch_tac >>
  rename1 `RTC (create_operand_native_step sx z E ctx fn p)
                (d,k,s,[]) (d',k',u,left)` >>
  rename1 `create_operand_fetch sx z fn u inst` >>
  drule_then drule ifexp_finish_native_positions >> simp[] >>
  disch_tac >>
  `~create_operand_at z u` by metis_tac[create_operand_fetch_def] >>
  `(create_operand_at sx u /\ inst.inst_opcode = ASSIGN) \/
   (create_operand_at sy u /\ inst.inst_opcode = JMP)` by metis_tac[] >>
  `trace_step p d' k' ctx fn inst u = []` by
    (irule trace_step_noninvoke >> simp[]) >>
  gvs[] >> metis_tac[]
QED
