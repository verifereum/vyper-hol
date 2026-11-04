(* Original-block first-emission probes. No claim about instructions in later
   blocks: expression joins may legitimately contain PHIs. *)
Theory compilerFirstEmission
Ancestors
  fragExec compileEnv emitHelper venomInst

Theorem first_emission_trans:
  cs_extends a b /\ cs_extends b c /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==>
     ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)) /\
  ((b.cs_blocks = c.cs_blocks /\ b.cs_current_bb = c.cs_current_bb /\
    b.cs_current_insts = c.cs_current_insts) \/
   (!fn. fn_has_code b c fn ==>
     ?bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (b.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)) ==>
  cs_extends a c /\
  ((a.cs_blocks = c.cs_blocks /\ a.cs_current_bb = c.cs_current_bb /\
    a.cs_current_insts = c.cs_current_insts) \/
   (!fn. fn_has_code a c fn ==>
     ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> disch_tac >> conj_tac
  >- metis_tac[cs_extends_trans] >>
  pop_assum strip_assume_tac >> gvs[] >>
  disj2_tac >> rpt strip_tac >>
  drule_all fn_has_code_split >> strip_tac >> metis_tac[]
QED

Theorem first_emission_preserved:
  cs_extends a b /\ cs_extends b c /\
  (!fn. fn_has_code a b fn ==>
    ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI) ==>
  !fn. fn_has_code a c fn ==>
    ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI
Proof
  metis_tac[fn_has_code_split]
QED

Theorem first_emission_return:
  comp_return x a = (y,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  simp[comp_return_def, cs_extends_refl] >> strip_tac >> gvs[cs_extends_refl]
QED

Theorem first_emission_fresh:
  fresh_var a = (x,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  simp[fresh_var_def] >> strip_tac >> gvs[] >>
  irule cs_extends_same_block >> simp[]
QED

Theorem first_emission_emit:
  emit i a = (x,b) /\ i.inst_opcode <> PHI ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==>
    ?bb h. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [h]) bb.bb_instructions /\ h.inst_opcode <> PHI)
Proof
  strip_tac >> conj_tac >- metis_tac[cs_extends_emit] >>
  gvs[emit_def, fn_has_code_def] >> rpt strip_tac >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem first_emission_empty_phi:
  a.cs_current_insts = [] /\ fn_has_code a z fn /\
  (!fn. fn_has_code a z fn ==>
    ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI) ==>
  !bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> first_x_assum drule >> strip_tac >> rpt strip_tac >> gvs[] >>
  Cases_on `bb.bb_instructions` >>
  gvs[venomExecSemanticsTheory.phi_prefix_length_def]
QED

(* Once the original block has its first instruction, later blocks need not
   satisfy any non-PHI restriction. Only code extension is required. *)
Theorem first_emission_prefix_run:
  cs_appends tail /\ i.inst_opcode <> PHI /\
  comp_ignore_bind (emit i) tail a = (x,z) ==>
  cs_extends a z /\
  (!fn. fn_has_code a z fn ==>
    ?bb h. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [h]) bb.bb_instructions /\ h.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `emit i a` >> rename1 `emit i a = (u,b)` >>
  simp_tac bool_ss [] >> strip_tac >>
  `cs_extends b z` by fs[cs_appends_def] >>
  drule_all first_emission_emit >> strip_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  ho_match_mp_tac first_emission_preserved >>
  simp[]
QED

Theorem first_emission_branch_before_phi:
  j.inst_opcode <> PHI /\ p.inst_opcode = PHI /\
  (do emit j; new_block lbl; emit p od) a = (x,z) ==>
  cs_extends a z /\
  (!fn. fn_has_code a z fn ==>
    ?bb h. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [h]) bb.bb_instructions /\ h.inst_opcode <> PHI)
Proof
  strip_tac >>
  irule (INST_TYPE [alpha |-> ``:unit``] first_emission_prefix_run) >>
    qexistsl_tac [`j`, `comp_ignore_bind (new_block lbl) (emit p)`, `x`] >>
  simp[] >> irule cs_appends_ignore_bind >> simp[cs_appends_prims]
QED

(* Compiler-facing monadic closure. The no-code alternative intentionally
   says nothing about counters or environment-valued results. *)
Theorem first_emission_bind:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!x b y c. k x b = (y,c) ==>
    cs_extends b c /\
    ((b.cs_blocks = c.cs_blocks /\ b.cs_current_bb = c.cs_current_bb /\
      b.cs_current_insts = c.cs_current_insts) \/
     (!fn. fn_has_code b c fn ==>
       ?bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (b.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a y c. comp_bind m k a = (y,c) ==>
    cs_extends a c /\
    ((a.cs_blocks = c.cs_blocks /\ a.cs_current_bb = c.cs_current_bb /\
      a.cs_current_insts = c.cs_current_insts) \/
     (!fn. fn_has_code a c fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac bool_ss [comp_bind_def] >>
  Cases_on `m a` >> rename1 `m a = (x,b)` >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  first_x_assum drule >> disch_then assume_tac >>
  first_x_assum drule >> disch_then assume_tac >>
  ho_match_mp_tac first_emission_trans >> simp[]
QED

Theorem first_emission_get:
  comp_get a = (x,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  simp[comp_get_def] >> strip_tac >> gvs[cs_extends_refl]
QED

Theorem first_emission_counters:
  (!s a x b. fresh_label s a = (x,b) ==>
    cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
    a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) /\
  (!a x b. fresh_id a = (x,b) ==>
    cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
    a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts)
Proof
  conj_tac >> rpt gen_tac >>
  simp[fresh_label_def, fresh_id_def] >> strip_tac >> gvs[] >>
  irule cs_extends_same_block >> simp[]
QED

Theorem first_emission_emit_helpers:
  (!opc ops outs a x b. opc <> PHI /\ emit_inst opc ops outs a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)) /\
  (!opc ops a x b. opc <> PHI /\ emit_void opc ops a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)) /\
  (!opc ops a x b. opc <> PHI /\ emit_op opc ops a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[emit_inst_def, emit_void_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  (conj_tac >- (irule cs_extends_same_block >> simp[])) >>
  simp[fn_has_code_def] >> rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `isPREFIX (_ ++ [i]) bb.bb_instructions` >>
  qexistsl_tac [`bb`, `i`] >> simp[Abbr `i`, mk_inst_def]
QED

Theorem first_emission_ignore_bind:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!b y c. n b = (y,c) ==>
    cs_extends b c /\
    ((b.cs_blocks = c.cs_blocks /\ b.cs_current_bb = c.cs_current_bb /\
      b.cs_current_insts = c.cs_current_insts) \/
     (!fn. fn_has_code b c fn ==>
       ?bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (b.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a y c. comp_ignore_bind m n a = (y,c) ==>
    cs_extends a c /\
    ((a.cs_blocks = c.cs_blocks /\ a.cs_current_bb = c.cs_current_bb /\
      a.cs_current_insts = c.cs_current_insts) \/
     (!fn. fn_has_code a c fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  ho_match_mp_tac first_emission_bind >> simp[]
QED

(* Generic code-preserving operations are FE even when they change counters. *)
Theorem first_emission_no_code:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
    a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) ==>
  !a x b. m a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  metis_tac[]
QED

Theorem first_emission_strong:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)) ==>
  !a x b. m a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  metis_tac[]
QED

(* Once a prefix emits, the suffix only needs to extend the code ledger. *)
Theorem first_emission_strong_bind:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)) /\
  (!x b y c. k x b = (y,c) ==> cs_extends b c) ==>
  !a y c. comp_bind m k a = (y,c) ==>
    cs_extends a c /\
    (!fn. fn_has_code a c fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac bool_ss [comp_bind_def] >>
  Cases_on `m a` >> rename1 `m a = (x,b)` >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  first_x_assum drule >> disch_then assume_tac >>
  first_x_assum drule >> disch_then strip_assume_tac >>
  (conj_tac >- metis_tac[cs_extends_trans]) >>
  ho_match_mp_tac first_emission_preserved >> simp[]
QED

Theorem first_emission_strong_ignore_bind:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)) /\
  (!b y c. n b = (y,c) ==> cs_extends b c) ==>
  !a y c. comp_ignore_bind m n a = (y,c) ==>
    cs_extends a c /\
    (!fn. fn_has_code a c fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  ho_match_mp_tac first_emission_strong_bind >> simp[]
QED

(* Explicit-state syntax companion: keep compiler calls opaque at pair lets. *)
Theorem state_pair_let_bind:
  pair$UNCURRY k (m a) = comp_bind m k a
Proof
  Cases_on `m a` >> simp[comp_bind_def]
QED

Theorem first_emission_pair_let:
  (!a v b. m a = (v,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!v b w c. k v b = (w,c) ==>
    cs_extends b c /\
    ((b.cs_blocks = c.cs_blocks /\ b.cs_current_bb = c.cs_current_bb /\
      b.cs_current_insts = c.cs_current_insts) \/
     (!fn. fn_has_code b c fn ==>
       ?bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (b.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a w c. pair$UNCURRY k (m a) = (w,c) ==>
    cs_extends a c /\
    ((a.cs_blocks = c.cs_blocks /\ a.cs_current_bb = c.cs_current_bb /\
      a.cs_current_insts = c.cs_current_insts) \/
     (!fn. fn_has_code a c fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rewrite_tac[state_pair_let_bind] >> strip_tac >>
  ho_match_mp_tac first_emission_bind >> conj_tac >> first_assum ACCEPT_TAC
QED
