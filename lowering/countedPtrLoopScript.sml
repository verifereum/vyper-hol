(* Finite counted loops compose pointer-safe headers and complete rounds.
   The invariant may measure a storage prefix in words of any element size. *)
Theory countedPtrLoop
Ancestors fragGasPathPtr venomState ptrDiscipline finite_map list arithmetic

Theorem counted_ptr_loop_remaining:
  !remaining i s G tn.
    (!j u H tt.
      j <= n /\ P j H tt u /\ u.vs_current_bb = hdr /\
      u.vs_inst_idx = 0 /\ ~u.vs_halted ==>
      ?H' tt' v.
        gas_path_ptr D 0 ctx func PG H tt u 0 H' tt' (OK v) /\
        P j H' tt' v /\ v.vs_current_bb = (if j<n then bodylbl else exit) /\
        v.vs_inst_idx = 0 /\ ~v.vs_halted /\
        (!x. ~MEM x scratch ==>
          lookup_var x v = lookup_var x u /\ FLOOKUP H' x = FLOOKUP H x /\
          op_taint tt' (Var x) = op_taint tt (Var x))) /\
    (!j u H tt.
      j < n /\ P j H tt u /\ u.vs_current_bb = bodylbl /\
      u.vs_inst_idx = 0 /\ ~u.vs_halted ==>
      ?H' tt' v.
        gas_path_ptr D 0 ctx func PG H tt u 0 H' tt' (OK v) /\
        P (SUC j) H' tt' v /\ v.vs_current_bb = hdr /\
        v.vs_inst_idx = 0 /\ ~v.vs_halted /\
        (!x. ~MEM x scratch ==>
          lookup_var x v = lookup_var x u /\ FLOOKUP H' x = FLOOKUP H x /\
          op_taint tt' (Var x) = op_taint tt (Var x))) /\
    i+remaining = n /\ P i G tn s /\ s.vs_current_bb = hdr /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u) /\
      P n Gf tf u /\ u.vs_current_bb = exit /\
      u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      (!x. ~MEM x scratch ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  Induct_on `remaining` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!j u H tt. j <= n /\ _ ==> _` (mk_asm "header") >>
  qpat_x_assum `!j u H tt. j < n /\ _ ==> _` (mk_asm "body") >>
  `i <= n` by decide_tac >>
  asm "header" drule_all >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac)
  >- (qexistsl_tac [`G1`, `tn1`, `s1`] >> gvs[]) >>
  `i<n /\ SUC i+remaining=n` by decide_tac >>
  `s1.vs_current_bb = bodylbl` by simp[] >>
  asm "body" drule_all >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qpat_x_assum `!i s G tn. (!j u H tt. _) /\ _ ==> _`
    (qspecl_then [`SUC i`, `s2`, `G2`, `tn2`] mp_tac) >>
  (impl_tac >- (asm "header" assume_tac >> asm "body" assume_tac >> simp[])) >>
  disch_then (qx_choosel_then [`Gf`, `tf`, `u`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tf`, `u`] >> simp[] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
    (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >>
  disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]
QED
