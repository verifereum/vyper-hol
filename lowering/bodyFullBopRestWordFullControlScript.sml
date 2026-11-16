(* Common-endpoint membership search, independent of the horizon index type. *)
Theory bodyFullBopRestWordFullControl
Ancestors bodyFullBopRestWordBoundedControl rich_list venomExecSemantics
  fragGasOriginPtrLoop bodyPtrBopInLoopContract bodyFullBopRestWordControl
  venomState finite_map

Theorem rest_word_membership_segment_full_horizon[local]:
  !i s Gs Ts.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  (!i s Gs Ts. i <= LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = (if i = LENGTH ws then
        fresh_label_output "in_exit" (sa.cs_next_label+5) else
        fresh_label_output "in_body" (sa.cs_next_label+2))) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2)) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand loaded t = SOME (EL i ws) /\
      op_prov (Gt H) loaded = NONE /\ op_taint (Tt H) loaded = {}) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand loaded s = SOME (EL i ws) /\
      op_prov (Gs H) loaded = NONE /\ op_taint (Ts H) loaded = {}) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = (if EL i ws = w then
        fresh_label_output "in_found" (sa.cs_next_label+3) else
        fresh_label_output "in_incr" (sa.cs_next_label+4))) /\
  (!i s Gs Ts.
    (!H. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_found" (sa.cs_next_label+3)) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 1w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)) /\
  (!i s Gs Ts.
    (!H. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_incr" (sa.cs_next_label+4)) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa (SUC i) 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)) /\
  i <= LENGTH ws /\
  (!H. guard H ==>
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
    ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
    s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)) ==>
  ?t Gt Tt j. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa j (bool_to_word (MEM w (DROP i ws))) (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)
Proof
  measureInduct_on `LENGTH ws-i` >> rpt strip_tac >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H. guard H ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ t.vs_current_bb = (if j = LENGTH ws then _ else _)`
    (mk_asm "condition") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H. guard H ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ t.vs_current_bb = (if EL j ws = w then _ else _)`
    (mk_asm "compare") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H. guard H ==> _ /\ _ /\ membership_loop_registers sa (SUC j) _ _ _ _ /\ _`
    (mk_asm "increment") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H. guard H ==> _ /\ _ /\ membership_loop_registers sa j 1w _ _ _ /\ _`
    (mk_asm "found") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H. guard H ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ eval_operand loaded t = _ /\ _`
    (mk_asm "load") >>
  asm "condition" (qspecl_then [`i`,`s`,`Gs`,`Ts`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `cs` (qx_choose_then `CG` (qx_choose_then `CT` assume_tac))) >>
  Cases_on `i = LENGTH ws`
  >- (qexistsl_tac [`cs`,`CG`,`CT`,`i`] >> gvs[bool_to_word_def] >> metis_tac[]) >>
  `i < LENGTH ws` by decide_tac >>
  asm "load" (qspecl_then [`i`,`cs`,`CG`,`CT`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `ls` (qx_choose_then `LG` (qx_choose_then `LTs` assume_tac))) >>
  asm "compare" (qspecl_then [`i`,`ls`,`LG`,`LTs`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `bs` (qx_choose_then `BG` (qx_choose_then `BT` assume_tac))) >>
  `DROP i ws = EL i ws :: DROP (SUC i) ws` by
    metis_tac[rich_listTheory.DROP_CONS_EL] >>
  Cases_on `EL i ws = w`
  >- suspend "hit" >>
  suspend "miss"
QED

Resume rest_word_membership_segment_full_horizon[hit]:
  asm "found" (qspecl_then [`i`,`bs`,`BG`,`BT`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `fin` (qx_choose_then `GF` (qx_choose_then `TF` assume_tac))) >>
  qexistsl_tac [`fin`,`GF`,`TF`,`i`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!y. LENGTH ws-y < _ ==> _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  simp[bool_to_word_def] >>
  metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED

Resume rest_word_membership_segment_full_horizon[miss]:
  asm "increment" (qspecl_then [`i`,`bs`,`BG`,`BT`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `is` (qx_choose_then `IG` (qx_choose_then `IT` assume_tac))) >>
  qpat_x_assum `!y. LENGTH ws-y < _ ==> _` (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`is`,`IG`,`IT`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- asm "condition" ACCEPT_TAC >>
    conj_tac >- asm "load" ACCEPT_TAC >>
    conj_tac >- asm "compare" ACCEPT_TAC >>
    conj_tac >- asm "found" ACCEPT_TAC >>
    conj_tac >- asm "increment" ACCEPT_TAC >>
    conj_tac >- decide_tac >>
    gen_tac >> disch_tac >>
    rpt (qpat_x_assum `!h. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> simp[])) >>
  disch_then (qx_choose_then `fin` (qx_choose_then `GF` (qx_choose_then `TF`
    (qx_choose_then `j` assume_tac)))) >>
  qexistsl_tac [`fin`,`GF`,`TF`,`j`] >> gen_tac >> disch_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  simp[] >> metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED

Finalise rest_word_membership_segment_full_horizon

Theorem rest_word_membership_suffix_full_horizon[local]:
  !i s Gs Ts.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ LENGTH ws < dimword (:256) /\
  (!H. guard H ==>
    eval_operand needle s0 = SOME w /\ op_prov (G0 H) needle = NONE /\
    op_taint (T0 H) needle = {} /\
    eval_operand len s0 = SOME (n2w (LENGTH ws)) /\
    op_prov (G0 H) len = NONE /\ op_taint (T0 H) len = {}) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) t = SOME (EL i ws) /\
      op_prov (Gt H) (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
      op_taint (Tt H) (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = {}) /\
  i <= LENGTH ws /\
  (!H. guard H ==>
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
    ~s.vs_halted /\ allocas_from lo s /\
    s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
    s.vs_inst_idx = 0) ==>
  ?t Gt Tt j. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa j (bool_to_word (MEM w (DROP i ws))) (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)
Proof
  rpt strip_tac >>
  qspecl_then [`i`,`s`,`Gs`,`Ts`] mp_tac
    (Q.INST [
      `loaded` |-> `Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))`]
      rest_word_membership_segment_full_horizon) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- suspend "condition" >>
    conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
    conj_tac >- suspend "compare" >>
    conj_tac >- suspend "found" >>
    conj_tac >- suspend "increment" >>
    simp[] >> metis_tac[])) >>
  disch_then ACCEPT_TAC
QED

Resume rest_word_membership_suffix_full_horizon[condition]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `ci = mk_inst (sa.cs_next_id+4+(if IS_SOME bound then 3 else 0)) EQ
    [Var ("%" ++ toString (sa.cs_next_var+1));len]
    ["%" ++ toString (sa.cs_next_var+2+(if IS_SOME bound then 2 else 0))]` >>
  qabbrev_tac `cv = update_var ("%" ++ toString (sa.cs_next_var+2+
    (if IS_SOME bound then 2 else 0)))
    (bool_to_word ((n2w j:bytes32) = n2w (LENGTH ws))) u` >>
  qabbrev_tac `cs = jump_to (if (n2w j:bytes32) = n2w (LENGTH ws) then
    fresh_label_output "in_exit" (sa.cs_next_label+5) else
    fresh_label_output "in_body" (sa.cs_next_label+2)) cv` >>
  qabbrev_tac `CG = \H. step_prov PG (Gu H) ci cv` >>
  qabbrev_tac `CT = \H. step_taint ci u cv (Tu H)` >>
  qexistsl_tac [`cs`,`CG`,`CT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `eval_operand len u = SOME (n2w (LENGTH ws)) /\
   op_prov (Gu H) len = NONE /\ op_taint (Tu H) len = {}` by
    metis_tac[membership_loop_frame_operand] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu H,Tu H) [] (OK cs,CG H,CT H) /\
   membership_loop_frame sa (G0 H) (T0 H) s0 (CG H) (CT H) cs /\
   membership_loop_registers sa j 0w (CG H) (CT H) cs /\
   ~cs.vs_halted /\ cs.vs_inst_idx = 0 /\ allocas_from lo cs` by
    (map_every qunabbrev_tac [`CG`,`CT`,`cs`,`cv`,`ci`] >> BETA_TAC >>
     Cases_on `bound`
     >- (simp_tac std_ss [] >>
         `eval_operand (Var ("%" ++ toString (sa.cs_next_var+1))) u = SOME (n2w j) /\
          op_prov (Gu H) (Var ("%" ++ toString (sa.cs_next_var+1))) = NONE /\
          op_taint (Tu H) (Var ("%" ++ toString (sa.cs_next_var+1))) = {}` by
           gvs[membership_loop_registers_def, eval_operand_def] >>
         irule (SIMP_RULE bool_ss [] (Q.GENL
           [`delta`,`width`,`lhs`,`rhs`,`dst`,`eid`,`yes`,`no`,`ins`,`t`,`G1`,`tn1`,`u`]
           (Q.INST [`cond_site` |-> `T`] rest_word_membership_compare_segment_joint))) >>
         simp[] >> metis_tac[]) >>
     simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >> irule (SIMP_RULE bool_ss [] (Q.GENL
       [`dst`,`ins`,`t`,`G1`,`tn1`,`target`] rest_word_membership_bounded_condition_joint)) >>
     metis_tac[]) >>
  `j < dimword (:256)` by decide_tac >>
  simp[] >> simp[Abbr `cs`, jump_to_def, wordsTheory.n2w_11]
QED

Resume rest_word_membership_suffix_full_horizon[compare]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `bi = mk_inst (sa.cs_next_id+((if IS_SOME bound then 11 else 8)+delta+width)) EQ
    [Var ("%" ++ toString (sa.cs_next_var+((if IS_SOME bound then 6 else 4)+delta+width)));needle]
    ["%" ++ toString (sa.cs_next_var+((if IS_SOME bound then 7 else 5)+delta+width))]` >>
  qabbrev_tac `bv = update_var ("%" ++ toString (sa.cs_next_var+((if IS_SOME bound then 7 else 5)+delta+width)))
    (bool_to_word (EL j ws = w)) u` >>
  qabbrev_tac `bs = jump_to (if EL j ws = w then
    fresh_label_output "in_found" (sa.cs_next_label+3) else
    fresh_label_output "in_incr" (sa.cs_next_label+4)) bv` >>
  qabbrev_tac `BG = \H. step_prov PG (Gu H) bi bv` >>
  qabbrev_tac `BT = \H. step_taint bi u bv (Tu H)` >>
  qexistsl_tac [`bs`,`BG`,`BT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `eval_operand needle u = SOME w /\ op_prov (Gu H) needle = NONE /\
   op_taint (Tu H) needle = {}` by metis_tac[membership_loop_frame_operand] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu H,Tu H) [] (OK bs,BG H,BT H) /\
   membership_loop_frame sa (G0 H) (T0 H) s0 (BG H) (BT H) bs /\
   membership_loop_registers sa j 0w (BG H) (BT H) bs /\
   ~bs.vs_halted /\ bs.vs_inst_idx = 0 /\ allocas_from lo bs` by
    (map_every qunabbrev_tac [`BG`,`BT`,`bs`,`bv`,`bi`,`delta`,`width`] >>
     BETA_TAC >> Cases_on `bound`
     >- (simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
         irule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
           [`delta`,`width`,`lhs`,`rhs`,`dst`,`eid`,`yes`,`no`,`ins`,`t`,`G1`,`tn1`,`u`]
           (Q.INST [`cond_site` |-> `F`] rest_word_membership_compare_segment_joint))) >>
         fs[GSYM arithmeticTheory.ADD_ASSOC] >> metis_tac[]) >>
     simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
     irule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
       [`delta`,`width`,`lhs`,`rhs`,`dst`,`eid`,`yes`,`no`,`ins`,`t`,`G1`,`tn1`,`u`]
       (Q.INST [`cond_site` |-> `F`] rest_word_membership_bounded_compare_segment_joint))) >>
     fs[GSYM arithmeticTheory.ADD_ASSOC] >> metis_tac[]) >>
  simp[] >> simp[Abbr `bs`, jump_to_def]
QED

Resume rest_word_membership_suffix_full_horizon[found]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `fu = jump_to (fresh_label_output "in_exit" (sa.cs_next_label+5))
    (update_var ("%" ++ toString sa.cs_next_var) 1w u)` >>
  qabbrev_tac `FG = \H. DRESTRICT (Gu H) (COMPL {"%" ++ toString sa.cs_next_var})` >>
  qabbrev_tac `FT = \H. (Tu H) with t_var := (Tu H).t_var |+
    ("%" ++ toString sa.cs_next_var,{})` >>
  qexistsl_tac [`fu`,`FG`,`FT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu H,Tu H) [] (OK fu,FG H,FT H) /\
   membership_loop_frame sa (G0 H) (T0 H) s0 (FG H) (FT H) fu /\
   membership_loop_registers sa j 1w (FG H) (FT H) fu /\
   ~fu.vs_halted /\ fu.vs_inst_idx = 0 /\ allocas_from lo fu` by
    (map_every qunabbrev_tac [`FG`,`FT`,`fu`] >> BETA_TAC >> Cases_on `bound`
     >- (irule (Q.GENL [`delta`,`width`,`dst`,`ins`,`t`,`G1`,`tn1`,`u`]
           rest_word_membership_found_joint) >> simp[] >> metis_tac[]) >>
     irule (Q.GENL [`delta`,`width`,`dst`,`ins`,`t`,`G1`,`tn1`,`u`]
       rest_word_membership_bounded_found_joint) >> simp[] >> metis_tac[]) >>
  simp[] >> simp[Abbr `fu`, jump_to_def]
QED

Resume rest_word_membership_suffix_full_horizon[increment]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `idx = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `dst = "%" ++ toString (sa.cs_next_var+((if IS_SOME bound then 8 else 6)+delta+width))` >>
  qabbrev_tac `a = mk_inst (sa.cs_next_id+((if IS_SOME bound then 15 else 12)+delta+width)) ADD [Var idx;Lit 1w] [dst]` >>
  qabbrev_tac `b = mk_inst (sa.cs_next_id+((if IS_SOME bound then 16 else 13)+delta+width)) ASSIGN [Var dst] [idx]` >>
  qabbrev_tac `v = update_var dst (n2w (SUC j)) u` >>
  qabbrev_tac `iv = update_var idx (n2w (SUC j)) (v with vs_inst_idx := 1)` >>
  qabbrev_tac `iu = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) iv` >>
  qabbrev_tac `IG = \H. step_prov PG (step_prov PG (Gu H) a v) b iv` >>
  qabbrev_tac `IT = \H. step_taint b (v with vs_inst_idx := 1) iv
    (step_taint a u v (Tu H))` >>
  qexistsl_tac [`iu`,`IG`,`IT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu H,Tu H) [] (OK iu,IG H,IT H) /\
   membership_loop_frame sa (G0 H) (T0 H) s0 (IG H) (IT H) iu /\
   membership_loop_registers sa (SUC j) 0w (IG H) (IT H) iu /\
   ~iu.vs_halted /\ iu.vs_inst_idx = 0 /\ allocas_from lo iu` by
    (map_every qunabbrev_tac [`IG`,`IT`,`iu`,`iv`,`v`,`a`,`b`,`idx`,`dst`,`delta`,`width`] >>
     BETA_TAC >> Cases_on `bound`
     >- (simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
         drule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
           [`delta`,`width`,`idx`,`dst`,`a`,`b`,`t`,`G1`,`tn1`,`v`,`G2`,`tn2`,`u`]
           rest_word_membership_increment_joint)) >>
         disch_then irule >> simp[] >> metis_tac[]) >>
     simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
     drule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
       [`delta`,`width`,`idx`,`dst`,`a`,`b`,`t`,`G1`,`tn1`,`v`,`G2`,`tn2`,`u`]
       rest_word_membership_bounded_increment_joint)) >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  simp[] >> simp[Abbr `iu`, jump_to_def]
QED

Finalise rest_word_membership_suffix_full_horizon

Theorem rest_word_membership_loop_full_horizon_joint_all:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ LENGTH ws < dimword (:256) /\
  (!cap. bound = SOME cap ==> LENGTH ws <= cap /\ cap < dimword (:256)) /\
  (!H. guard H ==>
    eval_operand needle s0 = SOME w /\ op_prov (G0 H) needle = NONE /\
    op_taint (T0 H) needle = {} /\
    eval_operand len s0 = SOME (n2w (LENGTH ws)) /\
    op_prov (G0 H) len = NONE /\ op_taint (T0 H) len = {}) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) t = SOME (EL i ws) /\
      op_prov (Gt H) (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
      op_taint (Tt H) (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = {}) /\
  (!H. guard H ==> ~s0.vs_halted /\ allocas_from lo s0 /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts) ==>
  ?t Gt Tt. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s0,G0 H,T0 H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    eval_operand op t = SOME (bool_to_word (if is_in then MEM w ws else ~MEM w ws)) /\
    op_prov (Gt H) op = NONE /\ op_taint (Tt H) op = {} /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qabbrev_tac `ix = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `res = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `a = "%" ++ toString (sa.cs_next_var+2)` >>
  qabbrev_tac `b = "%" ++ toString (sa.cs_next_var+3)` >>
  qabbrev_tac `it = update_var res 0w (update_var ix 0w
    (jump_to (fresh_label_output "in_entry" sa.cs_next_label) s0))` >>
  qabbrev_tac `iu = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1))
    (if IS_SOME bound then update_var b 1w (update_var a 0w it) else it)` >>
  qabbrev_tac `GI = \H. if IS_SOME bound then DRESTRICT (DRESTRICT
    (DRESTRICT (DRESTRICT (G0 H) (COMPL {ix})) (COMPL {res})) (COMPL {a})) (COMPL {b})
    else DRESTRICT (DRESTRICT (G0 H) (COMPL {ix})) (COMPL {res})` >>
  qabbrev_tac `TI = \H. if IS_SOME bound then (T0 H) with t_var :=
    ((((T0 H).t_var |+ (ix,{})) |+ (res,{})) |+ (a,{})) |+ (b,{})
    else (T0 H) with t_var := ((T0 H).t_var |+ (ix,{})) |+ (res,{})` >>
  `!H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s0,G0 H,T0 H) [] (OK iu,GI H,TI H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (GI H) (TI H) iu /\
    membership_loop_registers sa 0 0w (GI H) (TI H) iu /\
    ~iu.vs_halted /\ iu.vs_inst_idx = 0 /\ allocas_from lo iu /\
    iu.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)` by
    suspend "entry" >>
  `?fin GF TF j. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (iu,GI H,TI H) [] (OK fin,GF H,TF H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (GF H) (TF H) fin /\
    membership_loop_registers sa j (bool_to_word (MEM w ws)) (GF H) (TF H) fin /\
    ~fin.vs_halted /\ allocas_from lo fin /\ fin.vs_inst_idx = 0 /\
    fin.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)` by
    (mp_tac (Q.SPECL [`0`,`iu`,`GI`,`TI`] rest_word_membership_suffix_full_horizon) >>
     (impl_tac >-
       (pure_asm_rewrite_tac [] >> rewrite_tac [] >>
        conj_tac >- simp[] >>
        gen_tac >> disch_tac >>
        qpat_x_assum `!h. guard h ==> gas_origin_ptr_path _ (s0,_,_) _ _ /\ _`
          (qspec_then `H` (drule_then strip_assume_tac)) >>
        pure_asm_rewrite_tac [] >> rewrite_tac [])) >> simp[]) >>
  `sb.cs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5) /\
   LENGTH sb.cs_current_insts = (if is_in then 0 else 1) /\
   op = Var ("%" ++ toString (sa.cs_next_var + (if is_in then 0 else
     (if IS_SOME bound then 9 else 7) + (if 0 < skip then 1 else 0) +
     (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1))))` by
    (Cases_on `bound`
     >- (drule bodyPtrBopInLoopCodeTheory.membership_compiled_loop_exit >>
         simp_tac std_ss [] >> strip_tac >> asm_rewrite_tac []) >>
     drule bodyPtrBopInBoundedLayoutTheory.membership_bounded_loop_exit >>
     simp_tac std_ss [] >> strip_tac >> asm_rewrite_tac []) >>
  Cases_on `is_in` >- suspend "in_exit" >> suspend "notin_exit"
QED

Resume rest_word_membership_loop_full_horizon_joint_all[entry]:
  gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s0,G0 H,T0 H) [] (OK iu,GI H,TI H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (GI H) (TI H) iu /\
    membership_loop_registers sa 0 0w (GI H) (TI H) iu /\
    ~iu.vs_halted /\ iu.vs_inst_idx = 0 /\ allocas_from lo iu` by
    (map_every qunabbrev_tac [`GI`,`TI`,`iu`,`it`,`ix`,`res`,`a`,`b`] >> BETA_TAC >>
     Cases_on `bound`
     >- (simp_tac std_ss [] >> irule (SIMP_RULE bool_ss [] (Q.GENL
           [`idx`,`result`,`e`,`t`,`G2`,`tn2`,`u`] rest_word_membership_init_joint)) >>
         pure_asm_rewrite_tac [] >> metis_tac[]) >>
     simp_tac std_ss [] >> drule (Q.GENL
       [`idx`,`result`,`a`,`b`,`e`,`t`,`G2`,`tn2`,`G3`,`tn3`,`u`]
       rest_word_membership_bounded_init_joint) >>
     disch_then irule >> simp[] >> qexists_tac `LENGTH ws` >> simp[]) >>
  pure_asm_rewrite_tac [] >> simp[Abbr `iu`, jump_to_def]
QED

Resume rest_word_membership_loop_full_horizon_joint_all[in_exit]:
  qexistsl_tac [`fin`,`GF`,`TF`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s0,G0 H,T0 H) [] (OK fin,GF H,TF H)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  pure_asm_rewrite_tac [] >>
  gvs[membership_loop_registers_def, eval_operand_def,
    ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def]
QED

Resume rest_word_membership_loop_full_horizon_joint_all[notin_exit]:
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `dst = "%" ++ toString (sa.cs_next_var+((if IS_SOME bound then 9 else 7)+delta+width))` >>
  qabbrev_tac `ni = mk_inst (sa.cs_next_id+((if IS_SOME bound then 18 else 15)+delta+width)) ISZERO
    [Var ("%" ++ toString sa.cs_next_var)] [dst]` >>
  qabbrev_tac `nv = update_var dst (bool_to_word (~MEM w ws)) fin` >>
  qabbrev_tac `nu = nv with vs_inst_idx := 1` >>
  qabbrev_tac `NG = \H. step_prov PG (GF H) ni nv` >>
  qabbrev_tac `NT = \H. step_taint ni fin nv (TF H)` >>
  qexistsl_tac [`nu`,`NG`,`NT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (fin,GF H,TF H) [] (OK nu,NG H,NT H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (NG H) (NT H) nu /\
    eval_operand op nu = SOME (bool_to_word (~MEM w ws)) /\
    op_prov (NG H) op = NONE /\ op_taint (NT H) op = {} /\
    ~nu.vs_halted /\ nu.vs_current_bb = sb.cs_current_bb /\
    nu.vs_inst_idx = 1 /\ allocas_from lo nu` by
    (map_every qunabbrev_tac [`NG`,`NT`,`nu`,`nv`,`ni`,`dst`,`delta`,`width`] >>
     BETA_TAC >>
     `~MEM w ws <=> (bool_to_word (MEM w ws):bytes32) = 0w` by
       (Cases_on `MEM w ws` >> simp[bool_to_word_def]) >>
     pop_assum SUBST1_TAC >>
     Cases_on `bound`
     >- (simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
         irule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
           [`delta`,`width`,`dst`,`ins`,`t`,`G1`,`tn1`,`u`]
           rest_word_membership_notin_joint)) >>
         rule_assum_tac (REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
         pure_asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> rewrite_tac [] >>
         conj_tac
         >- (qexistsl_tac [`arr`,`len`,`needle`,`stride`] >>
             qpat_x_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` mp_tac >>
             asm_rewrite_tac []) >>
         qexists_tac `j` >> first_assum ACCEPT_TAC) >>
     simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
     irule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
       [`delta`,`width`,`dst`,`ins`,`t`,`G1`,`tn1`,`u`]
       rest_word_membership_bounded_notin_joint)) >>
     rule_assum_tac (REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
     pure_asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> rewrite_tac [] >>
     conj_tac
     >- (qexistsl_tac [`arr`,`x`,`len`,`needle`,`stride`] >>
         qpat_x_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         asm_rewrite_tac []) >>
     qexists_tac `j` >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s0,G0 H,T0 H) [] (OK nu,NG H,NT H)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  pure_asm_rewrite_tac [] >> simp[]
QED

Finalise rest_word_membership_loop_full_horizon_joint_all

(* Constant ghosts are chosen with the machine endpoint, before the horizon. *)
Theorem rest_word_membership_segment_const_full_horizon[local]:
  !i s Gs Ts.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  (!i s Gs Ts. i <= LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa G0 T0 s0 Gs Ts s /\
      membership_loop_registers sa i 0w Gs Ts s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs,Ts) [] (OK t,Gt,Tt) /\
      membership_loop_frame sa G0 T0 s0 Gt Tt t /\
      membership_loop_registers sa i 0w Gt Tt t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = (if i = LENGTH ws then
        fresh_label_output "in_exit" (sa.cs_next_label+5) else
        fresh_label_output "in_body" (sa.cs_next_label+2))) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa G0 T0 s0 Gs Ts s /\
      membership_loop_registers sa i 0w Gs Ts s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2)) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs,Ts) [] (OK t,Gt,Tt) /\
      membership_loop_frame sa G0 T0 s0 Gt Tt t /\
      membership_loop_registers sa i 0w Gt Tt t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand loaded t = SOME (EL i ws) /\
      op_prov Gt loaded = NONE /\ op_taint Tt loaded = {}) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa G0 T0 s0 Gs Ts s /\
      membership_loop_registers sa i 0w Gs Ts s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand loaded s = SOME (EL i ws) /\
      op_prov Gs loaded = NONE /\ op_taint Ts loaded = {}) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs,Ts) [] (OK t,Gt,Tt) /\
      membership_loop_frame sa G0 T0 s0 Gt Tt t /\
      membership_loop_registers sa i 0w Gt Tt t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = (if EL i ws = w then
        fresh_label_output "in_found" (sa.cs_next_label+3) else
        fresh_label_output "in_incr" (sa.cs_next_label+4))) /\
  (!i s Gs Ts.
    (!H. guard H ==>
      membership_loop_frame sa G0 T0 s0 Gs Ts s /\
      membership_loop_registers sa i 0w Gs Ts s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_found" (sa.cs_next_label+3)) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs,Ts) [] (OK t,Gt,Tt) /\
      membership_loop_frame sa G0 T0 s0 Gt Tt t /\
      membership_loop_registers sa i 1w Gt Tt t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)) /\
  (!i s Gs Ts.
    (!H. guard H ==>
      membership_loop_frame sa G0 T0 s0 Gs Ts s /\
      membership_loop_registers sa i 0w Gs Ts s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_incr" (sa.cs_next_label+4)) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs,Ts) [] (OK t,Gt,Tt) /\
      membership_loop_frame sa G0 T0 s0 Gt Tt t /\
      membership_loop_registers sa (SUC i) 0w Gt Tt t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)) /\
  i <= LENGTH ws /\
  (!H. guard H ==>
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i 0w Gs Ts s /\
    ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
    s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)) ==>
  ?t Gt Tt j. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa j (bool_to_word (MEM w (DROP i ws))) Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)
Proof
  measureInduct_on `LENGTH ws-i` >> rpt strip_tac >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H. guard H ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ t.vs_current_bb = (if j = LENGTH ws then _ else _)`
    (mk_asm "condition") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H. guard H ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ t.vs_current_bb = (if EL j ws = w then _ else _)`
    (mk_asm "compare") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H. guard H ==> _ /\ _ /\ membership_loop_registers sa (SUC j) _ _ _ _ /\ _`
    (mk_asm "increment") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H. guard H ==> _ /\ _ /\ membership_loop_registers sa j 1w _ _ _ /\ _`
    (mk_asm "found") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H. guard H ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ eval_operand loaded t = _ /\ _`
    (mk_asm "load") >>
  asm "condition" (qspecl_then [`i`,`s`,`Gs`,`Ts`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `cs` (qx_choose_then `CG` (qx_choose_then `CT` assume_tac))) >>
  Cases_on `i = LENGTH ws`
  >- (qexistsl_tac [`cs`,`CG`,`CT`,`i`] >> gvs[bool_to_word_def] >> metis_tac[]) >>
  `i < LENGTH ws` by decide_tac >>
  asm "load" (qspecl_then [`i`,`cs`,`CG`,`CT`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `ls` (qx_choose_then `LG` (qx_choose_then `LTs` assume_tac))) >>
  asm "compare" (qspecl_then [`i`,`ls`,`LG`,`LTs`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `bs` (qx_choose_then `BG` (qx_choose_then `BT` assume_tac))) >>
  `DROP i ws = EL i ws :: DROP (SUC i) ws` by
    metis_tac[rich_listTheory.DROP_CONS_EL] >>
  Cases_on `EL i ws = w`
  >- suspend "hit" >>
  suspend "miss"
QED

Resume rest_word_membership_segment_const_full_horizon[hit]:
  asm "found" (qspecl_then [`i`,`bs`,`BG`,`BT`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `fin` (qx_choose_then `GF` (qx_choose_then `TF` assume_tac))) >>
  qexistsl_tac [`fin`,`GF`,`TF`,`i`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!y. LENGTH ws-y < _ ==> _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  simp[bool_to_word_def] >>
  metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED

Resume rest_word_membership_segment_const_full_horizon[miss]:
  asm "increment" (qspecl_then [`i`,`bs`,`BG`,`BT`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `is` (qx_choose_then `IG` (qx_choose_then `IT` assume_tac))) >>
  qpat_x_assum `!y. LENGTH ws-y < _ ==> _` (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`is`,`IG`,`IT`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- asm "condition" ACCEPT_TAC >>
    conj_tac >- asm "load" ACCEPT_TAC >>
    conj_tac >- asm "compare" ACCEPT_TAC >>
    conj_tac >- asm "found" ACCEPT_TAC >>
    conj_tac >- asm "increment" ACCEPT_TAC >>
    conj_tac >- decide_tac >>
    gen_tac >> disch_tac >>
    rpt (qpat_x_assum `!h. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> simp[])) >>
  disch_then (qx_choose_then `fin` (qx_choose_then `GF` (qx_choose_then `TF`
    (qx_choose_then `j` assume_tac)))) >>
  qexistsl_tac [`fin`,`GF`,`TF`,`j`] >> gen_tac >> disch_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  simp[] >> metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED

Finalise rest_word_membership_segment_const_full_horizon

Theorem rest_word_membership_suffix_const_full_horizon[local]:
  !i s Gs Ts.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ LENGTH ws < dimword (:256) /\
  (!H. guard H ==>
    eval_operand needle s0 = SOME w /\ op_prov G0 needle = NONE /\
    op_taint T0 needle = {} /\
    eval_operand len s0 = SOME (n2w (LENGTH ws)) /\
    op_prov G0 len = NONE /\ op_taint T0 len = {}) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa G0 T0 s0 Gs Ts s /\
      membership_loop_registers sa i 0w Gs Ts s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs,Ts) [] (OK t,Gt,Tt) /\
      membership_loop_frame sa G0 T0 s0 Gt Tt t /\
      membership_loop_registers sa i 0w Gt Tt t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) t = SOME (EL i ws) /\
      op_prov Gt (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
      op_taint Tt (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = {}) /\
  i <= LENGTH ws /\
  (!H. guard H ==>
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i 0w Gs Ts s /\
    ~s.vs_halted /\ allocas_from lo s /\
    s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
    s.vs_inst_idx = 0) ==>
  ?t Gt Tt j. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa j (bool_to_word (MEM w (DROP i ws))) Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)
Proof
  rpt strip_tac >>
  qspecl_then [`i`,`s`,`Gs`,`Ts`] mp_tac
    (Q.INST [
      `loaded` |-> `Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))`]
      rest_word_membership_segment_const_full_horizon) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- suspend "condition" >>
    conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
    conj_tac >- suspend "compare" >>
    conj_tac >- suspend "found" >>
    conj_tac >- suspend "increment" >>
    simp[] >> metis_tac[])) >>
  disch_then ACCEPT_TAC
QED

Resume rest_word_membership_suffix_const_full_horizon[condition]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `ci = mk_inst (sa.cs_next_id+4+(if IS_SOME bound then 3 else 0)) EQ
    [Var ("%" ++ toString (sa.cs_next_var+1));len]
    ["%" ++ toString (sa.cs_next_var+2+(if IS_SOME bound then 2 else 0))]` >>
  qabbrev_tac `cv = update_var ("%" ++ toString (sa.cs_next_var+2+
    (if IS_SOME bound then 2 else 0)))
    (bool_to_word ((n2w j:bytes32) = n2w (LENGTH ws))) u` >>
  qabbrev_tac `cs = jump_to (if (n2w j:bytes32) = n2w (LENGTH ws) then
    fresh_label_output "in_exit" (sa.cs_next_label+5) else
    fresh_label_output "in_body" (sa.cs_next_label+2)) cv` >>
  qabbrev_tac `CG = step_prov PG Gu ci cv` >>
  qabbrev_tac `CT = step_taint ci u cv Tu` >>
  qexistsl_tac [`cs`,`CG`,`CT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `eval_operand len u = SOME (n2w (LENGTH ws)) /\
   op_prov Gu len = NONE /\ op_taint Tu len = {}` by
    metis_tac[membership_loop_frame_operand] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu,Tu) [] (OK cs,CG,CT) /\
   membership_loop_frame sa G0 T0 s0 CG CT cs /\
   membership_loop_registers sa j 0w CG CT cs /\
   ~cs.vs_halted /\ cs.vs_inst_idx = 0 /\ allocas_from lo cs` by
    (map_every qunabbrev_tac [`CG`,`CT`,`cs`,`cv`,`ci`] >>
     Cases_on `bound`
     >- (simp_tac std_ss [] >>
         `eval_operand (Var ("%" ++ toString (sa.cs_next_var+1))) u = SOME (n2w j) /\
          op_prov Gu (Var ("%" ++ toString (sa.cs_next_var+1))) = NONE /\
          op_taint Tu (Var ("%" ++ toString (sa.cs_next_var+1))) = {}` by
           gvs[membership_loop_registers_def, eval_operand_def] >>
         irule (SIMP_RULE bool_ss [] (Q.GENL
           [`delta`,`width`,`lhs`,`rhs`,`dst`,`eid`,`yes`,`no`,`ins`,`t`,`G1`,`tn1`,`u`]
           (Q.INST [`cond_site` |-> `T`] rest_word_membership_compare_segment_joint))) >>
         simp[] >> metis_tac[]) >>
     simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >> irule (SIMP_RULE bool_ss [] (Q.GENL
       [`dst`,`ins`,`t`,`G1`,`tn1`,`target`] rest_word_membership_bounded_condition_joint)) >>
     metis_tac[]) >>
  `j < dimword (:256)` by decide_tac >>
  simp[] >> simp[Abbr `cs`, jump_to_def, wordsTheory.n2w_11]
QED

Resume rest_word_membership_suffix_const_full_horizon[compare]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `bi = mk_inst (sa.cs_next_id+((if IS_SOME bound then 11 else 8)+delta+width)) EQ
    [Var ("%" ++ toString (sa.cs_next_var+((if IS_SOME bound then 6 else 4)+delta+width)));needle]
    ["%" ++ toString (sa.cs_next_var+((if IS_SOME bound then 7 else 5)+delta+width))]` >>
  qabbrev_tac `bv = update_var ("%" ++ toString (sa.cs_next_var+((if IS_SOME bound then 7 else 5)+delta+width)))
    (bool_to_word (EL j ws = w)) u` >>
  qabbrev_tac `bs = jump_to (if EL j ws = w then
    fresh_label_output "in_found" (sa.cs_next_label+3) else
    fresh_label_output "in_incr" (sa.cs_next_label+4)) bv` >>
  qabbrev_tac `BG = step_prov PG Gu bi bv` >>
  qabbrev_tac `BT = step_taint bi u bv Tu` >>
  qexistsl_tac [`bs`,`BG`,`BT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `eval_operand needle u = SOME w /\ op_prov Gu needle = NONE /\
   op_taint Tu needle = {}` by metis_tac[membership_loop_frame_operand] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu,Tu) [] (OK bs,BG,BT) /\
   membership_loop_frame sa G0 T0 s0 BG BT bs /\
   membership_loop_registers sa j 0w BG BT bs /\
   ~bs.vs_halted /\ bs.vs_inst_idx = 0 /\ allocas_from lo bs` by
    (map_every qunabbrev_tac [`BG`,`BT`,`bs`,`bv`,`bi`,`delta`,`width`] >>
     Cases_on `bound`
     >- (simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
         irule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
           [`delta`,`width`,`lhs`,`rhs`,`dst`,`eid`,`yes`,`no`,`ins`,`t`,`G1`,`tn1`,`u`]
           (Q.INST [`cond_site` |-> `F`] rest_word_membership_compare_segment_joint))) >>
         fs[GSYM arithmeticTheory.ADD_ASSOC] >> metis_tac[]) >>
     simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
     irule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
       [`delta`,`width`,`lhs`,`rhs`,`dst`,`eid`,`yes`,`no`,`ins`,`t`,`G1`,`tn1`,`u`]
       (Q.INST [`cond_site` |-> `F`] rest_word_membership_bounded_compare_segment_joint))) >>
     fs[GSYM arithmeticTheory.ADD_ASSOC] >> metis_tac[]) >>
  simp[] >> simp[Abbr `bs`, jump_to_def]
QED

Resume rest_word_membership_suffix_const_full_horizon[found]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `fu = jump_to (fresh_label_output "in_exit" (sa.cs_next_label+5))
    (update_var ("%" ++ toString sa.cs_next_var) 1w u)` >>
  qabbrev_tac `FG = DRESTRICT Gu (COMPL {"%" ++ toString sa.cs_next_var})` >>
  qabbrev_tac `FT = Tu with t_var := Tu.t_var |+
    ("%" ++ toString sa.cs_next_var,{})` >>
  qexistsl_tac [`fu`,`FG`,`FT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu,Tu) [] (OK fu,FG,FT) /\
   membership_loop_frame sa G0 T0 s0 FG FT fu /\
   membership_loop_registers sa j 1w FG FT fu /\
   ~fu.vs_halted /\ fu.vs_inst_idx = 0 /\ allocas_from lo fu` by
    (map_every qunabbrev_tac [`FG`,`FT`,`fu`] >> Cases_on `bound`
     >- (irule (Q.GENL [`delta`,`width`,`dst`,`ins`,`t`,`G1`,`tn1`,`u`]
           rest_word_membership_found_joint) >> simp[] >> metis_tac[]) >>
     irule (Q.GENL [`delta`,`width`,`dst`,`ins`,`t`,`G1`,`tn1`,`u`]
       rest_word_membership_bounded_found_joint) >> simp[] >> metis_tac[]) >>
  simp[] >> simp[Abbr `fu`, jump_to_def]
QED

Resume rest_word_membership_suffix_const_full_horizon[increment]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `idx = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `dst = "%" ++ toString (sa.cs_next_var+((if IS_SOME bound then 8 else 6)+delta+width))` >>
  qabbrev_tac `a = mk_inst (sa.cs_next_id+((if IS_SOME bound then 15 else 12)+delta+width)) ADD [Var idx;Lit 1w] [dst]` >>
  qabbrev_tac `b = mk_inst (sa.cs_next_id+((if IS_SOME bound then 16 else 13)+delta+width)) ASSIGN [Var dst] [idx]` >>
  qabbrev_tac `v = update_var dst (n2w (SUC j)) u` >>
  qabbrev_tac `iv = update_var idx (n2w (SUC j)) (v with vs_inst_idx := 1)` >>
  qabbrev_tac `iu = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) iv` >>
  qabbrev_tac `IG = step_prov PG (step_prov PG Gu a v) b iv` >>
  qabbrev_tac `IT = step_taint b (v with vs_inst_idx := 1) iv
    (step_taint a u v Tu)` >>
  qexistsl_tac [`iu`,`IG`,`IT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu,Tu) [] (OK iu,IG,IT) /\
   membership_loop_frame sa G0 T0 s0 IG IT iu /\
   membership_loop_registers sa (SUC j) 0w IG IT iu /\
   ~iu.vs_halted /\ iu.vs_inst_idx = 0 /\ allocas_from lo iu` by
    (map_every qunabbrev_tac [`IG`,`IT`,`iu`,`iv`,`v`,`a`,`b`,`idx`,`dst`,`delta`,`width`] >>
     Cases_on `bound`
     >- (simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
         drule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
           [`delta`,`width`,`idx`,`dst`,`a`,`b`,`t`,`G1`,`tn1`,`v`,`G2`,`tn2`,`u`]
           rest_word_membership_increment_joint)) >>
         disch_then irule >> simp[] >> metis_tac[]) >>
     simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
     drule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
       [`delta`,`width`,`idx`,`dst`,`a`,`b`,`t`,`G1`,`tn1`,`v`,`G2`,`tn2`,`u`]
       rest_word_membership_bounded_increment_joint)) >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  simp[] >> simp[Abbr `iu`, jump_to_def]
QED

Finalise rest_word_membership_suffix_const_full_horizon

Theorem rest_word_membership_loop_const_full_horizon_joint_all:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ LENGTH ws < dimword (:256) /\
  (!cap. bound = SOME cap ==> LENGTH ws <= cap /\ cap < dimword (:256)) /\
  (!H. guard H ==>
    eval_operand needle s0 = SOME w /\ op_prov G0 needle = NONE /\
    op_taint T0 needle = {} /\
    eval_operand len s0 = SOME (n2w (LENGTH ws)) /\
    op_prov G0 len = NONE /\ op_taint T0 len = {}) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa G0 T0 s0 Gs Ts s /\
      membership_loop_registers sa i 0w Gs Ts s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs,Ts) [] (OK t,Gt,Tt) /\
      membership_loop_frame sa G0 T0 s0 Gt Tt t /\
      membership_loop_registers sa i 0w Gt Tt t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) t = SOME (EL i ws) /\
      op_prov Gt (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
      op_taint Tt (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = {}) /\
  (!H. guard H ==> ~s0.vs_halted /\ allocas_from lo s0 /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts) ==>
  ?t Gt Tt. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s0,G0,T0) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    eval_operand op t = SOME (bool_to_word (if is_in then MEM w ws else ~MEM w ws)) /\
    op_prov Gt op = NONE /\ op_taint Tt op = {} /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qabbrev_tac `ix = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `res = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `a = "%" ++ toString (sa.cs_next_var+2)` >>
  qabbrev_tac `b = "%" ++ toString (sa.cs_next_var+3)` >>
  qabbrev_tac `it = update_var res 0w (update_var ix 0w
    (jump_to (fresh_label_output "in_entry" sa.cs_next_label) s0))` >>
  qabbrev_tac `iu = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1))
    (if IS_SOME bound then update_var b 1w (update_var a 0w it) else it)` >>
  qabbrev_tac `GI = if IS_SOME bound then DRESTRICT (DRESTRICT
    (DRESTRICT (DRESTRICT G0 (COMPL {ix})) (COMPL {res})) (COMPL {a})) (COMPL {b})
    else DRESTRICT (DRESTRICT G0 (COMPL {ix})) (COMPL {res})` >>
  qabbrev_tac `TI = if IS_SOME bound then T0 with t_var :=
    (((T0.t_var |+ (ix,{})) |+ (res,{})) |+ (a,{})) |+ (b,{})
    else T0 with t_var := (T0.t_var |+ (ix,{})) |+ (res,{})` >>
  `!H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s0,G0,T0) [] (OK iu,GI,TI) /\
    membership_loop_frame sa G0 T0 s0 GI TI iu /\
    membership_loop_registers sa 0 0w GI TI iu /\
    ~iu.vs_halted /\ iu.vs_inst_idx = 0 /\ allocas_from lo iu /\
    iu.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)` by
    suspend "entry" >>
  `?fin GF TF j. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (iu,GI,TI) [] (OK fin,GF,TF) /\
    membership_loop_frame sa G0 T0 s0 GF TF fin /\
    membership_loop_registers sa j (bool_to_word (MEM w ws)) GF TF fin /\
    ~fin.vs_halted /\ allocas_from lo fin /\ fin.vs_inst_idx = 0 /\
    fin.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)` by
    (mp_tac (Q.SPECL [`0`,`iu`,`GI`,`TI`] rest_word_membership_suffix_const_full_horizon) >>
     (impl_tac >-
       (pure_asm_rewrite_tac [] >> rewrite_tac [] >>
        conj_tac >- simp[] >>
        gen_tac >> disch_tac >>
        qpat_x_assum `!h. guard h ==> gas_origin_ptr_path _ (s0,_,_) _ _ /\ _`
          (qspec_then `H` (drule_then strip_assume_tac)) >>
        pure_asm_rewrite_tac [] >> rewrite_tac [])) >> simp[]) >>
  `sb.cs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5) /\
   LENGTH sb.cs_current_insts = (if is_in then 0 else 1) /\
   op = Var ("%" ++ toString (sa.cs_next_var + (if is_in then 0 else
     (if IS_SOME bound then 9 else 7) + (if 0 < skip then 1 else 0) +
     (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1))))` by
    (Cases_on `bound`
     >- (drule bodyPtrBopInLoopCodeTheory.membership_compiled_loop_exit >>
         simp_tac std_ss [] >> strip_tac >> asm_rewrite_tac []) >>
     drule bodyPtrBopInBoundedLayoutTheory.membership_bounded_loop_exit >>
     simp_tac std_ss [] >> strip_tac >> asm_rewrite_tac []) >>
  Cases_on `is_in` >- suspend "in_exit" >> suspend "notin_exit"
QED

Resume rest_word_membership_loop_const_full_horizon_joint_all[entry]:
  gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s0,G0,T0) [] (OK iu,GI,TI) /\
    membership_loop_frame sa G0 T0 s0 GI TI iu /\
    membership_loop_registers sa 0 0w GI TI iu /\
    ~iu.vs_halted /\ iu.vs_inst_idx = 0 /\ allocas_from lo iu` by
    (map_every qunabbrev_tac [`GI`,`TI`,`iu`,`it`,`ix`,`res`,`a`,`b`] >>
     Cases_on `bound`
     >- (simp_tac std_ss [] >> irule (SIMP_RULE bool_ss [] (Q.GENL
           [`idx`,`result`,`e`,`t`,`G2`,`tn2`,`u`] rest_word_membership_init_joint)) >>
         pure_asm_rewrite_tac [] >> metis_tac[]) >>
     simp_tac std_ss [] >> drule (Q.GENL
       [`idx`,`result`,`a`,`b`,`e`,`t`,`G2`,`tn2`,`G3`,`tn3`,`u`]
       rest_word_membership_bounded_init_joint) >>
     disch_then irule >> simp[] >> qexists_tac `LENGTH ws` >> simp[]) >>
  pure_asm_rewrite_tac [] >> simp[Abbr `iu`, jump_to_def]
QED

Resume rest_word_membership_loop_const_full_horizon_joint_all[in_exit]:
  qexistsl_tac [`fin`,`GF`,`TF`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s0,G0,T0) [] (OK fin,GF,TF)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  pure_asm_rewrite_tac [] >>
  gvs[membership_loop_registers_def, eval_operand_def,
    ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def]
QED

Resume rest_word_membership_loop_const_full_horizon_joint_all[notin_exit]:
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `dst = "%" ++ toString (sa.cs_next_var+((if IS_SOME bound then 9 else 7)+delta+width))` >>
  qabbrev_tac `ni = mk_inst (sa.cs_next_id+((if IS_SOME bound then 18 else 15)+delta+width)) ISZERO
    [Var ("%" ++ toString sa.cs_next_var)] [dst]` >>
  qabbrev_tac `nv = update_var dst (bool_to_word (~MEM w ws)) fin` >>
  qabbrev_tac `nu = nv with vs_inst_idx := 1` >>
  qabbrev_tac `NG = step_prov PG GF ni nv` >>
  qabbrev_tac `NT = step_taint ni fin nv TF` >>
  qexistsl_tac [`nu`,`NG`,`NT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (fin,GF,TF) [] (OK nu,NG,NT) /\
    membership_loop_frame sa G0 T0 s0 NG NT nu /\
    eval_operand op nu = SOME (bool_to_word (~MEM w ws)) /\
    op_prov NG op = NONE /\ op_taint NT op = {} /\
    ~nu.vs_halted /\ nu.vs_current_bb = sb.cs_current_bb /\
    nu.vs_inst_idx = 1 /\ allocas_from lo nu` by
    (map_every qunabbrev_tac [`NG`,`NT`,`nu`,`nv`,`ni`,`dst`,`delta`,`width`] >>
     `~MEM w ws <=> (bool_to_word (MEM w ws):bytes32) = 0w` by
       (Cases_on `MEM w ws` >> simp[bool_to_word_def]) >>
     pop_assum SUBST1_TAC >>
     Cases_on `bound`
     >- (simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
         irule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
           [`delta`,`width`,`dst`,`ins`,`t`,`G1`,`tn1`,`u`]
           rest_word_membership_notin_joint)) >>
         rule_assum_tac (REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
         pure_asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> rewrite_tac [] >>
         conj_tac
         >- (qexistsl_tac [`arr`,`len`,`needle`,`stride`] >>
             qpat_x_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` mp_tac >>
             asm_rewrite_tac []) >>
         qexists_tac `j` >> first_assum ACCEPT_TAC) >>
     simp_tac std_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
     irule (SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC] (Q.GENL
       [`delta`,`width`,`dst`,`ins`,`t`,`G1`,`tn1`,`u`]
       rest_word_membership_bounded_notin_joint)) >>
     rule_assum_tac (REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
     pure_asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> rewrite_tac [] >>
     conj_tac
     >- (qexistsl_tac [`arr`,`x`,`len`,`needle`,`stride`] >>
         qpat_x_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         asm_rewrite_tac []) >>
     qexists_tac `j` >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s0,G0,T0) [] (OK nu,NG,NT)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  pure_asm_rewrite_tac [] >> simp[]
QED

Finalise rest_word_membership_loop_const_full_horizon_joint_all
