(* Transfer the selected return witness without choosing a second path. *)
Theory entryReturnFirstExit
Ancestors
  entryCreatePathScope entryCreateFocusSpec entryCreateCompletedCut createSizeCutRegion
  createSizePrefixReplay createMarkedPath fragGasOriginPtr fragExec
  venomExecSemantics venomState compileEnv relation list pair

Theorem return_scope_prepend_empty[local]:
  create_prefix_step a b E ctx fnc s [] u /\
  create_operand_full_scope a b E ctx fnc u [] r ==>
  create_operand_full_scope a b E ctx fnc s [] r
Proof
  strip_tac >>
  `create_expr_prefix a b E ctx fnc s [] u` by
    (simp[create_expr_prefix_marked] >>
     irule RTC_SINGLE >> simp[create_marked_edge_def]) >>
  Cases_on `r` >> gvs[create_operand_full_scope_def] >>
  metis_tac[create_expr_prefix_append, APPEND]
QED

(* All facts about the observer are one-edge facts. Empty marks preclude
   crossing the marker, even when its GAS site would carry a false mark. *)
Theorem return_empty_path_first_exit:
  create_cut_region a b s /\
  (!u H h rr H' h'. create_operand_at b u ==>
     ~gas_origin_ptr_edge (D,lo,E,obsctx,obsfn,PG) (u,H,h) [] (rr,H',h')) /\
  (!u H h rr H' h'.
     create_cut_region a b u /\ ~create_operand_at b u /\
     gas_origin_ptr_edge (D,lo,E,obsctx,obsfn,PG) (u,H,h) [] (rr,H',h') ==>
     gas_origin_ptr_edge (D,lo,E,ctx,fnc,PG) (u,H,h) [] (rr,H',h') /\
     (!v. rr = OK v ==> create_prefix_step a b E ctx fnc u [] v /\
                        create_cut_region a b v)) /\
  (case r of OK t => create_operand_at b t | _ => exit_result r) /\
  gas_origin_ptr_path (D,lo,E,obsctx,obsfn,PG) (s,G,tn) [] (r,G',tn') ==>
  gas_origin_ptr_path (D,lo,E,ctx,fnc,PG) (s,G,tn) [] (r,G',tn') /\
  create_operand_full_scope a b E ctx fnc s [] r
Proof
  strip_tac >>
  qsuff_tac
    `!view st marks out. gas_origin_ptr_path view st marks out ==>
       view = (D,lo,E,obsctx,obsfn,PG) /\ marks = [] ==>
       case (st,out) of ((u,H,h),(rr,H',h')) =>
         create_cut_region a b u /\
         (case rr of OK t => create_operand_at b t | _ => exit_result rr) ==>
         gas_origin_ptr_path (D,lo,E,ctx,fnc,PG) (u,H,h) [] (rr,H',h') /\
         create_operand_full_scope a b E ctx fnc u [] rr`
  >- (disch_then drule >> simp[]) >>
  qpat_x_assum `gas_origin_ptr_path _ _ _ _` kall_tac >>
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac
  >- (simp[create_operand_full_scope_def,create_operand_at_def] >>
      metis_tac[cj 1 gas_origin_ptr_path_rules])
  >- (rpt gen_tac >> simp[] >> ntac 2 (strip_tac >> gvs[]) >> strip_tac >>
      rename1 `gas_origin_ptr_edge _ (u,_,_) [] (OK _,_,_)` >>
      `~create_operand_at b u` by metis_tac[] >>
      first_assum (drule_all_then strip_assume_tac) >>
      conj_tac
      >- metis_tac[cj 2 gas_origin_ptr_path_rules, APPEND]
      >> metis_tac[return_scope_prepend_empty]) >>
  rpt gen_tac >> simp[] >> ntac 2 (strip_tac >> gvs[]) >> strip_tac >>
  rename1 `gas_origin_ptr_edge _ (u,_,_) [] _` >>
  `~create_operand_at b u` by metis_tac[] >>
  first_assum (drule_all_then strip_assume_tac) >>
  conj_tac
  >- metis_tac[cj 3 gas_origin_ptr_path_rules]
  >> metis_tac[create_operand_full_scope_terminal, create_expr_prefix_nil,
       gas_origin_ptr_edge_def, create_operand_at_def, APPEND]
QED
