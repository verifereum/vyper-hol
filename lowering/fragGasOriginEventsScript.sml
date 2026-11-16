(* A source focus may stop inside INVOKE, before a terminal result exists. *)
Theory fragGasOriginEvents
Ancestors
  fragGasOrigin fragGasFocus fragExec gasEvents gasEventsFuel
  venomExecSemantics venomExecProofs venomInst venomInstProofs
  venomState list rich_list arithmetic pred_set

(* Transport through paths depends only on the edge observation contract. *)
Theorem gas_origin_path_prefix_lift:
  (!ctx func s left t n.
     gas_origin_edge memory explicit ctx func s left (OK t) ==>
     ?m extra. observe ctx func s m = left ++ observe ctx func t n ++ extra) ==>
  !ctx func s left t n.
    gas_origin_path memory explicit ctx func s left (OK t) ==>
    ?m extra. observe ctx func s m = left ++ observe ctx func t n ++ extra
Proof
  qsuff_tac
       `!memory explicit ctx func s left r.
          gas_origin_path memory explicit ctx func s left r ==>
          !t n. r = OK t ==>
          (!ctx func s left t n.
             gas_origin_edge memory explicit ctx func s left (OK t) ==>
             ?m extra.
               observe ctx func s m = left ++ observe ctx func t n ++ extra) ==>
          ?m extra.
            observe ctx func s m = left ++ observe ctx func t n ++ extra`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> qexistsl [`n`, `[]`] >> simp[])
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `!n. ?m extra. _` (qspec_then `n` strip_assume_tac) >>
      qpat_x_assum `!ctx func s left t n. _` drule >>
      disch_then (qspec_then `m` strip_assume_tac) >>
      metis_tac[APPEND_ASSOC])
  >> rpt strip_tac >> gvs[exit_result_def]
QED

Theorem gas_origin_focus_events_prefix:
  !memory explicit ctx func s marks leaf t.
    gas_origin_focus memory explicit (ctx,func) s marks (leaf,t) ==>
    ?fuel extra.
      MAP (\key. key IN explicit)
        (case lookup_block s.vs_current_bb func.fn_blocks of
           NONE => []
         | SOME bb =>
             gas_events_block fuel ctx func.fn_name bb s ++
             case exec_block fuel ctx bb s of
               OK u => if u.vs_halted then []
                       else gas_events_blocks fuel ctx func u
             | _ => []) = marks ++ extra
Proof
  (* Local proof target; removed by the origin-prefix proof task. *)
  cheat
QED
