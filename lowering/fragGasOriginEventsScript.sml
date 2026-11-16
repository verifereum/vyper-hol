(* A source focus may stop inside INVOKE, before a terminal result exists. *)
Theory fragGasOriginEvents
Ancestors
  fragGasOrigin fragGasFocus fragExec gasEvents gasEventsFuel
  venomExecSemantics venomExecProofs venomInst venomInstProofs
  venomState list rich_list arithmetic pred_set

Theorem gas_origin_focus_prefix_lift:
  (!ctx func s left t n.
     gas_origin_path memory explicit ctx func s left (OK t) ==>
     ?m extra. Obs ctx func s m = left ++ Obs ctx func t n ++ extra) /\
  (!ctx func s callee entered n.
     gas_invoke_entry (ctx,func) s callee entered ==>
     ?extra. Obs ctx func s (SUC n) = Obs ctx callee entered n ++ extra) ==>
  !ctx func s marks leaf t.
    gas_origin_focus memory explicit (ctx,func) s marks (leaf,t) ==>
    ?fuel extra. Obs ctx func s fuel = marks ++ extra
Proof
  qsuff_tac
    `!memory explicit p s marks q.
       gas_origin_focus memory explicit p s marks q ==>
       !Obs.
         (!ctx func s left t n.
            gas_origin_path memory explicit ctx func s left (OK t) ==>
            ?m extra. Obs ctx func s m = left ++ Obs ctx func t n ++ extra) /\
         (!ctx func s callee entered n.
            gas_invoke_entry (ctx,func) s callee entered ==>
            ?extra. Obs ctx func s (SUC n) = Obs ctx callee entered n ++ extra) ==>
         ?fuel extra. Obs (FST p) (SND p) s fuel = marks ++ extra`
  >- (rpt strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  ho_match_mp_tac gas_origin_focus_ind >> conj_tac
  >- (rpt strip_tac >> simp[] >>
      first_x_assum drule >>
      disch_then (qspec_then `0` strip_assume_tac) >>
      metis_tac[APPEND_ASSOC]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      first_x_assum (qspec_then `Obs` mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      first_x_assum drule >>
      disch_then (qspec_then `fuel` strip_assume_tac) >>
      gvs[] >> metis_tac[APPEND_ASSOC]) >>
  rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `Obs` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  first_x_assum drule >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  gvs[] >> metis_tac[APPEND_ASSOC]
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
