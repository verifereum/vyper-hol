(* A pure source prefix preserves an exempt certificate at its endpoint. *)
Theory gasExemptPurePrefix
Ancestors
  gasExemptCert gasSummary fragGasMode fragGasPathMem vyperState

(* A guarded boolean read factors a pure prefix globally, including states
   outside the invariant. The fallback retains the original computation. *)
Theorem gas_exempt_cert_pure_prefix:
  (!gs. a (es with gas_obs := gs) = (INL v,es with gas_obs := gs)) /\
  ~s0.vs_halted /\
  gas_exempt_cert memory tops (ctx,func) (k v)
    (es with gas_obs := [],s0) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func) (bind a k)
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  qabbrev_tac `b = (\st. (INL (a st = (INL v,st)),st) : bool evaluation_result)` >>
  qabbrev_tac `h = (\flag. if flag then k v else bind a k)` >>
  `bind a k = bind b h` by
    (simp[FUN_EQ_THM, Abbr `b`, Abbr `h`, bind_def] >>
     qx_gen_tac `st` >> Cases_on `a st = (INL v,st)` >> simp[] >>
     gvs[bind_def]) >>
  pop_assum SUBST1_TAC >>
  `gas_marked_exec memory (ctx,func) b (es,s0) [] (INL T)
     (es with gas_obs := []) (OK s0)` by
    (simp[gas_marked_exec_def,gas_explicit_def,Abbr `b`] >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  drule gas_exempt_cert_bind_bool >> simp[Abbr `h`] >> disch_then irule >> simp[]
QED
