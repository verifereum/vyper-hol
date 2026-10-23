(* Conditional continuation composition only: this theory does not establish
   execution of any emitted decoder loop. Local progress must be proved by
   concrete code adapters, with their memory/frame invariants, by consumers. *)
Theory abiDecoderLoop
Ancestors
  fragExec abiDecoderComposition arithmetic

Definition abi_decode_sim_def:
  abi_decode_sim ctx fn s t <=>
    !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r
End

Theorem abi_decode_sim_refl:
  abi_decode_sim ctx fn s s
Proof
  simp[abi_decode_sim_def] >> metis_tac[]
QED

Theorem abi_decode_sim_trans:
  abi_decode_sim ctx fn s t /\ abi_decode_sim ctx fn t u ==>
  abi_decode_sim ctx fn s u
Proof
  rw[abi_decode_sim_def] >> metis_tac[]
QED

(* Induction is entirely over naturals. In particular, no equality of fuels
   is required for the child or for successive iterations. *)
Theorem abi_decode_finite_iteration:
  !(bound:num) i loop_inv Q ctx fn s.
  i <= bound /\ loop_inv i s /\
  (!j u. loop_inv j u /\ j < bound ==>
    ?v. loop_inv (SUC j) v /\ abi_decode_sim ctx fn u v) /\
  (!u. loop_inv bound u ==> ?v. Q v /\ abi_decode_sim ctx fn u v) ==>
  ?t. Q t /\ abi_decode_sim ctx fn s t
Proof
  completeInduct_on `(bound:num) - i` >> rpt strip_tac >>
  Cases_on `i = bound`
  >- metis_tac[] >>
  `i < bound` by decide_tac >>
  `?v. loop_inv (SUC i) v /\ abi_decode_sim ctx fn s v` by metis_tac[] >>
  rename1 `loop_inv (SUC i) next` >>
  `?t. Q t /\ abi_decode_sim ctx fn next t` by
    (qpat_x_assum `!m. m < _ ==> _` (qspec_then `bound - SUC i` mp_tac) >>
     impl_tac >- decide_tac >>
     disch_then (qspecl_then [`bound`, `SUC i`] mp_tac) >>
     simp[] >> disch_then irule >> simp[] >>
     qexists_tac `loop_inv` >> simp[]) >>
  metis_tac[abi_decode_sim_trans]
QED

(* Extract the endpoint and the exact continuation simulation from a fragment
   whose exit predicate is false. fn_has_code remains an explicit premise. *)
Theorem abi_decode_sim_from_fragment:
  frag_exec ctx st st' P Q (K F) /\ fn_has_code st st' fn /\ P s /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. Q t /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx fn s t
Proof
  simp[frag_exec_def, abi_decode_sim_def] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_LOOP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder loop boundary not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderLoop");
