(* Generic EVAL configuration. No fixture results or selector cache.
   Closed ABI selector applications use the upstream kernel-checked CV
   translation; all other applications retain ordinary logical evaluation. *)
structure supportedEvalLib : sig
  val function_selector_conv : Abbrev.conv
  val configure : unit -> unit
end =
struct
  open HolKernel boolLib
  local
    open contractABITheory selectorDispatchTheory
    val selector = prim_mk_const {Thy="contractABI",Name="function_selector"}
    val fallback = REWR_CONV function_selector_compute
    fun checked tm th =
      let val (l,r) = boolSyntax.dest_eq (Thm.concl th)
          val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
      in
        if aconv l tm andalso type_of l = type_of r andalso
           null (Thm.hyp th) andalso null axioms andalso
           List.all (fn s => s = "DISK_THM") oracles
        then th else raise Fail "unsupported CV theorem"
      end
    fun selector_conv tm =
      let val (head,args) = strip_comb tm
          val () = if aconv head selector andalso length args = 2 then ()
                   else raise mk_HOL_ERR "supportedEvalLib" "function_selector_conv"
                     "expected a saturated contractABI$function_selector application"
          fun ordinary () = checked tm (fallback tm)
      in
        if not (null (free_vars tm)) orelse not (null (type_vars_in_term tm))
        then ordinary ()
        else (checked tm (cv_transLib.cv_eval tm)
              handle HOL_ERR _ => ordinary () | Fail _ => ordinary ())
      end
    (* Equations at this arity precede external conversions in computeLib.
       Remove both competing equations, rather than adding an unreachable
       callback. The existing proved equation is the total fallback. *)
  in
    val function_selector_conv = selector_conv

    fun configure () =
      let
        (* Existing rewrite RHSs retain refs to a removed constant's old
           dispatch cell. Reinstall its direct callers against the new cell;
           their own cells stay live, so higher callers need no changes. *)
        val rules = List.concat (List.concat (map
          (fn (_,xs) => map (fn clauses.RRules ths => ths
                            | clauses.Conversion _ => []) xs)
          (computeLib.listItems (computeLib.the_compset ()))))
        val callers = List.filter (fn th =>
          let val (_,body) = strip_forall (concl th)
              val (_,r) = boolSyntax.dest_eq body
          in can (find_term (aconv selector)) r end
          handle HOL_ERR _ => false) rules
      in
        computeLib.del_funs [function_selector_compute, function_selector_def];
        computeLib.add_convs [(selector,2,selector_conv)];
        computeLib.add_funs callers;
        computeLib.upd_compset (wordsLib.add_words_compset true)
      end
  end
end
