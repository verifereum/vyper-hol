(* TOP-LEVEL: configure. Project nested metadata getters before comparing
   their values; instruction payloads never need normalization for these fields. *)
structure compilerPassMetadataEvalLib = struct
  open HolKernel boolLib

  fun result current = let
    val [_,func,out] = snd (strip_comb current)
    val information = map compilerPassEffectsEvalLib.record_rules
      [type_of func,type_of out]
    val getters = List.concat (map #1 information)
    val rules = map Conv.REWR_CONV
      (DB.fetch "combin" "K_THM" :: List.concat (map #2 information))
    val k = prim_mk_const {Thy="combin",Name="K"}
    fun is_getter operator = is_const operator andalso
      (same_const operator k orelse List.exists (same_const operator) getters)
    fun value term =
      if is_comb term andalso is_getter (fst (strip_comb term)) then let
        val argument = Conv.RAND_CONV value term
        val body = rhs (concl argument)
        val rewritten = Conv.FIRST_CONV rules body
          handle HOL_ERR _ => REFL body | Conv.UNCHANGED => REFL body
        val next = rhs (concl rewritten)
      in if aconv body next then TRANS argument rewritten
        else TRANS argument (TRANS rewritten (value next)) end
      else REFL term
    fun project term =
      if boolSyntax.is_eq term then
        MK_COMB (AP_TERM (rator (rator term)) (value (lhs term)),value (rhs term))
      else if boolSyntax.is_conj term then let
        val (left,right) = boolSyntax.dest_conj term
      in MK_COMB (AP_TERM (rator (rator term)) (project left),project right) end
      else REFL term
    fun reduce term =
      if boolSyntax.is_eq term andalso aconv (lhs term) (rhs term) then
        EQT_INTRO (REFL (lhs term))
      else if boolSyntax.is_conj term then let
        val (left,right) = boolSyntax.dest_conj term
        val joined = MK_COMB
          (AP_TERM (rator (rator term)) (reduce left),reduce right)
      in TRANS joined (computeLib.EVAL_CONV (rhs (concl joined))) end
      else computeLib.EVAL_CONV term
    val operator = fst (strip_comb current)
    val prefix = compilerPassEffectsEvalLib.effects_step current
    val projected = evalCompilerBytecodeLib.timed_evaluation operator
      "nested metadata getters" (fn () => project (rhs (concl prefix)))
    val checked = evalCompilerBytecodeLib.timed_evaluation operator
      "projected metadata equality" (fn () => reduce (rhs (concl projected)))
  in TRANS prefix (TRANS projected checked) end

  fun configure () = compilerPassEvalLib.extend_phases []
    [(compilerPassEffectsEvalLib.head "fn_pass_effects_hold",result)] []
end
