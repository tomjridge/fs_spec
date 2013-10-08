structure tactic = struct

local
open HolKernel boolLib Parse bossLib proofManagerLib computeLib List
in

(******************************************************************************)
(* bug in LET_INTRO *)

(* following taken from pairTools *)
local open pairTools HolKernel Parse boolLib pairSyntax pairTheory in
fun flat_vstruct tuple rhs =
  let 
    (* behaviour of mk_fst and mk_snd should match PairedLambda.GEN_BETA_CONV in LET_INTRO *)
    val mk_fst = fn tm => if is_pair tm then #1 (dest_pair tm) else mk_fst tm
    val mk_snd = fn tm => if is_pair tm then #2 (dest_pair tm) else mk_snd tm
    fun flat tuple (v,rhs) =
      if is_var tuple then [(tuple, rhs)]
      else let val (fst,snd) = dest_pair tuple
           in  flat fst (v, mk_fst rhs) @
               flat snd (v, mk_snd rhs)
           end
  in map mk_eq (flat tuple (genvar alpha,rhs))
  end;
local val LET_THM1 = GSYM LET_THM
      val PAIR_RW = PURE_REWRITE_RULE [pairTheory.PAIR]
      fun lhs_repl th = (lhs(concl th) |-> th)
in
fun LET_INTRO thm =
  let 
      val (ant,conseq) = dest_imp(concl thm)
      val (lhs,rhs) = dest_eq ant
      val bindings = flat_vstruct lhs rhs
(*      val _ = map print_term bindings *)
(*      val _ = raise (ERR "here" "1") *)
      val thl = map ASSUME bindings
      val th0 = UNDISCH thm
(*      val _ = raise(ERR "" (thm_to_string th0)) *)
      val th1 = SUBS thl th0
      val Bredex = mk_comb(mk_pabs(lhs,conseq),rhs)
(*      val _ = raise (ERR (term_to_string(( Bredex))) "")
      val _ = raise(ERR (thm_to_string(GSYM(PairedLambda.GEN_BETA_CONV Bredex))) (thm_to_string th1)) *)
      val th2 = EQ_MP (GSYM(PairedLambda.GEN_BETA_CONV Bredex)) th1
      val th3 = PURE_ONCE_REWRITE_RULE[LET_THM1] th2
      val vstruct_thm = SUBST_CONV (map lhs_repl thl) lhs lhs;
      val th4 = PROVE_HYP (PAIR_RW vstruct_thm) th3
  in
  rev_itlist (fn bind => fn th =>
                 let val th' = DISCH bind th
                     val (lhs,rhs) = dest_eq bind
                 in MP (Thm.INST [lhs |-> rhs] th') (REFL rhs) end)
               bindings th4
  end
end;
fun unpabs tm =
   let val (vstr,body) = dest_pabs tm
       val V = free_vars_lr vstr
   in list_mk_abs(V,body)
   end
local
fun dot 0 vstr tm away = (vstr,tm)
  | dot n vstr tm away =
    let val (Bvar,Body) = dest_abs tm
        val v' = variant away Bvar
        val tm'  = beta_conv(mk_comb(tm, v'))
        val vstr' = subst[Bvar |-> v'] vstr
    in dot (n-1) vstr' tm' (v'::away)
    end
in
(*---------------------------------------------------------------------------
 * Alpha convert to ensure that variables bound by the "let" are not
 * free in the assumptions of the goal. Alpha-convert in reverse on way
 * back from achieving the goal.
 *---------------------------------------------------------------------------*)
val LET_INTRO_TAC :tactic =
fn  (asl,w) =>
  let 
      val (func,arg) = dest_let w
      val func' = unpabs func
      val (vstr,body) = dest_pabs func
      val away0 = Lib.op_union aconv (free_vars func) (free_varsl asl)
      val (vstr', body') = dot (length (free_vars vstr)) vstr func' away0
      val bind = mk_eq(vstr', arg)
  in
  ([(asl,mk_imp(bind,body'))],
   fn [th] => let val let_thm = LET_INTRO th
(*      val _ = raise(ERR (thm_to_string (ALPHA (concl let_thm) w)) (thm_to_string let_thm)) *)
               in EQ_MP (ALPHA (concl let_thm) w) let_thm end)
  end
end
end;


(******************************************************************************)
(* lifter from Q *)

fun normalise_quotation frags =
  case frags of
    [] => []
  | [x] => [x]
  | (QUOTE s1::QUOTE s2::rest) => normalise_quotation (QUOTE (s1^s2) :: rest)
  | x::xs => x :: normalise_quotation xs

fun contextTerm ctxt q = Parse.parse_in_context ctxt (normalise_quotation q);

fun ptm_with_ctxtty ctxt ty q =
 let val q' = QUOTE "(" :: (q @ [QUOTE "):", ANTIQUOTE(ty_antiq ty), QUOTE ""])
 in Parse.parse_in_context ctxt (normalise_quotation q')
end;

fun QTAC_OF_TMTAC tmtac q (g as (asl,w)) = 
    let val ctxt = free_varsl (w::asl)
    in
        tmtac (contextTerm ctxt q) g
    end


(******************************************************************************)
(* simp depth limit ... *)

val my_ss_limit = ref 10;


(* FIXME THIN_TAC should fail if asm not present, also THIN_TAC seems to take no notice of free vars *)

val CUT = PROVE_HYP;

(* dangerous *)
val CHEAT_TAC = fn (asl,w) => ([], fn [] => mk_thm (asl,w));

(* for matching curried rules *)
val MATCH_MP_TAC' = 
    let
	val r = PROVE [] ``(XXP ==> XXQ ==> XXR) = (XXP /\ XXQ ==> XXR)``
    in
	fn th => MATCH_MP_TAC th ORELSE MATCH_MP_TAC (SIMP_RULE std_ss [r] th)
    end;


val PIERCE = PROVE [] ``(((XXP ==> F) ==> F) ==> XXP)``;


(******************************************************************************)
(* tacticals *)

(* version of PAT_ASSUM that doesn't remove asm *)

local
  fun match_with_constants constants pat ob = let
    val (tm_inst, ty_inst) =
        ho_match_term [] empty_tmset pat ob
    val bound_vars = map #redex tm_inst
  in
    null (intersect constants bound_vars)
  end handle HOL_ERR _ => false
in
fun PAT_ASSUM pat thfun (asl, w) =
  case List.filter (can (ho_match_term [] empty_tmset pat)) asl
   of []  => raise ERR "PAT_ASSUM" "No assumptions match the given pattern"
    | [x] => let val (ob, asl') = Lib.pluck (Lib.equal x) asl
             in thfun (ASSUME ob) (asl, w)
             end
    |  _  =>
      let val fvars = free_varsl (w::asl)
          val (ob,asl') = Lib.pluck (match_with_constants fvars pat) asl
      in thfun (ASSUME ob) (asl,w)
      end
end;

val TM_PAT_X_ASSUM = Tactical.PAT_ASSUM;

val PAT_X_ASSUM = Q.PAT_ASSUM;

fun ITAC_OF_THM_TAC tt i = ASSUM_LIST (fn ths => tt (List.nth(List.rev ths,i)));

(* version of FIRST_ASSUM that actually applies to the first (numberwise) assumption *)

fun FIRST_ASSUM ttac (A,g) =
   let fun find ttac []     = raise ERR "FIRST_ASSUM"  ""
         | find ttac La =
             let val (L,a) = (Lib.butlast La, List.last La) in
             (ttac (ASSUME a) (A,g) handle HOL_ERR _ => find ttac L)
             end
   in find ttac A
   end;



(* this taken directly from Tactical.sml *)
local fun UNDISCH_THEN tm ttac (asl, w) =
       let val (_,A) = Lib.pluck (equal tm) asl in ttac (ASSUME tm) (A,w) end
in
fun FIRST_X_ASSUM ttac = FIRST_ASSUM (fn th => UNDISCH_THEN (concl th) ttac)
end;



(******************************************************************************)
(* variables *)

val RENAME_TAC = 
 fn sigma => (* sig is a variable to variable (term to term) substitution, e.g. x->y *)
 fn (asl,w) => 
    let 
	val sub = subst sigma
	val (asl',w') = (List.map sub asl, sub w)
	val sig' = List.map (fn {redex,residue} => {residue=redex,redex=residue}) sigma
    in
	([(asl',w')],fn [th] => INST sig' th)
    end;

(* hack to print the freevars of a goal- useful for checking initial goals *)
val FV_TAC = fn (asl,w) =>
  let val fvs = free_varsl (asl@[w])
      val _ = map (fn fv => (print_term fv; print_type (type_of fv); print("\n"))) fvs
  in ALL_TAC (asl,w) end;

val CLOSED_TAC = fn (asl,w) =>
  let val fvs = free_varsl (asl@[w])
      val _ = map (fn fv => (print_term fv; print_type (type_of fv); print("\n"))) fvs
      val _ = if fvs = [] then () else raise (ERR "CLOSE_TAC" "")
  in ALL_TAC (asl,w) end;


(******************************************************************************)
(* assumption handling *)

(*

peqp'
---------
G |- p=p'
-----------
G |- p==>p'      p'C
-----------     ----------
p,G |- p'        p',G |- C
---------------------------
p,G |- C

*)

val ASM_CONV_RULE =
 fn peqp' =>
 fn p'C =>
    let
	val pimpp' = fst (EQ_IMP_RULE peqp')
	val pp' = UNDISCH pimpp'
        val pC = CUT pp' p'C
    in
	pC
    end handle e as HOL_ERR _ => raise wrap_exn "ASM_CONV_RULE" "" e;

(* int is the assumption to conv *)
val (ASM_CONV_TAC:(thm list->conv)->int->tactic) =
 fn conv => 
 fn i => 
 fn (asl,w) =>
    let
val _ = if length asl <= i then raise Subscript else ()
	val i' = length asl - i - 1
	val (asll,p,aslr) = (take(asl,i'), nth(asl,i'), drop (asl,(i'+1)))
	val peqp' = conv (map ASSUME (asll@aslr)) p
	val p' = snd (dest_eq (concl peqp'))
    in
	([(asll@[p']@aslr,w)], fn [p'C] => ASM_CONV_RULE peqp' p'C)
    end handle e as UNCHANGED => raise wrap_exn "ASM_CONV_TAC" "UNCHANGED" e;

val ASM_EVAL_TAC = ASM_CONV_TAC (fn ths => EVAL);

val ASM_RESTR_EVAL_TAC = fn tms => ASM_CONV_TAC (fn ths => computeLib.RESTR_EVAL_CONV tms);

val assimp = fn ths1 => ASM_CONV_TAC (fn ths => SIMP_CONV (srw_ss()) (ths@ths1)); (* SIMP_CONV can throw unchanged *)
val asimp = fn ths1 => ASM_CONV_TAC (fn ths => SIMP_CONV (std_ss) (ths@ths1));


(******************************************************************************)
(* structural *)

val MY_ASSUME_TAC:thm_tactic = 
 fn bth => 
 fn (asl,w) =>
    ([(asl@[concl bth],w)], (fn [th] => CUT bth th));

val THIN_TAC:thm->tactic = fn th => fn (asl,w) => ([(filter (fn tm => not (aconv tm (concl th))) asl,w)],fn [th] => th);

val TM_THIN_TAC = fn tm =>(TM_PAT_X_ASSUM tm (fn th => ALL_TAC)); 

val Q_THIN_TAC = fn q => Q.PAT_ASSUM q (fn th => ALL_TAC);

val Q_THINS_TAC = fn qs => EVERY (List.map Q_THIN_TAC qs);

val TM_REORDER_TAC = fn tm => TM_PAT_X_ASSUM tm (fn th => MY_ASSUME_TAC th);

val TM_SUBTERM_REORDER_TAC = fn tm => 
  FIRST_ASSUM (fn th => if free_in tm (concl th) then TM_REORDER_TAC (concl th) else failwith "TM_SUBTERM_REORDER_TAC");

val SUBTERM_REORDER_TAC = QTAC_OF_TMTAC TM_SUBTERM_REORDER_TAC;

val REORDER_TAC = QTAC_OF_TMTAC TM_REORDER_TAC;

val TM_REMOVE_VAR_TAC = fn v => REPEAT (FIRST_X_ASSUM (fn th => if free_in v (concl th) then ALL_TAC else raise ERR "tactic" "REMOVE_VAR_TAC"));

fun REMOVE_VAR_TAC q = fn (g as (asl,w)) =>
    let val ctxt = free_varsl (w::asl)
    in
        TM_REMOVE_VAR_TAC (contextTerm ctxt q) g
    end

fun REMOVE_VARS_TAC qs = EVERY (List.map REMOVE_VAR_TAC qs);
                   

val CUT_TAC:term->tactic = fn tm => fn (asl,w) => ([(asl,tm),(asl@[tm],w)], fn [th1,th2] => CUT th1 th2);

val REV_CUT_TAC = fn tm => fn (asl,w) => ([(asl@[tm],w),(asl,tm)], fn [th2,th1] => CUT th1 th2);

(******************************************************************************)
(* standard propositional *)

val INIT_TAC = FIRST_ASSUM ACCEPT_TAC;
val FALSEL_TAC = FIRST_ASSUM CONTR_TAC;
val TRUER_TAC:tactic = fn (asl,w) => if aconv w ``T`` then ([],fn _ => TRUTH) else raise ERR "TRUER_TAC" "";

val CONJL'_TAC : thm_tactic = 
 fn th => 
    let val (th1,th2) = CONJ_PAIR th in
	MY_ASSUME_TAC th1 THEN MY_ASSUME_TAC th2 end;

val CONJL_TAC : tactic = FIRST_X_ASSUM CONJL'_TAC;

val CONJR_TAC = CONJ_TAC;

val DISJL_TAC = FIRST_X_ASSUM DISJ_CASES_TAC;

val DISJR1_TAC = DISJ1_TAC;

val DISJR2_TAC = DISJ2_TAC;

val IMPR_TAC = DISCH_TAC;
			
val IMPL_TAC = 
 fn th => 
 fn (asl,w) => 
		   let
val (a,b) = dest_imp (concl th)
val asl' = filter (fn a => not (aconv a (concl th))) asl 
		   in
			 ([(asl',a),(asl'@[b],w)],fn [th1,th2] => PROVE_HYP (MP th th1) th2) 
		   end


(******************************************************************************)
(* quantifiers *)

val MYSPEC = fn tm => fn th => SPEC tm th handle e => PairRules.PSPEC tm th;

val TM_FORALLL_TAC = fn th => fn tm => MY_ASSUME_TAC (MYSPEC tm th);
val TM_FORALLL_X_TAC = fn th => fn tm => TM_FORALLL_TAC th tm THEN THIN_TAC th;
val FORALLR_TAC = GEN_TAC;

val FORALLL_TAC = fn q => FIRST_ASSUM (fn th => QTAC_OF_TMTAC (TM_FORALLL_TAC th) q);
val FORALLL_X_TAC = fn q => FIRST_X_ASSUM (fn th => QTAC_OF_TMTAC (TM_FORALLL_TAC th) q);

val EXL_TAC = FIRST_X_ASSUM CHOOSE_TAC; (* FIXME should put first, or retain position...probably the latter *)
val TM_EXR_TAC = EXISTS_TAC;
val EXR_TAC = Q.EXISTS_TAC;

(* for pulling a particular quantified variable to the front *)

fun rem1 x xs = case xs of 
  [] => failwith "rem1"
  | y::ys => if x = y then ys else y::(rem1 x ys);

val PULL_QUANT_TAC = 
  fn tm =>
  fn (asl,w) =>
  let
    val qs = #1 (strip_forall w) 
    val qs' = rem1 tm qs 
    val UNFORALL_TACS = List.map (fn x => SPEC_TAC (x,x)) qs'
    val tac = REPEAT FORALLR_TAC THEN (EVERY UNFORALL_TACS) THEN (SPEC_TAC (tm,tm))
  in
    tac (asl,w)
  end;
    


(******************************************************************************)
(* equality *)

val EQR_TAC = EQ_TAC THEN IMPR_TAC;
val EQL_TAC = FIRST_X_ASSUM (fn p_eq_q => let val (p_imp_q, q_imp_p) = EQ_IMP_RULE p_eq_q in (ASSUME_TAC p_imp_q) THEN (ASSUME_TAC q_imp_p) end);;
(*val SYM_TAC = fn tm => TM_PAT_X_ASSUM tm (fn th => ASSUME_TAC (SYM th));*)
val SYM_TAC = fn q => Q.PAT_ASSUM q (fn th => MY_ASSUME_TAC (SYM th));

val UNFOLD_TAC = fn th => CONV_TAC (unwindLib.UNFOLD_CONV [th]);

(******************************************************************************)
(* let *)

val let_sym = PROVE [] ``((x=y)==>z) ==> ((y=x)==>z)``;

val MY_LET_INTRO_TAC = LET_INTRO_TAC THEN MATCH_MP_TAC let_sym;

val MY_LET_INTRO_ONCE_TAC = MY_LET_INTRO_TAC THEN IMPR_TAC;

val MY_LET_INTRO_TAC = MY_LET_INTRO_ONCE_TAC THEN REPEAT MY_LET_INTRO_ONCE_TAC;

val let_scope = simpLib.SIMP_PROVE (srw_ss()) [LET_THM] 
  ``((let x = y in z x) ==> q) = (let x = y in (z x) ==> q)``;;

(*
val let_scope_2 = simpLib.SIMP_PROVE (srw_ss()) [LET_THM] 
  ``((let (x,x') = y in z x x') ==> q) = (let (x,x') = y in (z x x') ==> q)``;;
*)
(*SIMP_CONV (srw_ss()) [LET_THM] ``(let (x,x') = y in z x x') ==> q``;*)
(* seems we have to case split manually *)

(* probably the following only works for simple lets, not paired *)

(* 
``LET (\ x. y ==> q) z ``;

``(LET (\ x. y ) z) ==> q``;

``(LET (UNCURRY (\ x1 x2. y)) z) ==> q``;

``(LET (UNCURRY (\ x1 x2. y ==> q)) z)``;
*)

val MY_LET_ELIM_TAC = 
    FIRST_ASSUM (
    fn th => 
       UNDISCH_TAC (concl th) 
                   THEN CHANGED_TAC (ONCE_REWRITE_TAC [let_scope])
                   THEN MY_LET_INTRO_TAC);


(******************************************************************************)
(* let on the left *)

(* given a term of the form 

let x1 = y1 in
...
let xn = yn in
z

produce a goal of the form 

? x1 ... xn. (y1 = x1) /\ ... /\ (yn = xn)

solve it by tac[], giving an extra assumption which can then be eliminated (maybe we should eliminate it?)

FIXME doesn't currently work with patterns for xi?

*)

val tmptm = ``let x = 1 in let y = 2 in 3``;
 
val my_dest_let = 
 fn tm => 
    let 
      val (lam,v) = dest_let tm 
      val (var,body) = dest_abs lam 
    in
      (var,v,body)
    end

val tmpa = my_dest_let tmptm                     

val rec my_dest_lets = 
 fn tm =>                     
    if (is_let tm) then 
      let
        val (var,v,body) = my_dest_let tm
      in
        (var,v)::(my_dest_lets body)
      end
    else
      []

val tmpa = my_dest_lets tmptm        

(* take a list of var,val bindings and construct the term *)
val rec my_let_term' = 
 fn xs => (case xs of 
             [] => ``T`` 
           | (var,v)::xs => (
          let 
            val rest = my_let_term' xs 
          in 
            ``(^v = ^var) /\ ^rest``
          end))

val tmpb = my_let_term' tmpa

val my_let_term = 
 fn tm => 
    let
      val xs = my_dest_lets tm 
    in
      foldr (fn (a,b) => mk_exists (a,b)) (my_let_term' xs) (List.map fst xs)
    end

val tmpc = my_let_term tmptm      

val LET_LEFT_TAC : term -> tactic = 
  fn tm => 
     CUT_TAC (my_let_term tm) 
     
           




(******************************************************************************)
(* combinations *)

val intros = REPEAT (IMPR_TAC ORELSE FORALLR_TAC);
val elims = REPEAT (EXL_TAC ORELSE CONJL_TAC);

val cintros = REPEAT (IMPR_TAC ORELSE FORALLR_TAC ORELSE CONJR_TAC);

fun defer () = rotate 1;


(******************************************************************************)
(* abbreviations *)

val ii = fn () => e INIT_TAC;
val cu = fn tm => e (CUT_TAC tm);
val fl = fn () => e (FALSEL_TAC);
val ir = fn () => e IMPR_TAC;
val il = fn i => e(ITAC_OF_THM_TAC IMPL_TAC i);
val cr = fn () => e CONJR_TAC;
val dl = fn () => e DISJL_TAC;
val dr1 = fn () => e DISJR1_TAC;
val dr2 = fn () => e DISJR2_TAC;
val al = fn q => e(FORALLL_TAC q);
val xal = fn q => e(FORALLL_X_TAC q);
val ar = fn () => e(FORALLR_TAC);
val er = fn q => e(EXR_TAC q);
(* el already bound *)
val eql = fn () => e EQL_TAC;


(******************************************************************************)
(* QCUT_TAC *)

fun QCUT_TAC q (g as (asl,w)) =
let val ctxt = free_varsl (w::asl)
in CUT_TAC (ptm_with_ctxtty ctxt Type.bool q) g
end;

fun Q_REV_CUT_TAC q (g as (asl,w)) =
let val ctxt = free_varsl (w::asl)
in REV_CUT_TAC (ptm_with_ctxtty ctxt Type.bool q) g
end;


val have = fn x => e(QCUT_TAC x);

val want = fn x => e(Q_REV_CUT_TAC x); 


(******************************************************************************)
(* simplification and first order proof *)

(* apply tac1 to all asms, until nothing changes, then apply tac2 *)

fun pre_simp tac1 tac2:tactic = fn (asl,w) => 
  let val ns = Lib.upto 0 (length asl  - 1)
      val tacs = map (fn i => TRY (tac1 i)) ns
      val ssimp_once = EVERY tacs
      val tac = 
		    (REPEAT (CHANGED_TAC ssimp_once))
		    THEN tac2
		    THEN (TRY (FALSEL_TAC ORELSE TRUER_TAC))
		    THEN elims
  in
	tac (asl,w)
  end;

val simp:thm list->tactic = fn ths => pre_simp (asimp ths) (ASM_SIMP_TAC (std_ss) ths);

val ssimp = fn ths => pre_simp (assimp ths) (ASM_SIMP_TAC (srw_ss()) ths);

val tac = METIS_TAC;



(******************************************************************************)
(* converting a cases into a list of individual clauses *)

fun dest_fun_type ty = case dest_type ty of 
			   ("fun",[a,b]) => [a,b];

val is_fun_type = can dest_fun_type;

val strip_fun_ty = 
    repeat (fn ty => case dest_fun_type ty of [a,b] => b)

fun rewrite_def def tm = 
    let
	val ty = type_of tm

	val constructors = 
	    let
		fun f con = 
		    let
			val ty2 = type_of con
			val ty' = strip_fun_ty ty2
			val tyinst = match_type ty' ty
		    in
			inst tyinst con
		    end
	    in
		    map f (TypeBase.constructors_of ty)		    
	    end
	    
	val cons2 = 
	    map (repeat (fn tm => 
			    let
				val ty = type_of tm
			    in
				if is_fun_type ty then 
				    let 
					val argty = hd(dest_fun_type(ty))
				    in
				    mk_comb(tm,mk_var("x",argty))
				    end
				else
				    failwith ""
			    end))
		constructors
		
	val insts2 = map (fn c => ISPEC c (GEN tm (SPEC_ALL def))) cons2
		     
	val rs = map (SIMP_RULE (srw_ss()) []) insts2
    in
	LIST_CONJ rs
    end;


end
end;


