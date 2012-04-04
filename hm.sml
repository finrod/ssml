structure TyEval =
struct
    structure A = Ast

    val tyvarCounter = ref 0
    fun freshTy () = 
        A.TyVar (!tyvarCounter) before tyvarCounter := (!tyvarCounter) + 1
    val reset = tyvarCounter := 0

    datatype cdecl   = TDef of A.knd * A.ty | TDec of A.knd | VDec of A.ty
    datatype closure = CPair of cdecl * (A.name * closure) list
    type environment = (A.name * closure) list

    fun lookup (x : Ast.name) (env : environment) =
	(case List.find (fn (y, _) => x = y) env of
	     SOME (_, t) => t
	   | NONE => raise Fail ("Undeclared identifier " ^ x))

    (* Kinding of types. Req's an environment mapping tyids to kinds and possibly definitions *)
    fun infKnd E (t as A.TyId x) =
	(case lookup x E of
	     CPair (TDef (k, _), _) => (k, t)
	   | CPair (TDec k, _) => (k, t)
	   | _ => raise Fail ("Identifier is not a type"))
      | infKnd _ (t as A.TyVar x) = (A.KTy, t)
      | infKnd _ (t as A.TyPoly x) = (A.KTy, t)
      | infKnd E (t as A.TyApp (t1, t2)) =
	let val f = Fail ("Kind mismatch at type expression " ^ A.ppty t)
	in (case (infKnd E t1, infKnd E t2) of
		((A.KArr (k1, k2), t1'), (k1', t2')) => if k1 = k1' then (k2, A.TyApp (t1', t2'))
							else raise f
	      | _ => raise f)
	end
      | infKnd E (A.TySig ds) = let val (_, ds') = kindSig E ds
				in  (A.KSig, A.TySig ds') end
      | infKnd E (t as A.TyArrow (t1, t2)) =
	let val (k1, t1') = infKnd E t1
	    val (k2, t2') = infKnd E t2
	in (case (k1, k2) of
		(A.KSig, A.KTy) => A.KTy
	      | (A.KTy, A.KTy) => A.KTy
	      | (A.KSig, A.KSig) => A.KSig
	      (* kind of types of functors (if I get things right, that is) *)
	      | _ => raise Fail ("First-class modules or some weird miskinding in " ^ A.ppty t),
	   A.TyArrow (t1', t2'))
	end
      | infKnd E (t as A.TyImpArr (t1, t2)) =
	let val (A.KSig, t1') = infKnd E t1
	    val (k2, t2') = infKnd E t2
	in (k2, A.TyImpArr (t1', t2'))
	end
      | infKnd E (A.TyLam (x, k, t)) =
	let val (kb, tb') = infKnd ((x, CPair (TDec k, E)) :: E) t
	in (A.KArr (k, kb), A.TyLam (x, k, tb')) end
      | infKnd E (t as A.TyLongName (xs, x)) =
	let fun aux (x, E) = (case lookup x E of
			       CPair (VDec (A.TySig ds), E') => #1 (kindSig E' ds) (* inefficient *)
			     | _ => raise Fail "Not structure declaration")
	    val E' = List.foldl aux E xs
	in case lookup x E' of
	       CPair (TDec k, _) => (k, t)
	     | CPair (TDef (k, _), _) => (k, t)
	     | _ => raise Fail "Not a type declaration"
	end
      | infKnd _ (A.TyInt) = (A.KTy, A.TyInt)
    and kindSig E [] = (E, [])
      | kindSig E (d :: ds) =
	(case d of
	     A.DTyDef (x, t, ok) =>
	     let val (k, t')  = infKnd E t
		 val k' = A.foldO (fn x => if (x = k) then x else raise Fail ("Kind mismatch")) k ok
		 val (E', ds') = kindSig ((x, CPair (TDef (k', t'), E)) :: E) ds
	     in (E', A.DTyDef (x, t', SOME k') :: ds')
	     end
	   | A.DTyDec (x, k) => let val (E', ds') = kindSig ((x, CPair (TDec k, E)) :: E) ds
				in (E', d :: ds') end
	   | A.DValDec (x, t) => let val (k, t') = infKnd E t
				     val (E', ds') = if k = A.KTy orelse k = A.KSig
						     then kindSig ((x, CPair (VDec t', E)) :: E) ds
						     else raise Fail "Not ground type for value"
				 in (E', A.DValDec (x, t') :: ds') end
	   | A.DData (x, k, cs) =>
	     let val (E', cs') = evalCons ((x, CPair (TDec k, E)) :: E) cs
		 val (E'', ds') = kindSig E' ds
	     in (E'', A.DData (x, k, cs') :: ds') end)
    and evalCons E [] = (E, [])
      | evalCons E ((n, t) :: cs) =
	let val (k, t') = infKnd E t
	    val _ = if k = A.KTy then () else raise Fail "Kind mismatch"
	    val (E', cs') = evalCons ((n, CPair (VDec t', E)) :: E) cs
	in (E', (n, t') :: cs') end

    fun plookup xs k = (case List.find (fn (j, _) => j = k) xs of
			   SOME (_, v) => v
			 | NONE => raise Fail ("Unbound variable " ^ A.ppty (A.TyVar k)))

    fun instantiate P (A.TyPoly x) =
	(plookup (!P) x handle _ => let val t = freshTy () in t before P := (x, t) :: !P end)
      | instantiate P (A.TyApp (t1, t2)) =
	let val t1' = instantiate P ( t1)
	    val t2' = instantiate P ( t2)
	in A.TyApp (t1', t2')
	end
      | instantiate P (A.TyArrow (t1, t2)) =
	let val t1' = instantiate P ( t1)
	    val t2' = instantiate P ( t2)
	in A.TyArrow (t1', t2')
	end
      | instantiate P (A.TyImpArr (t1, t2)) =
	let val t1' = instantiate P ( t1)
	    val t2' = instantiate P ( t2)
	in A.TyImpArr (t1', t2')
	end
      | instantiate P (A.TyLam (x, k, t)) = A.TyLam (x, k, instantiate P ( t))
      | instantiate P (A.TySig ds) = A.TySig (List.map (dinst P) ds)
      | instantiate _ t = t
    and dinst P (A.DValDec (x, t)) = A.DValDec (x, instantiate P t)
      | dinst _ d = d

    fun eval E (t as A.TyId x) =
	(case lookup x E of
	     CPair (TDef (_, t'), E') => eval E' t'
	   | CPair (TDec _, E') => (t, E)
	   | _ => raise Fail ("Identifier is not a type"))
      | eval E (t as A.TyApp (t1, t2)) =
	(case eval E t1 of
	     (A.TyLam (x, k, t'), E') => let val (t'', E'') = eval E t2
					 in (t', (x, CPair (TDef (k, t''), E'')) :: E')
					 end
	   | _ => (t, E))
      | eval E t = (t, E)

    (* caveat: PM should work as state in tyImp, and as an environment in sigImpl
     * due to universal quantifier scoping; this is now (hopefully) solved *)
    fun tyImp PM (t1, E1) (t2, E2) =
	(case (eval E1 t1, eval E2 t2) of
	     ((A.TyId x, _), (A.TyId y, _)) => x = y
	   | ((A.TyVar x, _), (A.TyVar y, _)) => x = y
	   | ((A.TyApp (t11, t12), E1), (A.TyApp (t21, t22), E2)) =>
	     tyImp PM (t11, E1) (t21, E2) andalso tyImp PM (t12, E1) (t22, E2)
	   | ((A.TyLam (x, k, t1), E1), (A.TyLam (y, k', t2), E2)) =>
	     let val v = freshTy ()
	     in k = k' andalso
		tyImp PM (t1, (x, CPair (TDef (k, v), E1)) :: E1)
		      (t2, (y, CPair (TDef (k, v), E2)) :: E2)
	     end
	   | ((A.TyArrow (t11, t12), E1), (A.TyArrow (t21, t22), E2)) =>
	     tyImp PM (t11, E1) (t21, E2) andalso tyImp PM (t12, E1) (t22, E2)
	   | ((A.TyLongName ([], x), E1), (A.TyLongName ([], y), E2)) =>
	     tyImp PM (A.TyId x, E1) (A.TyId y, E2)
	   | ((A.TyLongName (x::xs, t), E1), (A.TyLongName (y::ys, u), E2)) =>
	     (case (lookup x E1, lookup y E2) of
		  (CPair (VDec (tl as A.TySig dl), E1'), CPair (VDec (tr as A.TySig dr), E2')) =>
		  tyImp PM (tl, E1') (tr, E2') andalso
		  tyImp PM (A.TyLongName (xs, t), #1 (kindSig E1' dl))
			(A.TyLongName (ys, u), #1 (kindSig E2' dr))
		| _ => raise Fail "Ill kinded longname types or some shit")
	   | ((A.TySig ds, E1), (A.TySig es, E2)) => sigImpl PM (ds, E1) (es, E2)
	   | (c, (A.TyPoly x, _)) => (case List.find (fn (y, _) => x = y) (!PM) of
					  SOME (_, c') => tyImp PM c c'
					| NONE => true before (PM := (x, c) :: (!PM)))
	   | _ => raise Fail ("Types " ^ A.ppty t1 ^ " and " ^ A.ppty t2 ^ " not equal"))

    and sigImpl _ ([], E) _ = true
      | sigImpl PM (d :: ds, E) (es, F) =
	let val opm = !PM
	    fun consUntil x [] F = (NONE, F)
	      | consUntil x ((n, t) :: cs) F =
		if x = n then (SOME (VDec t, F), F) else consUntil x cs ((n, CPair (VDec t, F)) :: F)
	    fun evalUntil x [] F = NONE
	      | evalUntil x (A.DTyDef (y, t, SOME k) :: es) F =
		if x = y then SOME (TDef (k, t), F)
		else evalUntil x es ((y, CPair (TDef (k, t), F)) :: F)
	      | evalUntil x (A.DTyDec (y, k) :: es) F =
		if x = y then SOME (TDec k, F) else evalUntil x es ((y, CPair (TDec k, F)) :: F)
	      | evalUntil x (A.DValDec (y, t) :: es) F =
		if x = y then SOME (VDec t, F) else evalUntil x es ((y, CPair (VDec t, F)) :: F)
	      | evalUntil x (A.DData (y, k, cs) :: es) F =
		if x = y then SOME (TDec k, F)
		else (case consUntil x cs ((y, CPair (TDec k, F)) :: F) of
			  (NONE, F') => evalUntil x es F'
			| (SOME d, _) => SOME d)
	      | evalUntil x es F = raise Fail "Not kinded decs"
	in case d of
	       A.DTyDef (x, t1, ok) =>
	       (case evalUntil x es F of
		    SOME (TDef (k, t2), F') =>
		    tyImp PM (t1, E) (t2, F') andalso
		    (PM := opm; sigImpl PM (ds, (x, CPair (TDef (k, t1), E)) :: E) (es, F))
		  | _ => false)
	     | A.DTyDec (x, k) =>
	       (case evalUntil x es F of
		    SOME (TDec k', F') => if k = k' then
					      sigImpl PM (ds, (x, CPair (TDec k, E)) :: E) (es, F)
					  else false
		  | SOME (cl as (TDef (k', t), F')) => if k = k' then
							   sigImpl PM (ds, (x, CPair cl) :: E) (es, F)
						       else false
		  | _ => false)
	     | A.DValDec (x, t1) =>
	       (case evalUntil x es F of
		    SOME (VDec t2, F') => tyImp PM (instantiate (ref []) t1, E) (t2, F') andalso
					  (PM := opm;
					   sigImpl PM (ds, (x, CPair (VDec t1, E)) :: E) (es, F))
		  | _ => false)
	     | A.DData (x, k, cs) =>
	       let fun consImpl [] E = SOME E
		     | consImpl ((n, t1) :: cs) E =
		       (case evalUntil n es F of
			    SOME (VDec t2, F') => (print (n ^ " : " ^ (A.ppty t2) ^ "\n"); 
			    if tyImp PM (instantiate (ref []) t1, E) (t2, F')
			    then (PM := opm; consImpl cs ((n, CPair (VDec t1, E)) :: E)) else NONE)
			  | _ => NONE)
	       in case evalUntil x es F of
		      SOME (TDec k', F') =>
		      (print (x ^ " : " ^ (A.ppknd k') ^ "\n"); if k = k' then
						case consImpl cs ((x, CPair (TDec k, E)) :: E) of
						    SOME E' => (PM := opm; sigImpl PM (ds, E') (es, F))
						  | NONE => false
					    else false)
		    | _ => false
	       end
	end

    fun subt t1 t2 env = tyImp (ref []) (t1, env) (t2, env)

end

structure TCRes =
struct

  structure A = Ast
  structure T = TyEval

  (* Instance: a type for which it's defined, a list of parameters
   * (binding type to a name for resolved exp'n) and the resulting 
   * expression (a structure, possibly applied to the bound names in params) *)
  type inst = A.ty * (A.ty * A.name) list * A.exp

  (* instance database: a map from signature name into list of instances *)
  val DB = ref [] : (A.name * (inst list ref)) list ref

  fun matchInst t [] _ = raise Fail ("No matching instance for type " ^ Ast.ppty t)
    | matchInst t ((ti, ps, e) :: ts) env =
      let val P = ref []
	  val nti = T.instantiate P ti
      (* val nps = List.map (fn (t, n) => (T.instantiate P t, n)) ps
	  val env = List.foldl (fn ((t, n), env) => (n, resolve t) :: env) [] nps
	  fun substApps =*)
      in if T.subt t ti env then e else matchInst t ts env end

  and findInstance (x, t, env) =
      (case List.find (fn (y, _) => x = y) (!DB) of
           NONE => raise Fail ("Undefined signature " ^ x)
	 | SOME (_, insts) => matchInst t (!insts) env)

  and resolve (A.TyApp (A.TyId x, t), env) = findInstance (x, t, env)
    | resolve (t, env) = raise Fail ("Not an applied signature passed " ^ A.ppty t)

  fun checkInstance ins insts =
      print ("Warning: adding instances is unchecked; might cause inconsistency\n")

  (* Only primitive structures can be added as instances at this time *)
  fun addInstance (e, A.TyApp (A.TyId x, t)) =
      (case List.find (fn (y, _) => x = y) (!DB) of
	   SOME (_, insts) => insts := (t, [], e) :: (!insts)
	 | NONE => print ("No typeclass-like sig for type " ^ x ^ "; instance " ^
			  A.ppexp e ^ "not added\n"))
    | addInstance (e, t) = print ("Unable to add instance at type " ^ A.ppty t ^ " (yet!)\n")

  fun addSig (x, A.KArr (k, A.KSig)) =
      (case List.find (fn (y, _) => x = y) (!DB) of
	   NONE => (print ("Adding signature " ^ x ^ " to database\n"); DB := (x, ref []) :: (!DB))
	 | _ => raise Fail ("Signature " ^ x ^ " already declared"))
    | addSig _ = ()

end

structure HM =
struct
    structure A = Ast
    structure T = TyEval

    val freshTy = T.freshTy

    structure UF = IUnionFind

    val tysets : (A.id * (A.ty UF.set)) list ref = ref []

    fun getSet i = (case List.find (fn (i', _) => i = i') (!tysets) of
			SOME (_, s) => s
		      | NONE => let val ns = UF.new (A.TyVar i)
				in ns before tysets := (i, ns) :: (!tysets)
				end)
    fun lookup xs k = (case List.find (fn (j, _) => j = k) xs of
			   SOME (_, v) => v
			 | NONE => raise Fail ("Unbound variable " ^ A.ppty (A.TyVar k)))

    fun force (A.TyVar x) = UF.find (getSet x)
      | force t = t

    fun forceAll t =
	let fun aux (A.TyApp (t1, t2)) = A.TyApp (forceAll t1, forceAll t2)
	      | aux (A.TyArrow (t1, t2)) = A.TyArrow (forceAll t1, forceAll t2)
	      | aux t = t
	in aux (force t)
	end

    fun occursUF i t =
	(case t of
	     A.TyArrow (t1, t2) => occursUF i (force t1) orelse occursUF i (force t2)
	   | A.TyApp   (t1, t2) => occursUF i (force t1) orelse occursUF i (force t2)
	   | A.TyVar j => i = j
	   | _ => false)

    fun pickCanon _ (A.TyVar _, t) = t
      | pickCanon _ (t, A.TyVar _) = t
      | pickCanon D (t1, t2) =
	if T.subt t1 t2 D then t1
	else raise Fail ("Non-substitution union called on " ^ A.ppty t1 ^ " and " ^ A.ppty t2)

    fun solve D (A.TyVar x, A.TyVar y) =
	UF.union (pickCanon D) (getSet x) (getSet y)
      | solve D (A.TyVar x, tr) =
	if occursUF x tr then
	    raise Fail ("Circular type constraints: " ^ A.ppty (A.TyVar x) ^ " in " ^ A.ppty tr)
	else UF.union (pickCanon D) (getSet x) (UF.new tr)
      | solve D (tl, tr as A.TyVar x) = solve D (tr, tl)
      | solve D (t1 as A.TyId a, t2 as A.TyId b) =
        if T.subt t1 t2 D then () else raise Fail ("Type error: " ^ A.ppty t1 ^ " =/= " ^ A.ppty t2)
      | solve D (A.TyPoly a, A.TyPoly b) =
        if a = b then () else raise Fail ("Polymorphic unification")
      | solve D (A.TyApp (t1, c1), A.TyApp (t2, c2)) =
	(solve D (force t1, force t2);
	 solve D (force c1, force c2))
      | solve D (A.TyArrow (t1, t2), A.TyArrow (t3, t4)) =
        (solve D (force t1, force t3); solve D (force t2, force t4))
      | solve D (t1, t2) = raise Fail ("Type error: " ^ A.ppty t1 ^ " =/= " ^ A.ppty t2)

    fun solveList D xs = List.foldl (fn (c, ()) => solve D c) () xs

    fun mkPoly k t =
	let val src = ref 0
	    val map : (int * int) list ref = ref []
	    fun get x = (case List.find (fn (y, _) => x = y) (!map) of
			     NONE => let val k = !src
				     in k before (src := k + 1; map := (x, k) :: !map) end
			   | SOME (_, k) => k)
	    fun aux (t as A.TyVar x) = if k > x then t else A.TyPoly (get x)
	      | aux (A.TyApp (t1, t2)) = A.TyApp (aux (force t1), aux (force t2))
	      | aux (A.TyArrow (t1, t2)) = A.TyArrow (aux (force t1), aux (force t2))
	      | aux (A.TyImpArr (tc, tr)) = A.TyImpArr (aux (force tc), aux (force tr))
	      | aux t = t
	in aux t end

    fun getType (A.ValBind (_, SOME t, _)) = t
      | getType (A.ValRecBind (_, SOME t, _)) = t
      | getType (A.StructDec (_, _, SOME t)) = t
      | getType _ = raise Fail "Blah"

    fun resolve (tc, _) = (print ("Resolve: " ^ A.ppty (forceAll tc) ^ "\n"); A.VInt 1)

    fun solveImpsT (A.TyImpArr (tc, tr), e, env) =
	let val ec = TCRes.resolve (forceAll tc, env)
	in solveImpsT (tr, A.App (e, ec, SOME tr), env)
	end
      | solveImpsT (_, e, _) = e

    fun solveImps' (e as A.Fn (_, _, SOME t), env) = solveImpsT (t, e, env)
      | solveImps' (e as A.Var (_, SOME t), env) = solveImpsT (t, e, env)
      | solveImps' (A.App (e1, e2, SOME t), env) =
	solveImpsT (t, A.App (solveImps' (e1, env), solveImps' (e2, env), SOME t), env)
      | solveImps' (A.Let (ds, e, SOME t), env) =
	solveImpsT (t, A.Let (ds, solveImps' (e, env), SOME t), env)
      | solveImps' (A.Case (e, cs, SOME t), env) =
	let val cs' = map (fn (p, e) => (p, solveImps' (e, env))) cs
	in solveImpsT (t, A.Case (solveImps' (e, env), cs', SOME t), env)
	end
      | solveImps' (e, _) = e

    fun solveImps (A.Case (e, cs, SOME t), env) =
	let val cs' = map (fn (p, e) => (p, solveImps (e, env))) cs
	in A.Case (solveImps' (e, env), cs', SOME t) end
      | solveImps (A.App (e1, e2, SOME t), env) =
	A.App (solveImps' (e1, env), solveImps' (e2, env), SOME t)
      | solveImps (A.Let (ds, e, SOME t), env) = A.Let (ds, solveImps (e, env), SOME t)
      | solveImps (e, _) = e

    fun instExp P (A.Fn (a, e, NONE)) =
	let val a' = (case a of A.Expl (i, NONE) => a
			      | A.Expl (i, SOME t) => A.Expl (i, SOME (T.instantiate P t))
			      | A.Impl (i, t) => A.Impl (i, T.instantiate P t))
	    val e' = instExp P e
	in A.Fn (a', e', NONE) end
      | instExp P (A.App (e1, e2, NONE)) = A.App (instExp P e1, instExp P e2, NONE)
      | instExp P (A.Ann (e, t)) = A.Ann (instExp P e, T.instantiate P t)
      | instExp P (A.Struct (ds, NONE)) = A.Struct (ds, NONE)
      | instExp P (A.Case (e, cs, NONE)) =
	A.Case (instExp P e, map (fn (p, e) => (p, instExp P e)) cs, NONE)
      | instExp P (A.Let (ds, e, NONE)) = A.Let (ds, instExp P e, NONE)
      | instExp _ e = e

    fun evalIds env (t as A.TyId x) =
	(case T.lookup x env of
	     T.CPair (T.TDef (k, t'), env') => evalIds env' t'
	   | _ => t)
      | evalIds env (A.TyApp (t1, t2)) = A.TyApp (evalIds env t1, evalIds env t2)
      | evalIds env (A.TyArrow (t1, t2)) = A.TyArrow (evalIds env t1, evalIds env t2)
      | evalIds env (A.TyImpArr (t1, t2)) = A.TyImpArr (evalIds env t1, evalIds env t2)
      | evalIds _ t = t

    val PolyMap = ref [] : (int * A.ty) list ref

    fun tyinfExp env (A.Fn (A.Expl (i, ot), e, NONE)) =
	let val t = (case ot of
			 NONE => freshTy ()
		       | SOME t => t)
	    val (t', e') = tyinfExp ((i, T.CPair (T.VDec t, env)) :: env) e
	    val tx = A.TyArrow (t, t')
	in (tx, A.Fn (A.Expl (i, SOME t), e', SOME tx))
	end
      | tyinfExp env (A.Fn (A.Impl (i, t), e, NONE)) =
	let val (t', e') = tyinfExp ((i, T.CPair (T.VDec t, env)) :: env) e
	    val tx = A.TyImpArr (t, t')
	in (tx, A.Fn (A.Impl (i, t), e', SOME tx))
	end
      | tyinfExp env (A.App (e1, e2, NONE)) =
	let val (t1, e1') = tyinfExp env e1
	    (*val _ = print ("Left: " ^ A.ppexp e1' ^ ": " ^ A.ppty t1 ^ "\n")*)
	    val (t2, e2') = tyinfExp env e2
	    val tr = freshTy ()
	    fun dropImps t = (case t of A.TyImpArr (tc, tf) => dropImps (force tf)
				      | _ => t)
	    (*val _  = print ("Solving " ^ A.ppty (forceAll t1) ^ " ?= " ^ A.ppty (A.TyArrow (forceAll t2, tr)) ^ "\n")*)
	    val _  = solve env (dropImps (force t1), A.TyArrow (t2, tr))
	in (tr, A.App (e1', e2', SOME (forceAll tr)))
	end
      | tyinfExp env (A.Var (x, NONE)) =
	let val (T.CPair (T.VDec t, _)) = T.lookup x env
	    val t' = T.instantiate (ref []) (forceAll t)
	in (t', A.Var (x, SOME t'))
	end
      | tyinfExp env (A.Let (ds, e, NONE)) =
	let val (env', ds') = tyinfDecList env ds
	    val (t, e') = tyinfExp env' e
	in (t, A.Let (ds', e', SOME t))
	end
      | tyinfExp env (A.Ann (e, t)) =
	let val (t', e') = tyinfExp env e
	    val _ = solve env (force t', t)
	in (t, e')
	end
      (*| tyinfExp env (e as A.Literal t) = (t, e)*)
      | tyinfExp env (e as A.Struct (ds, NONE)) =
	let val (env', ds') = tyinfDecList env ds
	    fun toDecl (A.ValBind (x, SOME t, _)) = A.DValDec (x, t)
	      | toDecl (A.ValRecBind (x, SOME t, _)) = A.DValDec (x, t)
	      | toDecl (A.StructDec (x, d, SOME t)) = A.DValDec (x, t)
	      | toDecl (A.SigDec (x, SOME (y, k), t)) =
		A.DTyDef (x, A.TyLam (y, k, t), SOME (A.KArr (k, A.KSig)))
	      | toDecl (A.SigDec (x, NONE, t)) = A.DTyDef (x, t, SOME A.KSig)
	      | toDecl (A.TyDef args) = A.DTyDef args
	      | toDecl d = raise Fail "Untyped definition located"
	    val decls = List.map toDecl ds'
	in (A.TySig decls, A.Struct (ds', SOME (A.TySig decls)))
	end
      | tyinfExp env (e as A.LongName (xs, x, NONE)) =
	let fun step (x, env) = (case T.lookup x env of
				     T.CPair (T.VDec t, env') =>
				     (case T.eval env' t of
					  (t as A.TySig ds, env'') => #1 (T.kindSig env'' ds)
					| (t, _) => raise Fail ("Path not built of structures " ^ A.ppty t))
				   | _ => raise Fail "Very big fail")
	    val env' = List.foldl step env xs
	in case T.lookup x env' of
	       (* TODO: type scopes should be determined for t below *)
	       T.CPair (T.VDec t, env'') =>
	       (T.instantiate (ref []) (evalIds env'' t), A.LongName (xs, x, SOME t))
	     | _ => raise Fail "Not a value"
	end
      | tyinfExp env (A.Case (e, cs, NONE)) =
	let val (t, e') = tyinfExp env e
	    val rt = T.freshTy ()
	    val cs'  = List.map (fn c => checkCase env t c rt) cs
	in (rt, A.Case (e', cs', SOME rt))
	end
      | tyinfExp _ (e as A.VInt n)  = (A.TyInt, e)
      | tyinfExp env e =
        raise (Fail ("Unhandled expression in tyinfExp: " ^ A.ppexp e))

    and checkCase env ct ((ctor, args), e) rt =
	let fun foldArgs [] (A.TyArrow _) = raise Fail "Not enough arguments to a constructor"
	      | foldArgs [] t = ([], t)
	      | foldArgs (arg :: args) (A.TyArrow (ta, tr)) = let val (bt, t) = foldArgs args tr
							      in ((arg, ta) :: bt, t) end
	      | foldArgs (_ :: _) _ = raise Fail "Too many arguments to a constructor"
	    val (ctype, cenv) = (case T.lookup ctor env of
				     T.CPair (T.VDec t, env') => (T.instantiate (ref []) t, env')
				   | _ => raise Fail "Not a constructor")	    
	    val (bargs, nct) = foldArgs args ctype
	    val _ = solve env (force nct, force ct)
	    val env' = List.foldl (fn ((an, at), E) => (an, T.CPair (T.VDec at, E)) :: E) env bargs
	    val (nrt, e') = tyinfExp env' e
	    val _ = solve env (force nrt, force rt)
	in ((ctor, args), e')
	end

    and tyinfDec env (A.ValBind (i, NONE, e)) =
	let val k = !T.tyvarCounter
	    val (t, e') = tyinfExp env (instExp PolyMap e)
	    val e'' = solveImps (e', env)
	    val t' = mkPoly k (force t)
	in ((i, T.CPair (T.VDec t', env)) :: env, A.ValBind (i, SOME t', e''))
	end
      | tyinfDec env (A.ValRecBind (i, NONE, e)) =
	let val k = !T.tyvarCounter
	    val t = freshTy ()
	    val (t', e') = tyinfExp ((i, T.CPair (T.VDec t, env)) :: env) (instExp PolyMap e)
	    val _ = solve env (force t, force t')
	    val e'' = solveImps (e', env)
	    val t'' = mkPoly k (force t')
	in ((i, T.CPair (T.VDec t'', env)) :: env, A.ValRecBind (i, SOME t'', e''))
	end
      (* Code slightly duplicated between here and kinding of signature types *)
      | tyinfDec env (d as A.TyDef (x, t, NONE)) =
	let val kt as (k, t') = T.infKnd env t
	in ((x, T.CPair (T.TDef kt, env)) :: env, A.TyDef (x, t', SOME k))
	end
      | tyinfDec env (d as A.Data (x, k, cs)) =
	let val (env', cs') = T.evalCons ((x, T.CPair (T.TDec k, env)) :: env) cs
	in (env', A.Data (x, k, cs')) end
      | tyinfDec env (d as A.SigDec (x, ps, A.TySig ds)) =
	let val env' = A.foldO (fn (x, k) => (x, T.CPair (T.TDec k, env)) :: env) env ps
	    val (_, ds') = T.kindSig env' ds
	    val nt = A.foldO (fn (x, k) => A.TyLam (x, k, A.TySig ds'))
			     (A.TySig ds') ps
	    val kt = T.infKnd env nt
	    val _ = TCRes.addSig (x, #1 kt)
	in ((x, T.CPair (T.TDef kt, env)) :: env, A.SigDec (x, ps, A.TySig ds'))
	end
      | tyinfDec env (A.StructDec (x, e, NONE)) =
	let val (t, e') = tyinfExp env (instExp PolyMap e)
	    val (k, t') = T.infKnd env t
	in if k = A.KSig then ((x, T.CPair (T.VDec t', env)) :: env, A.StructDec (x, e', SOME t'))
	   else raise Fail "Blah"
	end
      | tyinfDec env (A.StructDec (x, e, SOME t)) =
	let val (t', e') = tyinfExp env (instExp PolyMap e)
	    val (k, nt) = T.infKnd env t'
	    val _  = if k = A.KSig then () else raise Fail "Blah"
	    val _  = TCRes.addInstance (A.Var (x, SOME t), t)
	in if T.subt t nt env then ((x, T.CPair (T.VDec t, env)) :: env, A.StructDec (x, e', SOME t))
	   else raise Fail ("Type mismatch")
	end
      | tyinfDec env d =
	raise Fail ("Unhandled declaration in tyinfDec: " ^ A.ppdef d)

    and tyinfDecList env [] = (env, [])
      | tyinfDecList env (d :: ds) =
	let val oldPM = !PolyMap
	    val (env', d') = tyinfDec env d
	    val _ = PolyMap := oldPM
	    val (env'', ds') = tyinfDecList env' ds
	in (env'', d' :: ds')
	end

end

