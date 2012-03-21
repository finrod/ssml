structure TyEval =
struct
    structure A = Ast

    val tyvarCounter = ref 0
    fun freshTy () = 
        A.TyVar (!tyvarCounter) before tyvarCounter := (!tyvarCounter) + 1

    datatype cdecl   = TDef of A.knd * A.ty | TDec of A.knd | VDec of A.ty
    datatype closure = CPair of cdecl * (A.id * closure) list
    type environment = (A.id * closure) list

    fun lookup (x : Ast.id) (env : environment) =
	(case List.find (fn (y, _) => x = y) env of
	     SOME (_, t) => t
	   | NONE => raise Fail ("Undeclared identifier " ^ Ast.ppid x))

    (* Kinding of types. Req's an environment mapping tyids to kinds and possibly definitions *)
    fun infKnd E (A.TyId x) =
	(case lookup x E of
	     CPair (TDef (k, _), _) => k
	   | CPair (TDec k, _) => k
	   | _ => raise Fail ("Identifier is not a type"))
      | infKnd _ (A.TyVar x) = A.KTy
      | infKnd _ (A.TyPoly x) = A.KTy
      | infKnd E (t as A.TyApp (t1, t2)) =
	let val f = Fail ("Kind mismatch at type expression " ^ A.ppty t)
	in (case infKnd E t1 of
		A.KArr (k1, k2) => if infKnd E t2 = k1 then k2 else raise f
	      | _ => raise f)
	end
      | infKnd E (A.TySig ds) = (chckSigKnd E ds; A.KSig)
      | infKnd E (t as A.TyArrow (t1, t2)) =
	(case (infKnd E t1, infKnd E t2) of
	     (A.KSig, A.KTy) => A.KTy
	   | (A.KTy, A.KTy) => A.KTy
	   | (A.KSig, A.KSig) => A.KSig
	   (* kind of types of functors (if I get things right, that is) *)
	   | _ => raise Fail ("First-class modules or some weird miskinding in " ^ A.ppty t))
      | infKnd E (A.TyLam (x, k, t)) =
	let val kb = infKnd ((x, CPair (TDec k, E)) :: E) t
	in A.KArr (k, kb) end
      | infKnd E (A.TyLongName (xs, x)) =
	let fun aux (x, E) = (case lookup x E of
			       CPair (VDec (A.TySig ds), E') => chckSigKnd E' ds (* inefficient *)
			     | _ => raise Fail "Not structure declaration")
	    val E' = List.foldl aux E xs
	in case lookup x E' of
	       CPair (TDec k, _) => k
	     | CPair (TDef (k, _), _) => k
	     | _ => raise Fail "Not a type declaration"
	end
    and chckSigKnd E [] = E
      | chckSigKnd E (d :: ds) =
	(case d of
	     A.TyDef (x, t, ok) =>
	     let val k  = infKnd E t
		 val k' = A.foldO (fn x => if (x = k) then x else raise Fail ("Kind mismatch")) k ok
	     in chckSigKnd ((x, CPair (TDef (k', t), E)) :: E) ds
	     end
	   | A.TyDec (x, k) => chckSigKnd ((x, CPair (TDec k, E)) :: E) ds
	   | A.ValDec (x, t) => let val k = infKnd E t
				in if k = A.KTy orelse k = A.KSig
				   then chckSigKnd ((x, CPair (VDec t, E)) :: E) ds
				   else raise Fail "Not ground type for value"
				end
	   | _ => raise Fail ("Impossible"))

    fun eval E (t as A.TyId x) =
	(case lookup x E of
	     CPair (TDef (_, t'), E') => eval E' t'
	   | CPair (TDec _, E') => (t, E')
	   | _ => raise Fail ("Identifier is not a type"))
      | eval E (t as A.TyApp (t1, t2)) =
	(case eval E t1 of
	     (A.TyLam (x, k, t'), E') => let val (t'', E'') = eval E t2
					 in (t', (x, CPair (TDef (k, t''), E'')) :: E')
					 end
	   | _ => (t, E))
      | eval E t = (t, E)

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
		  tyImp PM (A.TyLongName (xs, t), chckSigKnd E1' dl) 
			(A.TyLongName (ys, u), chckSigKnd E2' dr)
		| _ => raise Fail "Ill kinded longname types or some shit")
	   | ((A.TySig ds, E1), (A.TySig es, E2)) => sigImpl PM (ds, E1) (es, E2)
	   | (c, (A.TyPoly x, _)) => (case List.find (fn (y, _) => x = y) (!PM) of
					  SOME (_, c') => tyImp PM c c'
					| NONE => true before (PM := (x, c) :: (!PM)))
	   | _ => raise Fail ("Types " ^ A.ppty t1 ^ " and " ^ A.ppty t2 ^ " not equal"))

    and sigImpl _ ([], E) _ = true
      | sigImpl PM (d :: ds, E) (es, F) =
	let fun evalUntil x [] F = NONE
	      | evalUntil x (A.TyDef (y, t, SOME k) :: es) F =
		if x = y then SOME (TDef (k, t), F)
		else evalUntil x es ((y, CPair (TDef (k, t), F)) :: F)
	      | evalUntil x (A.TyDec (y, k) :: es) F =
		if x = y then SOME (TDec k, F) else evalUntil x es ((y, CPair (TDec k, F)) :: F)
	      | evalUntil x (A.ValDec (y, t) :: es) F =
		if x = y then SOME (VDec t, F) else evalUntil x es ((y, CPair (VDec t, F)) :: F)
	      | evalUntil x es F = raise Fail "Not kinded defs"
	in case d of
	       A.TyDef (x, t1, ok) =>
	       (case evalUntil x es F of
		    SOME (TDef (k, t2), F') =>
		    tyImp PM (t1, E) (t2, F') andalso
		    sigImpl PM (ds, (x, CPair (TDef (k, t1), E)) :: E) (es, F)
		  | _ => false)
	     | A.TyDec (x, k) =>
	       (case evalUntil x es F of
		    SOME (TDec k', F') => sigImpl PM (ds, (x, CPair (TDec k, E)) :: E) (es, F)
		  | SOME (cl as (TDef (k', t), F')) => sigImpl PM (ds, (x, CPair cl) :: E) (es, F)
		  | _ => false)
	     | A.ValDec (x, t1) =>
	       (case evalUntil x es F of
		    SOME (VDec t2, F') => tyImp PM (t1, E) (t2, F') andalso
					  sigImpl PM (ds, (x, CPair (VDec t1, E)) :: E) (es, F)
		  | _ => false)
	     | _ => raise Fail "Impossible"
	end

    fun subt t1 t2 env = tyImp (ref []) (t1, env) (t2, env)

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
        if a = b then () else raise Fail ("Type error: " ^ A.ppty t1 ^ " =/= " ^ A.ppty t2)
      | solve D (A.TyPoly a, A.TyPoly b) =
        if a = b then () else raise Fail ("Polymorphic unification")
      | solve D (A.TyApp (t1, c1), A.TyApp (t2, c2)) =
	(solve D (force t1, force t2); solve D (force c1, force c2))
      | solve D (A.TyArrow (t1, t2), A.TyArrow (t3, t4)) =
        (solve D (force t1, force t3); solve D (force t2, force t4))
      | solve D (t1, t2) = raise Fail ("Type error: " ^ A.ppty t1 ^ " =/= " ^ A.ppty t2)

    fun solveList D xs = List.foldl (fn (c, ()) => solve D c) () xs

    fun mkPoly k (t as A.TyVar x) = if k > x then t else A.TyPoly x
      | mkPoly k (A.TyApp (t1, t2)) = A.TyApp (mkPoly k (force t1), mkPoly k (force t2))
      | mkPoly k (A.TyArrow (t1, t2)) = A.TyArrow (mkPoly k (force t1), mkPoly k (force t2))
      | mkPoly k t = t

    fun instantiate P (A.TyPoly x) =
	(lookup (!P) x handle _ => let val t = freshTy () in t before P := (x, t) :: !P end)
      | instantiate P (A.TyApp (t1, t2)) =
	let val t1' = instantiate P (force t1)
	    val t2' = instantiate P (force t2)
	in A.TyApp (t1', t2')
	end
      | instantiate P (A.TyArrow (t1, t2)) =
	let val t1' = instantiate P (force t1)
	    val t2' = instantiate P (force t2)
	in A.TyArrow (t1', t2')
	end
      | instantiate P (A.TyLam (x, k, t)) = A.TyLam (x, k, instantiate P (force t))
      | instantiate P (A.TySig ds) = A.TySig (List.map (dinst P) ds)
      | instantiate _ t = t
    and dinst P (A.ValDec (x, t)) = A.ValDec (x, instantiate P t)
      | dinst _ d = d

    fun getType (A.ValBind (_, SOME t, _)) = t
      | getType (A.ValRecBind (_, SOME t, _)) = t
      | getType (A.ValDec (_, t)) = t
      | getType (A.Struct (_, SOME t)) = t
      | getType (A.StructDec (_, _, SOME t)) = t
      | getType _ = raise Fail "Blah"

    fun tyinfExp env (A.Fn (a, e, NONE)) =
	let val (t, i) = (case a of
			      A.Expl (i, NONE) => (freshTy (), i)
			    | A.Expl (i, SOME t) => (t, i)
			    | A.Impl (i, t) => (t, i))
	    val (t', e') = tyinfExp ((i, T.CPair (T.VDec t, env)) :: env) e
	    val tx = A.TyArrow (t, t')
	    val a' = (case a of
			  A.Expl _ => A.Expl (i, SOME t)
			| _ => a)
	in (tx, A.Fn (a', e', SOME tx))
	end
      | tyinfExp env (A.App (e1, e2, NONE)) =
	let val (t1, e1') = tyinfExp env e1
	    val (t2, e2') = tyinfExp env e2
	    val tr = freshTy ()
	    val _  = solve env (force t1, A.TyArrow (t2, tr))
	in (tr, A.App (e1', e2', SOME (forceAll tr)))
	end
      | tyinfExp env (A.Var (x, NONE)) =
	let val (T.CPair (T.VDec t, _)) = T.lookup x env
	    val t' = instantiate (ref []) t
	in (t', A.Var (x, SOME t'))
	end
      | tyinfExp env (A.Let (ds, e, NONE)) =
	let val (env', ds') = tyinfDecList env ds
	    val (t, e') = tyinfExp env' e
	in (t, A.Let (ds', e', SOME t))
	end
      | tyinfExp env (A.Ann (e, t)) =
	let val (t', e') = tyinfExp env e
	    val _ = solve env (t', t)
	in (t, e')
	end
      | tyinfExp env (e as A.Literal t) = (t, e)
      | tyinfExp env (e as A.LongName (xs, x, NONE)) =
	let fun step (x, env) = (case T.lookup x env of
				     T.CPair (T.VDec (A.TySig ds), env') => T.chckSigKnd env' ds
				   | _ => raise Fail "Path not build of structures")
	    val env' = List.foldl step env xs
	in case T.lookup x env' of
	       (* TODO: type scopes should be determined for t below *)
	       T.CPair (T.VDec t, env'') => (t, A.LongName (xs, x, SOME t))
	     | _ => raise Fail "Not a value"
	end
      | tyinfExp env e =
        raise (Fail ("Unhandled expression in tyinfExp: " ^ A.ppexp e))

    and tyinfDec env (A.ValBind (i, NONE, e)) =
	let val k = !T.tyvarCounter
	    val (t, e') = tyinfExp env e
	    val t' = mkPoly k (force t)
	in ((i, T.CPair (T.VDec t', env)) :: env, A.ValBind (i, SOME t', e'))
	end
      | tyinfDec env (A.ValRecBind (i, NONE, e)) =
	let val k = !T.tyvarCounter
	    val t = freshTy ()
	    val (t', e') = tyinfExp ((i, T.CPair (T.VDec t, env)) :: env) e
	    val _ = solve env (t, t')
	    val t'' = mkPoly k (force t')
	in ((i, T.CPair (T.VDec t'', env)) :: env, A.ValRecBind (i, SOME t'', e'))
	end
      (* Code slightly duplicated between here and kinding of signature types *)
      | tyinfDec env (d as A.TyDec (x, k)) = ((x, T.CPair (T.TDec k, env)) :: env, d)
      | tyinfDec env (d as A.TyDef (x, t, NONE)) =
	let val k = T.infKnd env t
	in ((x, T.CPair (T.TDef (k, t), env)) :: env, A.TyDef (x, t, SOME k))
	end
      | tyinfDec env (d as A.ValDec (x, t)) =
	let val k = T.infKnd env t
	in if k = A.KTy orelse k = A.KSig then ((x, T.CPair (T.VDec t, env)) :: env, d)
	   else raise Fail ("Ill kinded value declaration " ^ A.ppdec d)
	end
      | tyinfDec env (d as A.SigDec (x, ps, A.TySig ds)) =
	let val env' = A.foldO (fn (x, k) => (x, T.CPair (T.TDec k, env)) :: env) env ps
	    val (_, ds') = tyinfDecList env' ds
	    val nt = A.foldO (fn (x, k) => A.TyLam (x, k, A.TySig ds'))
			     (A.TySig ds') ps
	    val k  = T.infKnd env nt
	in ((x, T.CPair (T.TDef (k, nt), env)) :: env, A.SigDec (x, ps, A.TySig ds'))
	end
      | tyinfDec env (d as A.Struct (ds, NONE)) =
	let val (env', ds') = tyinfDecList env ds
	    fun toDecl (A.ValBind (x, SOME t, _)) = A.ValDec (x, t)
	      | toDecl (A.ValRecBind (x, SOME t, _)) = A.ValDec (x, t)
	      | toDecl (A.StructDec (x, d, SOME t)) = A.ValDec (x, t)
	      | toDecl (A.SigDec (x, SOME (y, k), t)) =
		A.TyDef (x, A.TyLam (y, k, t), SOME (A.KArr (k, A.KSig)))
	      | toDecl (A.SigDec (x, NONE, t)) = A.TyDef (x, t, SOME A.KSig)
	      | toDecl d = d
	    val decls = List.map toDecl ds'
	in (env, A.Struct (ds', SOME (A.TySig decls)))
	end
      | tyinfDec env (A.StructDec (x, d, NONE)) =
	let val (env', d') = tyinfDec env d
	    val t = getType d'
	    val k = T.infKnd env' t
	in if k = A.KSig then ((x, T.CPair (T.VDec t, env')) :: env, A.StructDec (x, d', SOME t))
	   else raise Fail "Blah"
	end
      | tyinfDec env (A.StructDec (x, d, SOME t)) =
	let val (env', d') = tyinfDec env d
	    val t' = getType d'
	    val k  = T.infKnd env' t'
	    val _  = if k = A.KSig then () else raise Fail "Blah"
	in if T.subt t t' env then ((x, T.CPair (T.VDec t, env')) :: env, A.StructDec (x, d', SOME t))
	   else raise Fail ("Type mismatch")
	end
      | tyinfDec env d =
	raise Fail ("Unhandled declaration in tyinfDec: " ^ A.ppdec d)

    and tyinfDecList env ds =
	List.foldl (fn (d, (env, ds)) =>
		       let val (env', d') = tyinfDec env d
		       in (env', d'::ds) end) (env, []) ds

end
