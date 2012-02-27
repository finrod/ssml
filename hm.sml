structure HM =
struct
    structure A = Ast

    val tyvarCounter = ref 0
    fun freshTy () = 
        A.TyVar (!tyvarCounter) before tyvarCounter := (!tyvarCounter) + 1

    structure UF = IUnionFind

    (* Kinding of types. Req's an environment mapping tyids to kinds and possibly definitions *)
    fun infKnd D (A.TyId x) =
	(case List.find (fn (y, _, _) => x = y) D of
	     SOME (_, k, _) => k
	   | NONE => raise Fail ("Undefined type identifier t" ^ A.ppid x))
      | infKnd D (A.TyVar x) = A.KTy
      | infKnd D (A.TyPoly x) = A.KTy
      | infKnd D (t as A.TyApp (t1, t2)) =
	let val f = Fail ("Kind mismatch at type expression " ^ A.ppty t)
	in (case infKnd D t1 of
		A.KArr (k1, k2) => if infKnd D t2 = k1 then k2 else raise f
	      | _ => raise f)
	end
      | infKnd D (A.TySig ds) = A.KSig before chckSigKnd D ds
      | infKnd D (t as A.TyArrow (t1, t2)) =
	(case (infKnd D t1, infKnd D t2) of
	     (A.KSig, A.KTy) => A.KTy
	   | (A.KTy, A.KTy) => A.KTy
	   | (A.KSig, A.KSig) => A.KSig (* kind of types of functors (if I get it right, that is) *)
	   | _ => raise Fail ("Higher-order modules or some weird miskinding in " ^ A.ppty t))
      | infKnd D (A.TyLam (x, k, t)) =
	let val kb = infKnd ((x, k, NONE) :: D) t
	in (A.KArr (k, kb)) end

    and chckSigKnd D [] = ()
      | chckSigKnd D (A.TyDef (x, t) :: ds) =
	let val k = infKnd D t
	in chckSigKnd ((x, k, SOME t) :: D) ds
	end
      | chckSigKnd D (A.TyDec (x, k) :: ds) =
	chckSigKnd ((x, k, NONE) :: D) ds
      | chckSigKnd D ((d as A.ValDec (x, t)) :: ds) =
	if infKnd D t = A.KTy then chckSigKnd D ds
	else raise Fail ("Ill-kinded value declaration: " ^ A.ppdec d)
      | chckSigKnd D (d :: ds) =
	raise Fail ("Illegal construct in signature type: " ^ A.ppdec d)

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
	if t1 = t2 then t1
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
      | instantiate _ t = t

    fun tyinfExp D G (A.Fn (a, e, NONE)) =
	let val (t, i) = (case a of
			      A.Expl (i, NONE) => (freshTy (), i)
			    | A.Expl (i, SOME t) => (t, i)
			    | A.Impl (i, t) => (t, i))
	    val (t', e') = tyinfExp D ((i, t) :: G) e
	    val tx = A.TyArrow (t, t')
	    val a' = (case a of
			  A.Expl _ => A.Expl (i, SOME t)
			| _ => a)
	in (tx, A.Fn (a', e', SOME tx))
	end
      | tyinfExp D G (A.App (e1, e2, NONE)) =
	let val (t1, e1') = tyinfExp D G e1
	    val (t2, e2') = tyinfExp D G e2
	    val tr = freshTy ()
	    val _  = solve D (force t1, A.TyArrow (t2, tr))
	in (tr, A.App (e1', e2', SOME (forceAll tr)))
	end
      | tyinfExp D G (A.Var (x, NONE)) =
	let val t = instantiate (ref []) (lookup G x)
	in (t, A.Var (x, SOME t))
	end
      | tyinfExp D G (A.Let (ds, e, NONE)) =
	let val (D', G', ds') = tyinfDecList D G ds
	    val (t, e') = tyinfExp D' G' e
	in (t, A.Let (ds', e', SOME t))
	end
      | tyinfExp D G (A.Ann (e, t)) =
	let val (t', e') = tyinfExp D G e
	    val _ = solve (t', t)
	in (t, e')
	end
      | tyinfExp D G (e as A.Literal t) = (t, e)
      | tyinfExp D G e =
        raise (Fail ("Unhandled expression in tyinfExp: " ^ A.ppexp e))

    and tyinfDec D G (A.ValBind (i, NONE, e)) =
	let val k = !tyvarCounter
	    val (t, e') = tyinfExp D G e
	    val t' = mkPoly k (force t)
	in (D, (i, t') :: G, A.ValBind (i, SOME t', e'))
	end
      | tyinfDec D G (A.ValRecBind (i, NONE, e)) =
	let val k = !tyvarCounter
	    val t = freshTy ()
	    val (t', e') = tyinfExp D ((i, t) :: G) e
	    val _ = solve (t, t')
	    val t'' = mkPoly k (force t')
	in (D, (i, t'') :: G, A.ValRecBind (i, SOME t'', e'))
	end
      (* Code a slightly duplicated between here and kinding of signature types *)
      | tyinfDec D G (d as A.TyDec (x, k)) = ((x, k, NONE) :: D, G, d)
      | tyinfDec D G (d as A.TyDef (x, t)) =
	let val k = infKnd D t
	in ((x, k, SOME t) :: D, G, d)
	end
      | tyinfDec D G (d as A.ValDec (x, t)) =
	let val k = infKnd D t
	in if k = A.KTy then (D, (x, t) :: G, d)
	   else raise Fail ("Ill kinded value declaration " ^ A.ppdec d)
	end
      | tyinfDec D G (d as A.SigDec (x, ps, t as A.TySig ds)) =
	let val nt = A.foldO (fn (x, k) => A.TyLam (x, k, t)) t ps
	    val k = infKnd D nt
	in ((x, k, SOME nt) :: D, G, d)
	end
      | tyinfDec D G (d as A.Struct (ds, NONE)) =
	let val (D', G', ds') = tyinfDecList D G ds
	in (D, G, A.Struct (ds', SOME (A.TySig ds')))
	end
	(* TODO: get the proper signature type from the definitions *)
(*      | tyinfDec D G (d as A.StructDec (x, d, ot)) =
	let val (D', G', d') = tyinfDec D G d
	    val k = infKnd D' (getType d')*)
      | tyinfDec D G d =
	raise Fail ("Unhandled declaration in tyinfDec: " ^ A.ppdec d)

    and tyinfDecList D G ds =
	List.foldl (fn (d, (D, G, ds)) =>
		       let val (D', G', d') = tyinfDec D G d
		       in (D', G', d'::ds) end) (D, G, []) ds

 end

