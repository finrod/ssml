structure Examples =
struct
    val a = 0
    val x = 1


    val example1
        = Ast.ValRecBind (a, NONE, 
            Ast.Fn (Ast.Expl (x, NONE), Ast.Var (x, NONE), NONE))

    val example2
      = Ast.ValBind (a, NONE, Ast.Fn (Ast.Expl (x, NONE), Ast.App (Ast.Var (x, NONE), Ast.Var (x, NONE), NONE), NONE))

    val example3
      = Ast.Let ([Ast.ValBind (a, NONE, Ast.Fn (Ast.Expl (x, NONE), Ast.Var (x, NONE), NONE))],
		 Ast.App (Ast.Var (a, NONE), Ast.Var (a, NONE), NONE), NONE)

    val example4
      = Ast.ValRecBind (a, NONE, Ast.Fn (Ast.Expl (x, NONE), Ast.App (Ast.Var (a, NONE), Ast.Var (x, NONE), NONE), NONE))

    val monad = 2
    val t = 3
    val return = 4
    val bind = 5

    val monadDecl
      = Ast.SigDec (monad, SOME (t, Ast.KArr (Ast.KTy, Ast.KTy)), Ast.TySig
				[Ast.ValDec (return, Ast.TyArrow (Ast.TyPoly x, Ast.TyApp (Ast.TyId t, Ast.TyPoly x))),
				 Ast.ValDec (bind, Ast.TyArrow (Ast.TyApp (Ast.TyId t, Ast.TyPoly a), Ast.TyArrow (Ast.TyArrow (Ast.TyPoly a, Ast.TyApp (Ast.TyId t, Ast.TyPoly x)), Ast.TyApp (Ast.TyId t, Ast.TyPoly x))))])

    val monadType = Ast.TyLam (t, Ast.KArr (Ast.KTy, Ast.KTy), Ast.TySig
				[Ast.ValDec (return, Ast.TyArrow (Ast.TyPoly x, Ast.TyApp (Ast.TyId t, Ast.TyPoly x))),
				 Ast.ValDec (bind, Ast.TyArrow (Ast.TyApp (Ast.TyId t, Ast.TyPoly a), Ast.TyArrow (Ast.TyArrow (Ast.TyPoly a, Ast.TyApp (Ast.TyId t, Ast.TyPoly x)), Ast.TyApp (Ast.TyId t, Ast.TyPoly x))))])

(*    fun run' e =
        let
            val s = HM.reset ()
            val e' = HM.constrDec e
        in
            (print "===========================================\n";
             print ("Pre-constr: " ^ (Ast.ppdec e) ^ "\n");
             HM.constrDec e;
             print ((HM.printConstr ()) ^ "\n");
             print ("Post-constr: " ^ (Ast.ppdec e') ^ "\n");
	     print (HM.printConstr' (HM.unify (!HM.constraints)) ^ "\n");
	     print ("Post-uni: " ^ (Ast.ppdec e') ^ "\n");
             print "===========================================\n";
             ())
         end

    fun run () = 
        (run' example1;
         ())*)
end


